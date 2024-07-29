open Mopsa
open Sig.Abstraction.Stacked
open Jasmin
open Universal.Ast
open Ast
open Array_common


let todo loc = panic ~loc "Oups todo"

module Present = struct
  type t = NON_EMPTY | MAYBE_EMPTY

  let equal = ( = )

  let compare a1 a2 =
    match (a1, a2) with
    | NON_EMPTY, NON_EMPTY | MAYBE_EMPTY, MAYBE_EMPTY -> 0
    | NON_EMPTY, MAYBE_EMPTY -> -1
    | MAYBE_EMPTY, NON_EMPTY -> 1

  let join a1 a2 =
    match (a1, a2) with
    | MAYBE_EMPTY, _ | _, MAYBE_EMPTY -> MAYBE_EMPTY
    | _ -> NON_EMPTY

  let meet a1 a2 =
    match (a1, a2) with
    | NON_EMPTY, _ | _, NON_EMPTY -> NON_EMPTY
    | _ -> MAYBE_EMPTY

  let fprint_present fmt t =
    match t with
    | NON_EMPTY -> Format.fprintf fmt "_"
    | MAYBE_EMPTY -> Format.fprintf fmt "?"

  let print_present printer t = unformat fprint_present printer t
end

type var_kind +=
  | (* Variable to represent elements of an array *)
      V_arr_element of
      var * int (* array * ID *)
  | (* Variable to represent bounds of an array *)
      V_arr_bounds of
      var * int (* array * ID *)

let () =
  register_var
    {
      compare =
        (fun next v1 v2 ->
          match (vkind v1, vkind v2) with
          | V_arr_element (a1, id1), V_arr_element (a2, id2)
          | V_arr_bounds (a1, id1), V_arr_bounds (a2, id2) ->
              Compare.compose
                [ (fun () -> compare a1 a2); (fun () -> compare id1 id2) ]
          | _ -> next v1 v2);
      print =
        (fun next fmt v ->
          match vkind v with
          | V_arr_element (arr, id) ->
              Format.fprintf fmt "element(%a)_%i" pp_var arr id
          | V_arr_bounds (arr, id) ->
              Format.fprintf fmt "bounds(%a)_%i" pp_var arr id
          | _ -> next fmt v);
    }

module ArraySegment = struct
  type t = { bounds : var list; segments : var list }

  let bottom = { bounds = []; segments = [] }
  let top = { bounds = []; segments = [] }
  let is_bottom _ = false

  (** Utils *)

  let new_id =
    let id = ref 0 in
    fun () ->
      incr id;
      !id

  let mkv_bounds varr =
    let id = new_id () in
    let name = Format.sprintf "%s_bounds_%i" (vname varr) id in
    mkv name (V_arr_bounds (varr, new_id ())) T_int

  let mkv_element varr =
    let id = new_id () in
    let name = Format.sprintf "%s_element_%i" (vname varr) id in
    mkv name (V_arr_element (varr, new_id ())) T_int

  (* By default f2 take the bound of the first segment *)
  (* Ensures : segment need to be the same otherwise an error can be raised*)
  let map2_segment f a1 a2 =
    { bounds = a1.bounds; segments = List.map2 f a1.segments a2.segments }

  (** Ensures : segment need to be the same otherwise an error can be raised*)
  let forall2_segment f a1 a2 = List.for_all2 f a1.segments a2.segments

  let panic_not_well_formed loc =
    panic ~loc "invariant on the structure of array segments is not respected"

  let iter f ?(flast = fun _ -> ()) arr =
    let rec aux bounds segments =
      match (bounds, segments) with
      | [ last_bounds ], [] -> flast last_bounds
      | b :: qb, s :: qs ->
          f b s;
          aux qb qs
      | _ ->
          Format.printf "debug iter";
          List.iter (fun a -> Format.printf "%a" pp_var a) bounds;
          List.iter (fun a -> Format.printf "%a" pp_var a) segments;
          panic_not_well_formed __LOC__
    in
    aux arr.bounds arr.segments

  let fold_left f flast acc_bounds acc_segments arr =
    let rec aux (acc_bounds, acc_segments) bounds segments =
      match (bounds, segments) with
      | [ last_bounds ], [] -> flast acc_bounds acc_segments last_bounds
      | b :: qb, s :: qs -> aux (f qb qs acc_bounds acc_segments) qb qs
      | _ -> panic_not_well_formed __LOC__
    in
    aux (acc_bounds, acc_segments) arr.bounds arr.segments

  (** Printers *)

  let fprint_array_segments fmt a =
    iter
      (fun bounds element ->
        Format.fprintf fmt "{%a} [%a] " pp_var bounds pp_var element)
      ~flast:(fun bounds -> Format.fprintf fmt "{%a}" pp_var bounds)
      a

  let print printer a = unformat fprint_array_segments printer a

  (* Useful command *)

  let mk_segment_array_element arr range man flow =
    let v = mkv_element arr in
    let ex = mk_add (mk_var v range) range in
    man.exec ex flow >>$ fun out flow -> Cases.return v flow

  let mk_convex_join expr1 expr2 range =
    mk_binop ~etyp:T_int expr1 O_convex_join expr2 range

  type e =
    | EQUAL of (var * Present.t) * var * bool
    | SOMETIMES_EQUAL
    | NOT_EQUAL

  let eq_to_pres = function
    | EQUAL _ -> panic "not supported"
    | SOMETIMES_EQUAL -> Present.MAYBE_EMPTY
    | NOT_EQUAL -> Present.NON_EMPTY

  (* Assignment to an array element *)
  let set va a index value ?(len = mk_one dummy_range) ?(range = dummy_range)
      man flow =
    let debug s = Debug.debug ~channel:"array set" s in
    let index_up = mk_binop index O_plus len range in
    match (a.bounds, a.segments) with
    | [ zero; b1; b2; bounds ], [ s1; s2; s3 ] ->
        assume
          (mk_eq (mk_var b1 range) index range)
          ~fthen:(fun flow ->
            (* b1 = i *)
            assume
              (mk_eq (mk_var b2 range) index_up range)
              ~fthen:(fun flow ->
                (* b2 = i + len *)
                man.exec (mk_assign (mk_var s2 range) value range) flow)
              ~felse:(fun flow ->
                (* b2 <> i + len*)
                assume
                  (mk_le (mk_var b2 range) index_up range)
                  ~fthen:(fun flow ->
                    (* b2 < i + len*)
                    man.exec (mk_assign (mk_var b2 range) index_up range) flow
                    >>% fun flow ->
                    man.exec (mk_assign (mk_var s2 range) value range) flow)
                  ~felse:(fun flow ->
                    (* b2 > i + len*)
                    assume
                      (mk_eq (mk_var b1 range) (mk_zero range) range)
                      ~fthen:(fun flow ->
                        man.exec
                          (mk_assign (mk_var b1 range) index_up range)
                          flow
                        >>% fun flow ->
                        man.exec (mk_assign (mk_var s1 range) value range) flow)
                      ~felse:(fun flow ->
                        man.exec
                          (mk_assign (mk_var b1 range) index_up range)
                          flow
                        >>% fun flow ->
                        man.exec
                          (mk_assign (mk_var s1 range)
                             (mk_convex_join (mk_var s1 range) value range)
                             range)
                          flow)
                      ~fboth:(fun _ _ ->
                        man.exec
                          (mk_assign (mk_var b1 range) index_up range)
                          flow
                        >>% fun flow ->
                        man.exec
                          (mk_assign (mk_var s1 range)
                             (mk_convex_join (mk_var s1 range) value range)
                             range)
                          flow)
                      man flow)
                  ~fboth:(fun flow -> todo __LOC__)
                  man flow)
              ~fboth:(fun _ _ ->
                (* b1 = i && b2 <> i + len*)
                assume
                  (mk_le index_up (mk_var b2 range) range)
                  ~fthen:(fun flow ->
                    (* i + len <= b2 *)
                    assume
                      (mk_eq (mk_var b1 range) (mk_zero range) range)
                      ~fthen:(fun flow ->
                        man.exec
                          (mk_assign (mk_var b1 range) index_up range)
                          flow
                        >>% fun flow ->
                        man.exec (mk_assign (mk_var s1 range) value range) flow)
                      ~felse:(fun flow ->
                        man.exec
                          (mk_assign (mk_var b1 range) index_up range)
                          flow
                        >>% fun flow ->
                        man.exec
                          (mk_assign (mk_var s1 range)
                             (mk_convex_join (mk_var s1 range) value range)
                             range)
                          flow)
                      ~fboth:(fun _ _ ->
                        man.exec
                          (mk_assign (mk_var b1 range) index_up range)
                          flow
                        >>% fun flow ->
                        man.exec
                          (mk_assign (mk_var s1 range)
                             (mk_convex_join (mk_var s1 range) value range)
                             range)
                          flow)
                      man flow)
                  ~felse:(fun flow -> (* b2 > i + len*)
                                      todo __LOC__)
                  ~fboth:(fun _ _ ->
                    (* b2 > i + len && b2 <= i + len*)
                    todo __LOC__)
                  man flow)
              man flow)
          ~felse:(fun flow ->
            (* b1 <> i *)
            assume
              (mk_lt (mk_var b1 range) index range) (* b1 < i *)
              ~fthen:(fun flow ->
                assume
                  (mk_eq (mk_var b2 range) index_up range)
                  ~fthen:(fun flow ->
                    (* b2 = i + len *)
                    assume
                      (mk_eq (mk_var b2 range) (mk_var bounds range) range)
                      ~fthen:(fun flow ->
                        man.exec (mk_assign (mk_var b2 range) index range) flow
                        >>% fun flow ->
                        man.exec (mk_assign (mk_var s3 range) value range) flow)
                      ~felse:(fun flow ->
                        man.exec (mk_assign (mk_var b2 range) index range) flow
                        >>% fun flow ->
                        man.exec
                          (mk_assign (mk_var s3 range)
                             (mk_convex_join (mk_var s3 range) value range)
                             range)
                          flow)
                      ~fboth:(fun _ _ ->
                        man.exec (mk_assign (mk_var b2 range) index range) flow
                        >>% fun flow ->
                        man.exec
                          (mk_assign (mk_var s3 range)
                             (mk_convex_join (mk_var s3 range) value range)
                             range)
                          flow)
                      man flow)
                  ~felse:(fun flow ->
                    (* b2 <> i + len*)
                    assume
                      (mk_le index_up (mk_var b2 range) range)
                      ~fthen:(fun flow ->
                        (* i + len < b2 *)
                        man.exec
                          (mk_assign (mk_var s2 range)
                             (mk_convex_join (mk_var s2 range) value range)
                             range)
                          flow)
                      ~felse:(fun flow ->
                        (* b2 < i + len*)
                        man.exec
                          (mk_assign (mk_var s3 range)
                             (mk_convex_join (mk_var s3 range) value range)
                             range)
                          flow)
                      ~fboth:(fun _ _ ->
                        assume
                          (mk_eq (mk_var b2 range) (mk_var bounds range) range)
                          ~fthen:(fun flow ->
                            todo __LOC__ (* raise warning over bounds*)
                          )
                          ~felse:(fun flow ->
                            man.exec
                              (mk_assign (mk_var b2 range) index_up range)
                              flow
                            >>% fun flow ->
                            man.exec
                              (mk_assign (mk_var s2 range)
                                 (mk_convex_join (mk_var s2 range) value range)
                                 range)
                              flow
                            >>% fun flow ->
                            man.exec
                              (mk_assign (mk_var s2 range)
                                 (mk_convex_join (mk_var s2 range)
                                    (mk_var s1 range) range)
                                 range)
                              flow)
                          ~fboth:(fun _ _ ->
                            todo __LOC__ (* raise warning over bounds *))
                          man flow)
                      man flow)
                  ~fboth:(fun _ _ ->
                    (* b2 = i + len && b2 <> i + len*)
                    assume
                      (mk_le index_up (mk_var b2 range) range)
                      ~fthen:(fun flow ->
                        (* i + len <= b2 *)
                        man.exec
                          (mk_assign (mk_var s2 range)
                             (mk_convex_join (mk_var s2 range) value range)
                             range)
                          flow)
                      ~felse:(fun flow ->
                        (* i + len > b2*)
                            man.exec (mk_assign (mk_var b2 range) index_up range) flow 
                            >>% man.exec (mk_assign (mk_var s2 range) (mk_convex_join (mk_var s2 range) value range) range)
                        )
                      ~fboth:(fun _ _ -> 
                            man.exec (mk_assign (mk_var b2 range) index_up range) flow 
                            >>% man.exec (mk_assign (mk_var s2 range) (mk_convex_join (mk_var s2 range) value range) range)
                            >>% man.exec (mk_assign (mk_var s2 range) (mk_convex_join (mk_var s2 range) (mk_var s3 range) range) range)
                      )
                      man flow)
                  man flow)
              ~felse:(fun flow ->
                (* b1 > i *)
                assume
                  (mk_le index_up (mk_var b1 range) range)
                  ~fthen:(fun flow ->
                    (* i + len <= b1 *)
                    man.exec
                      (mk_assign (mk_var s1 range)
                         (mk_convex_join (mk_var s1 range) value range)
                         range)
                      flow
                    )
                  ~felse:(fun flow ->
                    (* i + len > b1 *)
                    man.exec (mk_assign (mk_var b1 range) index_up range) flow
                    >>% man.exec (mk_assign (mk_var s1 range) (mk_convex_join (mk_var s1 range) value range) range)
                  )
                  ~fboth:(fun _ _ -> 
                    man.exec (mk_assign (mk_var b1 range) index_up range) flow
                    >>% man.exec (mk_assign (mk_var s1 range) (mk_convex_join (mk_var s1 range) value range) range)
                    >>% man.exec (mk_assign (mk_var s1 range) (mk_convex_join (mk_var s1 range) (mk_var s2 range) range) range)
                  )
                  man flow)
              ~fboth:(fun _ _ -> todo __LOC__)
              man flow)
          ~fboth:(fun _ _ -> todo __LOC__)
          man flow
    | _ -> panic_not_well_formed __LOC__

  let get arr index ?(len = mk_one dummy_range) ?(range = dummy_range) man flow
      =
    let index_plus = mk_binop index O_plus len range in
    let rec start_region bounds segments flow =
      match (bounds, segments) with
      | b :: b2 :: qbounds, s :: seg ->
          assume
            (mk_lt index (mk_var b2 range) range)
            ~fthen:(fun flow ->
              end_region (b2 :: qbounds) segments flow >>$ fun out flow ->
              Cases.return (mk_convex_join (mk_var s range) out range) flow)
            ~felse:(fun flow -> start_region (b2 :: qbounds) seg flow)
            ~fboth:(fun _ _ ->
              end_region (b2 :: qbounds) seg flow >>$ fun out flow ->
              Cases.return (mk_convex_join (mk_var s range) out range) flow)
            man flow
      | _ -> todo __LOC__
    and end_region bounds segments flow =
      match (bounds, segments) with
      | b1 :: qbounds, s :: seg ->
          assume
            (mk_le index_plus (mk_var b1 range) range) (* i + len  <= b*)
            ~fthen:(fun flow -> Cases.return (mk_var s range) flow)
            ~felse:(fun flow ->
              end_region qbounds seg flow >>$ fun expr flow ->
              Cases.return (mk_convex_join expr (mk_var s range) range) flow)
            ~fboth:(fun _ flow ->
              end_region qbounds seg flow >>$ fun expr flow ->
              Cases.return (mk_convex_join expr (mk_var s range) range) flow)
            man flow
      | _ -> todo __LOC__
    in
    start_region arr.bounds arr.segments flow >>$ fun out flow ->
    man.eval out flow

  let is_bottom _ = false

  let subset e1 e2 =
    true

  let join e1 e2 =
    todo __LOC__

  let meet e1 e2 =
    todo __LOC__

  let widen ctx e1 e2 =
    todo __LOC__

  let merge pre (a, e) (a', e') =
    panic ~loc:__LOC__ "Merge is impossible with ArraySegment"

  let add_arr var typ range man flow =
    match typ with
    | T_J_Array (wsize, len) ->
        let zero = mkv_bounds var in
        let zero_move = mkv_bounds var in
        let len_move = mkv_bounds var in
        let len_var = mkv_bounds var in
        man.exec
          (mk_assign (mk_var zero range) (mk_zero ~typ:T_int range) range)
          flow
        >>% fun flow ->
        man.exec
          (mk_assign (mk_var zero_move range) (mk_zero ~typ:T_int range) range)
          flow
        >>% fun flow ->
        man.exec
          (mk_assign (mk_var len_move range)
             (mk_int len ~typ:T_int range)
             range)
          flow
        >>% fun flow ->
        man.exec
          (mk_assign (mk_var len_var range) (mk_int len ~typ:T_int range) range)
          flow
        >>% fun flow ->
        mk_segment_array_element var range man flow >>$ fun element1 flow ->
        mk_segment_array_element var range man flow >>$ fun element2 flow ->
        mk_segment_array_element var range man flow >>$ fun element3 flow ->
        Cases.return
          {
            bounds = [ zero; zero_move; len_move; len_var ];
            segments = [ element1; element2; element3 ];
          }
          flow
    | _ -> panic "cannot add something that is not an jasmin array"
end

module Domain = struct
  (* type t = ArraySegment.t *)
  module Arrays = Framework.Lattices.Partial_map.Make (Var) (ArraySegment)

  type t = Arrays.t

  include GenDomainId (struct
    type nonrec t = t

    let name = "jasmin.array.segments3"
  end)

  let checks = []
  let bottom = Arrays.bottom
  let top = Arrays.top
  let is_bottom = Arrays.is_bottom
  let init prog man flow = set_env T_cur Arrays.empty man flow

  (* Unificator *)
  (* A really important algorithm to be able to do classic operation after *)
  let subset man ctx (a1, s) (a2, s') =
    (* let (s,s') = do_op man ctx ArraySegment.Element.bottom ArraySegment.Element.top (a1,s) (a2,s') in *)
    let r =
      Arrays.fold2zo
        (fun _ _ _ -> false)
        (fun _ _ out -> out)
        (fun _ a1 a2 out -> if out then ArraySegment.subset a1 a2 else out)
        a1 a2 true
    in
    Debug.debug ~channel:name "subset %a %a \b is_sub : %b"
      (Print.format Arrays.print)
      a1
      (Print.format Arrays.print)
      a2 r;
    (r, s, s')

  let join man ctx ((a1, s): Arrays.t * 'a) ((a2, s'): Arrays.t * 'b) =
    match (a1, a2) with
    | BOT, a2 -> (a2, s, s')
    | a1, BOT -> (a1, s, s')
    | a1, a2 ->
       (a2, s, s')

  let meet man ctx (a1, s) (a2, s') =
    (* let (s,s') = do_op man ctx (todo __LOC__) (todo __LOC__) (a1,s) (a2,s') in *)
    (* Debug.debug ~channel:name "meet %a %a" (Print.format Arrays.print) a1 (Print.format Arrays.print) a2; *)
    (* (Arrays.meet a1 a2, s, s') *)
    todo __LOC__

  let widen man ctx (a1, s) (a2, s') =
   let a1, a2, a3 = join man ctx (a1, s) (a1, s') in
    (a1, a2, a3, true)

  let merge _ _ =
    Debug.debug ~channel:name "why ?";
    assert false

  (** { Transfert functions } *)

  (** *********************** *)

  let exec stmt man flow =
    let range = srange stmt in
    match skind stmt with
    | S_add ({ ekind = E_var (v, mode) } as expr)
      when is_jasmin_array_type @@ etyp expr ->
        Debug.debug ~channel:name "add %a" pp_var v;
        ArraySegment.add_arr v (etyp expr) (srange stmt) man flow
        >>$? fun arr flow ->
        map_env T_cur (Arrays.add v arr) man flow
        |> Post.return |> OptionExt.return
    | S_remove ({ ekind = E_var (v, mode) } as expr)
      when is_jasmin_array_type @@ etyp expr ->
        let arrays = get_env T_cur man flow in
        set_env T_cur (Arrays.remove v arrays) man flow
        |> Post.return |> OptionExt.return
    | S_assign ({ ekind = E_var (arr, _) as lval }, { ekind = E_J_arr_init len })
      ->
        let arr_abs = Arrays.find arr (get_env T_cur man flow) in
        let rec iter bounds segments flow =
          match (bounds, segments) with
          | [ b1; b2 ], [ s ] ->
              man.exec (mk_forget (mk_var s range) range) flow >>%? fun flow ->
              map_env T_cur (Arrays.add arr { bounds; segments }) man flow
              |> Post.return |> OptionExt.return
          | bound :: b2 :: qbounds, s :: seg :: qseg ->
              man.exec (mk_forget (mk_var seg range) range) flow
              >>%? fun flow ->
              man.exec (mk_forget (mk_var b2 range) range) flow >>%? fun flow ->
              iter (bound :: qbounds) (s :: qseg) flow
          | _ -> todo __LOC__
        in
        iter arr_abs.bounds arr_abs.segments flow
    (* a = b *)
    | S_assign (({ ekind = E_var _ } as lval), expr)
      when is_jasmin_array_type @@ etyp lval ->
        todo __LOC__
    | S_assign ({ ekind = E_J_Laset (access, wsize, var, index) }, expr) ->
        man.eval expr flow >>$? fun e flow ->
        let range = srange stmt in
        if is_bottom (get_env T_cur man flow) then
          Cases.empty flow |> OptionExt.return
        else
          let arr = Arrays.find var (get_env T_cur man flow) in
          ArraySegment.set var arr index e ~range man flow >>%? fun flow ->
          flow |> Post.return |> OptionExt.return
    | S_assume
        {
          ekind =
            E_stub_J_abstract
              (Init_array, [ { ekind = E_var (arr, _) }; pos; len ]);
        } ->
        let range = srange stmt in
        let arr_abs = Arrays.find arr (get_env T_cur man flow) in
        ArraySegment.set arr arr_abs pos ~len
          (mk_constant ~etyp:T_int Integer.Initialized.(C_init Init.INIT) range)
          ~range man flow
        >>%? fun flow ->
        flow |> Post.return |> OptionExt.return
    | _ -> None

  let eval expr man flow =
    match ekind expr with
    | E_J_get (arr_access, wsize, var, index) ->
        let range = erange expr in
        if is_bottom (get_env T_cur man flow) then
          Cases.empty flow |> OptionExt.return
        else
          let arr = Arrays.find var (get_env T_cur man flow) in
         ArraySegment.get arr index ~range man flow |> OptionExt.return
    | E_stub_J_abstract (Init_array, [ { ekind = E_var (arr, _) }; pos; len ])
      ->
       let range = erange expr in
        let arr_abs = Arrays.find arr (get_env T_cur man flow) in
        ArraySegment.set arr arr_abs pos ~len
          (mk_constant ~etyp:T_int Integer.Initialized.(C_init Init.INIT) range)
          ~range man flow
        >>%? fun flow ->
       flow |> Cases.return (mk_true range) |> OptionExt.return
    | _ -> None

  (** { Communication handlers } *)

  (** ************************** *)

  let ask query man flow = None

  (** { Pretty printer } *)

  (** ****************** *)

  let print_state printer a =
    pprint printer ~path:[ Key "arrays" ] (pbox Arrays.print a)

  let print_expr man flow printer exp = ()
end

let () = register_stacked_domain (module Domain)
