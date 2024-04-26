open Mopsa
open Format
open Sig.Abstraction.Simplified_value
open Sig.Abstraction.Domain
open Universal.Ast
open Stubs.Ast
open Ast
open Bot_top

  (* from the source code of Ocaml 5.1 *)
  let pp_print_iter ?(pp_sep = pp_print_cut) iter pp_v ppf v =
    let is_first = ref true in
    let pp_v v =
      if !is_first then is_first := false else pp_sep ppf ();
      pp_v ppf v
    in
    iter pp_v v

  let pp_print_array ?(pp_sep = pp_print_cut) pp_v ppf v =
    pp_print_iter ~pp_sep Array.iter pp_v ppf v



(* module ArrayPower = *)
(*   struct *)
(*     include Framework.Lattices.Powerset.Make( *)
(*         struct *)
(*           type t = bool array *)

(*           let compare = Stdlib.compare *)

(*           let print = unformat (pp_print_array pp_print_bool) *)
(*         end *)
(*       ) *)


(*     let print printer abs = *)
(*       match abs with *)
(*       | Top.TOP -> pp_string printer "⊤" *)
(*       | Top.Nt s -> *)
(*          match s with *)
(*          |  _ -> printf "a faire %s" __LOC__ *)

(*   end *)

(* type _ avalue_kind += V_array_powersets : Jasmin.Wsize.wsize * int -> ArrayPower.t avalue_kind *)


(* let mk_array_powerset_query e typ size= Q_avalue (e, V_array_powersets(typ,size)) *)




(* let () = *)
(*   register_avalue { *)
(*     typ = (fun  (type a) next (avk: a avalue_kind) -> *)
(*       match avk with *)
(*         | V_array_powersets(typ,size) -> T_J_Array(typ, size) *)
(*         | _ -> next.pool_typ avk *)
(*       ); *)
(*     bottom = ( *)
(*       let f : type a. avalue_pool -> a avalue_kind -> a = *)
(*         fun next avk -> *)
(*           match avk with *)
(*           | V_array_powersets(typ,size) -> ArrayPower.bottom *)
(*           | _ -> next.pool_bottom avk in f *)
(*     ); *)
(*     top = ( *)
(*       let f : type a. avalue_pool -> a avalue_kind -> a = *)
(*         fun next avk -> *)
(*           match avk with *)
(*           | V_array_powersets(typ,size) -> ArrayPower.top *)
(*           | _ -> next.pool_top avk in f *)
(*     ); *)
(*     join = ( *)
(*       let f : type a. avalue_pool -> a avalue_kind -> a -> a -> a = *)
(*         fun next avk av1 av2 -> *)
(*           match avk with *)
(*           | V_array_powersets(typ,size) -> ArrayPower.join av1 av2 *)
(*           | _ -> next.pool_join avk av1 av2 in f *)
(*     ); *)
(*     meet = ( *)
(*       let f : type a. avalue_pool -> a avalue_kind -> a -> a -> a = *)
(*         fun next avk av1 av2 -> *)
(*           match avk with *)
(*           | V_array_powersets(typ,size) -> ArrayPower.meet av1 av2 *)
(*           | _ -> next.pool_meet avk av1 av2 in f *)
(*     ); *)
(*     print = ( *)
(*       let f : type a. avalue_pool -> a avalue_kind -> Format.formatter -> a -> unit = *)
(*         fun next avk fmt av -> *)
(*           match avk with *)
(*           | V_array_powersets(typ,size) -> (format ArrayPower.print) fmt av *)
(*           | _ -> next.pool_print avk fmt av in f *)
(*     ); *)

(*     compare = ( *)
(*       let f : type a b. avalue_pool -> a avalue_kind -> a -> b avalue_kind -> b -> int = *)
(*         fun next avk1 av1 avk2 av2 -> *)
(*           match avk1, avk2 with *)
(*           | V_array_powersets(typ,size), V_array_powersets(typ1,size2)-> ArrayPower.compare av1 av2 *)
(*           | _ -> next.pool_compare avk1 av1 avk2 av2 in f *)
(*     ); *)
(*   } *)


























(* module SimplifiedValue = struct *)

(*   let name = "jasmin.memory.array_initialized" *)

(*   include ArrayPower *)


(*   include GenValueId(struct *)
(*       type nonrec t = t *)
(*       let name = name *)
(*       let display = "array init" *)
(*     end) *)

(*   include DefaultValueFunctions *)


(*   let accept_type typ = *)
(*     Debug.debug ~channel:name "test du type %a" pp_typ typ; *)
(*     is_jasmin_array_type typ *)



(*   let constant c t : t= *)
(*     match c with *)
(*     | C_avalue(k,v) -> *)
(*       (match k with *)
(*       | V_array_powersets(_) -> v *)
(*       | _ -> top) *)
(*     | _ -> top *)



(*   let unop op t v tr = assert false *)
(*   let binop op t1 a1 t2 a2 tr = assert false *)

(*   let compare op b t1 a1 t2 a2 = *)
(*     assert false *)

(*   let avalue : type r. r avalue_kind -> t -> r option = *)
(*     fun aval a -> *)
(*     match aval with *)
(*     | V_array_powersets(_) -> Some a *)
(*     | _ -> None *)



(*   (\* let bottom = BOT *)

(*   let top = TOP *)

(*   let is_bottom b = b = bottom *)

(*   let is_top b = b = top *\) *)


(*   (\* let subset a1 a2 = *)
(*     Format.printf  "test icic : %s \n" __LOC__; *)
(*     flush_all (); *)
(*     match a1, a2 with *)
(*     | BOT, _ *)
(*     | _ , TOP -> true *)
(*     | _, BOT | TOP, _  -> false *)
(*     | Arr a1, Arr a2 -> *)
(*     if Array.length a1 <> Array.length a2 then false *)
(*     else Array.for_all2 (fun a1 a2 -> (a1 = a2) || a1 ) a1 a2 *)

(*   let join a1 a2 = *)
(*     Format.printf  "test icic : %s \n" __LOC__; *)
(*     flush_all (); *)
(*     match a1, a2 with *)
(*     | _ , TOP | TOP, _ -> TOP *)
(*     | BOT, BOT -> BOT *)
(*     | BOT, Arr a | Arr a, BOT -> Arr a *)
(*     | Arr a1, Arr a2 -> *)
(*     if Array.length a1 <> Array.length a2 then failwith "join for differents size not supported" *)
(*     else  Arr (Array.map2 (fun a1 a2 -> a1 && a2) a1 a2) *)

(*   let meet a1 a2 = *)
(*     Format.printf  "test icic : %s \n" __LOC__; *)
(*     flush_all (); *)
(*     match a1, a2 with *)
(*     | _ , BOT | BOT, _ -> BOT *)
(*     | TOP, TOP -> TOP *)
(*     | TOP, Arr a | Arr a, TOP -> Arr a *)
(*     | Arr a1, Arr a2 -> *)
(*     if Array.length a1 <> Array.length a2 then failwith "__FUNCTION__ for differents size not supported" *)
(*     else Arr (Array.map2 (fun a1 a2 -> a1 || a2) a1 a2) *)

(*   let widen ctx a1 a2 = *)
(*     join a1 a2 *)

(*   let constant c t = *)
(*     Format.printf  "test icic : %s \n" __LOC__; *)
(*     flush_all (); *)
(*     top *)

(*   let unop op t a tr = *)
(*     match op with *)
(*     | _ -> top *)

(*   let binop op t1 a1 t2 a2 tr = *)
(*     match op with *)
(*     | _ -> top *)



(*   let filter b t a = *)
(*     Format.printf  "test icic : %s \n" __LOC__; *)
(*     flush_all (); *)
(*     a *)

(*   let backward_unop op t a t r = *)
(*     Format.printf  "test icic : %s \n" __LOC__; *)
(*     flush_all (); *)
(*     bottom *)

(*   let backward_binop op t1 a1 t2 a2 tr r = *)
(*     Format.printf  "test icic : %s \n" __LOC__; *)
(*     flush_all (); *)
(*     bottom, bottom *)

(*   let compare op b t1 a1 t2 a2 = *)
(*     bottom, bottom *)


(*   let avalue _ _ = *)
(*     None *)




(*   let print printer a = *)
(*     match a with *)
(*     | Arr a -> unformat (pp_print_array pp_print_bool) printer a *)
(*     | TOP -> unformat (pp_print_string) printer "TOP" *)
(*     | BOT -> unformat (pp_print_string) printer "BOT" *\) *)


(* end *)


(* open Sig.Abstraction.Value *)

(* module Value = struct *)

(*   include SimplifiedValue *)

(*   module V = MakeValue(SimplifiedValue) *)

(*   include V *)

(*   let eval man e = *)
(*     match ekind e with *)
(*     | E_J_Laset(_) -> Debug.debug ~channel:name "ca eval"; V.eval man e *)
(*     | _ -> *)
(*     Format.printf "%s" __LOC__; *)
(*     flush_all (); *)
(*     V.eval man e *)


(*   let () = *)
(*     Format.printf "%s" __LOC__; *)
(*     flush_all (); *)

(* end *)


(* let () = *)
(*     Format.printf "%s" __LOC__; *)
(*     flush_all (); *)
(*   register_value_abstraction (module Value) *)


module ArrayPower =
  struct
    include Framework.Lattices.Powerset.Make(
        struct
          type t = bool array

          let compare = Stdlib.compare

          let print = unformat ~path:[Key "arraypower"] (pp_print_array pp_print_bool)
        end
      )


    let print printer abs =
      match abs with
      | Top.TOP -> pp_string ~path:[Key "arraypower"] printer "⊤"
      | Top.Nt s ->
         match s with
         |  _ -> printf "a faire %s" __LOC__

  end


module ArrayInit = struct

  type t = bool array with_bot_top

  let compare a1 a2 =
    match a1, a2 with
    | BOT, BOT | TOP, TOP -> 0
    | BOT, _ | _ , TOP -> -1
    | TOP, _ | _, BOT -> 1
    | Nbt a1, Nbt a2 ->
    Compare.compose [
      (fun () -> compare (Array.length a1) (Array.length a2));
      (fun () -> compare a1 a2);
    ]


  let subset a1 a2 =
    match a1, a2 with
    | BOT, _ | _, TOP -> true
    | _, BOT | TOP, _ -> false
    | Nbt a1, Nbt a2 ->
      Array.for_all2 (fun a1 a2 -> a2 || (a1 = a2)) a1 a2

  let join a1 a2 =
    match a1, a2 with
    | BOT, a | a, BOT -> a
    | TOP,_ | _, TOP -> TOP
    | Nbt a1, Nbt a2 ->
      Nbt (Array.map2 (||) a1 a2)


  let meet a1 a2 =
    match a1, a2 with
    | BOT, _ | _, BOT -> BOT
    | TOP, a | a, TOP -> a
    | Nbt a1, Nbt a2 ->
      Nbt (Array.map2 (&&) a1 a2)



  let print printer a =
    match a with
    | BOT ->
      pp_string printer "⊥"
    | TOP ->
      pp_string printer "⊤"
    | Nbt a ->
      unformat (pp_print_array pp_print_bool) printer a





end


module ArrayInitSet = Framework.Lattices.Powerset.Make(ArrayInit)

module Domain =
struct

  module Map = VarMap


  type t = ArrayInit.t Map.t


  include GenDomainId(struct
      type nonrec t = t
      let name = "jasmin.memory.array_init"

    end)


  let checks = []


  (* Lattice *)

  let bottom = Map.empty

  let top = Map.empty

  let is_bottom t = false

  (* Lattices operator *)

  let subset (a1:t) (a2:t) : bool =
    Map.for_all2 (fun k -> ArrayInit.subset) a1 a2


  let join a1 a2 =
    Map.map2o (fun k a -> a) (fun k a -> a) (fun k -> ArrayInit.join) a1 a2


  let meet a1 a2 =
    Map.map2o (fun k a -> BOT) (fun k a -> BOT) (fun k -> ArrayInit.meet) a1 a2

  let widen ctx a1 a2 = join a1 a2

  let merge pre (post1, effect1) (post2,effect2) =
    assert false


  (* Domain *)

  let init prog man flow =
    set_env T_cur Map.empty man flow



  let set_init a ?(a_start_index=0) b ?(b_start_index=0) len=
    let a = Array.copy a in
    for i = 0 to len - 1 do
      a.(a_start_index + i) <- b.(b_start_index + i)
    done;
    a



  let get_initialization expr man flow =
    let env = get_env T_cur man flow in





  let assign_arr lval expr range man flow =
    match ekind lval with
    | E_var (var,mode) ->
      let env = get_env T_cur man flow in
      let len = (get_array_type_len (vtyp var)) in
      if Map.mem var env then
        begin
          match Map.find var env with
          | Nbt a -> let new_a = set_init a (Array.init len (fun _ -> true)) len in
            set_env T_cur (Map.add var (Nbt new_a) env) man flow
            |> OptionExt.return
          | _ -> None
        end
      else let new_a = set_init (Array.init len (fun _ -> false)) 0 (Array.init len (fun _ -> true)) 0 len in
            set_env T_cur (Map.add var (Nbt new_a) env) man flow
            |> OptionExt.return
    | _ -> None




  let exec stmt man flow =
    match skind stmt with
    | S_J_declare(var) when is_jasmin_array_type @@ vtyp var ->
      let len = match vtyp var with T_J_Array(_,len) -> len | _ -> assert false in
      map_env T_cur (Map.add var (Nbt (Array.init len (fun _ -> false)))) man flow
      |> man.exec stmt ~route:(Below name)
      |> OptionExt.return

    | S_assign (lval,expr) when is_jasmin_array_type @@ etyp lval -> begin
      match assign_arr lval expr (srange stmt) man flow with
      | Some a -> Some (man.exec ~route:(Below name) stmt a)
      | None -> None
        end
    | _ -> None

  let eval expr man flow =
    match ekind expr with
    | _ -> None

  let ask query man flow = None


  let print_state printer t =
    pp_map ~path:[Key "array init"] pp_variable ArrayInit.print printer (Map.bindings t)

  let print_expr man flow printer expr =
    pp_string ~path:[Key "my expr"] printer "une expr"


end


let () =
  register_standard_domain (module Domain)
