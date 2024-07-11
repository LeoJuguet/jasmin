open Mopsa
open Sig.Abstraction.Stacked
open Jasmin
open Universal.Ast
open Ast


(* This is inspired by the paper : *)
(* Patrick Cousot, Radhia Cousot, and Francesco Logozzo. 2011. A parametric *)
(* segmentation functor for fully automatic and scalable array content *)
(* analysis. SIGPLAN Not. 46, 1 (January 2011), 105–118. *)
(* https://doi.org/10.1145/1925844.1926399 *)


let todo loc = panic ~loc "Oups todo"

module Present = struct
    type t = NON_EMPTY | MAYBE_EMPTY

    let equal = (=)

    let compare a1 a2 = match a1, a2 with
      | NON_EMPTY, NON_EMPTY
      | MAYBE_EMPTY, MAYBE_EMPTY -> 0
      | NON_EMPTY, MAYBE_EMPTY -> -1
      | MAYBE_EMPTY, NON_EMPTY -> 1

    let join a1 a2 = match a1, a2 with
      | MAYBE_EMPTY, _ | _, MAYBE_EMPTY -> MAYBE_EMPTY
      | _ -> NON_EMPTY

    let meet a1 a2 = match a1, a2 with
      | NON_EMPTY,_ | _, NON_EMPTY -> NON_EMPTY
      | _ -> MAYBE_EMPTY

    let fprint_present fmt t =
      match t with
      | NON_EMPTY -> Format.fprintf fmt "_"
      | MAYBE_EMPTY -> Format.fprintf fmt "?"

    let print_present printer t =
      unformat fprint_present printer t
end

type var_kind += 
  (* Variable to represent elements of an array *)
  | V_arr_element of var * int (* array * ID *)
  (* Variable to represent bounds of an array *)
  | V_arr_bounds of var * int (* array * ID *)

let () =
  register_var {
    compare = (fun next v1 v2 -> match vkind v1,vkind v2 with
      | (V_arr_element (a1,id1)), (V_arr_element (a2,id2)) 
      | (V_arr_bounds (a1,id1)), (V_arr_bounds (a2,id2)) ->
        Compare.compose [
          (fun () -> compare a1 a2);
          (fun () -> compare id1 id2);
        ]
      | _ -> next v1 v2
    );
    print = (fun next fmt v -> match vkind v with
      | V_arr_element (arr, id) -> 
        Format.fprintf fmt "element(%a)_%i" pp_var arr id
      | V_arr_bounds (arr, id) -> 
        Format.fprintf fmt "bounds(%a)_%i" pp_var arr id
      | _ -> next fmt v
    )
  }


module ArraySegment = struct


    module Element = Framework.Lattices.Powerset.Make(Var)

    module Bounds = Framework.Lattices.Powerset.Make(Var)
  
    type t = {
          bounds : (Bounds.t * Present.t) ListExt.t;
          segments : Element.t ListExt.t;
      }

    let bottom = {
          bounds = [];
          segments = [];
      }

    let top = {
        bounds = [(Bounds.top, Present.MAYBE_EMPTY)];
        segments = []      
      }

    let is_bottom _ = false


    (** Utils *)

    let new_id =
      let id = ref 0 in
      fun () -> incr id; !id

    let mkv_bounds varr =
      let id = new_id () in
      let name = Format.sprintf "%s_bounds_%i" (vname varr) id in
      mkv name (V_arr_bounds (varr, new_id ())) T_int

    let mkv_element varr =
      let id = new_id () in
      let name = Format.sprintf "%s_element_%i" (vname varr) id in
      mkv name (V_arr_element (varr, new_id ())) T_int

    (** By default f2 take the bound of the first segment *)
    (** Ensures : segment need to be the same otherwise an error can be raised*)
    let map2_segment f a1 a2 =
      {
        bounds = a1.bounds;
        segments = List.map2 f a1.segments a2.segments;
      }

    (** Ensures : segment need to be the same otherwise an error can be raised*)
    let forall2_segment f a1 a2 =
      List.for_all2 f a1.segments a2.segments

    let panic_not_well_formed loc =
      panic ~loc "invariant on the structure of array segments is not respected"

    let iter f ?(flast = fun _ -> ()) arr =
      let rec aux bounds segments = match bounds, segments with
      | [last_bounds], [] -> flast last_bounds
      | b::qb, s::qs -> f b s; aux qb qs
      | _ -> panic_not_well_formed __LOC__
    in aux arr.bounds arr.segments

    let fold_left f flast acc_bounds acc_segments arr =
      let rec aux (acc_bounds, acc_segments) bounds segments  = match bounds, segments with
      | [last_bounds], [] -> flast acc_bounds acc_segments last_bounds
      | b::qb, s::qs -> aux (f qb qs acc_bounds acc_segments) qb qs 
      | _ -> panic_not_well_formed __LOC__
    in aux (acc_bounds, acc_segments) arr.bounds arr.segments


    (** Printers *)

    let fprint_array_segments fmt a =
      iter (fun (bounds, present) element ->
            Format.fprintf fmt "[%a]%a %a " (format Bounds.print) bounds Present.fprint_present present (format Element.print) element 
          )
          ~flast:(fun (bounds, present) ->
            Format.fprintf fmt "[%a]%a" (format Bounds.print) bounds Present.fprint_present present
          )
          a

    let print printer a =
      unformat  fprint_array_segments printer a


    let get_bounds bounds =
      let b = Bounds.choose bounds in
      mk_var b dummy_range
    

    (* Useful command *)

    let get a index ?(len= mk_one dummy_range) ?(range = dummy_range) man flow = 
      let index_plus = mk_binop index O_plus len range in
  
      let rec parcours bounds segments ?(is_lower = true) acc flow = match bounds, segments with
      | (i1,p1)::bounds, s::seg when is_lower -> 
        let fthen = (fun flow -> 
          parcours bounds seg (Element.union acc s) ~is_lower:false flow
        )
        in
        assume (mk_le (get_bounds i1) index range) 
          ~fthen
          ~felse:(fun flow -> 
            parcours bounds seg acc flow 
          )
          ~fboth:(fun tflow _ -> fthen tflow )
        man flow
      | (i1,p1)::bounds, s::seg when not is_lower -> 
        let fthen = (fun flow -> 
          parcours bounds seg (Element.union acc s) ~is_lower:false flow        
        )
        in
        assume (mk_le index_plus (get_bounds i1) range) 
          ~fthen
          ~felse:(fun flow -> 
            Cases.return acc flow
          )
          ~fboth:(fun tflow _ -> fthen tflow )
        man flow
      | _ -> 
        (* Overflow *)
        Flow.raise_alarm (mk_alarm (todo __LOC__) (Flow.get_callstack flow) range) man.lattice flow 
        |> Cases.empty 
      in 
      parcours a.bounds a.segments Element.empty flow 

    let mk_segment_array_index_bounds arr i range man flow = 
      match ekind i with
      | E_var (v,mode) -> Cases.return (Bounds.singleton v) flow
      | _ ->
        let v = mkv_bounds arr in
        let ex = mk_assign (mk_var v range) i range in 
        man.exec ex flow >>$ fun out flow -> 
        Cases.return (Bounds.singleton v) flow

    let mk_segment_array_element arr range man flow = 
        let v = mkv_element arr in
        let ex = mk_add (mk_var v range) range in 
        man.exec ex flow >>$ fun out flow -> 
        Cases.return (Element.singleton v) flow

    
    (* Assignment to an array element *)
    let set va a index value ?(len=mk_one dummy_range) ?(range = dummy_range) man flow =
      (* let v = mkv_element va in *)
      (* let ex = mk_assign (mk_var v range) value range in *)
      (* man.exec ex flow >>% fun flow -> *) 
      (* mk_segment_array_element va range man flow >>$ fun var_val flow -> *)
      (* mk_segment_array_index_bounds va index range man flow >>$ fun i flow -> *)
      let index_up = mk_binop index O_plus len range in
      (* mk_segment_array_index_bounds va index_up range man flow >>$ fun i_plus flow -> *)
      
      let rec parcours bounds segments ?(is_lower = true) acc flow = match bounds, segments with
      | (i1,p1)::bounds, s::seg when is_lower -> 
        Debug.debug ~channel:"set" "add is_lower";
        let fthen = (fun flow -> 
          Debug.debug ~channel:"set" "add is_lower fthen";
          parcours bounds seg (Element.union acc s) ~is_lower:false flow >>$ fun (bounds,seg) flow ->
          Cases.return ((i1,p1)::bounds, seg) flow
        )
        in
        (* i1 <= index *)
        assume (mk_le (get_bounds i1) index range) 
          ~fthen
          ~felse:(fun flow -> 
            Debug.debug ~channel:"set" "add is_lower felse";
            parcours bounds seg acc flow >>$ fun (bounds, seg) flow ->
            Cases.return ((i1,p1)::bounds, s::seg) flow
          )
          ~fboth:(fun tflow _ ->
            Debug.debug ~channel:"set" "add is_lower fboth";
            fthen tflow 
          )
        man flow
      | (i1,p1)::bounds, s::seg when not is_lower -> 
        Debug.debug ~channel:"set" "add not is_lower";
        let felse = (fun flow ->
          Debug.debug ~channel:"set" "add not is lower fthen";
          parcours bounds seg (Element.union acc s) ~is_lower:false flow        
        )
        in
        (* index <= bounds *)
        assume (mk_le index_up (get_bounds i1) range) 
          ~felse
          ~fthen:(fun flow -> 
            Debug.debug ~channel:"set" "add not is_lower felse";
            let v = mkv_element va in
            let ex = mk_assign (mk_var v range) value range in
            man.exec ex flow >>% fun flow -> 
            mk_segment_array_index_bounds va index range man flow >>$ fun i flow ->
            mk_segment_array_index_bounds va index_up range man flow >>$ fun i_plus flow ->
            let vunion = mkv_element va in
            man.exec (mk_assign (mk_var vunion range) (mk_var (Element.choose acc) range) range) flow >>% fun  flow ->
            let flow = Element.fold
            (fun e flow ->
              let expr = mk_binop ~etyp:T_int (mk_var vunion range) O_convex_join (mk_var e range) range in
              man.exec (mk_assign (mk_var vunion range) expr range) flow
              |> post_to_flow man
            ) acc flow  
            in
            let acc = Element.singleton vunion in
            Cases.return (
            (i,Present.MAYBE_EMPTY)::(i_plus, Present.MAYBE_EMPTY)::(i1,p1)::bounds, 
            acc::                (Element.singleton v)         ::acc     ::s     ::seg) flow
          )
          ~fboth:(fun tflow _ -> felse tflow )
        man flow
      | [(last_bounds,present)] as bounds, [] ->
        Debug.debug ~channel:"set" "last bounds";
        let fthen = (fun flow ->
            let v = mkv_element va in
            let ex = mk_assign (mk_var v range) value range in
             man.exec ex flow >>% fun flow -> 
            mk_segment_array_index_bounds va index range man flow >>$ fun i flow ->
            mk_segment_array_index_bounds va index_up range man flow >>$ fun i_plus flow ->
            let vunion = mkv_element va in
            man.exec (mk_assign (mk_var vunion range) (mk_var (Element.choose acc) range) range) flow >>% fun  flow ->
            let flow = Element.fold
            (fun e flow ->
              let expr = mk_binop ~etyp:T_int (mk_var vunion range) O_convex_join (mk_var e range) range in
              man.exec (mk_assign (mk_var vunion range) expr range) flow
              |> post_to_flow man
            ) acc flow  
            in
            let acc = Element.singleton vunion in
            Cases.return (
                 (i,Present.MAYBE_EMPTY)::(i_plus, Present.MAYBE_EMPTY)::bounds, 
            acc::               (Element.singleton v)                ::acc     :: []) flow
        )
        in
        assume (mk_le index_up (get_bounds last_bounds) range) 
          ~fthen
          ~felse:(fun flow -> 
            todo __LOC__
          )
          ~fboth:(fun tflow _ -> fthen tflow )
        man flow
      | _ -> 
        Debug.debug ~channel:"set" "other case";
        (* Overflow *)
        (* Flow.raise_alarm (mk_alarm (todo __LOC__) (Flow.get_callstack flow) range) man.lattice flow *) 
        flow |> Cases.empty 
        (* Cases.return (bounds, segments) flow *)
      in 
      parcours a.bounds a.segments Element.empty ~is_lower:true flow >>$ fun (bounds, segments) flow ->
      List.iter (fun (b,_) -> Debug.debug ~channel:"set" "b: %a" (Print.format Bounds.print) b) bounds;
      List.iter (fun b -> Debug.debug ~channel:"set" "e: %a" (Print.format Element.print) b) segments;
      Cases.return {bounds; segments} flow


    


    (** { Lattice operators}  *)
    (** ********************* *)

    let seg_bot = Element.bottom 
    let seg_top = Element.top


    let is_bottom _ = 
      false

    let subset e1 e2 = 
      forall2_segment Element.subset e1 e2

    let partial_op ~neutral_left ~neutral_right f e1 e2 = 
      map2_segment f e1 e2    

    let join e1 e2 =
      (* bot bot *)
      partial_op ~neutral_left:seg_bot ~neutral_right:seg_bot Element.join e1 e2

    let meet e1 e2=
      (* top top *)
      partial_op ~neutral_left:seg_top ~neutral_right:seg_top Element.meet e1 e2

    let widen ctx e1 e2 =
      (* bot bot*)
      let (wid) = partial_op ~neutral_left:seg_bot ~neutral_right:seg_bot (Element.widen ctx) e1 e2 in
      wid

    let merge pre (a,e) (a',e') =
      panic ~loc:__LOC__ "Merge is impossible with ArraySegment"


    let add_arr var typ range man flow = match typ with
      | T_J_Array(wsize,len) ->
        (* TODO : fix size of array *)
        mk_segment_array_index_bounds var (mk_zero range) range man flow >>$ fun bound_zero flow ->
        mk_segment_array_index_bounds var (mk_int len range) range man flow >>$ fun bound_len flow ->
        mk_segment_array_element var range man flow >>$ fun element flow ->
        Cases.return {
          bounds = (bound_zero, Present.NON_EMPTY) :: (bound_len, Present.NON_EMPTY) :: [];
          segments = [element];
        } flow
      | _ -> panic "cannot add something that is not an jasmin array"
    
end



module Domain = struct


    (* type t = ArraySegment.t *) 
    module Arrays = Framework.Lattices.Partial_map.Make(Var)(ArraySegment)


    type t = Arrays.t
    

    include GenDomainId(struct
      type nonrec t = t 
      let name = "jasmin.array.segments"
    end)

    let checks = []

    let bottom = Arrays.bottom 
    let top = Arrays.top
    let is_bottom = Arrays.is_bottom
    

    let init prog man flow =
      set_env T_cur Arrays.empty man flow

    (** Unificator *)
    (** A really important algorithm to be able to do classic operation after *)

    let segment_unification_range = tag_range (mk_fresh_range ()) "segment-unification"

    let get_bar bound bound_list = 
      List.fold_left (fun b1 (b2,_) -> ArraySegment.Bounds.diff b1 b2) bound bound_list

    let bound_is_subset b1 b2 = 
      ArraySegment.Bounds.subset b1 b2

    let is_empty_bounds b1 = 
      ArraySegment.Bounds.is_empty b1
    
    let separate b1 b2 =
      ArraySegment.Bounds.diff b1 b2, ArraySegment.Bounds.meet b1 b2, ArraySegment.Bounds.diff b2 b1

    let rec segment_unification man ctx ~neutral_left ~neutral_right ?(prec = None, None) var (seg1,s) (seg2,s') = 
      let open ArraySegment in
      let debug s s1 s2 = 
        Debug.debug ~channel:"segment unification" s;
       
      List.iter (fun (b,_) -> Debug.debug ~channel:"segunif" "b1: %a" (Print.format Bounds.print) b) s1.bounds;
      List.iter (fun b -> Debug.debug ~channel:"segunif" "e1: %a" (Print.format Element.print) b) s1.segments;
      List.iter (fun (b,_) -> Debug.debug ~channel:"segunif" "b2: %a" (Print.format Bounds.print) b) s2.bounds;
      List.iter (fun b -> Debug.debug ~channel:"segunif" "e2: %a" (Print.format Element.print) b) s2.segments;
      
      in
      let rec segment_unification seg1 seg2 ss = 
      match seg1, seg2 with
      (* 1) B[?_1] P_1 B'_1[?'_1]... && B[?_2] P2 B'_2[?'_2]...    *)
      | { bounds = ((i1,_) as b1)::iq1; segments = p1::q1},
        { bounds = ((i2,_) as b2)::iq2; segments = p2::q2} when i1 = i2 ->
        debug "case 1" seg1 seg2;
        let (r1,r2) = segment_unification { bounds = iq1; segments = q1} {bounds = iq2; segments = q2} ss in
        { bounds = b1::r1.bounds ; segments = p1::r1.segments}, {bounds = b2::r2.bounds; segments = p2::r2.segments}
      (* 2) (B ∪ B1)[?1] P1 B1′[?1′]... and B[?2] P2 B2′[?2′]... with B1 <> ∅ and B ∩ B1 = ∅,*)
      | { bounds = (bubb1,pres1)::bq1; segments = s1},
        ({ bounds = (b2,pres2)::(b2',pres2')::bq2; segments = s2} as segment2)
        when bound_is_subset b2 bubb1 -> (
          debug "case 2" seg1 seg2;
          let (b1,b,_) = separate bubb1 b2 in
          let b1_bar = get_bar b1 ((b2',pres2')::bq2) in
          if is_empty_bounds b1_bar then
          (* 2.1) B1_bar is empty*)
            segment_unification { bounds = (b,pres1)::bq1; segments = s1} segment2 ss
          (* 2.2) Otherwise*)
          else
            segment_unification 
                { bounds = (b,pres1)::(b1,Present.MAYBE_EMPTY)::bq1; segments = neutral_left::s1}
                segment2 ss
      )
      (* 3) symmetrical case of 2) *)
      | ({ bounds = (b1,pres1)::(b1',pres1')::bq1; segments = s1} as segment1),
        { bounds = (bubb2,pres2)::bq2; segments = s2}
        when bound_is_subset b1 bubb2 ->(
          debug "cas 3" seg1 seg2;
          let (_,b,b2) = separate b1 bubb2 in
          let b1_bar = get_bar b2 ((b1',pres1')::bq1) in
          if is_empty_bounds b1_bar then
          (* 3.1) B2_bar is empty*)
            segment_unification segment1 { bounds = (b,pres2)::bq2; segments = s2} ss
          (* 3.2) Otherwise *)
          else
            segment_unification 
                segment1
                { bounds = (b,pres2)::(b2,Present.MAYBE_EMPTY)::bq2; segments = neutral_right::s2}
                ss
      )
      (* 4) In case (B∪B1)[?1]P1 B1′[?1′] . . . and (B∪B2)[?2]P2 B2′[?2′]... with B1, B2 <> ∅ *)
      (*    and B ∩ B1 = B ∩ B2 = ∅*)
      | {bounds = (bub1, pres1)::((b1',pres1') as bounds1')::bq1; segments = s1},
        {bounds = (bub2, pres2)::((b2',pres2') as bounds2')::bq2; segments = s2}
        when let (b1,b,b2) = separate bub1 bub2 in not @@ Bounds.is_bottom b
        -> (
          debug "cas 4" seg1 seg2;
          let (b1,b,b2) = separate bub1 bub2 in
          let b1_bar = get_bar b1 (bounds2'::bq2) in
          let b2_bar = get_bar b2 (bounds1'::bq1) in

          match is_empty_bounds b1_bar, is_empty_bounds b2_bar with
          (* 4.1) B1_bar and B2_bar are both empty *)
          | true, true ->
            debug "4.1" seg1 seg2;
            segment_unification 
                {bounds = (b,pres1)::bounds1'::bq1; segments = s1}
                {bounds = (b,pres2)::bounds2'::bq1; segments = s2}
              ss
          (* 4.2) Only B1_bar is empty *)
          | true, false ->
            debug "4.2" seg1 seg2;
            segment_unification 
                {bounds = (b,pres1)::bounds1'::bq1; segments = s1}
                {bounds = (b,pres2)::(b2_bar, Present.MAYBE_EMPTY)::bounds2'::bq2; segments = neutral_right::s2}
              ss
          (* 4.3) Only B2_bar is empty *)
          | false, true ->
            debug "4.3" seg1 seg2;
            segment_unification 
                {bounds = (b,pres1)::(b1_bar, Present.MAYBE_EMPTY)::bounds1'::bq2; segments = neutral_left::s1}
                {bounds = (b,pres2)::bounds2'::bq2; segments = s2}
              ss
          (* 4.4) B1_bar and B2_bar are both non-empty *)
          | false, false ->
            debug "4.4" seg1 seg2;
            segment_unification 
                {bounds = (b,pres1)::(b1_bar, Present.MAYBE_EMPTY)::bounds1'::bq2; segments = neutral_left::s1}
                {bounds = (b,pres2)::(b2_bar, Present.MAYBE_EMPTY)::bounds2'::bq2; segments = neutral_right::s2}
              ss
        )
      (* 5) B1[?1] P1 B1′[?1′]... and B2[?2] P2 B2′[?2′]... with B1 ∩ B2 = ∅ *)
      | {bounds = (b1,pres1)::(b1',pres1')::bq1; segments = p1::s1},
        {bounds = (b2,pres2)::(b2',pres2')::bq2; segments = p2::s2}
        when is_empty_bounds @@ Bounds.meet b1 b2
        -> (
          debug "5" seg1 seg2;
        (* TODO : check this is correct (spoiler: no) *)
          match prec with
          | Some p0, Some p0' ->
            segment_unification 
            {bounds = (b1', Present.meet pres1 pres1')::bq1 ; segments = (Element.join p0  p1)::s1}
            {bounds = (b2', Present.meet pres2 pres2')::bq2 ; segments = (Element.join p0' p2)::s2}
          ss
          | _ -> panic ~loc:__LOC__ "something goes wrong"
      )
      (* 6) B1[?1] P1 B1′[?1′]and B2[?2] with B1′ = B2 *)
      | { bounds = (b1,pres1)::(b1',pres1')::[]; segments = p1::[]},
        { bounds = (b2,pres2)::[]; segments = []} when b1' = b2 ->
        debug "6" seg1 seg2;
        let new_bound = Bounds.join b1 (Bounds.join b1' b2) in
        { bounds = (new_bound, pres1) :: []; segments = []},
        { bounds = (new_bound, pres2) :: []; segments = []}
      | _ -> 
        debug "other" seg1 seg2;
        seg1, seg2
      in 
      
      let seg1',seg2' = segment_unification seg1 seg2 (s,s') in
      debug "out" seg1' seg2' ;
      let range = segment_unification_range in
      let update_env seg flow =
        let (flow,segment_elements) = List.fold_left_map (fun flow e ->
          if Element.cardinal e = 1 then (flow,e)
          else
            (* Join all variables inside a set *)
            (let vunion = mkv_element var in
            let truc = man.exec (mk_assign (mk_var vunion range) (mk_var (Element.choose e) range) range) flow >>% fun  flow ->
            let flow = Element.fold
            (fun e flow ->
              (
              let ee = (mk_var e range)  in             
              let evunion = (mk_var vunion range) in
              let expr = mk_binop ~etyp:T_int evunion O_convex_join ee range in
              man.exec (mk_assign (mk_var vunion range) expr range) flow)
              |> post_to_flow man
            ) e flow  
            in
            Post.return flow
            in
            (post_to_flow man truc,Element.singleton vunion)
            )
        ) flow seg.segments
        in
        map_env T_cur (Arrays.add var {seg with segments = segment_elements}) man flow 
        |> Post.return
      in
      let s1 = env_exec (update_env seg1') ctx man s in 
      let s2 = env_exec (update_env seg2') ctx man s' in 
      (s1,s2)


    
    let do_op ctx man neutral_left neutral_right (e1,s) (e2,s')=
      Debug.debug ~channel:name "unify %a %a" (Print.format Arrays.print) e1 (Print.format Arrays.print) e2;
      Arrays.fold2zo 
        (fun b init acc -> acc)
        (fun b' init acc -> acc)
        (fun base init init' (s,s') -> 
          segment_unification ctx man ~neutral_left ~neutral_right base (init,s) (init,s') 
        )
      e1 e2 (s,s')
    
    let subset man ctx (a1,s) (a2,s') =
      let (s,s') = do_op man ctx ArraySegment.Element.bottom ArraySegment.Element.top (a1,s) (a2,s') in
      Debug.debug ~channel:name "subset %a %a" (Print.format Arrays.print) a1 (Print.format Arrays.print) a2;
      (true (* Arrays.subset a1 a2 *), s, s')

    let join man ctx (a1,s) (a2,s') =
      let (s,s') = do_op man ctx ArraySegment.Element.bottom ArraySegment.Element.bottom (a1,s) (a2,s') in
      (Arrays.join a1 a2, s , s')

    let meet man ctx (a1,s) (a2,s') =
      let (s,s') = do_op man ctx (todo __LOC__) (todo __LOC__) (a1,s) (a2,s') in
      (Arrays.meet a1 a2, s, s')

    let widen man ctx (a1,s) (a2,s') =
      Debug.debug ~channel:name "widen arrays %a %a" (Print.format Arrays.print) a1 (Print.format Arrays.print) a2;
      let (s,s') = do_op man ctx ArraySegment.Element.bottom ArraySegment.Element.bottom (a1,s) (a2,s') in
      (Arrays.widen ctx a1 a2, s, s', true)

    let merge _ _ =
      Debug.debug ~channel:name "why ?";
      assert false
    
    (** { Transfert functions } *)
    (** *********************** *)

    let exec stmt man flow = match skind stmt with
      | S_add({ekind = E_var (v,mode)} as expr) when is_jasmin_array_type @@ etyp expr  ->
        Debug.debug ~channel:name "add %a" pp_var v;
        ArraySegment.add_arr v (etyp expr) (srange stmt) man flow >>$? fun arr flow ->
        map_env T_cur (Arrays.add v arr) man flow 
        |> Post.return
        |> OptionExt.return
      | S_remove({ekind = E_var(v,mode)} as expr) when is_jasmin_array_type @@ etyp expr ->
        let arrays = get_env T_cur man flow in
        set_env T_cur (Arrays.remove v arrays) man flow
        |> Post.return
        |> OptionExt.return
      (* a = b *)
      | S_assign({ekind = E_var(_)} as lval, expr) when is_jasmin_array_type @@ etyp lval -> 
        todo __LOC__
      | S_assign({ekind = E_J_Laset(access,wsize,var,index)}, expr) -> 
        man.eval expr flow >>$? fun e flow ->
        let range = srange stmt in
        let arr = Arrays.find var (get_env T_cur man flow) in
        ArraySegment.set var arr index e ~range man flow >>$? fun arr_val flow ->
        map_env T_cur (Arrays.add var arr_val) man flow
        |> Post.return
        |> OptionExt.return
      | _ -> None

    let eval expr man flow = match ekind expr with
    | _ -> None

    (** { Communication handlers } *)
    (** ************************** *)

    let ask query man flow = None

    (** { Pretty printer } *)
    (** ****************** *)

    let print_state printer a =
      pprint printer ~path:[Key "arrays"] (pbox Arrays.print a)

    let print_expr man flow printer exp =
      ()
  
end

let () =
  register_stacked_domain (module Domain)

(* open Sig.Abstraction.Stateless *)
(* let () = *) 
  (* register_stacked_domain (module Domain) *)

(* module ArrayDomain = *) 
(* struct *)

  (* include GenStatelessDomainId(struct *)
    (* let name = "jamsmin.array" *)
  (* end) *)

  (* let checks = [] *)

  (* let init prog man flow = flow *)


  (* let exec stmt man flow = match skind stmt with *) 
    (* | S_assign( {ekind = E_J_Laset(access,wsize,var,index)}, expr) -> *)
      (* None *)
    (* | S_assign( {ekind = E_J_Lasub(access,wsize,len,var,index)}, expr) -> *)
      (* None *)
    (* | _ -> None *)

  (* let eval expr man flow = match ekind expr with *)
    (* | E_J_get(acc,wsize,var, index) -> None *)
    (* | E_J_sub(acc,wsize,len,var, index) -> None *)
    (* | _ -> None *)

  (* let ask _ _ _ = None *)

  (* let print_expr man flow printer expr = () *)

(* end *)

(* let () = *)
  (* register_stateless_domain (module ArrayDomain) *)
