
open Mopsa
open Sig.Abstraction.Domain
open Sig.Abstraction.Simplified_value
open Jasmin
open Universal.Ast
open Ast


(* This is inspired by the paper : *)
(* Patrick Cousot, Radhia Cousot, and Francesco Logozzo. 2011. A parametric *)
(* segmentation functor for fully automatic and scalable array content *)
(* analysis. SIGPLAN Not. 46, 1 (January 2011), 105–118. *)
(* https://doi.org/10.1145/1925844.1926399 *)


module type SEGMENTATION_FUNCTOR = sig
end


let todo loc = panic ~loc "todo"

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

end



module ArraySegment (SegmentBounds : Lattices.Powerset.ELT) (A : Sig.Abstraction.Value.VALUE) (ScalarVariable : ValueSig.S) = struct

    module Bounds = Lattices.Powerset.Make(SegmentBounds)

    type t = {
        bounds : (Bounds.t * Present.t) list;
        segments : A.t list;
    }

    (** Utils *)

    (** By default f2 take the bound of the first segment *)
    (** Ensures : segment need to be the same otherwise an error can be raised*)
    let map2_elements f a1 a2 =
      {
        bounds = a1.bounds;
        segments = List.map2 f a1.segments a2.segments;
      }

    (** Ensures : segment need to be the same otherwise an error can be raised*)
    let forall2_elements f a1 a2 =
      List.for_all2 f a1.segments a2.segments

    let uniq_id =
      let id = ref 0 in
      fun () -> incr id; !id

    let insert arr index value man flow =
      let var_name = Printf.sprintf "arr_element(%s,%i)" arr.name (uniq_id ()) in
      let var_lower_bound = Printf.sprintf "arr_bound(%s,%i)" arr.name (uniq_id ()) in
      let var_upper_bound = Printf.sprintf "arr_bound(%s,%i)" arr.name (uniq_id ()) in
      let range = mk_program_range ["no idea"] in

      let rec parcours bounds segments acc_bounds acc_segments flow = match bounds, segments with
      | [last], [] -> failwith "cannot insert"
      | (lower_bound,present)::((upper_bound,present2) as i2)::other_bounds, condition::segments when is_bellow ->
          (* check if we can insert the bound *)
          let lower_var = mk_var lower_bound range in
          let upper_var = mk_var upper_bound range in
          assume (mk_binop lower_var O_le index range)
            ~fthen:(fun tflow ->
                let r = parcours (i2::other_bounds) segments acc_bounds acc_segments tflow in
                let new_array = {
                  bounds = (* acc_bounds *) [] @ (* other_bounds *) [];
                  segments = acc_segments @ segments ;
                } in

                todo __LOC__
            )
            ~felse:(fun fflow ->
                parcours (i2::other_bounds) segments acc_bounds acc_segments fflow
            ) 
            man flow
        | _ -> panic ~loc:__LOC__ "invariant on the structure of the array abstraction are not guaranted"
      in parcours


    let get arr index range man flow= 
      let in_bound i1 i2 index =
        mk_in ~left_strict:false ~right_strict:true (mk_var i1 range) (mk_var i2 range) index 
      in

      let rec parcours bounds segments out flow is_bellow = match bounds, segments with
      | [last], [] -> Cases.empty flow
      | (i1,_)::((i2,_) as b1)::bound, e1::seg  when is_bellow ->
        assume (in_bound i1 i2 index)
        ~fthen:(fun tflow -> 
          parcours (b1::bound) seg (A.join e1 out) tflow
        )
        ~felse:(fun fflow ->
          parcours bound seg out fflow
        ) man flow 
      | _ -> panic ~loc:__LOC__ "invariant on the structure of the array abstraction are not guaranted"
      in
      parcours arr.bounds arr.segments A.bottom flow

    (** Segment unification *)

    (* Return (e only in b1, e in b1 and b2, e only in b2) *)
    let separate b1 b2 =
        Bounds.filter (fun e -> Bounds.mem e b2) b1,
        Bounds.meet b1 b2,
        Bounds.filter (fun e -> Bounds.mem e b1) b2

    let get_bounds_bar b1 b2 =
      let (_,bar,_) = separate b1 b2 in
      bar

    let is_empty_bounds b =
      Bounds.is_empty b

    let rec segment_unification ~neutral_left ~neutral_right ?(prec = None, None) seg1 seg2 =
      match seg1, seg2 with
      (* 1) B[?_1] P_1 B'_1[?'_1]... && B[?_2] P2 B'_2[?'_2]...    *)
      | { bounds = ((i1,_) as b1)::iq1; segments = p1::q1},
        { bounds = ((i2,_) as b2)::iq2; segments = p2::q2} when i1 = i2 ->
        let (r1,r2) = segment_unification ~neutral_left ~neutral_right { bounds = iq1; segments = q1} {bounds = iq2; segments = q2} in
        { bounds = b1::r1.bounds ; segments = p1::r1.segments}, {bounds = b2::r2.bounds; segments = p2::r2.segments}
      (* 2) (B ∪ B1)[?1] P1 B1′[?1′]... and B[?2] P2 B2′[?2′]... with B1 <> ∅ and B ∩ B1 = ∅,*)
      | { bounds = (bubb1,pres1)::bq1; segments = s1},
        ({ bounds = (b2,pres2)::(b2',pres2')::bq2; segments = s2} as segment2)
        when Bounds.subset b2 bubb1 -> (
          let (b1,b,_) = separate bubb1 b2 in
          let b1_bar = get_bounds_bar b1 b2' in
          if is_empty_bounds b1_bar then
          (* 2.1) B1_bar is empty*)
            segment_unification ~neutral_left ~neutral_right { bounds = (b,pres1)::bq1; segments = s1} segment2
          (* 2.2) Otherwise*)
          else
            segment_unification ~neutral_left ~neutral_right
                { bounds = (b,pres1)::(b1,Present.MAYBE_EMPTY)::bq1; segments = neutral_left::s1}
                segment2
      )
      (* 3) symmetrical case of 2) *)
      | ({ bounds = (b1,pres1)::(b1',pres1')::bq1; segments = s1} as segment1),
        { bounds = (bubb2,pres2)::bq2; segments = s2}
        when Bounds.subset b1 bubb2 ->(
          let (_,b,b2) = separate b1 bubb2 in
          let b1_bar = get_bounds_bar b2 b1' in
          if is_empty_bounds b1_bar then
          (* 3.1) B2_bar is empty*)
            segment_unification ~neutral_left ~neutral_right  segment1 { bounds = (b,pres2)::bq2; segments = s2}
          (* 3.2) Otherwise *)
          else
            segment_unification ~neutral_left ~neutral_right
                segment1
                { bounds = (b,pres2)::(b2,Present.MAYBE_EMPTY)::bq2; segments = neutral_right::s2}
      )
      (* 4) In case (B∪B1)[?1]P1 B1′[?1′] . . . and (B∪B2)[?2]P2 B2′[?2′]... with B1, B2 <> ∅ *)
      (*    and B ∩ B1 = B ∩ B2 = ∅*)
      | {bounds = (bub1, pres1)::((b1',pres1') as bounds1')::bq1; segments = s1},
        {bounds = (bub2, pres2)::((b2',pres2') as bounds2')::bq2; segments = s2}
        when let (b1,b,b2) = separate bub1 bub2 in not @@ Bounds.is_bottom b
        -> (
          let (b1,b,b2) = separate bub1 bub2 in
          let b1_bar = get_bounds_bar b1 b2' in
          let b2_bar = get_bounds_bar b2 b1' in

          match is_empty_bounds b1_bar, is_empty_bounds b2_bar with
          (* 4.1) B1_bar and B2_bar are both empty *)
          | true, true ->
            segment_unification ~neutral_left ~neutral_right
                {bounds = (b,pres1)::bounds1'::bq1; segments = s1}
                {bounds = (b,pres2)::bounds2'::bq1; segments = s2}
          (* 4.2) Only B1_bar is empty *)
          | true, false ->
            segment_unification ~neutral_left ~neutral_right
                {bounds = (b,pres1)::bounds1'::bq1; segments = s1}
                {bounds = (b,pres2)::(b2_bar, Present.MAYBE_EMPTY)::bounds2'::bq2; segments = neutral_right::s2}
          (* 4.3) Only B2_bar is empty *)
          | false, true ->
            segment_unification ~neutral_left ~neutral_right
                {bounds = (b,pres1)::(b1_bar, Present.MAYBE_EMPTY)::bounds1'::bq2; segments = neutral_left::s1}
                {bounds = (b,pres2)::bounds2'::bq2; segments = s2}
          (* 4.4) B1_bar and B2_bar are both non-empty *)
          | false, false ->
            segment_unification ~neutral_left ~neutral_right
                {bounds = (b,pres1)::(b1_bar, Present.MAYBE_EMPTY)::bounds1'::bq2; segments = neutral_left::s1}
                {bounds = (b,pres2)::(b2_bar, Present.MAYBE_EMPTY)::bounds2'::bq2; segments = neutral_right::s2}
        )
      (* 5) B1[?1] P1 B1′[?1′]... and B2[?2] P2 B2′[?2′]... with B1 ∩ B2 = ∅ *)
      | {bounds = (b1,pres1)::(b1',pres1')::bq1; segments = p1::s1},
        {bounds = (b2,pres2)::(b2',pres2')::bq2; segments = p2::s2}
        when is_empty_bounds @@ Bounds.meet b1 b2
        -> (
          match prec with
          | Some p0, Some p0' ->
            segment_unification ~neutral_left ~neutral_right
            {bounds = (b1', Present.meet pres1 pres1')::bq1 ; segments = (A.join p0 p1)::s1}
            {bounds = (b2', Present.meet pres2 pres2')::bq2 ; segments = (A.join p0' p2)::s2}
          | _ -> panic ~loc:__LOC__ "something goes wrong"
      )
      (* 6) B1[?1] P1 B1′[?1′]and B2[?2] with B1′ = B2 *)
      | { bounds = (b1,pres1)::(b1',pres1')::[]; segments = p1::[]},
        { bounds = (b2,pres2)::[]; segments = []} when b1' = b2 ->
        let new_bound = Bounds.join b1 (Bounds.join b1' b2) in
        { bounds = (new_bound, pres1) :: []; segments = []},
        { bounds = (new_bound, pres2) :: []; segments = []}
      | _ -> todo __LOC__


    (** Classic functions for a Sig.Abstraction.Value.VALUE *)

    let join a1 a2 =
        let (a1,a2) = segment_unification ~neutral_left:A.bottom ~neutral_right:A.bottom a1 a2 in
        map2_elements A.join a1 a2

    let meet a1 a2 =
        let (a1,a2) = segment_unification ~neutral_left:A.top ~neutral_right:A.top a1 a2 in
        map2_elements A.meet a1 a2

    let widen ctx a1 a2 =
        let (a1,a2) = segment_unification ~neutral_left:A.bottom ~neutral_right:A.bottom a1 a2 in
        map2_elements (A.widen ctx) a1 a2

    let subset a1 a2 =
        let (a1,a2) = segment_unification ~neutral_left:A.bottom ~neutral_right:A.top a1 a2 in
        forall2_elements A.subset a1 a2

    let pp_array_segment fmt e =
      ()
end


(***********************************************************)
(*                 Make                                    *)
(***********************************************************)


(** *)
(** @arguments : Bounds, ArrayElements and scalar variables *)

(* module Make (Bounds : Lattices.Powerset.ELT) (A : Sig.Abstraction.Value.VALUE) (ScalarVariable : ValueSig.S) : SIMPLIFIED_VALUE = struct *)
(*     open Bot_top *)

(*     module AS = ArraySegment(Bounds)(A)(ScalarVariable) *)

(*     type t = AS.t with_bot_top *)

(*     include GenValueId(struct *)
(*           type nonrec t = t *)
(*           let name = "array.segmentation" *)
(*           let display = "array segmentation" *)
(*       end) *)

(*     let accept_type t = is_jasmin_array_type t *)

(*     let bottom = BOT (\* never reach *\) *)
(*     let top = TOP (\* never reach *\) *)
(*     let is_bottom b = b = bottom *)

(*     let join = bot_top_neutral2 AS.join *)
(*     let meet = bot_top_lift2 AS.meet *)

(*     let subset = bot_top_included AS.subset *)

(*     let widen ctx = bot_top_neutral2 (AS.widen ctx) *)

(*     include DefaultValueFunctions *)

(*     let unop op typ t typ2= bottom *)
(*     let binop op typ1 t1 typ2 t2 typ3 = bottom *)

(*     let constant c typ = bottom *)

(*     let print printer t  = () *)

(* end *)
