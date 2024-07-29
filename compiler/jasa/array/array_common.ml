open Mopsa
module I = Mopsa.ItvUtils.IntItv

type check +=
  CHK_J_NOT_INIT_ARRAY

let () =
  register_check (fun next fmt check ->
    match check with
      | CHK_J_NOT_INIT_ARRAY -> Format.fprintf fmt "Jasmin array not initialized"
      | _ -> next fmt check)

type alarm_kind +=
  A_J_NOT_INIT_ARRAY of var * I.t_with_bot

let () =
  register_alarm {
    check = (fun next -> function
        | A_J_NOT_INIT_ARRAY _ -> CHK_J_NOT_INIT_ARRAY
        | a -> next a);
    compare = (fun next a1 a2 ->
      match a1, a2 with
        | A_J_NOT_INIT_ARRAY (e1,i1), A_J_NOT_INIT_ARRAY(e2,i2) ->
          Compare.compose [
            (fun () -> compare_var e1 e2);
            (fun () -> I.compare_bot i1 i2);
          ]
        | _ -> next a1 a2
      );
    print = (fun next fmt -> function
        | A_J_NOT_INIT_ARRAY (arr, range) ->
      Format.fprintf fmt "%a is maybe not init in range : %a" pp_var arr I.fprint_bot range
        | a -> next fmt a
      );
    join = (fun next -> next);
  }

(* ========================================================================== *)
(* Out of bounds *)
(* ========================================================================== *)

type check += CHK_J_OUT_OF_BOUNDS_ARRAY

let () =
  register_check (fun next fmt check ->
      match check with
      | CHK_J_OUT_OF_BOUNDS_ARRAY ->
          Format.fprintf fmt "Jasmin Array out of bounds"
      | _ -> next fmt check)

type alarm_kind +=
  | A_J_out_of_bounds_array of expr (* array *) * expr (* index *)

let () =
  register_alarm
    {
      check =
        (fun next -> function
          | A_J_out_of_bounds_array _ -> CHK_J_OUT_OF_BOUNDS_ARRAY
          | a -> next a);
      compare =
        (fun next a1 a2 ->
          match (a1, a2) with
          | A_J_out_of_bounds_array (a1, i1), A_J_out_of_bounds_array (a2, i2)
            ->
              Compare.compose
                [
                  (fun () -> compare_expr a1 a2); (fun () -> compare_expr i1 i2);
                ]
          | _ -> next a1 a2);
      print =
        (fun next fmt -> function
          | A_J_out_of_bounds_array (arr, index) ->
              Format.fprintf fmt "maybe a out of bounds with %a at index %a"
                pp_expr arr pp_expr index
          | a -> next fmt a);
      join = (fun next -> next);
    }
