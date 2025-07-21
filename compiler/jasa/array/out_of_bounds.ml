open Mopsa
open Sig.Abstraction.Stateless
open Universal.Ast
open Stubs.Ast
open Ast
open Array_common

(* ========================================================================== *)
(* Domain *)
(* ========================================================================== *)

module Domain = struct
  let name = "jasmin.memory.array"

  (* =============================================== *)
  (* Array *)
  (* =============================================== *)

  module J_Array = struct
    type t = {
      size : Z.t;
      elements : var option array;
      typ : typ;
      is_initialized : bool;
    }

    let compare a1 a2 =
      Compare.compose
        [
          (fun () -> Z.compare a1.size a2.size);
          (fun () -> compare_typ a1.typ a2.typ);
          (fun () -> compare a1.is_initialized a2.is_initialized);
        ]

    let print =
      unformat (fun fmt a ->
          Format.fprintf fmt "{size : %a, typ : %a}" Z.pp_print a.size pp_typ
            a.typ)
  end

  type base = { cell_sizes : int }
  type var_kind += V_j_array of J_Array.t

  let mk_j_array ?(is_initialized = false) ?(typ = None) elements range = ()

  module J_Arrays = Framework.Lattices.Powerset.Make (J_Array)

  type t = unit

  (* =============================================== *)
  (* Domain functions *)
  (* =============================================== *)

  include GenStatelessDomainId (struct
    let name = name
  end)

  let get_len typ =
    match typ with
    | T_J_Array (_, len) -> len
    | _ -> failwith "this is not an array"

  let get_base typ =
    match typ with
    | T_J_Array (base, len) -> Utils.wsize_to_int base
    | _ -> failwith "this is not an array"

  let check_in_bounds arr access wsize ?(size = 1) index man flow range
      ~in_bounds =
    let open Jasmin.Warray_ in
    let len = get_len (etyp arr) in
    let scale_factor_index = Utils.wsize_to_int wsize / 8 in
    let scale_factor_array = get_base (etyp arr) / 8 in

    let index_up =
      match (size, access) with
      | 0, AAscale -> index
      | s, AAscale -> mk_binop (mk_int (size - 1) range) O_plus index range
      | s, AAdirect ->
          mk_binop
            (mk_int ((scale_factor_index * size) - 1) range)
            O_plus index range
    in
    let upper_bound =
      match access with AAscale -> len | AAdirect -> scale_factor_array * len
    in
    (* Is : 0 <= index < len *)
    assume
      (mk_log_and ~etyp:T_bool
         (mk_le (mk_zero range) index range)
         (mk_lt index_up (mk_int upper_bound range) range)
         range)
      (* in bounds *)
      ~fthen:(fun tflow ->
        Flow.add_safe_check CHK_J_OUT_OF_BOUNDS_ARRAY (erange arr) tflow
        |> in_bounds) (* out of bounds *)
      ~felse:(fun fflow ->
        let call_stack = Flow.get_callstack fflow in
        let alarm =
          mk_alarm
            (A_J_out_of_bounds_array (arr, index))
            call_stack (erange arr)
        in
        Debug.debug ~channel:name "raise alarm out of bounds";
        Flow.raise_alarm alarm ~bottom:false man.lattice fflow |> Cases.empty)
      man flow

  let checks = [ CHK_J_OUT_OF_BOUNDS_ARRAY ]

  let init prog man flow =
    (* set_env T_cur () man flow *)
    None

  let exec_assign_array lval expr range man flow =
    match ekind lval with
    (* E[| array[index] |]] *)
    | E_J_Laset (access, wsize, array, index) ->
        check_in_bounds
          (mk_var array (erange lval))
          access wsize index man flow range ~in_bounds:Post.return
        |> OptionExt.return
    | E_J_Lasub (access, wsize, size, array, index) ->
        check_in_bounds
          (mk_var array (erange lval))
          ~size access wsize index man flow range ~in_bounds:Post.return
        |> OptionExt.return
    | _ -> None

  let exec stmt man flow =
    match skind stmt with
    (* declare(array) *)
    | S_add v when is_jasmin_array_type @@ etyp v ->
        Post.return flow |> OptionExt.return
    | S_J_declare var when is_jasmin_array_type @@ vtyp var ->
        Post.return flow |> OptionExt.return
    (* S[| a[c] = expr |] *)
    | S_assign (({ ekind = E_J_Laset _ | E_J_Lasub _ } as lval), expr) ->
        man.eval expr flow >>$? fun _ flow ->
        exec_assign_array lval expr (srange stmt) man flow
    (* size of the slice is checked during the typing *)
    | S_assign (({ ekind = E_var _ } as lval), expr)
      when is_jasmin_array_type @@ etyp lval ->
        man.eval expr flow >>$? fun _ flow ->
        Post.return flow |> OptionExt.return
    | _ -> None

  let eval expr man flow =
    match ekind expr with
    | E_J_sub (access, wsize, size, array, index) ->
        man.eval index flow >>$? fun index flow ->
        let range_down, range_up = Utils.wsize_to_range wsize in
        check_in_bounds
          (mk_var array (erange expr))
          ~size access wsize index man flow (erange expr)
          ~in_bounds:
            (Cases.return (mk_z_interval range_down range_up (erange expr)))
        |> OptionExt.return
    (* E[| array[index] |] *)
    | E_J_get (access, wsize, array, index) ->
        man.eval index flow >>$? fun index flow ->
        let range_down, range_up = Utils.wsize_to_range wsize in
        check_in_bounds
          (mk_var array (erange expr))
          access wsize index man flow (erange expr)
          ~in_bounds:
            (Cases.return (mk_z_interval range_down range_up (erange expr)))
        |> OptionExt.return
    (* E[| array[index] |] *)
    | E_J_Laset (access, wsize, array, index) ->
        check_in_bounds
          (mk_var array (erange expr))
          access wsize index man flow (erange expr)
          ~in_bounds:(fun flow -> Eval.singleton expr flow)
        |> OptionExt.return
    | _ -> None

  let ask _ _ _ = None
  let print_expr _ _ _ _ : unit = ()
end

let () = register_stateless_domain (module Domain)
