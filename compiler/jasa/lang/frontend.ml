open Jasmin
open Ast

module Arch = Ast.Arch
  (* (val let use_set0 = true and use_lea = true in *)
       (* let call_conv = Glob_options.Linux in *)
       (* let module C : Arch_full.Core_arch = *)
         (* (val CoreArchFactory.core_arch_x86 ~use_lea ~use_set0 call_conv) *)
       (* in *)
       (* (module Arch_full.Arch_from_Core_arch (C) : Arch_full.Arch)) *)

let load_file name =
  let open Pretyping in
  let idirs = !Glob_options.idirs in
  let env = List.fold_left Pretyping.Env.add_from Pretyping.Env.empty idirs in
  try
    name
    |> tt_file Arch.arch_info env None None
    |> fst |> Env.decls
    |> Compile.preprocess Arch.reg_size Arch.asmOp
  with
  | TyError (loc, e) ->
      Format.eprintf "%a: %a@." Location.pp_loc loc pp_tyerror e;
      assert false
  | Syntax.ParseError (loc, None) ->
      Format.eprintf "Parse error: %a@." Location.pp_loc loc;
      assert false

open Mopsa
open Universal

let opt_functions = ref []

let () =
  register_language_option "Jasmin"
    {
      key = "-jazz-slice";
      category = "Jasmin";
      doc = " select functions to check";
      spec = ArgExt.String (ArgExt.set_string_list_lifter opt_functions, ArgExt.empty);
      default = "all";
    }

let () =
  register_language_option "Jasmin"
    {
      key = "-I";
      category = "Jasmin";
      doc = "include files";
      spec = ArgExt.String (Jasmin.Glob_options.set_idirs, ArgExt.empty);
      default = "";
    }

(* ======================================================================  *)
(*                              Domains                                    *)
(* ======================================================================  *)

(** Jasmin parser, create a `Mopsa.Ast.Program.program` *)
let jasmin_parser files =
  match files with
  | file :: _ ->
      let prog = load_file file in
      let prog_slice =
        match !opt_functions with
        | [] -> prog
        | _ -> Jasmin.Slicing.slice !opt_functions prog
      in
      {
        prog_kind = Jasmin_Program (mk_jasmin_program prog_slice);
        prog_range = mk_program_range [ file ];
      }
  | [] -> panic "no input file"

open Sig.Abstraction.Stateless

(** Jasmin Entry Domain, start to analyze a Jasmin program with MOPSA *)
module EntryDomainJasmin = struct
  include GenStatelessDomainId (struct
    let name = "jasmin.program"
  end)

  type check += CHK_J_ENSURES

  let () =
    register_check (fun next fmt check ->
      match check with
      | CHK_J_ENSURES -> Format.fprintf fmt "Jasmin Ensures"
      | _ -> next fmt check
    )

  type alarm_kind += A_J_ENSURES of expr

  let () =
    register_alarm {
      check = (fun next -> function A_J_ENSURES _ -> CHK_J_ENSURES | a -> next a);
      compare = (fun next a1 a2 ->
        match (a1,a2) with
        | A_J_ENSURES e1, A_J_ENSURES e2 -> compare_expr e1 e2
        | _ -> next a1 a2
      );
      print = (
        fun next fmt -> function
          | A_J_ENSURES e ->
              Format.fprintf fmt "'%a' doesn't holds"
                pp_expr e
          | a -> next fmt a
      );
      join = (fun next -> next);
  }

  let checks = [CHK_J_ENSURES]

  let init prog man flow =
    match prog.prog_kind with
    | Jasmin_Program jprog ->
        Debug.debug ~channel:name "init jasmin program\n";
        set_jasmin_program jprog flow
        |> set_target_info (module Arch)
        |> Post.return
        |> OptionExt.return
    | _ -> None

  (* Get requires and transform them *)
  let get_requires stub =
    let open Stubs.Ast in
    let rec aux sections acc =
      match sections with
      | [] -> acc
      | S_leaf (S_requires require_with_range) :: q -> (
          Debug.debug ~channel:name "is a leaf with requires";
          let require = get_content require_with_range in
          match get_content require with
          | F_expr expr -> aux q (mk_assume expr (erange expr) :: acc)
          | _ -> aux q acc)
      | _ :: q ->
          Debug.debug ~channel:name "is not a leaf";
          aux q acc
    in

    aux stub.stub_func_body []
  
  (* Get requires and transform them *)
  let get_ensures stub man flow =
    let open Stubs.Ast in
    let rec aux sections man flow =
      match sections with
      | [] -> Cases.return () flow
      | S_leaf (S_ensures ensures_with_range) :: q -> (
          Debug.debug ~channel:name "is a leaf with requires";
          let ensures = get_content ensures_with_range in
          match get_content ensures with
          | F_expr expr ->
              assume expr
                ~fthen:(fun flow ->
                Flow.add_safe_check CHK_J_ENSURES (erange expr) flow
                |> aux q man
                )
                ~felse:(fun flow ->
                  let call_stack = Flow.get_callstack flow in
                  let expr_origin = get_orig_expr expr in
                  let alarm =
                    mk_alarm (A_J_ENSURES expr_origin) call_stack expr.erange
                  in
                  Flow.raise_alarm alarm ~bottom:false ~warning:true man.lattice
                    flow
                  |> aux q man
                ) man flow
          | _ -> aux q man flow)
      | _ :: q ->
          Debug.debug ~channel:name "is not a leaf";
          aux q man flow
    in
    aux stub.stub_func_body man flow

  let get_requires_in_assumes prog =
    let stub = prog.f_stub in
    let range = prog.f_loc in
    let requires = get_requires stub in
    requires
  
  let get_ensures_in_assumes prog =
    let stub = prog.f_stub in
    let range = prog.f_loc in
    let ensures = get_ensures stub in
    ensures

  let exec stmt man flow =
    match skind stmt with
    | S_program ({ prog_kind = Jasmin_Program prog }, _) ->
        let open Stubs.Ast in
        Flow.join_list man.lattice
          ~empty:(fun () -> flow)
          (List.map
             (fun prog ->
               let body = prog.f_body in
               let locals_vars = VarSet.elements (get_locals_var body) in
               (* add vars to values domains *)
               let range = srange body in
               let f = Flow.add T_cur flow in
               let declare_args = declare_args prog.f_args in
               let add_vars =
                 List.map
                   (fun v ->
                     mk_add
                       (mk_var
                          {
                            v with
                            vtyp =
                              (match vtyp v with
                              | T_J_U _ | T_J_Int -> Ast.T_int
                              | a -> a);
                          }
                          range)
                       range)
                   locals_vars
               in
               List.iter
                 (fun v ->
                   Debug.debug ~channel:name "type %a : %a" pp_var v pp_typ
                     (vtyp v))
                 locals_vars;
               let requires = get_requires_in_assumes prog in
               let new_block =
                 Ast.mk_block (declare_args :: add_vars @ requires @ [ body ]) range
               in
               (
               man.exec new_block flow
               >>% fun flow ->
                 get_ensures_in_assumes prog man flow
                )
               |> post_to_flow man
               |> Flow.remove T_cur
             )
             prog.functions)
        |> Post.return |> OptionExt.return
    | _ -> None

  let eval exp man flow = None
  let ask _ _ _ = None
  let print_expr _ _ _ _ = ()
end

let () = register_stateless_domain (module EntryDomainJasmin)
let () = register_frontend {
  lang = "Jasmin";
  parse = jasmin_parser;
  on_panic = fun _ _ _ -> ();
}
