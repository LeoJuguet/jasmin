open Jasmin
open Ast



module Arch =
  (val let use_set0 = true and use_lea = true in
       let call_conv = Glob_options.Linux in
       let module C : Arch_full.Core_arch =
         (val CoreArchFactory.core_arch_x86 ~use_lea ~use_set0 call_conv)
       in
       (module Arch_full.Arch_from_Core_arch (C) : Arch_full.Arch))

let load_file name =
  let open Pretyping in
  try
    name
    |> tt_file Arch.arch_info Env.empty None None
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
open Ast

let opt_functions = ref []

let () =
    register_language_option "Jasmin" {
        key = "-jazz-strip";
        category = "Jasmin";
        doc = " select functions to check";
        spec = ArgExt.Set_string_list opt_functions;
        default = "all";
    }

(* ======================================================================  *)
(*                              Domains                                    *)
(* ======================================================================  *)

(** Jasmin parser, create a `Mopsa.Ast.Program.program` *)
let jasmin_parser files =
  match files with
  | file :: _ ->
    let prog = load_file file in
    let prog_slice = match !opt_functions with
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

  let checks = []

  let init prog man flow =
    match prog.prog_kind with
    | Jasmin_Program jprog ->
        Debug.debug ~channel:name "%a" pp_program prog;
        Debug.debug ~channel:name "init jasmin program\n";
        (* really mandatory ? *)
        set_jasmin_program jprog flow
        |> set_target_info (module Arch)
    | _ -> flow


  (* Get requires and transform them *)
  let get_requires stub =
    let open Stubs.Ast in
    let rec aux sections acc =
      match sections with
      | [] -> acc
      | S_leaf (S_requires require_with_range)::q -> (Debug.debug ~channel:name "is a leaf with requires";
        let require = get_content require_with_range in
        match get_content require with
          | F_expr expr -> aux q (mk_assume expr (erange expr)::acc)
          | _ -> aux q acc
        )
      | _ :: q -> Debug.debug ~channel:name "is not a leaf"; aux q acc
    in

    aux stub.stub_func_body []

  let get_requires_in_assumes prog=
    let stub = prog.f_stub in
    let range = prog.f_loc in
    let requires = get_requires stub in
    requires




  let exec stmt man flow =
    match skind stmt with
    (* | S_program ({ prog_kind = Jasmin_Program prog }, _) -> *)
    (*     (\* List.iter *\) *)
    (*     (\*   (fun func -> pp_stmt Format.std_formatter func.f_body) *\) *)
    (*     (\*   prog.functions; *\) *)

    (*     let prog = (List.hd prog.functions).f_body in *)
    (*     let locals_vars = VarSet.elements (get_locals_var prog) in *)
    (*     (\* add vars to values domains *\) *)
    (*     let range = srange prog in *)
    (*     let add_vars = List.map (fun v -> mk_add (mk_var {v with vtyp = match vtyp v with *)
    (*           T_J_U _ | T_J_Int -> T_int | a -> a} range) range) locals_vars in *)
    (*     let new_block = mk_block (add_vars @ [prog])  range in *)
    (*     man.exec new_block flow |> OptionExt.return *)
    | S_program ({ prog_kind = Jasmin_Program prog }, _) ->
        (* List.iter *)
        (*   (fun func -> pp_stmt Format.std_formatter func.f_body) *)
        (*   prog.functions; *)
      let open Stubs.Ast in
      Flow.join_list man.lattice
      ~empty:(fun () -> flow )
      (
        List.map (fun prog ->
            let body = prog.f_body in
            let locals_vars = VarSet.elements (get_locals_var body) in
            (* add vars to values domains *)
            let range = srange body in
            let f = Flow.add T_cur flow in
            let add_vars = List.map (fun v ->
              mk_add (mk_var {v with
                vtyp = match vtyp v with
                      | T_J_U _ | T_J_Int -> T_int
                      | a -> a
              } range) range) locals_vars in
            List.iter (fun v -> Debug.debug ~channel:name "type %a : %a" pp_var v pp_typ (vtyp v)) locals_vars;
            let requires = get_requires_in_assumes prog in
            let new_block = mk_block (add_vars @ requires @ [body])  range in
            man.exec new_block flow |> post_to_flow man
            |> Flow.remove T_cur
          ) prog.functions
      )
    |> Post.return
    |> OptionExt.return

    | _ -> None

  let eval exp man flow = None
  let ask _ _ _ = None
  let print_expr _ _ _ _ = ()
end

let () = register_stateless_domain (module EntryDomainJasmin)

let () = register_frontend { lang = "Jasmin"; parse = jasmin_parser }
