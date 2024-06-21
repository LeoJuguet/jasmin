
open Jasmin
open Mopsa
open Ast
open Sig.Abstraction.Stateless
open Universal.Iterators.Interproc.Common

module Domain = struct
  include GenStatelessDomainId (struct
    let name = "jasmin.iterators.interproc"
  end)

  let checks = []
  let init prog man flow = flow

  let exec stmt man flow =
    let range = srange stmt in
    let open Universal.Ast in
    match skind stmt with
    | S_J_call(lvars, func, args) ->
      let prog = get_jasmin_program flow in
      let stub = match List.find_opt (fun f -> f.f_name = func) prog.functions with
        | Some ( f_info ) -> f_info.f_stub
        | None -> panic "function %s not found" func.fn_name
      in
      let s = Stubs.Ast.mk_stub_call stub args range in
      man.eval s flow >>$? fun expr flow ->
      (match ekind expr with
      | E_J_return_vars vars ->
        panic "output is E_J_return_vars ... : %a : %a" pp_expr expr pp_typ (etyp expr)
      | _ -> Debug.debug "output is not E_J_return_vars ... : %a : %a" pp_expr expr pp_typ (etyp expr);
        let result_query = mk_avalue_query expr (Return.V_return_value) in
        let result = ask_and_reduce man.ask result_query flow in
        match result with
        | TOP -> (Debug.debug "TOP TOP";
        let block = List.map (fun expr ->
            mk_assign expr (mk_top (etyp expr) range) range
        ) lvars in
        let block = mk_block block range in
        man.exec block flow
        |> OptionExt.return
        )
        | BOT -> Debug.debug "BOT BOT"; None
        | Nbt a -> Debug.debug "%a" (Jasmin.Utils.pp_list ", " pp_expr) a; None
      )

        (*let stub = mk_pass range in
        man.exec stub flow >>$? fun expr flow ->
        Eval.singleton expr flow
        |> OptionExt.return*)
    | S_J_return (vars) ->
      (* man.exec (mk_stmt (S_return (Some (mk_expr (E_J_return_vars vars) range))) range) flow >>%? fun flow -> *)
      (* (\* Now clean the post-state using scope updater *\) *)
      (* (\* To do that, first move the return environment to cur *\) *)
      (* let flow = Flow.copy (T_return stmt.srange) T_cur man.lattice flow flow in *)
      (* (\* Finally, move cur to return flow *\) *)
      (* let cur = Flow.get T_cur man.lattice flow in *)
      (* Flow.set (T_return (stmt.srange)) cur man.lattice flow |> *)
      (* Flow.remove T_cur |> *)
      (* Post.return |> OptionExt.return *)
      None

    | _ -> None

  let eval expr man flow =
    match ekind expr with
    | _ -> None

  let ask _ _ _ = None
  let print_expr _ _ _ _ = ()
end

let () = register_stateless_domain (module Domain)
