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
    | S_J_call (lvars, func, args) -> (
        let prog = get_jasmin_program flow in
        let stub =
          match List.find_opt (fun f -> f.f_name = func) prog.functions with
          | Some f_info -> f_info.f_stub
          | None -> panic "function %s not found" func.fn_name
        in
        let stub_call = Stubs.Ast.mk_stub_call stub args range in
        man.eval stub_call flow >>$? fun expr flow ->
        match ekind expr with
        | E_J_return_vars vars ->
            panic "output is E_J_return_vars ... : %a : %a" pp_expr expr pp_typ
              (etyp expr)
        | _ -> (
            Debug.debug "output is not E_J_return_vars ... : %a : %a" pp_expr
              expr pp_typ (etyp expr);
            let result_query = mk_avalue_query expr Return.V_return_value in
            let result = ask_and_reduce man.ask result_query flow in
            match result with
            | TOP ->
                Debug.debug "TOP TOP";
                let block =
                  List.map
                    (fun expr ->
                      [
                        (* mk_remove expr range; *)
                        mk_assign expr (mk_top (etyp expr) range) range;
                        mk_assign expr
                          (mk_constant ~etyp:(etyp expr)
                             Initialized.(C_init Init.INIT)
                             range)
                          range;
                      ])
                    lvars
                in
                let block = mk_block (List.concat block) range in
                man.exec block flow |> OptionExt.return
            | BOT ->
                Debug.debug "BOT BOT";
                None
            | Nbt a ->
                Debug.debug "%a" (Jasmin.Utils.pp_list ", " pp_expr) a;
                None))
    | S_J_return vars -> None
    | _ -> None

  let eval expr man flow = match ekind expr with _ -> None
  let ask _ _ _ = None
  let print_expr _ _ _ _ = ()
end

let () = register_stateless_domain (module Domain)
