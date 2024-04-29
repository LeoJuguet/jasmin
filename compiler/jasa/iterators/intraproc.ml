open Jasmin
open Mopsa
open Ast
open Sig.Abstraction.Stateless

module JasminFlowDomain = struct
  include GenStatelessDomainId (struct
    let name = "jasmin.iterators.intraproc"
  end)

  let checks = []
  let init prog man flow = flow

  let exec stmt man flow =
    let open Universal.Ast in
    match skind stmt with
    | S_J_if (cond, stmt_true, stmt_false) ->
        man.exec (mk_if cond stmt_true stmt_false (srange stmt)) flow
        |> OptionExt.return

    | S_assign(x,e) when is_jasmin_type (etyp e)->
      Debug.debug ~channel:name "assign";
      man.eval e flow >>$? fun e flow ->
      Debug.debug ~channel:name "assign suite";
      man.exec (mk_assign x e stmt.srange) flow ~route:(Below name) |>
      OptionExt.return
    | _ -> None

  let eval expr man flow =
    match ekind expr with
    | E_var (v,_) when is_jasmin_scalar (vtyp v) ->
      (* Add var to environments *)
      man.eval expr ~translate:"Universal" flow ~route:(Below name) >>$? fun e_univ flow ->
      man.exec (mk_add e_univ (erange e_univ)) flow ~route:(Below name) >>$? fun _ flow ->
      Eval.singleton expr flow
      |> Eval.add_translation "Universal" e_univ
      |> OptionExt.return
    | _ -> None



  let ask _ _ _ = None
  let print_expr _ _ _ _ = ()
end

let () = register_stateless_domain (module JasminFlowDomain)
