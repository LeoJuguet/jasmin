open Jasmin
open Mopsa
open Ast
open Sig.Abstraction.Stateless

(* ====================================================================== *)
(*                          Translator                                    *)
(* ====================================================================== *)

module JasminTranslatorDomain = struct
  include GenStatelessDomainId (struct
    let name = "jasmin.translator"
  end)

  let checks = []
  let init prog man flow = flow

  let exec stmt man flow =
    match skind stmt with
    | S_J_assgn (lval, assgn_tag, typ, expr) ->
        man.eval lval flow >>$? fun lval flow ->
        man.eval expr flow >>$? fun expr flow ->
        let stmt = mk_assign lval expr (srange stmt) in
        man.exec stmt flow |> OptionExt.return
    | _ -> None

  let eval exp man flow =
    let open Universal.Ast in
    let range = erange exp in
    match ekind exp with
    (* | E_J_Lvar var -> *)
    (*     let new_expr = mk_var { var with vtyp = T_int } range in *)
    (*     Eval.singleton exp flow *)
    (*     |> Eval.add_translation universal new_expr *)
    (*     |> OptionExt.return *)
    (* | E_var (var, opt) when not (is_universal_type (vtyp var)) -> *)
    (*     let new_expr = mk_var { var with vtyp = T_int } range in *)
    (*     Eval.singleton exp flow *)
    (*     |> Eval.add_translation universal new_expr *)
    (*     |> OptionExt.return *)
    (* | E_J_app1 (op, expr) -> ( *)
    (*     match op with *)
    (*     | Jasmin.Expr.Oword_of_int _ -> *)
    (*         man.eval expr ~translate:universal flow >>$? fun new_expr flow -> *)
    (*         Eval.singleton exp flow *)
    (*         |> Eval.add_translation universal new_expr *)
    (*         |> OptionExt.return *)
    (*     | _ -> *)
    (*         None *)
            (* | E_binop (op, expr1, expr2) when etyp exp <> T_int -> begin *)
    (*     Debug.debug ~channel:"Translator" "E_Binop : %a ; type : %a" pp_expr exp pp_typ (etyp exp); *)
    (*     man.eval ~translate:universal expr1 flow >>$? fun new_expr1 flow -> *)
    (*     man.eval ~translate:universal expr2 flow >>$? fun new_expr2 flow -> *)
    (*     let typ = match etyp exp with *)
    (*       | T_bool -> T_bool *)
    (*       | T_int -> T_int *)
    (*       | T_J_U _ -> T_int *)
    (*       | t -> t *)
    (*       in *)
    (*     let new_expr = mk_binop ~etyp:typ new_expr1 op new_expr2 range in *)
    (*     Eval.singleton exp flow *)
    (*     |> Eval.add_translation universal new_expr *)
    (*   |> OptionExt.return *)
    (*     end *)
    | _ ->
        None

  let ask _ _ _ = None
  let print_expr _ _ _ _ = ()
end

let () = register_stateless_domain (module JasminTranslatorDomain)
