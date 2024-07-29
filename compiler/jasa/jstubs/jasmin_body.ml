open Jasmin
open Mopsa
open Ast
open Sig.Abstraction.Stateless

module Domain = struct
  include GenStatelessDomainId (struct
    let name = "jasmin.stubs.body"
  end)

  let checks = []
  let init prog man flow = flow

  let exec stmt man flow =
    match skind stmt with
    | S_add ({ etyp = T_J_Return _ } as expr) ->
        let is_var = match ekind expr with E_var _ -> true | _ -> false in
        Debug.debug ~channel:name "%a : %a is var : %b" pp_expr expr pp_typ
          (etyp expr) is_var;
        None
    | _ -> None

  let eval expr man flow = match ekind expr with _ -> None
  let ask _ _ _ = None
  let print_expr _ _ _ _ = ()
end

let () = register_stateless_domain (module Domain)
