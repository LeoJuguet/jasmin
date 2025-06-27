open Jasmin
open Mopsa
open Ast
open Sig.Abstraction.Stateless
open Universal.Iterators.Interproc.Common




let analyze_opn stmt man flow lvalues opn args =
    let range = srange stmt in
  let open Sopn in
  match opn with
  | Opseudo_op pseudo_op ->
    print_string "pseudo_op";
    None
  | Oslh slh ->
    print_string "slh";
    Post.return flow
    |> OptionExt.return
  | Oasm asm_op ->
    let open Arch_extra in
    print_string "asm_op";
    match asm_op with
    | BaseOp (wsize, op) -> print_string "BaseOp"; None
    | ExtOp (op : Arch.extra_op) ->
      let block =
        List.map (fun lval ->
          mk_assign lval (mk_top (etyp lval) range) range

        ) lvalues
      in
      let block = Universal.Ast.mk_block block range in
      man.exec block flow |> OptionExt.return
  







module Domain = struct
  include GenStatelessDomainId (struct
    let name = "jasmin.iterators.interproc_assembly"
  end)

  let checks = []
  let init prog man flow = None

  let exec stmt man flow =
    let range = srange stmt in
    let open Universal.Ast in
    match skind stmt with
    | S_J_opn(lvalues,_,opn,args) ->
      analyze_opn stmt man flow lvalues opn args
    | S_J_return vars -> None
    | _ -> None

  let eval expr man flow = match ekind expr with _ -> None
  let ask _ _ _ = None
  let print_expr _ _ _ _ = ()
end

let () = register_stateless_domain (module Domain)
