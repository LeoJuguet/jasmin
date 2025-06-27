open Jasmin
open Mopsa
open Ast
open Sig.Abstraction.Stateless

(* Domain to translate jasmin loop to universal loop *)

module Domain = struct
  include GenStatelessDomainId (struct
    let name = "jasmin.iterators.loop"
  end)

  let checks = []
  let init prog man flow = None

  let exec stmt man flow =
    let open Universal.Ast in
    match skind stmt with
    | S_J_for (var, (dir, start, last), body) ->
        let range = stmt.srange in

        let var = { var with vtyp = T_int } in
        let var = mk_var var range in
        (* forloop initialisation : var = start *)
        let init = mk_assign var start range in

        (* correct operation direction *)
        let op_dir = match dir with UpTo -> O_plus | DownTo -> O_minus in
        (* instruction to simulate the +/- 1 of the forloop *)
        let post_intr =
          mk_assign var
            (mk_binop ~etyp:T_int var op_dir (mk_one range) range)
            range
        in

        (* Condition check by the while *)
        (* TODO maybe switch for only a <= or >= to avoid both *)
        (* last index is not excluded *)
        let cond =
          Universal.Ast.mk_in ~right_strict:true var start last range
        in

        (* The forloop is translate into an equivalent while loop *)
        let stmt =
          Universal.Ast.(
            mk_block
              [
                init;
                mk_while cond (mk_block [ body; post_intr ] body.srange) range;
              ]
              range)
        in
        man.exec stmt flow |> OptionExt.return
    | S_J_while (s1, cond, s2) ->
        let range = srange stmt in
        let universal_while =
          mk_block
            [ s1; mk_while cond (mk_block [ s2; s1 ] (srange s2)) range ]
            range
        in
        man.exec universal_while flow |> OptionExt.return
    | _ -> None

  let eval exp man flow = None
  let ask _ _ _ = None
  let print_expr _ _ _ _ = ()
end

let () = register_stateless_domain (module Domain)
