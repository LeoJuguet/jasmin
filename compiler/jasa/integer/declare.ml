open Mopsa
open Sig.Abstraction.Stateless
open Universal.Ast
open Stubs.Ast
open Ast
open Lang.Ast
module IntItv = Universal.Numeric.Values.Intervals.Integer.Value
module FltItv = Universal.Numeric.Values.Intervals.Float.I
open Utils

module Domain = struct
  include GenStatelessDomainId (struct
    let name = "jasmin.declare"
  end)

  let checks = []
  let init _ _ flow = flow

  let declare_var v range man flow =
    let new_var = mk_var { v with vtyp = T_int } range in
    let l, h = Utils.range_of v.vtyp in
    Eval.singleton (mk_z_interval l h range) flow >>$ fun init flow ->
    man.exec (mk_assign new_var init range) flow

  let exec stmt man flow =
    match skind stmt with
    | S_J_declare v when is_jasmin_scalar (vtyp v) ->
        declare_var v (srange stmt) man flow |> OptionExt.return
    | _ -> None

  let eval expr man flow = None
  let ask _ _ _ = None
  let print_expr man flow printer exp = ()
end

let () = register_stateless_domain (module Domain)
