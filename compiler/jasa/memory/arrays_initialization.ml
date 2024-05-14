open Mopsa
open Sig.Abstraction.Simplified_value
open Universal.Ast
open Stubs.Ast
open Ast
open Bot
module I = Mopsa.ItvUtils.IntItv
module B = Mopsa.ItvUtils.IntBound

module ArrayInit = struct
  type t = I.t_with_bot with_bot (* interval with empty *)

  let bottom = BOT
  let top = Nb BOT (* empty set *)
  let is_bottom a = a = BOT
  let subset a1 a2 = bot_included I.included_bot a1 a2
  let join a1 a2 = bot_neutral2 I.join_bot a1 a2
  let meet a1 a2 = bot_absorb2 (fun a1 a2 -> Nb (I.meet_bot a1 a2)) a1 a2
  let widen ctx a1 a2 = join a1 a2
  let fprint = bot_fprint I.fprint_bot
  let print printer a = unformat fprint printer a
end

module SimplifiedValue = struct
  include ArrayInit

  include GenValueId (struct
    type nonrec t = ArrayInit.t

    let name = "jasmin.array.values.init"
    let display = "array init"
  end)

  let accept_type typ =
    Debug.debug ~channel:name "LE type est %a" pp_typ typ;
    is_jasmin_array_type typ

  include DefaultValueFunctions

  let constant c t =
    Debug.debug ~channel:name "constant";
    match c with _ -> top

  let unop op t a tr = match op with _ -> top
  let binop op t1 a1 t2 a2 tr = match op with _ -> top
end

let () = register_simplified_value_abstraction (module SimplifiedValue)


open Sig.Abstraction.Stateless

module Domain =
struct

  include GenStatelessDomainId(struct
      let name = "jasmin.array.init"
    end)

  let mk_init_array ?(mode = WEAK) s = mk_attr_var ~mode s "no_init_range" T_int

  let checks = []

  let init prog man flow = flow

  let eval expr man flow =
    let range = erange expr in
    match ekind expr with
    | E_J_get(access,wisze, var, index) ->
      None
    | _ -> None


  let minus_range a b =
    match a,b with
    | _ when I.is_singleton a && I.is_singleton b ->
      if I.equal a b then BOT
      else Nb a
    | (l1,h1), (l2,h2) when I.is_singleton b ->
      if l2 == l1 then
        Nb (
          B.add l1 B.one, l2
        )
      else BOT
    | (l1,h1), (l2,h2) when I.intersect a b ->
      if B.gt l1 h2 &&  true then BOT
      else BOT
    | _ -> Nb a



  let update_set is_init wsize ?(len = 1) var index value range man flow=
    let open Universal.Numeric.Common in
    let index_interval = ask_and_reduce man.ask (mk_int_interval_query ~fast:false index) flow in
    let array_init = mk_var (mk_init_array var) range in
    let array_no_init_interval = ask_and_reduce man.ask (mk_int_interval_query ~fast:false array_init) flow in
    match index_interval, array_no_init_interval with
    (* No index found *)
    | BOT, _ -> None
    (* index can take only one value *)
    | Nb index_interval, Nb array_interval when I.is_singleton index_interval  && I.is_singleton array_interval -> None
    | _, BOT -> None
    (* index can take many values *)
    | Nb (li, hi), Nb (ali, ahi) -> None

  (* a_3n   = a3(n-1)+1 a3(n-1)+2 *)
  (* a_3n+1 = (a3n[0] + a3n[-1]) :: a3n-1 :: (a3n[0] + a3n[-1]) *)
  (* a_3n+2 = a3n :: 3 *)

  let exec stmt man flow =
    let range = srange stmt in
    match skind stmt with
    | S_assign ({ekind = E_J_Laset(access,wsize,var,index)}, expr) when is_jasmin_scalar @@ etyp expr ->
      man.eval ~translate:"Universal" expr flow >>$? fun value flow ->
      let query = Initialized.mk_scalar_is_init_query value in
      let is_init = ask_and_reduce man.ask query flow in
      (if Initialized.Init.is_init is_init then
        man.exec (mk_assign (mk_var (mk_init_array var) range) index range) flow
      else
        Post.return flow)
    |> OptionExt.return

    | S_assign ({ekind = E_J_Laset(access,wsize,var,index)}, t) ->
      None
    | S_assign ({ekind = E_J_Lasub(access,wsize,len,var,index)}, t) ->
      None
    | _ -> None


  let ask query man flow = None

  let print_expr man flow printer expr = ()

end


let () =
  register_stateless_domain (module Domain)
