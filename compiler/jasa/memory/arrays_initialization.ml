open Mopsa
open Sig.Abstraction.Simplified_value
open Universal.Ast
open Stubs.Ast
open Ast
open Bot
module I = Mopsa.ItvUtils.IntItv

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
