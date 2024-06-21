open Mopsa
open Ast
open Sig.Abstraction.Simplified_value
open Bot_top


type _ avalue_kind +=
   | V_return_value : expr list with_bot_top avalue_kind



module SimplifiedValue =
struct
    type t = expr list with_bot_top

    include GenValueId(struct
        type nonrec t = t
        let name = "jasmin.stub.return"
        let display = "return_values"
    end)

    let accept_type t =
    match t with
    | T_J_Return _ -> true
    | _ -> false

    include DefaultValueFunctions

    let bottom = BOT

    let top = TOP

    let is_bottom e = e = BOT

    let subset e1 e2 =
        bot_top_included (fun e1 e2 ->
            if List.length e1 < List.length e2 then e1 < e2
            else false
            ) e1 e2

    let join e1 e2 = panic ~loc:__LOC__ "join not used"
    let meet e1 e2 = panic ~loc:__LOC__ "meet not used"
    let widen e1 e2 = panic ~loc:__LOC__ "join not used"

    let constant t c =
        top

    let unop op top e t1 = TOP

    let binop op top e1 t1 e2 t2 = TOP


    let print printer e =
        unformat (bot_top_fprint (Jasmin.Utils.pp_list ", " pp_expr)) printer e

  let avalue : type r. r avalue_kind -> t -> r option =
    fun aval a ->
    match aval with
    | V_return_value -> Some a
    | _ -> None

end


let () =
    register_simplified_value_abstraction (module SimplifiedValue)
