open Mopsa
open Sig.Abstraction.Value
open Sig.Abstraction.Simplified_value
open Universal.Ast
open Stubs.Ast
open Ast







type ('a,_) query +=
  | Q_J_is_initialized_var : var -> ('a, bool) query




module Simplified_value = struct
  type t = bool

  let print fmt t =
    pp_bool ~path:[Key "init"] fmt t


  let top = true

  let bottom = false

  let is_bottom b = b = bottom

  let join = (||)

  let meet = (&&)

  let widen ctx = join

  let subset a1 a2 = a2 || (a1 = a2)


  include GenValueId(struct
      type nonrec t = t
      let name = "jasmin.integer.initialized"
      let display = "init"
    end)
  
  let constant c t =
    match t with
    | T_int | T_bool -> true
    | _ -> false

  let unop op t x t2=
    x

  let binop op t x1 t1 x2 t2 = x1 && x2

  let filter b t x = x

  let compare = Bool.compare

  include DefaultValueFunctions

  let accept_type = function
    | T_int | T_bool -> true
    | _ -> false


  let ask : type r. ('a,r) query -> ('a, t) man -> 'a ctx -> t -> r option =
    fun query man ctx env ->
    None



end


let () =
  register_simplified_value_abstraction (module Simplified_value)
