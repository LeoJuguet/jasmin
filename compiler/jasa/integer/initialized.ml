open Mopsa
open Sig.Abstraction.Value
open Sig.Abstraction.Simplified_value
open Sig.Abstraction.Stateless
open Universal.Ast
open Stubs.Ast
open Ast
open Bot



module Init =
  struct
  type t = bool with_bot

  let print fmt t =
    unformat (bot_fprint Format.pp_print_bool) ~path:[Key "init"] fmt t



  let top = Nb false

  let bottom = BOT

  let is_bottom t = match t with
    | BOT -> true
    | _ -> false

  let join = bot_neutral2 (||)

  let meet = bot_absorb2 (fun a1 a2 -> Nb (a1 && a2))

  let widen ctx = join

  let subset a1 a2 =
    bot_included (fun a1 a2 ->
    a2 || (a1 = a2)) a1 a2


  let compare a1 a2 =
    bot_compare (Stdlib.Bool.compare) a1 a2

  let is_init t = match t with
    | Nb true -> true
    | _ -> false

  end



(* Avalue *)

type _ avalue_kind +=
  V_jasmin_scalar_initialized : Init.t avalue_kind



let () =
  register_avalue {
    typ = (fun (type a) next (avk:a avalue_kind) ->
      match avk with
        | V_jasmin_scalar_initialized -> T_int
        | _ -> next.pool_typ avk
      );
    bottom = (
      let f : type a. avalue_pool -> a avalue_kind -> a =
        fun next avk ->
          match avk with
          | V_jasmin_scalar_initialized -> Init.bottom
          | _ -> next.pool_bottom avk
      in f
    );
    top = (
      let f : type a. avalue_pool -> a avalue_kind -> a =
        fun next avk ->
          match avk with
          | V_jasmin_scalar_initialized -> Init.top
          | _ -> next.pool_top avk
      in f
    );
    join = (
        let f : type a. avalue_pool -> a avalue_kind -> a -> a -> a =
          fun next avk av1 av2 ->
            match avk with
            | V_jasmin_scalar_initialized -> Init.join av1 av2
            | _ -> next.pool_join avk av1 av2
        in f
      );
    meet = (
        let f : type a. avalue_pool -> a avalue_kind -> a -> a -> a =
          fun next avk av1 av2 ->
            match avk with
            | V_jasmin_scalar_initialized -> Init.meet av1 av2
            | _ -> next.pool_meet avk av1 av2
        in f
      );
    print = (
      let f : type a. avalue_pool -> a avalue_kind -> Format.formatter -> a -> unit =
        fun next avk fmt av ->
          match avk with
          | V_jasmin_scalar_initialized -> Bot.bot_fprint (Format.pp_print_bool) fmt av
          | _ -> next.pool_print avk fmt av
      in f
    );

    compare = (
        let f : type a b. avalue_pool -> a avalue_kind -> a -> b avalue_kind -> b -> int =
          fun next avk1 av1 avk2 av2 ->
            match avk1, avk2 with
            | V_jasmin_scalar_initialized, V_jasmin_scalar_initialized -> Init.compare av1 av2
            | _ -> next.pool_compare avk1 av1 avk2 av2
        in f
      );
  }

(* Value *)
module Simplified_Value = struct
  type t = bool with_bot

  let print fmt t =
    unformat (bot_fprint Format.pp_print_bool) ~path:[Key "init"] fmt t



  let top = Nb false

  let bottom = BOT

  let is_bottom t = match t with
    | BOT -> true
    | _ -> false

  let join = bot_neutral2 (||)

  let meet = bot_absorb2 (fun a1 a2 -> Nb (a1 && a2))

  let widen ctx = join

  let subset a1 a2 =
    bot_included (fun a1 a2 ->
    a2 || (a1 = a2)) a1 a2


  include GenValueId(struct
      type nonrec t = t
      let name = "jasmin.integer.initialized"
      let display = "init"
    end)
  
  let constant c t =
    match c with
    | C_int _ | C_bool _ -> Nb true
    | C_top _ -> Nb false (* default value of variables (when S_add is executed) *)
    | _ -> Nb false

  let unop op t x t2=
    x

  let binop op t x1 t1 x2 t2 = meet x1 x2

  let filter b t x = x

  let compare = Bool.compare

  include DefaultValueFunctions

  let accept_type = function
    | T_int | T_bool  | T_J_Bool | T_J_Int | T_J_U _ -> true
    | _ -> false

  let avalue : type r. r avalue_kind -> t -> r option =
    fun aval a ->
    match aval with
    | V_jasmin_scalar_initialized -> Some a
    | _ -> None

end


let () =
  register_simplified_value_abstraction (module Simplified_Value)



type check +=
  | CHK_J_SCALAR_INIT

let () =
  register_check (fun next fmt chk ->
    match chk with
      | CHK_J_SCALAR_INIT -> Format.fprintf fmt "Jasmin Scalar Initialization"
      | _ -> next fmt chk)

type alarm_kind +=
  | A_J_Not_Init of expr

let () =
  register_alarm {
    check = (fun next -> function A_J_Not_Init _ -> CHK_J_SCALAR_INIT | a -> next a);
    compare = (fun next a1 a2 ->
      match a1, a2 with
        | A_J_Not_Init a1, A_J_Not_Init a2 -> compare_expr a1 a2
        | _ -> next a1 a2);
    print = (fun next fmt -> function
        | A_J_Not_Init e -> Format.fprintf fmt "'%a' may not be initialized" pp_expr e
        | c -> next fmt c
      );
    join = (fun a -> a)
  }


module Domain =
  struct
    include GenStatelessDomainId(struct
        let name = "jasmin.integer.domain"
      end)

  let checks = []

  module V = MakeValue(Simplified_Value)

  let init prog man flow = flow


  let exec stmt (man:('a, unit) man) flow =
    match skind stmt with
    | S_assign (lval, expr) when is_jasmin_scalar (etyp expr) ->
      man.eval expr ~translate:"Universal" flow >>$? fun e flow ->
      let aval = mk_avalue_query e V_jasmin_scalar_initialized in
      let is_init = ask_and_reduce man.ask aval flow in
      let flow' = if Init.is_init is_init then (
        Debug.debug ~channel:name "Is initialized";
        Flow.add_safe_check CHK_J_SCALAR_INIT (erange expr) flow
      )
      else (
        Debug.debug ~channel:name "Is not initialized";
        let call_stack = Flow.get_callstack flow in
        let origin = get_orig_expr expr in
        let alarm = mk_alarm (A_J_Not_Init origin) call_stack (erange expr) in
        Flow.raise_alarm alarm ~bottom:false  man.lattice flow
      ) in
      man.exec stmt ~route:(Below name) flow'
    |> OptionExt.return
    | _ -> None

  let eval expr man flow = None


  let ask _ _ _ = None

  let print_expr man flow printer exp = ()

  end

let () =
  register_stateless_domain (module Domain)
