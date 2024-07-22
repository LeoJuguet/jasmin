open Mopsa
open Sig.Abstraction.Stateless
open Universal.Ast
open Stubs.Ast
open Ast
module IntItv = Universal.Numeric.Values.Intervals.Integer.Value
module FltItv = Universal.Numeric.Values.Intervals.Float.I

(** This domain try to detect if there exist a division by zero *)

type check += CHK_J_OVERFLOW

let () =
  register_check (fun next fmt check ->
      match check with
      | CHK_J_OVERFLOW -> Format.fprintf fmt "Jasmin Overflow"
      | _ -> next fmt check)

type alarm_kind += A_J_overflow of expr

let () =
  register_alarm
    {
      check =
        (fun next -> function A_J_overflow _ -> CHK_J_OVERFLOW | a -> next a);
      compare =
        (fun next a1 a2 ->
          match (a1, a2) with
          | A_J_overflow e1, A_J_overflow e2 -> compare_expr e1 e2
          | _ -> next a1 a2);
      print =
        (fun next fmt -> function
          | A_J_overflow e ->
              Format.fprintf fmt "'%a' overflow may be present"
                (Debug.bold pp_expr) e
          | a -> next fmt a);
      join = (fun next -> next);
    }

type check += CHK_J_DIVIDE_BY_ZERO

let () =
  register_check (fun next fmt check ->
      match check with
      | CHK_J_DIVIDE_BY_ZERO -> Format.fprintf fmt "Jasmin Division by zero"
      | _ -> next fmt check)

type alarm_kind += A_J_divide_by_zero of expr

let () =
  register_alarm
    {
      check =
        (fun next -> function
          | A_J_divide_by_zero _ -> CHK_J_DIVIDE_BY_ZERO
          | a -> next a);
      compare =
        (fun next a1 a2 ->
          match (a1, a2) with
          | A_J_divide_by_zero e1, A_J_divide_by_zero e2 -> compare_expr e1 e2
          | _ -> next a1 a2);
      print =
        (fun next fmt -> function
          | A_J_divide_by_zero e ->
              Format.fprintf fmt "denominator '%a' may be null"
                (Debug.bold pp_expr) e
          | a -> next fmt a);
      join = (fun next -> next);
    }

module Domain = struct
  include GenStatelessDomainId (struct
    let name = "jasmin.integer.overflow"
  end)

  let do_check_arithmetic_overflow = ref false

  let () =
    register_domain_option name
      {
        key = "-j-check-arithmetic-overflow";
        doc = "check overflows in integer arithmetic";
        category = "Jasmin";
        default = string_of_bool !do_check_arithmetic_overflow;
        spec = Bool (fun b -> do_check_arithmetic_overflow := b);
      }

  let universal = "Universal"
  let checks = [ CHK_J_OVERFLOW ]
  let init _ _ flow = flow

  let jazz2num jexp =
    let parts, builder = structure_of_expr jexp in
    let nparts =
      {
        exprs = List.map (get_expr_translation "Universal") parts.exprs;
        stmts = [];
      }
    in
    let e = builder nparts in
    Debug.debug ~channel:"jazz2num" "%a -> %a" pp_expr jexp pp_expr e;
    { e with etyp = T_int }

  let check_overflow exp ?(nexp = jazz2num exp) man flow =
    if not !do_check_arithmetic_overflow then
      Eval.singleton exp flow |> Eval.add_translation "Universal" nexp
    else (
      Debug.debug ~channel:"Overflow" "overflow start";
      let typ = etyp exp in
      let rmin, rmax = Utils.range_of typ in
      Debug.debug ~channel:"Overflow info" "test range [%a, %a]" Z.pp_print rmin
        Z.pp_print rmax;
      let ritv = IntItv.of_z rmin rmax in
      Debug.debug ~channel:"Overflow" "marker";
      let itv =
        ask_and_reduce man.ask
          (Universal.Numeric.Common.mk_int_interval_query nexp)
          flow
      in
      Debug.debug ~channel:"Overflow" "overflow itv";
      if IntItv.subset itv ritv then (
        Debug.debug ~channel:"Overflow info" "safe [%a, %a]" Z.pp_print rmin
          Z.pp_print rmax;
        Flow.add_safe_check CHK_J_OVERFLOW (erange exp) flow
        |> Eval.singleton exp
        |> Eval.add_translation "Universal" nexp)
      else
        let itv =
          ask_and_reduce man.ask
            (Universal.Numeric.Common.mk_int_interval_query ~fast:false nexp)
            flow
        in
        if IntItv.subset itv ritv then (
          Debug.debug ~channel:"Overflow info" "safe finally [%a, %a]"
            Z.pp_print rmin Z.pp_print rmax;
          Flow.add_safe_check CHK_J_OVERFLOW (erange exp) flow
          |> Eval.singleton exp
          |> Eval.add_translation "Universal" nexp)
        else
          let flow' =
            if IntItv.meet itv ritv |> IntItv.is_bottom then
              let call_stack = Flow.get_callstack flow in
              let e2_origine = get_orig_expr exp in
              let alarm =
                mk_alarm (A_J_overflow e2_origine) call_stack exp.erange
              in
              Flow.raise_alarm alarm ~bottom:false ~warning:true man.lattice
                flow
            else
              let call_stack = Flow.get_callstack flow in
              let e2_origine = get_orig_expr exp in
              let alarm =
                mk_alarm (A_J_overflow e2_origine) call_stack exp.erange
              in
              Flow.raise_alarm alarm ~bottom:false ~warning:false man.lattice
                flow
          in
          Eval.singleton exp flow' |> Eval.add_translation "Universal" nexp)

  let rebuild_jazz_expr exp parts =
    let _, builder = structure_of_expr exp in
    builder { exprs = parts; stmts = [] }

  let exec stmt man flow =
    match skind stmt with
    | S_assign (({ ekind = E_var (v, mode) } as lval), expr)
      when etyp lval |> is_jasmin_scalar ->
        let new_var = mk_var ~mode { v with vtyp = T_int } (erange lval) in
        man.eval ~translate:universal expr flow >>$? fun expr' flow ->
        Debug.debug ~channel:name "exec assign finish";
        man.exec
          (mk_assign new_var expr' (srange stmt))
          flow ~route:(Semantic universal)
        |> OptionExt.return
    | _ -> None

  let eval expr man flow =
    match ekind expr with
    | E_var (var, opt)
      when (not (is_universal_type (vtyp var)))
           && not (is_jasmin_array_type (vtyp var)) ->
        let new_expr = mk_var { var with vtyp = T_int } (erange expr) in
        Eval.singleton expr flow
        |> Eval.add_translation universal new_expr
        |> OptionExt.return
    | E_binop (O_div, e1, e2) | E_binop (O_mod, e1, e2) ->
        man.eval e1 flow >>$? fun e1 flow ->
        man.eval e2 flow >>$? fun e2 flow ->
        let cond = ne e2 zero e2.erange in
        assume cond
          ~fthen:(fun tflow ->
            let flow =
              Flow.add_safe_check CHK_J_DIVIDE_BY_ZERO (erange expr) tflow
            in
            Debug.debug ~channel:"Overflow" "Binop test";
            let jexp = rebuild_jazz_expr expr [ e1; e2 ] in
            Debug.debug ~channel:"Overflow" "expr rebuild";
            check_overflow jexp man flow)
          ~felse:(fun fflow ->
            (* Raise a possible division by zero *)
            let call_stack = Flow.get_callstack fflow in
            let e2_origine = get_orig_expr e2 in
            let alarm =
              mk_alarm (A_J_divide_by_zero e2_origine) call_stack e2.erange
            in
            Flow.raise_alarm alarm ~bottom:true man.lattice fflow |> Eval.empty)
          man flow
        |> OptionExt.return
    | E_binop ((O_plus | O_mult | O_minus), e1, e2) ->
        Debug.debug ~channel:"Overflow" "Binop test";
        man.eval e1 flow >>$? fun e1 flow ->
        man.eval e2 flow >>$? fun e2 flow ->
        Debug.debug ~channel:"Overflow" "2 expr evaluate";
        let jexp = rebuild_jazz_expr expr [ e1; e2 ] in
        Debug.debug ~channel:"Overflow" "expr rebuild";
        Debug.debug ~channel:"Overflow" "%a : %a -> %a : %a" pp_expr expr pp_typ
          (etyp expr) pp_expr jexp pp_typ (etyp jexp);
        check_overflow jexp man flow |> OptionExt.return
    (* FIXME *)
    | E_binop (op, e1, e2) when is_jasmin_numeric_type (etyp expr) ->
        man.eval e1 ~translate:universal flow >>$? fun e1 flow ->
        man.eval e2 ~translate:universal flow >>$? fun e2 flow ->
        let new_expr =
          mk_binop
            ~etyp:(match etyp expr with T_J_U _ -> T_int | a -> a)
            e1 op e2 (erange expr)
        in
        Eval.singleton expr flow
        |> Eval.add_translation universal new_expr
        |> OptionExt.return
    | E_unop (O_J_int_of_word _, e) ->
        Debug.debug "is executed";
        man.eval e ~translate:universal flow >>$? fun e1 flow ->
        Eval.singleton expr flow
        |> Eval.add_translation universal { e1 with etyp = T_int }
        |> OptionExt.return
    | E_unop (op, e) when is_jasmin_numeric_type (etyp expr) ->
        Debug.debug "is executed";
        man.eval e ~translate:universal flow >>$? fun e1 flow ->
        Eval.singleton expr flow
        |> Eval.add_translation universal e1
        |> OptionExt.return
    | _ -> None

  let ask _ _ _ = None
  let print_expr man flow printer exp = ()
end

let () = register_stateless_domain (module Domain)
