open Format
open Printer
open Leakage

let rec pp_leak_e fmt =
  let p s = fprintf fmt "%s" s in
  function
  | LEmpty  -> p "ε"
  | LIdx _i -> p "ι"
  | LAdr _a -> p "α"
  | LSub s  -> fprintf fmt "sub(%a)" (pp_list ", " pp_leak_e) s  

let rec pp_tr_p fmt =
  let p s = fprintf fmt "%s" s in
  function
  | LS_const _n -> p "const"
  | LS_stk -> p "stk"
  | LS_Add (x, y) -> fprintf fmt "%a + %a" pp_tr_p x pp_tr_p y
  | LS_Mul (x, y) -> fprintf fmt "%a × %a" pp_tr_p x pp_tr_p y

let rec pp_e_tr fmt =
  let p s = fprintf fmt "%s" s in
  function
  | LT_id -> p "id"
  | LT_remove -> p "remove"
  | LT_const p -> pp_tr_p fmt p
  | LT_subi _n -> p "subi"
  | LT_lidx _n -> p "lidx"
  | LT_map m -> fprintf fmt "[↦%a]" (pp_list "; " pp_e_tr) m
  | LT_seq m -> fprintf fmt "[%a]" (pp_list "; " pp_e_tr) m
  | LT_compose (e, f) -> fprintf fmt "%a ∘ %a" pp_e_tr e pp_e_tr f
  | LT_rev -> p "rev"

let rec pp_il fmt =
  let p s = fprintf fmt "%s" s in
  let aux fmt ils = pp_list ";@." pp_il fmt ils in
  function
  | LT_ilkeep -> p "ilkeep"
  | LT_ilkeepa -> p "ilkeepa"
  | LT_ilcond_0 (e, f) -> fprintf fmt "cond0(%a, %a)" pp_e_tr e aux f
  | LT_ilcond_0' (e, f) -> fprintf fmt "cond0'(%a, %a)" pp_e_tr e aux f
  | LT_ilcond (e, f, g) -> fprintf fmt "cond(%a, %a, %a)" pp_e_tr e aux f aux g
  | LT_ilwhile_c'0 (_a, body) -> fprintf fmt "while0(%a)" aux body
  | LT_ilwhile_f body -> fprintf fmt "whileF(%a)" aux body
  | LT_ilwhile (a, e, f) -> fprintf fmt "while(%a, %a, %a)" Printer.pp_align a aux e aux f

let pp_nat fmt n =
  fprintf fmt "%d" (Conv.int_of_nat n)

let pp_i tbl fmt =
  let rec pp_i fmt =
  let p s = fprintf fmt "%s" s in
  function
  | LT_ikeep -> p "ikeep"
  | LT_ile e -> fprintf fmt "ile(%a)" pp_e_tr e
  | LT_icond (b, t, e) -> fprintf fmt "icond(%a, %a, %a)" pp_e_tr b (pp_list ";" pp_i) t (pp_list ";" pp_i) e
  | LT_icond_eval (b, a) -> fprintf fmt "icond_eval(%a, %a)" pp_bool b (pp_list ";" pp_i) a
  | LT_iwhile (a, b, c) -> fprintf fmt "iwhile(%a, %a, %a)" (pp_list ";" pp_i) a pp_e_tr b  (pp_list ";" pp_i) c
  | LT_ifor (a, b) -> fprintf fmt "ifor(%a, %a)" pp_e_tr a (pp_list ";" pp_i) b
  | LT_ifor_unroll (n, a) -> fprintf fmt "ifor_unroll(%a, %a)" pp_nat n (pp_list ";" pp_i) a
  | LT_icall (n, a, b) -> fprintf fmt "icall(%s, %a, %a)" (Conv.fun_of_cfun tbl n).Prog.fn_name pp_e_tr a pp_e_tr b
  | LT_icall_inline (a, n, i, r) -> fprintf fmt "icall_inline(%a, %s, %a, %a)" pp_nat a (Conv.fun_of_cfun tbl n).Prog.fn_name pp_nat i pp_nat r
  | LT_iwhilel(a, b, c, d) -> fprintf fmt "iwhilel(TODO, %a, %a, %a)" pp_e_tr b (pp_list ";" pp_i) c (pp_list ";" pp_i) d
  | LT_iremove -> p "iremove"
  | LT_icopn e -> p "icopn(TODO)"
  | LT_ilmul (a, b, c) -> fprintf fmt "ilmul(TODO, %a, TODO)" pp_e_tr b
  | LT_ilfopn (e, f) -> p "ilfopn(TODO, TODO)"
  | LT_icondl (a, b, c, d) -> fprintf fmt "icondl(TODO, %a, %a, %a)" pp_e_tr b (pp_list ";" pp_i) c (pp_list ";" pp_i) d
  | LT_ilif (a, b) -> fprintf fmt "ilif(TODO, %a)" pp_e_tr b
  | LT_ildiv (a, b) -> fprintf fmt "ildiv(%a, TODO)" pp_i a
  | LT_isingle a -> p "isingle(TODO)"
  | LT_idouble a -> p "idouble(TODO)"
  in pp_i fmt

let pp_funs pp_one tbl fmt =
  let pp_fun fmt (n, ils) =
    fprintf fmt "Function %s@.  %a@." (Conv.fun_of_cfun tbl n).Prog.fn_name
      (pp_list "\n  " pp_one) ils
  in
  pp_list "\n" pp_fun fmt

let pp_f_tr tbl fmt = pp_funs (pp_i tbl) tbl fmt
let pp_lf_tr tbl fmt = pp_funs pp_il tbl fmt

let pp_unr tbl fmt =
  List.iteri (fun n ->
      function
      | [ u ; cp ; dc ] -> begin
          fprintf fmt "Unrolling n° %d@.%a" n (pp_f_tr tbl) u;
          fprintf fmt "Constant-propagation@.%a" (pp_f_tr tbl) cp;
          fprintf fmt "Dead-code elimination@.%a" (pp_f_tr tbl) dc
        end
      | _ -> assert false)

let pp tbl fmt (tr, lin) : unit =
  fprintf fmt "Leakage transformers:@.";
  List.iteri (fun i -> fprintf fmt "Pass n° %d:@.%a@." i (pp_f_tr tbl)) tr;
  fprintf fmt "Linearization:@.%a@." (pp_lf_tr tbl) lin
