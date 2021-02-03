(* ** License
 * -----------------------------------------------------------------------
 * Copyright 2016--2017 IMDEA Software Institute
 * Copyright 2016--2017 Inria
 *
 * Permission is hereby granted, free of charge, to any person obtaining
 * a copy of this software and associated documentation files (the
 * "Software"), to deal in the Software without restriction, including
 * without limitation the rights to use, copy, modify, merge, publish,
 * distribute, sublicense, and/or sell copies of the Software, and to
 * permit persons to whom the Software is furnished to do so, subject to
 * the following conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
 * IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
 * CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
 * TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
 * SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 * ----------------------------------------------------------------------- *)

From mathcomp Require Import all_ssreflect.
Require Import x86_gen expr.
Import ZArith.
Require Import compiler_util allocation inline dead_calls unrolling remove_globals
   constant_prop dead_code array_expansion lowering stack_alloc linear x86_sem.
Import Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition unroll1 (p:prog) : cfexec (prog * seq leak_f_tr) :=
  let up := unroll_prog p in
  let cp := const_prop_prog up.1 in
  Let dp := dead_code_prog cp.1 in 
  cfok (dp.1, [:: up.2; cp.2; dp.2]).

Fixpoint unroll (n:nat) (p:prog) : cfexec (prog * seq leak_f_tr) :=
  match n with
  | O   => cferror Ferr_loop
  | S n =>
    Let p' := unroll1 p in
    if p == p'.1 then cfok (p, p'.2)
    else unroll n p'.1
  end.

Definition unroll_loop (p:prog) : cfexec (prog * seq leak_f_tr) := unroll Loop.nb p.

Section COMPILER.

Variant compiler_step :=
  | Typing                      : compiler_step
  | ParamsExpansion             : compiler_step
  | Inlining                    : compiler_step
  | RemoveUnusedFunction        : compiler_step
  | Unrolling                   : compiler_step
  | Splitting                   : compiler_step
  | AllocInlineAssgn            : compiler_step
  | DeadCode_AllocInlineAssgn   : compiler_step
  | ShareStackVariable          : compiler_step
  | DeadCode_ShareStackVariable : compiler_step
  | RegArrayExpansion           : compiler_step
  | RemoveArrInit               : compiler_step
  | RemoveGlobal                : compiler_step
  | LowerInstruction            : compiler_step
  | RegAllocation               : compiler_step
  | DeadCode_RegAllocation      : compiler_step
  | StackAllocation             : compiler_step
  | Linearisation               : compiler_step
  | Assembly                    : compiler_step.

Record compiler_params := {
  rename_fd    : instr_info -> funname -> fundef -> fundef;
  expand_fd    : funname -> fundef -> fundef;
  var_alloc_fd : funname -> fundef -> fundef;
  share_stk_fd : funname -> fundef -> fundef;
  lowering_vars : fresh_vars;
  inline_var   : var -> bool;
  is_var_in_memory : var_i → bool;
  reg_alloc_fd : funname -> fundef -> fundef;
  stk_alloc_fd : fun_decl -> Z * Ident.ident * list (var * Z) * (list var * stack_alloc.saved_stack);
  print_prog   : compiler_step -> prog -> prog;
  print_linear : lprog -> lprog;
  warning      : instr_info -> warning_msg -> instr_info;
  lowering_opt : lowering_options;
  is_glob      : var -> bool;
  fresh_id     : glob_decls -> var -> Ident.ident;
}.

Variable cparams : compiler_params.

Definition expand_prog (p:prog) :=
  {| p_globs := p_globs p;
     p_funcs := List.map (fun f => (f.1, cparams.(expand_fd) f.1 f.2)) (p_funcs p) |}.

Definition var_alloc_prog (p:prog) :=
  {| p_globs := p_globs p;
     p_funcs := List.map (fun f => (f.1, cparams.(var_alloc_fd) f.1 f.2)) (p_funcs p) |}.

Definition share_stack_prog (p:prog) :=
  {| p_globs := p_globs p;
     p_funcs := List.map (fun f => (f.1, cparams.(share_stk_fd) f.1 f.2)) (p_funcs p) |}.

Definition reg_alloc_prog (p:prog) :=
  {| p_globs := p_globs p;
     p_funcs := List.map (fun f => (f.1, cparams.(reg_alloc_fd) f.1 f.2)) (p_funcs p) |}.

(* need to also return sequence of leak transformers *)
Definition compile_prog (entries : seq funname) (p:prog) : result fun_error (glob_decls * lprog * seq leak_f_tr) :=
  Let pi := inline_prog_err cparams.(inline_var) cparams.(rename_fd) p in
  let p := cparams.(print_prog) Inlining pi.1 in

  Let p := dead_calls_err_seq entries p in
  let p := cparams.(print_prog) RemoveUnusedFunction p in

  Let pu := unroll Loop.nb p in
  let p := cparams.(print_prog) Unrolling pu.1 in

  let pc := const_prop_prog p in
  let p := cparams.(print_prog) Unrolling pc.1 in

  let pv := var_alloc_prog p in
  let pv := cparams.(print_prog) AllocInlineAssgn pv in
  Let _ := CheckAllocReg.check_prog p pv in
  Let pvd := dead_code_prog pv in
  let pv := cparams.(print_prog) DeadCode_AllocInlineAssgn pvd.1 in

  let ps := share_stack_prog pv in
  let ps := cparams.(print_prog) ShareStackVariable ps in
  Let _ := CheckAllocReg.check_prog pv ps in
  Let psd := dead_code_prog ps in
  let ps := cparams.(print_prog) DeadCode_ShareStackVariable psd.1 in

  let prr := remove_init_prog ps in
  let pr := cparams.(print_prog) RemoveArrInit prr.1 in

  let pe := expand_prog pr in
  let pe := cparams.(print_prog) RegArrayExpansion pe in
  Let _ := CheckExpansion.check_prog pr pe in

  Let pgr := remove_glob_prog cparams.(is_glob) cparams.(fresh_id) pe in
  let pg := cparams.(print_prog) RemoveGlobal pgr.1 in

  if (fvars_correct cparams.(lowering_vars) (p_funcs pg)) then
    let pll := lower_prog cparams.(lowering_opt) cparams.(warning) cparams.(lowering_vars) cparams.(is_var_in_memory) pg in
    let pl := cparams.(print_prog) LowerInstruction pll.1 in

    let pa := reg_alloc_prog pl in
    let pa := cparams.(print_prog) RegAllocation pa in
    Let _ := CheckAllocReg.check_prog pl pa in
    Let pdd := dead_code_prog pa in
    let pd := cparams.(print_prog) DeadCode_RegAllocation pdd.1 in

    (* stack_allocation                    *)
    Let ps := stack_alloc.alloc_prog cparams.(stk_alloc_fd) pd in
    (* linearisation                     *)
    Let pl := linear_prog ps.1 in
    let pl := cparams.(print_linear) pl.1 in
    (* asm                               *)
    cfok (p_globs pd, pl, [:: pi.2] ++ pu.2 ++ [:: pc.2; pvd.2; psd.2; prr.2; pgr.2; pll.2; pdd.2])

  else cferror Ferr_lowering.

Check compile_prog.

Definition check_signature (p: prog) (lp: lprog) (fn: funname) : bool :=
  if get_fundef lp fn is Some fd' then
    if get_fundef (p_funcs p) fn is Some fd then
      signature_of_fundef fd == signature_of_lfundef fd'
    else true
  else true.

Definition compile_prog_to_x86 entries (p: prog): result fun_error (glob_decls * xprog * seq leak_f_tr) :=
  Let lp := compile_prog entries p in
  let : (lpg, lpp, lpl) := lp in 
  Let _ := assert (all (check_signature p lpp) entries) Ferr_lowering in
  Let lx := assemble_prog lpp in
  ok (lpg, lx, lpl).

End COMPILER.
