From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import word_ssrZ.

Require Import
  arch_params
  compiler_util
  expr
  fexpr
  one_varmap.
Require Import
  clear_stack
  register_zeroization
  register_zeroization_utils
  linearization
  lowering
  stack_alloc
  slh_lowering.
Require Import
  arch_decl
  arch_extra
  asm_gen
  label.
Require Import
  x86_decl
  x86_extra
  x86_instr_decl
  x86_lowering.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Section.
Context {atoI : arch_toIdent}.

Let flags_lexprs :=
  map (fun f => LLvar (mk_var_i (to_var f))) [:: OF; CF; SF; PF; ZF ].

(* Used to set up stack. *)
Definition x86_op_align (x : var_i) (ws : wsize) (al : wsize) : fopn_args :=
  let eflags := flags_lexprs in
  let ex := Rexpr (Fvar x) in
  let emask := fconst ws (- wsize_size al) in
  (eflags ++ [:: LLvar x ], Ox86 (AND ws), [:: ex; Rexpr emask ]).

(* ------------------------------------------------------------------------ *)
(* Stack alloc parameters. *)

Definition lea_ptr x y tag ofs : instr_r :=
  Copn [:: x] tag (Ox86 (LEA Uptr)) [:: add y (cast_const ofs)].

Definition x86_mov_ofs x tag vpk y ofs :=
  let addr :=
    if mk_mov vpk is MK_LEA
    then
      lea_ptr x y tag ofs
    else
      if ofs == 0%Z
      then mov_ws Uptr x y tag
      else lea_ptr x y tag ofs
  in
  Some addr.

Definition x86_immediate x z :=
  mov_ws Uptr (Lvar x) (cast_const z) AT_none.

Definition x86_saparams : stack_alloc_params :=
  {|
    sap_mov_ofs := x86_mov_ofs;
    sap_immediate := x86_immediate;
  |}.

(* ------------------------------------------------------------------------ *)
(* Linearization parameters. *)

Section LINEARIZATION.

Notation vtmpi := {| v_var := to_var RAX; v_info := dummy_var_info; |}.

Definition x86_allocate_stack_frame (rspi: var_i) (sz: Z) :=
  let p := Fapp2 (Osub (Op_w Uptr)) (Fvar rspi) (fconst Uptr sz) in
  ([:: LLvar rspi ], Ox86 (LEA Uptr), [:: Rexpr p ]).

Definition x86_free_stack_frame (rspi: var_i) (sz: Z) :=
  let p := Fapp2 (Oadd (Op_w Uptr)) (Fvar rspi) (fconst Uptr sz) in
  ([:: LLvar rspi ], Ox86 (LEA Uptr), [:: Rexpr p ]).

(* TODO: consider using VMOVDQA when the address is known to be aligned *)
Definition x86_lassign (x: lexpr) (ws: wsize) (e: rexpr) :=
  let op := if (ws <= U64)%CMP
            then MOV ws
            else VMOVDQU ws
  in ([:: x ], Ox86 op, [:: e ]).

Definition x86_set_up_sp_register
  (rspi : var_i) (sf_sz : Z) (al : wsize) (r : var_i) : seq fopn_args :=
  let i0 := x86_lassign (LLvar r) Uptr (Rexpr (Fvar rspi)) in
  let i1 := x86_allocate_stack_frame rspi sf_sz in
  let i2 := x86_op_align rspi Uptr al in
  [:: i0; i1; i2 ].

Definition x86_set_up_sp_stack
  (rspi : var_i) (sf_sz : Z) (al : wsize) (off : Z) : seq fopn_args :=
  let vtmpg := Fvar vtmpi in
  let i := x86_lassign (Store Uptr rspi (fconst Uptr off)) Uptr (Rexpr vtmpg) in
  x86_set_up_sp_register rspi sf_sz al vtmpi ++ [:: i ].

Definition x86_liparams : linearization_params :=
  {|
    lip_tmp := vname (v_var vtmpi);
    lip_not_saved_stack := [::];
    lip_allocate_stack_frame := x86_allocate_stack_frame;
    lip_free_stack_frame := x86_free_stack_frame;
    lip_set_up_sp_register :=
      fun rspi sf_sz al r => Some (x86_set_up_sp_register rspi sf_sz al r);
    lip_set_up_sp_stack :=
      fun rspi sf_sz al off => Some (x86_set_up_sp_stack rspi sf_sz al off);
    lip_lassign := fun x ws e => Some (x86_lassign x ws e);
  |}.

End LINEARIZATION.

(* ------------------------------------------------------------------------ *)
(* Lowering parameters. *)

Definition x86_loparams : lowering_params lowering_options :=
  {|
    lop_lower_i := lower_i;
    lop_fvars_correct := fvars_correct;
  |}.


(* ------------------------------------------------------------------------ *)
(* Speculative execution operator lowering parameters. *)

Definition lflags := nseq 5 (Lnone dummy_var_info sbool).

Definition x86_sh_lower
  (lvs : seq lval)
  (slho : slh_op)
  (es : seq pexpr) :
  option copn_args :=
  let O x := Oasm (ExtOp x) in
  match slho with
  | SLHinit   => Some (lvs, O Ox86SLHinit, es)

  | SLHupdate => Some (Lnone dummy_var_info ty_msf :: lvs, O Ox86SLHupdate, es)

  | SLHmove   => Some (lvs, O (Ox86SLHmove), es)

  | SLHprotect ws =>
    let extra := if (ws <= U64)%CMP then lflags else [:: Lnone dummy_var_info (sword ws)] in
    Some (extra ++ lvs, O (Ox86SLHprotect ws), es)

  | SLHprotect_ptr _ | SLHprotect_ptr_fail _ => None (* Taken into account by stack alloc *)
  end.

Definition x86_shparams : sh_params :=
  {|
    shp_lower := x86_sh_lower;
  |}.

(* ------------------------------------------------------------------------ *)
(* Assembly generation parameters. *)

Definition not_condt (c : condt) :=
  match c with
  | O_ct => NO_ct
  | NO_ct => O_ct
  | B_ct => NB_ct
  | NB_ct => B_ct
  | E_ct => NE_ct
  | NE_ct => E_ct
  | BE_ct => NBE_ct
  | NBE_ct => BE_ct
  | S_ct => NS_ct
  | NS_ct => S_ct
  | P_ct => NP_ct
  | NP_ct => P_ct
  | L_ct => NL_ct
  | NL_ct => L_ct
  | LE_ct => NLE_ct
  | NLE_ct => LE_ct
  end.

Definition or_condt ii e c1 c2 : cexec condt :=
  match c1, c2 with
  | L_ct, E_ct => ok LE_ct
  | E_ct, L_ct => ok LE_ct
  | B_ct, E_ct => ok BE_ct
  | E_ct, B_ct => ok BE_ct
  | _, _ => Error (E.berror ii e "Invalid condition (OR)")
  end.

Definition and_condt ii e c1 c2 :=
  match c1, c2 with
  | NB_ct, NE_ct => ok NBE_ct
  | NE_ct, NB_ct => ok NBE_ct
  | NE_ct, NL_ct => ok NLE_ct
  | NL_ct, NE_ct => ok NLE_ct
  | _, _ => Error (E.berror ii e "Invalid condition (AND)")
  end.

Definition of_var_e_bool ii (v: var_i) : cexec rflag :=
  match of_var v with
  | Some r => ok r
  | None => Error (asm_gen.E.invalid_flag ii v)
  end.

Fixpoint assemble_cond_r ii (e : fexpr) : cexec condt :=
  match e with
  | Fvar v =>
      Let r := of_var_e_bool ii v in
      match r with
      | OF => ok O_ct
      | CF => ok B_ct
      | ZF => ok E_ct
      | SF => ok S_ct
      | PF => ok P_ct
      end

  | Fapp1 Onot e =>
      Let c := assemble_cond_r ii e in
      ok (not_condt c)

  | Fapp2 Oor e1 e2 =>
      Let c1 := assemble_cond_r ii e1 in
      Let c2 := assemble_cond_r ii e2 in
      or_condt ii e c1 c2

  | Fapp2 Oand e1 e2 =>
      Let c1 := assemble_cond_r ii e1 in
      Let c2 := assemble_cond_r ii e2 in
      and_condt ii e c1 c2

  | Fapp2 Obeq (Fvar x1) (Fvar x2) =>
      Let r1 := of_var_e_bool ii x1 in
      Let r2 := of_var_e_bool ii x2 in
      if ((r1 == SF) && (r2 == OF)) || ((r1 == OF) && (r2 == SF))
      then ok NL_ct
      else Error (E.berror ii e "Invalid condition (NL)")

  | _ => Error (E.berror ii e "don't known how to compile the condition")

  end.

Definition assemble_cond ii (e: fexpr) : cexec condt :=
  assemble_cond_r ii e.

Definition x86_agparams : asm_gen_params :=
  {|
    agp_assemble_cond := assemble_cond;
  |}.


(* ------------------------------------------------------------------------ *)
(* Stack clearing parameters. *)

Section CLEAR_STACK.

Section RSP.

Context (rspi : var_i).

Let vlocal {t T} {_ : ToString t T} {_ : ToIdent T} (x : T) : gvar :=
  mk_lvar (mk_var_i (to_var x)).

Let tmp : gvar := vlocal RSI.
Let off : gvar := vlocal RDI.
Let r   : gvar := vlocal RCX.
Let vlr : gvar := vlocal XMM2.

Let rsp : gvar := mk_lvar rspi.
Let zf : gvar := vlocal ZF.
Let tmpi : var_i := gv tmp.
Let offi : var_i := gv off.
Let ri   : var_i := gv r.
Let vlri : var_i := gv vlr.
Let zfi : var_i := gv zf.

Notation rvar := (fun v => Rexpr (Fvar v)) (only parsing).
Notation rconst := (fun ws imm => Rexpr (fconst ws imm)) (only parsing).

Definition x86_clear_stack_loop_small (lbl : label) ws_align ws (max_stk_size : Z) : lcmd :=
  (* tmp = rsp; *)
  let i0 := Lopn [:: LLvar tmpi ] (Ox86 (MOV U64)) [:: rvar rspi ] in

  (* tmp &= - (wsize_size ws_align); *)
  let i1 :=
    Lopn
      (flags_lexprs ++ [:: LLvar tmpi ])
      (Ox86 (AND U64))
      [:: rvar tmpi; rconst U64 (- wsize_size ws_align)%Z ]
  in

  (* off = -max_stk_size; *)
  let i2 :=
    Lopn
      [:: LLvar offi ]
      (Ox86 (MOV U64))
      [:: rconst U64 (- max_stk_size)%Z ]
  in

  (* l1: *)
  let i3 := Llabel InternalLabel lbl in

  (* (ws)[tmp + off] = 0; *)
  let i4 :=
    Lopn [:: Store ws tmpi (Fvar offi) ] (Ox86 (MOV ws)) [:: rconst ws 0 ]
  in

  (* ?{zf}, off = #ADD(off, wsize_size ws); *)
  let i5 :=
    Lopn
      (flags_lexprs ++ [:: LLvar offi ])
      (Ox86 (ADD U64))
      [:: rvar offi; rconst U64 (wsize_size ws) ]
  in

  (* if (!zf) goto l1 *)
  let i6 := Lcond (Fapp1 Onot (Fvar zfi)) lbl in

  map (MkLI dummy_instr_info) [:: i0; i1; i2; i3; i4; i5; i6 ].

(* we read rsp first, so that we are sure that we don't modify it ; otherwise,
   we would have to add hypotheses like rsp <> XMM2 *)
Definition x86_clear_stack_loop_large (lbl : label) ws_align ws (max_stk_size : Z) : lcmd :=
  (* tmp = rsp; *)
  let i1 := Lopn [:: LLvar tmpi ] (Ox86 (MOV U64)) [:: rvar rspi ] in

  (* ymm = #set0_ws(); *)
  let i0 := Lopn [:: LLvar vlri ] (Oasm (ExtOp (Oset0 ws))) [::] in

  (* tmp &= - (wsize_size ws_align); *)
  let i2 :=
    Lopn
      (flags_lexprs ++ [:: LLvar tmpi ])
      (Ox86 (AND U64))
      [:: rvar tmpi; rconst U64 (- wsize_size ws_align)%Z ]
  in

  (* off = -max_stk_size; *)
  let i3 :=
    Lopn [:: LLvar offi ] (Ox86 (MOV U64)) [:: rconst U64 (- max_stk_size)%Z ]
  in

  (* l1: *)
  let i4 := Llabel InternalLabel lbl in

  (* (ws)[tmp + off] = ymm; *)
  let i5 :=
    Lopn [:: Store ws tmpi (Fvar offi) ] (Ox86 (VMOVDQU ws)) [:: rvar vlri ]
  in

  (* ?{zf}, off = #ADD(off, wsize_size ws); *)
  let i6 :=
    Lopn
      (flags_lexprs ++ [:: LLvar offi ])
      (Ox86 (ADD U64))
      [:: rvar offi; rconst U64 (wsize_size ws) ]
  in

  (* if (!zf) goto l1 *)
  let i7 := Lcond (Fapp1 Onot (Fvar zfi)) lbl in

  map (MkLI dummy_instr_info) [:: i1; i0; i2; i3; i4; i5; i6; i7 ].

Definition x86_clear_stack_loop lbl ws_align ws max_stk_size :=
  if (ws <= U64)%CMP then x86_clear_stack_loop_small lbl ws_align ws max_stk_size
  else x86_clear_stack_loop_large lbl ws_align ws max_stk_size.

Definition x86_clear_stack_unrolled_small ws_align ws (max_stk_size : Z) : lcmd :=
  (* tmp = rsp; *)
  let i0 := Lopn [:: LLvar tmpi ] (Ox86 (MOV U64)) [:: rvar rspi ] in

  (* tmp &= - (wsize_size ws_align); *)
  let i1 :=
    Lopn
      (flags_lexprs ++ [:: LLvar tmpi ])
      (Ox86 (AND U64))
      [:: rvar tmpi; rconst U64 (- wsize_size ws_align)%Z ]
  in

  (* (ws)[tmp + off] = 0; *)
  let f off :=
    Lopn
      [:: Store ws tmpi (fconst U64 (- off)) ]
      (Ox86 (MOV ws))
      [:: rconst ws 0 ]
  in

  let offs := map (fun x => x * wsize_size ws)%Z (rev (ziota 1 (max_stk_size / wsize_size ws))) in

  map (MkLI dummy_instr_info) [:: i0, i1 & map f offs].

Definition x86_clear_stack_unrolled_large ws_align ws (max_stk_size : Z) : lcmd :=
  (* tmp = rsp; *)
  let i1 := Lopn [:: LLvar tmpi ] (Ox86 (MOV U64)) [:: rvar rspi ] in

  (* ymm = #set0_ws(); *)
  let i0 := Lopn [:: LLvar vlri ] (Oasm (ExtOp (Oset0 ws))) [::] in

  (* tmp &= - (wsize_size ws_align); *)
  let i2 :=
    Lopn
      (flags_lexprs ++ [:: LLvar tmpi ])
      (Ox86 (AND U64))
      [:: rvar tmpi; rconst U64 (- wsize_size ws_align)%Z ]
  in

  (* (ws)[tmp + off] = ymm; *)
  let f off :=
    Lopn
      [:: Store ws tmpi (fconst U64 (- off)) ]
      (Ox86 (VMOVDQU ws))
      [:: rvar vlri ]
  in

  let offs := map (fun x => x * wsize_size ws)%Z (rev (ziota 1 (max_stk_size / wsize_size ws))) in

  map (MkLI dummy_instr_info) [:: i1, i0, i2 & map f offs].

End RSP.

Definition x86_clear_stack_unrolled rsp ws_align ws max_stk_size :=
  if (ws <= U64)%CMP then x86_clear_stack_unrolled_small rsp ws_align ws max_stk_size
  else x86_clear_stack_unrolled_large rsp ws_align ws max_stk_size.

Definition x86_clear_stack_cmd
  (css : cs_strategy) rsp (lbl : label) ws_align ws (max_stk_size : Z) : cexec lcmd :=
  match css with
  | CSSloop => ok (x86_clear_stack_loop rsp lbl ws_align ws max_stk_size)
  | CSSunrolled => ok (x86_clear_stack_unrolled rsp ws_align ws max_stk_size)
  end.

End CLEAR_STACK.

Definition x86_csparams : clear_stack_params :=
  {|
    cs_clear_stack_cmd := x86_clear_stack_cmd;
  |}.


(* ------------------------------------------------------------------------ *)
(* Register zeroization parameters. *)

Section REGISTER_ZEROIZATION.

Context {ovmi : one_varmap_info}.

Definition x86_zeroize_var
  (err_register : var -> pp_error_loc) (x : var) : cexec lopn_args :=
  if vtype x is sword ws
  then
    let xi := {| v_var := x; v_info := dummy_var_info; |} in
    if (ws <= U64)%CMP
    then ok ([:: LLvar xi ], Ox86 (MOV ws), [:: Rexpr (fconst ws 0) ])
    else ok ([:: LLvar xi ], Oasm (ExtOp (Oset0 ws)), [::])
  else
    Error (err_register x).

Definition x86_zeroize_flags
  (err_flags : pp_error_loc) (ox : option var) : cexec (seq lopn_args) :=
  if ox is Some x
  then
    let xi := {| v_var := x; v_info := dummy_var_info; |} in
    let e := Rexpr (Fvar xi) in
    let
      to_lflag f := LLvar {| v_var := to_var f; v_info := dummy_var_info; |}
    in
    let lflags := map to_lflag [:: OF; CF; SF; PF; ZF ] in
    ok [:: (lflags, Ox86 (CMP reg_size), [:: e; e ]) ]
  else
    Error (err_flags).

Definition x86_rzparams : register_zeroization_params :=
  {|
    rz_cmd_args := naive_rz_cmd_args x86_zeroize_var x86_zeroize_flags;
  |}.

End REGISTER_ZEROIZATION.


(* ------------------------------------------------------------------------ *)
(* Shared parameters. *)

Definition x86_is_move_op (o : asm_op_t) :=
  match o with
  | BaseOp (None, MOV _) => true
  | BaseOp (None, VMOVDQA _) => true
  | BaseOp (None, VMOVDQU _) => true
  | ExtOp Ox86SLHmove => true
  | _ => false
  end.

(* ------------------------------------------------------------------------ *)

Definition x86_params
  {ovmi : one_varmap_info} : architecture_params lowering_options :=
  {|
    ap_sap := x86_saparams;
    ap_lip := x86_liparams;
    ap_lop := x86_loparams;
    ap_agp := x86_agparams;
    ap_csp := x86_csparams;
    ap_rzp := x86_rzparams;
    ap_shp := x86_shparams;
    ap_is_move_op := x86_is_move_op;
  |}.

End Section.
