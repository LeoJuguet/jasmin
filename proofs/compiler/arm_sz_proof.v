From Coq Require Import
  Relations
  ZArith.
From mathcomp Require Import all_ssreflect all_algebra.

Require Import
  fexpr
  fexpr_sem
  linear
  linear_sem
  psem
  psem_facts.
Require Import linearization.
Require Import
  arch_decl
  arch_extra
  asm_gen
  sem_params_of_arch_extra.
Require Import
  arm_decl
  arm_extra
  arm_instr_decl
  arm_lowering
  arm_lowering_proof.
Require Export arm_params.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Section Section.

Context
  {atoI  : arch_toIdent}
  {syscall_state : Type}
  {sc_sem : syscall_sem syscall_state}
  {call_conv : calling_convention}.

Section ARM_PARAMS_PROOF.
Lemma arm_cmd_load_large_imm_lsem lp fn s ii P Q xname imm :
  let: x := {| vname := xname; vtype := sword reg_size; |} in
  let: xi := {| v_var := x; v_info := dummy_var_info; |} in
  let: lcmd := map (li_of_lopn_args ii) (arm_cmd_load_large_imm xi imm) in
  is_linear_of lp fn (P ++ lcmd ++ Q)
  -> (0 <= imm < wbase reg_size)%Z
  -> exists vm',
       let: ls := of_estate s fn (size P) in
       let: ls' :=
         {|
           lscs := lscs ls;
           lmem := lmem ls;
           lvm := vm';
           lfn := fn;
           lpc := size P + size lcmd;
         |}
       in
       [/\ lsem lp ls ls'
         , vm' = lvm ls [\ Sv.singleton x ]
         & get_var vm' x = ok (Vword (wrepr reg_size imm))
       ].
Proof. Admitted.

Notation next_ls ls m vm :=
  {|
    lscs := lscs ls;
    lmem := m;
    lvm := vm;
    lfn := lfn ls;
    lpc := lpc ls + 1;
  |}
  (only parsing).

Notation next_vm_ls ls vm := (next_ls ls (lmem ls) vm) (only parsing).
Context
  (xname : Ident.ident)
  (vi : var_info).

Notation x :=
  {|
    v_var := {| vname := xname; vtype := sword reg_size; |};
    v_info := vi;
  |}.


Lemma arm_op_align_eval_instr lp ls ii y al wy :
  get_var (lvm ls) (v_var y) = ok (Vword wy)
  -> let: li := li_of_lopn_args ii (arm_op_align x y al) in
     let: wx' := align_word al wy in
     let: vm' := (lvm ls).[v_var x <- ok (pword_of_word wx')]%vmap in
     eval_instr lp li ls = ok (next_vm_ls ls vm').
Proof. Admitted.


End ARM_PARAMS_PROOF.

Let vrsp := mk_var_i (to_var SP).
Let vsaved_sp := mk_var_i (to_var R02).
Let voff := mk_var_i (to_var R03).
Let vzero := mk_var_i (to_var R12).
Let vzf := mk_var_i (to_var ZF).
Let leflags := [seq LLvar (mk_var_i (to_var f)) | f <- rflags ].

Definition vm_of_init
  (vm : vmap) (al : wsize) (max_stk_size : Z) (wrsp : word Uptr) : vmap :=
  let: wmax := wrepr reg_size max_stk_size in
  let: wrsp' := (align_word al wrsp - wmax)%R in
  vm.[v_var vsaved_sp <- ok (pword_of_word wrsp)]
    .[v_var voff <- ok (pword_of_word wmax)]
    .[v_var vrsp <- ok (pword_of_word wrsp')]
    .[v_var vzero <- ok (pword_of_word 0%R)]%vmap.

Lemma cat_cons1 {T} {p q} {x : T} :
  p ++ x :: q = (p ++ [:: x ]) ++ q.
Proof. by rewrite /= -catA. Qed.

Lemma help :
  [/\ v_var vrsp <> v_var vsaved_sp
    , v_var vrsp <> v_var voff
    , v_var vrsp <> v_var vzero
    , v_var vsaved_sp <> v_var vzero
    , v_var vsaved_sp <> v_var voff
    & v_var vzero <> v_var voff
  ].
Proof. split; move=> h; by have := inj_to_var h. Qed.

Lemma sz_initP lp fn al max_stk_size pre pos s (wrsp : word arm_reg_size) :
  let: lc := sz_init vrsp al max_stk_size in
  is_linear_of lp fn (pre ++ lc ++ pos) ->
  (0 <= max_stk_size < wbase reg_size)%Z ->
  get_var (evm s) (v_var vrsp) = ok (Vword wrsp) ->
  let: ls := of_estate s fn (size pre) in
  exists2 vm',
    let: ls' := of_estate (with_vm s vm') fn (size pre + size lc) in
    lsem lp ls ls'
    & (forall x, vm'.[x] = (vm_of_init (evm s) al max_stk_size wrsp).[x])%vmap.
Proof.
  move: help => [??????].
  rewrite /= map_cat /= -catA.
  set isave_sp := li_of_lopn_args _ (arm_op_mov _ _).
  set iload_off := map _ (arm_cmd_load_large_imm _ _).
  set ialign := li_of_lopn_args _ (arm_op_align _ _ _).
  set istore_sp := li_of_lopn_args _ (arm_op_mov _ _).
  set isub_sp := li_of_lopn_args _ (arm_op_sub _ _ _).
  set izero := li_of_lopn_args _ (arm_op_movi _ _).
  move=> hbody hmax hgetrsp.

  set wmax := wrepr reg_size max_stk_size.
  set wrsp' := (align_word al wrsp - wmax)%R.
  set vm0 := (evm s).[v_var vsaved_sp <- ok (pword_of_word wrsp)]%vmap.

  rewrite cat_cons1 in hbody.
  have /= [vm1 [hsem1 hvm1 hgetoff]] :=
    arm_cmd_load_large_imm_lsem (with_vm s vm0) hbody hmax.
  rewrite size_cat /= in hsem1.

  eexists.
  - apply: lsem_step.
    + rewrite -!catA in hbody.
      rewrite /lsem1 /step (find_instrE hbody) oseq.onth_cat ltnn subnn /=.
      rewrite /eval_instr /= hgetrsp /= /exec_sopn /= truncate_word_u /=.
      rewrite /of_estate /with_vm /= pword_of_wordE -addn1.
      reflexivity.

    apply: (lsem_trans hsem1).
    clear hsem1.

    rewrite catA in hbody.
    apply: lsem_step.
    + rewrite /lsem1 /step (find_instrE hbody) oseq.onth_cat.
      rewrite !size_cat size_map /=.
      rewrite ltnn subnn.
      Opaque wsize_size.
      rewrite /eval_instr /=.
      rewrite (get_var_eq_except _ hvm1); last by move=> /Sv.singleton_spec.
      rewrite get_var_eq /= /exec_sopn /= !truncate_word_u /=.
      rewrite /of_estate /with_vm /=.
      rewrite wrepr_wnot ZlnotE Z.sub_1_r Z.add_1_r Z.succ_pred.
      rewrite -/(align_word al wrsp) pword_of_wordE.
      reflexivity.

    rewrite (cat_cons1 (x := ialign)) in hbody.
    apply: lsem_step.
    + rewrite /lsem1 /step (find_instrE hbody) oseq.onth_cat.
      rewrite !size_cat size_map /= !addn1 ltnn subnn.
      rewrite /eval_instr /= get_var_eq /exec_sopn /= !truncate_word_u /=.
      rewrite /of_estate /with_vm /= pword_of_wordE.
      reflexivity.

    rewrite (cat_cons1 (x := istore_sp)) in hbody.
    apply: lsem_step.
    + rewrite /lsem1 /step (find_instrE hbody) oseq.onth_cat.
      rewrite !size_cat size_map !addn1 ltnn subnn.
      rewrite /eval_instr /= get_var_eq /exec_sopn /=.
      t_get_var.
      rewrite hgetoff /= !truncate_word_u /=.
      rewrite /of_estate /with_vm /= pword_of_wordE.
      reflexivity.

    rewrite (cat_cons1 (x := isub_sp)) in hbody.
    apply: lsem_step.
    + rewrite /lsem1 /step (find_instrE hbody) oseq.onth_cat.
      rewrite !size_cat size_map !addn1 ltnn subnn.
      rewrite /eval_instr /= /exec_sopn /= !truncate_word_u /=.
      rewrite /of_estate /with_vm /= pword_of_wordE.
      reflexivity.

    rewrite /of_estate /=.
    rewrite size_cat size_map /=.
    rewrite -addn4 -addnA addSnnS.
    exact: rt_refl.

  clear - hgetrsp hgetoff hvm1.
  move: help => [??????].
  move=> x.

  case: (x =P v_var vsaved_sp) => [-> | hssp].
  - t_vm_get.
    have : get_var vm1 vsaved_sp = ok (Vword wrsp).
    + rewrite (get_var_eq_except _ hvm1); last by move=> /Sv.singleton_spec.
      exact: get_var_eq.
    rewrite get_varE.
    rewrite /get_var /=.
    case: vm1.[ _ ]%vmap => [[???]|[] //].
    move=> /ok_inj /Vword_inj /= [?]; subst.
    rewrite /= => ?; subst.
    by rewrite pword_of_wordE.

  case: (x =P v_var voff) => [-> | hoff].
  - t_vm_get.
    move: hgetoff.
    rewrite /get_var /=.
    case: vm1.[ _ ]%vmap => [[???]|[] //].
    move=> /ok_inj /Vword_inj /= [?]; subst.
    rewrite /= => ?; subst.
    by rewrite pword_of_wordE.

  case: (x =P v_var vrsp) => [-> | hrsp].
  - t_vm_get. by rewrite -GRing.addrA wnot1_wopp.

  case: (x =P v_var vzero) => [-> | hzero].
  - t_vm_get. by rewrite wrepr0.

  t_vm_get.

  have : Let y := (evm s).[x]%vmap in ok (pto_val y) = get_var vm1 x.
  - rewrite (get_var_eq_except _ hvm1); last by move=> /Sv.singleton_spec.
    rewrite -get_varE.
    by t_get_var.

  rewrite /get_var /=.
  case: vm1.[ _ ]%vmap => [?|] /=; first by t_xrbindP=> /= ? -> /pto_val_inj ->.

  move=> []; by case: (evm s).[ _ ]%vmap => //= ? [->].
Qed.
