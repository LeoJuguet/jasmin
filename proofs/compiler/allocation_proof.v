(* ** Imports and settings *)
From mathcomp Require Import all_ssreflect all_algebra.
Require Import psem compiler_util.
Require Export allocation.

Import Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope vmap.
Local Open Scope seq_scope.

Section WITH_PARAMS.

Context
  {asm_op syscall_state : Type}
  {spp : SemPexprParams asm_op syscall_state}.

Lemma wextend_typeP t1 t2 : 
  reflect (t1 = t2 \/ exists s1 s2, [/\ t1 = sword s1, t2 = sword s2 & (s1 <= s2)%CMP])
          (wextend_type t1 t2).
Proof.
  apply (iffP orP); (move => -[/eqP | ];first by left).
  + by case: t1 => // s1; case: t2 => // s2; right; exists s1, s2.
  by move=> [] s1 [] s2 [ -> -> ?]; right.
Qed.

Lemma extend_subtype t1 t2 : wextend_type t1 t2 -> subtype t1 t2.
Proof. by move=> /wextend_typeP [ -> | []s1[]s2[-> -> ?]]. Qed.

Lemma wextend_type_pundef_addr t1 t2 : 
  wextend_type t1 t2 -> eval_uincl (pundef_addr t1) (pundef_addr t2).
Proof. move/wextend_typeP => [-> | []s1[]s2[]->->?] //=. Qed.

Lemma wextend_typeP_bool t: wextend_type sbool t -> t = sbool.
Proof. by move=>/wextend_typeP => -[ -> | []?[]?[]]. Qed.

Lemma eval_uincl_ok_undefb t1 t2 v1 v2 :
  wextend_type t1 t2 ->
  eval_uincl v1 v2 ->
  (∃ v' : psem_t t1, v1 = ok v') ∨ v1 = undef_error ∧ t1 = sbool ->
  (∃ v' : psem_t t2, v2 = ok v') ∨ v2 = undef_error ∧ t2 = sbool.
Proof.
  move=> hex hu [[v1' ?] | [? hx1]]; subst v1.
  + by move: hu => /=; case: v2 => //; eauto.
  move: hex v2 hu;rewrite hx1 => /wextend_typeP_bool ->.
  by case => /= [ | ? <-]; eauto.
Qed.

Lemma subtype_pof_val_ok t1 t2 v v1 :
  wextend_type t1 t2 ->
  pof_val t1 v = ok v1 ->
  exists2 v2, pof_val t2 v = ok v2 & value_uincl (pto_val v1) (pto_val v2).
Proof.
  move=>/wextend_typeP [ <- | []s1[]s2[?? hle]]; first by eauto.
  subst t1 t2 => /=; case: v => //=; last by case.
  move=> s' w [<-]; eexists; first reflexivity.
  case: Sumbool.sumbool_of_bool => e /=.
  + by rewrite (sumbool_of_boolET (cmp_le_trans e hle)).
  case: Sumbool.sumbool_of_bool => e' /=.
  + move: e => /negbT e.
    by apply/andP; split => //; exact: cmp_nle_le.
  rewrite -(zero_extend_idem _ hle).
  exact: word_uincl_zero_ext.
Qed.

Definition eq_alloc (r:M.t) (vm1 vm2:vmap) :=
    [/\ vm_uincl vmap0 vm2,
        (forall x, ~Sv.In x (M.mset r) -> vm1.[x] = pundef_addr x.(vtype)) &
        (forall x x', M.get r x = Some x' ->
                      eval_uincl vm1.[x] vm2.[x'])].

Lemma eq_alloc_empty: eq_alloc M.empty vmap0 vmap0.
Proof. by split;rewrite /vm_uincl=> *;rewrite /vmap0 !Fv.get0. Qed.

Lemma eq_alloc_incl r1 r2 vm vm':
  M.incl r2 r1 ->
  eq_alloc r1 vm vm' ->
  eq_alloc r2 vm vm'.
Proof.
  move=> /M.inclP [Hi Hsub] [ Huincl epa eqa];split=>//.
  + by move=> x Hx;apply epa;SvD.fsetdec.
  move=> x x'; case: (Sv_memP x (M.mset r1)) => [ /Hi H /H /eqa // | /epa -> hget].
  have := Huincl x'.
  have [_ /(_ x') /= heq _ ]:= eq_alloc_empty.
  rewrite heq;last by rewrite SvD.F.empty_iff.
  apply: eval_uincl_trans; apply/subtype_eval_uincl_pundef/extend_subtype.
  by have []:= M.svalid hget.
Qed.

Lemma check_vP x1 x2 r re vm1 vm2 :
  check_v x1 x2 r = ok re ->
  eq_alloc r vm1 vm2 ->
  eq_alloc re vm1 vm2 /\
  (forall v1 : value,
     get_var vm1 x1 = ok v1 ->
     exists v2 : value, get_var vm2 x2 = ok v2 /\ value_uincl v1 v2).
Proof.
  rewrite /check_v;case: M.v_wextendtyP => // hsub.
  case Hget : M.get => [id | ].
  + case: eqP => //= ? [<-];subst id => Hea;split=>//.
    case: Hea => _ _ /(_ _ _ Hget) Hev v1 {Hget} Hget.
    case: x1 x2 hsub Hget Hev=> [[xt1 xn1] ii1] [[xt2 xn2] ii2] /= hsub.
    rewrite /get_var;apply: on_vuP => //= t -> <- /=.
    by case: (vm2.[_])%vmap => //= z' Hz';exists (pto_val z').
  case: ifPn => //= /Sv_memP Hnot [] <- [ Hvm0 Hset Huincl];split;first split=>//.
  + by move=> x;rewrite M.setP_mset => ?;apply Hset;SvD.fsetdec.
  + move=> x id;rewrite M.setP;case:eqP => [<- [<-]| Hne].
    + rewrite (Hset _ Hnot) /=.
      apply: (eval_uincl_trans (wextend_type_pundef_addr hsub)).
      by have := Hvm0 x2; rewrite Fv.get0.
    by case:ifP => // _;apply Huincl.
  move=> v1;rewrite /get_var (Hset _ Hnot) //=.
  case: x2 hsub (Hvm0 x2) => [[xt2 xn2] ?] /= hsub;rewrite Fv.get0 /= => heval.
  apply on_vuP => [ v heq| //] ?;subst v1.
  have : eval_uincl (pundef_addr (vtype x1)) vm2.[{| vtype := xt2; vname := xn2 |}].
  + by apply: eval_uincl_trans heval; apply wextend_type_pundef_addr. 
  by rewrite heq; case: (vm2.[_]) => //= a ?; eexists;split;first by reflexivity.
Qed.

Lemma check_gvP x1 x2 r re gd vm1 vm2 : 
  check_gv x1 x2 r = ok re ->
  eq_alloc r vm1 vm2 ->
  eq_alloc re vm1 vm2 /\
  (forall v1 : value,
     get_gvar gd vm1 x1 = ok v1 ->
     exists v2 : value, get_gvar gd vm2 x2 = ok v2 /\ value_uincl v1 v2).
Proof.
  rewrite /check_gv /get_gvar /is_lvar; case: x1 x2 => x1 k1 [x2 k2] /=.
  case:eqP => [-> | //]; case:eqP => _; first by apply check_vP.
  case:eqP => [-> [<-] ?| //]; split;eauto.
Qed.

Lemma is_PvarP e ty x : is_Pvar e = Some (ty,x) -> e = Some (ty, Plvar x).
Proof. by case: e => //= -[? []] //= [] v [] // [<- <-]. Qed.

Section CHECK_EP.
  Context (gd: glob_decls) (vm2: vmap).

  Let P e1 : Prop :=
    ∀ e2 r re vm1, check_e e1 e2 r = ok re →
    eq_alloc r vm1 vm2 →
    eq_alloc re vm1 vm2 ∧
    ∀ scs m v1,
      sem_pexpr gd {| escs := scs; emem := m ; evm := vm1 |} e1 = ok v1 →
    ∃ v2, sem_pexpr gd {| escs := scs; emem := m ; evm := vm2 |} e2 = ok v2 ∧
          value_uincl v1 v2.

  Let Q es1 : Prop :=
    ∀ es2 r re vm1 err,
    fold2 err check_e es1 es2 r = ok re →
    eq_alloc r vm1 vm2 →
    eq_alloc re vm1 vm2 ∧
    ∀ scs m vs1,
      sem_pexprs gd {| escs := scs; emem := m ; evm := vm1 |} es1 = ok vs1 →
    ∃ vs2, sem_pexprs gd {| escs := scs; emem := m ; evm := vm2 |} es2 = ok vs2 ∧
           List.Forall2 value_uincl vs1 vs2.

  Lemma check_e_esP : (∀ e, P e) ∧ (∀ es, Q es).
  Proof.
    apply: pexprs_ind_pair; split; subst P Q => /=.
    - case => // r _ vm1 _ [<-] h; split => // scs m _ [<-] /=; eauto.
    - move => e1 he1 es1 hes1 [] // e2 es2 r re vm1 err; t_xrbindP => r' ok_r' ok_re h.
      move: he1 => /(_ e2 r r' vm1 ok_r' h) [] h' he1.
      move: hes1 => /(_ es2 r' re vm1 err ok_re h') [] hre hes1.
      apply: (conj hre) => scs m vs1'; t_xrbindP => v1 ok_v1 vs1 ok_vs1 <- {vs1'} /=.
      move: he1 => /(_ _ _ _ ok_v1) [] v2 [] -> hv.
      move: hes1 => /(_ _ _ _ ok_vs1) [] vs2 [] -> hvs.
      eexists; split; first reflexivity. by constructor.
    - move => z1 [] // z2 r re vm1.
      by case: ifPn => // /eqP <- [->] ?; split=> // ??? [] <-; exists z1.
    - move => b1 [] // b2 r re vm1.
      by case: ifPn => // /eqP <- [->] ?;split=> // ??? [] <-; exists b1.
    - move => n1 [] // n2 r re vm1.
      by case: eqP => //= <- [<-] ?; split => // ??? [<-]; eauto.
    - move => x1 [] // x2 r re vm1.
      by move=> /check_gvP Hv /(Hv gd) [Hea H].
    - move => aa1 sz1 x1 e1 He1 [] // aa2 sz2 x2 e2 r re vm1.
      case: andP  => // -[/eqP ? /eqP ?]; subst aa2 sz2.
      apply: rbindP => r' Hcv Hce Hea.
      have [Hea' Hget]:= check_gvP gd Hcv Hea.
      have [Hre Hse1]:= He1 _ _ _ _ Hce Hea';split => //= scs m v1.
      apply: on_arr_gvarP => n t Heqt /Hget [v2 []].
      rewrite /on_arr_var; case: v2 => //= n' t' -> /WArray.uincl_get Ht.
      t_xrbindP=> w ve /Hse1 [v2 [-> ]] /[swap] /to_intI -> /value_uinclE ->
        ? /= /Ht -> /= <-.
      by eauto.
    - move => aa1 sz1 len1 x1 e1 He1 [] // aa2 sz2 len2 x2 e2 r re vm1.
      case: andP => // -[] /andP[] /eqP ? /eqP ? /eqP ?; subst aa2 sz2 len2.
      apply: rbindP => r' Hcv Hce Hea.
      have [Hea' Hget]:= check_gvP gd Hcv Hea.
      have [Hre Hse1]:= He1 _ _ _ _ Hce Hea';split => //= scs m v1.
      apply: on_arr_gvarP => n t Heqt /Hget [v2 []].
      rewrite /on_arr_var; case: v2 => //= n' t' -> /WArray.uincl_get_sub Ht.
      t_xrbindP => w ve /Hse1 [v2 [-> ]] /[swap] /to_intI -> /value_uinclE ->
        ? /= /Ht [? -> ?] <- /=.
      by eauto.
    - move => sz1 x1 e1 He1 [] // sz2 x2 e2 r re vm1.
      case: eqP => // ->.
      apply: rbindP => r' Hcv Hce Hea.
      have [Hea' Hget]:= check_vP Hcv Hea.
      have [Hre Hse1]:= He1 _ _ _ _ Hce Hea';split => //= scs m v1.
      t_xrbindP => w1 ve1 /Hget [ve1' [->]] /[swap] /to_wordI [? [? [-> ]]]
        /word_uincl_truncate h /value_uinclE [? [? [-> /h{h} /= ->]]]
        > /Hse1{Hse1} [? [-> ]] /[swap] /to_wordI [? [? [-> ]]]
        /word_uincl_truncate h /value_uinclE [? [? [-> /h{h} /= ->]]] ? /= -> /= ->.
      by eauto.
    - move => op1 e1 He1 [] // op2 e2 r re vm1.
      case: eqP => // <-. move=> H /(He1 _ _ _ _ H) [Hea Hse1];split=>//=.
      move=> scs m v1;apply:rbindP => v /Hse1 [v1'] [-> U1].
      by move=> /(vuincl_sem_sop1 U1);exists v1.
    - move => op1 e11 He11 e12 He12 [] // op2 e21 e22 r re vm1.
      case: eqP => // <-;apply:rbindP => r' Hs1 Hs2 Hea.
      have [Hea' Hse1]:= He11 _ _ _ _ Hs1 Hea.
      have [? Hse2]:= He12 _ _ _ _ Hs2 Hea'; split => //= scs m v.
      apply: rbindP => v1 /Hse1 [v1' [-> U1]].
      apply: rbindP => v2 /Hse2 [v2' [-> U2]].
      by move=> /(vuincl_sem_sop2 U1 U2);exists v.
    - move => op1 es1 Hes1 [] // op2 es2 r re vm1.
      case: eqP => // <- {op2} ok_re hr.
      move: Hes1 => /(_ _ _ _ _ _  ok_re hr) [] hre h.
      split => //= scs m v1; t_xrbindP => vs1 ok_vs1 ok_v1.
      rewrite -/(sem_pexprs _ _).
      move: h => /(_ _ _ _ ok_vs1) [] vs2 [] -> hs /=.
      by have [] := vuincl_sem_opN ok_v1 hs; eauto.
    move => t e He e11 He11 e12 He12 [] // t' e2 e21 e22 r re vm1.
    case: eqP => // <-.
    t_xrbindP => r1 r' /He Hr' /He11 Hr1 /He12 Hr2 {He He11 He12}.
    move=> /Hr'{Hr'}[] /Hr1{Hr1}[] /Hr2{Hr2}[] Hre Hs2 Hs1 Hs;split=>// scs m v1.
    t_xrbindP=> b > /Hs [_] /= [->] /= /[swap] /to_boolI -> /value_uinclE ->.
    move=> ?? /Hs1 [?[-> /=]] /value_uincl_truncate H/H{H} [? -> ?].
    move=> ?? /Hs2 [?[-> /=]] /value_uincl_truncate H/H{H} [? -> ?] <- /=.
    by eexists;split;eauto;case: (b).
Qed.

End CHECK_EP.

Definition check_eP gd e1 e2 r re vm1 vm2 :=
  (check_e_esP gd vm2).1 e1 e2 r re vm1.

Lemma vm_uincl0_set vm x (v : exec (psem_t (vtype x))) :
  vm_uincl vmap0 vm ->
  ((exists v', v = ok v') \/ v = undef_error) ->
  vm_uincl vmap0 vm.[x <- apply_undef v].
Proof.
  move=> Hvm0 H z; case (x =P z) => [<- | /eqP Hne].
  + rewrite Fv.setP_eq /vmap0 Fv.get0 /=.
    by case: H => [[v']|] ?;subst v => //=;apply eval_uincl_undef.
  by rewrite Fv.setP_neq.
Qed.

Lemma eq_alloc_set x1 (v1 :exec (psem_t (vtype x1))) r x2 (v2 :exec (psem_t (vtype x2)))
          vm1 vm2 (h:M.v_wextendty x1 x2) :
  eq_alloc r vm1 vm2 ->
  eval_uincl v1 v2 ->
  ((exists v', v1 = ok v') \/ (v1 = undef_error /\ vtype x1 = sbool)) ->
  eq_alloc (M.set r x1 x2 h) vm1.[x1 <- apply_undef v1]
                             vm2.[x2 <- apply_undef v2].
Proof.
  move=> [Hvm0 Hin Hget] Hu H1.
  have H2:= eval_uincl_ok_undefb h Hu H1.
  split.
  + apply vm_uincl0_set => //;intuition.
  + move=> z;rewrite M.setP_mset => Hnin.
    by rewrite Fv.setP_neq;[apply Hin|apply /eqP];SvD.fsetdec.
  move=> x id;rewrite M.setP;case:eqP => [<-[<-] | /eqP Hne].
  + rewrite !Fv.setP_eq.
    case: H1 Hu => [ [v1' ?]| [? heq1]];subst v1;
    case: H2 => [ [v2' ?]| [? heq2]];subst v2 => //=; last by rewrite heq1 heq2.
    by move: h v2'; rewrite /M.v_wextendty heq1 => /wextend_typeP_bool ->.
  case: ifPn => //= /Sv_memP Hid Hgetx.
  rewrite !Fv.setP_neq //;first by apply Hget.
  move: Hgetx;rewrite M.Mv.mvalid => Hgetx.
  by apply/eqP => ?; subst id; apply: Hid.
Qed.

Lemma eq_alloc_add x1 (v1:exec (psem_t (vtype x1))) r x2  vm1 vm2 (h:M.v_wextendty x1 x2) :
  eq_alloc r vm1 vm2 ->
  let v2 := vm2.[x2] in
  eval_uincl v1 v2 ->
  ((exists v', v1 = ok v') \/ (v1 = undef_error /\ vtype x1 = sbool)) ->
  eq_alloc (M.add r x1 x2 h) vm1.[x1 <- apply_undef v1]
                             vm2.[x2 <- apply_undef v2].
Proof.
  move=> [Hvm0 Hin Hget] v2 /= Hu H1.
  have H2:= eval_uincl_ok_undefb h Hu H1.
  split.
  + by apply vm_uincl0_set => //;intuition.
  + move=> z;rewrite M.addP_mset => Hnin.
    by rewrite Fv.setP_neq;[apply Hin|apply /eqP];SvD.fsetdec.
  move=> x id;rewrite M.addP;case:eqP => [<-[<-] | /eqP Hne].
  + rewrite !Fv.setP_eq.
    case: H1 Hu => [ [v1' ?]| [? heq1]];subst v1;
    case: H2 => [ [v2' ->]| [-> heq2]] => //=;last by rewrite heq1 heq2.
    by move: h v2'; rewrite /M.v_wextendty heq1 => /wextend_typeP_bool ->.
  move=> hx;rewrite Fv.setP_neq //.
  case: (x2 =P id) => [? | /eqP hne];last by rewrite Fv.setP_neq //;apply Hget.
  subst;rewrite Fv.setP_eq;have := Hget _ _ hx.
  move: H2;rewrite /v2 => -[ [v' ->]| [-> ?]] /=; case : vm1.[x] => //= -[] // _.
  by case: (vtype id).
Qed.

Lemma check_varP r1 r1' vm1 vm2 vm1' x1 x2 v1 v2 (h:M.v_wextendty x1 x2):
  eq_alloc r1 vm1 vm2 ->
  @check_var_aux x1 x2 r1 h = ok r1' ->
  set_var vm1 x1 v1 = ok vm1' ->
  value_uincl v1 v2 ->
  exists vm2' : vmap,
    set_var vm2 x2 v2 = ok vm2' /\ eq_alloc r1' vm1' vm2'.
Proof.
  rewrite /check_var => Hea -[<-].
  apply: set_varP; rewrite /set_var.
  + move=> vx1 hvx1 <- hu.
    have [vx1' [hv2x1 hvx1']]:= pof_val_uincl hu hvx1.
    have [vx2 -> hsub /=] := subtype_pof_val_ok h hv2x1.
    eexists;split;first reflexivity.
    have hincl: eval_uincl (ok vx1) (ok vx2).
    + by apply: (eval_uincl_trans (v2:= ok vx1')).
    by apply (eq_alloc_set h Hea hincl); eauto.
  move=> v1' Hv1' <- Hu.
  case: x1 v1' h Hv1' (h) => t1 x1 /= /eqP ?;subst t1.
  case: x2 => t2 x2 h;rewrite /M.v_wextendty => /to_bool_undef ? /=;subst v1.
  move=> h0; have ? := wextend_typeP_bool h0; subst t2; move: Hu => /eqP.
  move=> /type_of_valI [? | [b ?]]; subst v2 => /=;
    eexists; (split; first reflexivity).
  + have hincl : @eval_uincl sbool sbool undef_error undef_error by done.
    by apply (eq_alloc_set h Hea hincl);eauto.
  have hincl : @eval_uincl sbool sbool undef_error (ok b) by done.
  apply (eq_alloc_set h Hea hincl);eauto.
Qed.

Lemma check_varcP r1 r1' vm1 vm2 vm1' x1 x2 v1 v2 :
  eq_alloc r1 vm1 vm2 ->
  check_varc x1 x2 r1 = ok r1' ->
  set_var vm1 x1 v1 = ok vm1' ->
  value_uincl v1 v2 ->
  exists vm2' : vmap,
    set_var vm2 x2 v2 = ok vm2' /\ eq_alloc r1' vm1' vm2'.
Proof.
  by rewrite /check_varc; case: M.v_wextendtyP => // h; apply check_varP.
Qed.

Lemma eq_alloc_rm r x s vm z :
  eval_uincl (pundef_addr (vtype x)) z ->
  eq_alloc r (evm s) vm ->
  eq_alloc (M.remove r x) (evm s) vm.[x <- z].
Proof.
  move=> Hz [Hmap0 Hinit Halloc];split.
  + move=> y;case:(x =P y) => [<-|/eqP ne].
    + by rewrite Fv.setP_eq /vmap0 Fv.get0.
    by rewrite Fv.setP_neq.
  + by move=> y /=;apply: Hinit.
  move=> x0 id; rewrite M.removeP.
  case: M.get (Halloc x0) => [id' | ] //.
  move=> /(_ _ (refl_equal _));case:ifPn => //= Hne He [?];subst id'.
  rewrite Fv.setP_neq //;by apply: contra Hne => /eqP ->.
Qed.

Lemma check_lvalP gd r1 r1' x1 x2 e2 s1 s1' vm1 v1 v2 :
  check_lval e2 x1 x2 r1 = ok r1' ->
  eq_alloc r1 s1.(evm) vm1 ->
  value_uincl v1 v2 ->
  oapp (fun te2 =>
      sem_pexpr gd (with_vm s1 vm1) te2.2 >>= truncate_val te2.1 = ok v2) true e2 ->
  write_lval gd x1 v1 s1 = ok s1' ->
  exists vm1',
    write_lval gd x2 v2 (with_vm s1 vm1) = ok (with_vm s1' vm1') /\
    eq_alloc r1' s1'.(evm) vm1'.
Proof.
  case: x1 x2 => /= [ii1 t1 | x1 | sz1 x1 p1 | aa1 sz1 x1 p1 | aa1 sz1 len1 x1 p1]
                    [ii2 t2 | x2 | sz2 x2 p2 | aa2 sz2 x2 p2 | aa2 sz2 len2 x2 p2] //=.
  + case:ifP => //= hs [] <- ? Hv _ H.
    have [-> [ [u hpof]| [hpof ?]]]:= write_noneP H; rewrite /write_none.
    + have [v1' ]:= subtype_pof_val_ok hs hpof.
      by move=> /(pof_val_uincl Hv) [v2' [-> ]] /= ??;eauto.
    subst t1; have ? := wextend_typeP_bool hs; subst t2.
    have [->|[b] ->] /=:= pof_val_undef Hv hpof; eauto.
  + case:ifP => //= hs [] <- Heqa Hu Happ H.
    have [-> ]:= write_noneP H.
    rewrite /write_var /set_var => -[ [u]| ].
    + move=> /(subtype_pof_val_ok hs) [v3].
      move=> /(pof_val_uincl Hu) [z' [-> ?]] /= ?.
      eexists; rewrite with_vm_idem;split; eauto. 
      by apply eq_alloc_rm => //; apply eval_uincl_undef.
    move=> [hpof ?];subst t1; case : x2 hs => -[tx2 x2] ii2 /= /wextend_typeP_bool ?;subst tx2.
    have [->|[b] ->] /= := pof_val_undef Hu hpof; eexists;(split; first by eauto);
      apply eq_alloc_rm => //.
  + rewrite /write_var=> Hc Hvm1 Hv Happ; apply rbindP => vm1' Hset [<-] /=.
    move: Hc;case: is_Pvar (@is_PvarP e2).
    + move=> [ty x] /(_ _ _ (refl_equal _)) ?;subst e2.
      case: M.v_wextendtyP => // ht;case:ifPn; last first.
      + move=> ? hc;have [vm2' [-> /= ?]]:= check_varP Hvm1 hc Hset Hv;eexists.
        by rewrite !with_vm_idem;eauto.
      move=> /andP[]/andP[]/eqP ? /eqP heqt /eqP;subst ty.
      move: x1 x2 x heqt ht Hset Happ=> [[xt1 xn1] ii1] [[xt2 xn2] ii2] [x ii] /=.
      set x1 := {| vname := xn1 |}; set x2 := {| vname := xn2 |}.
      move=> hteq ht hset; t_xrbindP => v2' Happ htr ? ?;subst => /=.
      apply: set_varP hset => /=;rewrite /set_var.
      + move=> v1' Hv1 ?;subst.
        apply: on_vuP Happ => //.
        move=> v2_ hv2_ ?;subst.
        have ?:= truncate_pto_val htr;subst v2.
        rewrite pof_val_pto_val /=;eexists;rewrite !with_vm_idem;split;first reflexivity.
        have /= := @eq_alloc_add x1 (ok v1') r1 x2 (evm s1) vm1 ht Hvm1.
        rewrite hv2_ /= /pval_uincl => H;apply H;last by eauto.
        by apply (value_uincl_pof_val Hv1 Hv).
      move=> /= hniw hv1 ?;subst; rewrite hniw /=.
      apply: on_vuP Happ => //.
      move=> v2_ heq ?;subst;have ?:= truncate_pto_val htr;subst v2.
      rewrite pof_val_pto_val /=;eexists;rewrite !with_vm_idem;split;first reflexivity.
      have /= := @eq_alloc_add x1 (pundef_addr xt2) r1 x2 (evm s1) vm1 ht Hvm1.
      rewrite heq /= apply_undef_pundef_addr=> H;apply H.
      + by apply eval_uincl_undef.
      by move /eqP: hniw => ->;right.
    by move=> ? hc;have [vm2' [-> /= ?]]:= check_varcP Hvm1 hc Hset Hv;eexists;
     rewrite !with_vm_idem;eauto.
  + case: eqP => // -> /=.
    t_xrbindP => r2 Hcv Hce Hvm1 Hv Happ wx vx.
    have [Hr2 H/H{H} [vx' [-> ]]]:= check_vP Hcv Hvm1.
    move=> /of_value_uincl_te h/(h (sword _) _){h} /= -> >.
    case: (s1) Hvm1 Hr2 => scs1 sm1 svm1 /= Hvm1 Hr2.
    have [Hr1' H/H{H} [ve' [-> ]]]:= check_eP gd Hce Hr2.
    move=> /of_value_uincl_te h/(h (sword _) _){h} /= -> ?
      /(@of_value_uincl_te (sword _) _ _ _ Hv) /= -> ? /= -> <-.
    by eexists.
  + case: andP => // -[/eqP -> /eqP ->] /=.
    t_xrbindP => r2 r3 Hcv Hce Hcva Hvm1 Hv Happ.
    apply: on_arr_varP => n t Htx;rewrite /on_arr_var /=.
    have [Hr3 H/H{H} [vx2 [->]]]:= check_vP Hcv Hvm1.
    case: vx2 => //= n0 t2 Ht.
    t_xrbindP => we ve.
    case: (s1) Hvm1 Hr3 => scs1 sm1 svm1 /= Hvm1 Hr3.
    have [Hr1' H/H{H} [ve' [-> ]]]:= check_eP gd Hce Hr3.
    move=> /of_value_uincl_te h/(h sint _){h} /= -> ?
      /(@of_value_uincl_te (sword _) _ _ _ Hv) /= -> ?
      /(WArray.uincl_set Ht) [? [/= -> Ht2']].
    have: value_uincl (Varr _) (Varr _) := Ht2'.
    rewrite /write_var; t_xrbindP=> /(check_varcP Hr1' Hcva) h ?
      /h{h} [vm2' [/= -> ?]] <-.
    by eexists.
  case: andP => // -[] /andP[] /eqP -> /eqP -> /eqP -> /=.
  t_xrbindP=> r2 r3 Hcv Hce Hcva Hvm1 Hv Happ.
  apply: on_arr_varP => n t Htx;rewrite /on_arr_var /=.
  have [Hr3 H/H{H} [vx2 [->]]]:= check_vP Hcv Hvm1.
  case: vx2 => //= n0 t2 Ht.
  t_xrbindP => we ve.
  case: (s1) Hvm1 Hr3 => scs1 sm1 svm1 /= Hvm1 Hr3.
  have [Hr1' H/H{H} [ve' [-> ]]]:= check_eP gd Hce Hr3.
    move=> /of_value_uincl_te h/(h sint _){h} /= -> ?
      /(@of_value_uincl_te (sarr _) _ _ _ Hv) [? /= -> ]
      /(WArray.uincl_set_sub Ht) h ? /h{h}[? /= -> Ht2'].
  have: value_uincl (Varr _) (Varr _) := Ht2'.
  rewrite /write_var; t_xrbindP=> /(check_varcP Hr1' Hcva) h ?
    /h{h} [vm2' [/= -> ?]] <-.
  by eexists.
Qed.

Section PROG.

Context
  {T:eqType} {pT:progT T}
  {sCP : semCallParams}.

Variable init_alloc : extra_fun_t -> extra_prog_t -> extra_prog_t -> cexec M.t.

Hypothesis init_allocP :
  forall (ef: extra_fun_t) (ep1 ep2: extra_prog_t) ev s1 scs m r,
    init_alloc ef ep1 ep2 = ok r ->
    init_state ef ep1 ev (Estate scs m vmap0) = ok s1 ->
    exists vm2,
      init_state ef ep2 ev (Estate scs m vmap0) = ok (with_vm s1 vm2) /\
      eq_alloc r s1.(evm) vm2.

Local Notation check_fundef := (check_fundef init_alloc).
Local Notation check_prog := (check_prog init_alloc).

Lemma check_fundef_meta ep1 ep2 ffd1 ffd2 u u' :
  check_fundef ep1 ep2 ffd1 ffd2 u = ok u' →
  let fd1 := ffd1.2 in
  let fd2 := ffd2.2 in
  [/\
   ffd1.1 = ffd2.1,
   fd1.(f_tyin) = fd2.(f_tyin),
   fd1.(f_tyout) = fd2.(f_tyout) &
   fd1.(f_extra) = fd2.(f_extra)
  ].
Proof.
  case: ffd1 ffd2 => f1 fd1 [] f2 fd2.
  by rewrite /check_fundef; case: andP => // - [] /andP[] /andP[] /eqP -> /eqP -> /eqP -> /eqP -> _.
Qed.

Section PROOF.

  Variable p1 p2:prog.
  Variable ev : extra_val_t.

  Local Notation gd := (p_globs p1).
  Local Notation ep1 := (p_extra p1).
  Local Notation ep2 := (p_extra p2).

  Hypothesis Hcheck: check_prog ep1 p1.(p_funcs) ep2 p2.(p_funcs) = ok tt.
  Hypothesis eq_globs : p_globs p1 = p_globs p2.

  Lemma all_checked : forall fn fd1,
    get_fundef (p_funcs p1) fn = Some fd1 ->
    exists fd2, get_fundef (p_funcs p2) fn = Some fd2 /\ 
                check_fundef ep1 ep2 (fn,fd1) (fn,fd2) tt = ok tt.
  Proof.
    move: Hcheck; rewrite /check_prog;clear Hcheck eq_globs.
    move: (p_funcs p1) (p_funcs p2). 
    elim => [ | [fn1' fd1'] pf1 Hrec] [ | [fn2 fd2] pf2] //.
    apply: rbindP => -[] Hc /Hrec {Hrec} Hrec.
    have ? : fn1' = fn2.
    + by move: Hc;rewrite /check_fundef; case:ifP => // /andP[]/andP[]/andP[]/eqP.
    subst=> fn fd1;rewrite !get_fundef_cons.
    case:ifPn => [/eqP -> [] <-| _ /Hrec //].
    by exists fd2.
  Qed.

  Let Pi_r s1 (i1:instr_r) s2:=
    forall r1 i2 r2 vm1, eq_alloc r1 (evm s1) vm1 ->
    check_i i1 i2 r1 = ok r2 ->
    exists vm2, eq_alloc r2 (evm s2) vm2 /\
      sem_i p2 ev (with_vm s1 vm1) i2 (with_vm s2 vm2).

  Let Pi s1 (i1:instr) s2:=
    forall r1 i2 r2 vm1, eq_alloc r1 (evm s1) vm1 ->
    check_I i1 i2 r1 = ok r2 ->
    exists vm2, eq_alloc r2 (evm s2) vm2 /\
      sem_I p2 ev (with_vm s1 vm1) i2 (with_vm s2 vm2).

  Let Pc s1 (c1:cmd) s2:=
    forall r1 c2 r2 vm1, eq_alloc r1 (evm s1) vm1 ->
    check_cmd c1 c2 r1 = ok r2 ->
    exists vm2, eq_alloc r2 (evm s2) vm2 /\
      sem p2 ev (with_vm s1 vm1) c2 (with_vm s2 vm2).

  Let Pfor (i1:var_i) vs s1 c1 s2 :=
    forall i2 r1 r1' c2 r2 vm1, eq_alloc r1 (evm s1) vm1 ->
    check_var i1 i2 r1 = ok r1' ->
    check_cmd c1 c2 r1' = ok r2 -> M.incl r1 r2 ->
    exists vm2, eq_alloc r1 (evm s2) vm2 /\
      sem_for p2 ev i2 vs (with_vm s1 vm1) c2 (with_vm s2 vm2).

  Let Pfun scs m fn vargs1 scs' m' vres :=
    forall vargs2, List.Forall2 value_uincl vargs1 vargs2 ->
    exists vres',
       sem_call p2 ev scs m fn vargs2 scs' m' vres' /\
       List.Forall2 value_uincl vres vres'.

  Local Lemma Hskip : sem_Ind_nil Pc.
  Proof.
    move=> s r1 [ | ??] //= r2 vm1 ? [] <-;exists vm1;split=>//;constructor.
  Qed.

  Local Lemma Hcons : sem_Ind_cons p1 ev Pc Pi.
  Proof.
    move=> s1 s2 s3 i c _ Hi _ Hc r1 [ | i2 c2] //= r2 vm1 /Hi Hvm1.
    apply: rbindP => r3 /Hvm1 [vm2 []] /Hc Hvm2 ? /Hvm2.
    by move=> [vm3 [??]];exists vm3;split=>//;econstructor;eauto.
  Qed.

  Local Lemma HmkI : sem_Ind_mkI p1 ev Pi_r Pi.
  Proof.
    move=> ii i s1 s2 _ Hi  r1 [? i2] r2 vm1 /Hi Hvm /= /Hvm [vm2 [??]].
    by exists vm2;split=>//;constructor.
  Qed.

  Local Lemma Hassgn : sem_Ind_assgn p1 Pi_r.
  Proof.
    move => s1 s2 x tag ty e v v'.
    case: s1 => scs1 sm1 svm1 He Htr Hw r1 [] //= x2 tag2 ty2 e2 r2 vm1 Hvm1.
    rewrite /check_i.
    case: eqP => // <- {ty2}; t_xrbindP.
    move=> r1' /check_eP -/(_ (p_globs p1) _ _ Hvm1) [Hr1'] /(_ _ _ _ He) [v2 [He2 Hu2]] Hcx.
    have [v2' Htr' Hu2']:= value_uincl_truncate Hu2 Htr.
    have  /(_ _ Hr1') [|]:= check_lvalP Hcx _ Hu2' _ Hw.
    + by rewrite /= He2 /= Htr'.
    move=> vm2 [Hwv Hvm2].
    by exists vm2; split=>//;econstructor;rewrite -?eq_globs;eauto.
  Qed.

  Lemma check_esP e1 e2 r re s vm:
    check_es e1 e2 r = ok re ->
    eq_alloc r s.(evm) vm ->
    eq_alloc re s.(evm) vm /\
    forall v1,  sem_pexprs gd s e1 = ok v1 ->
    exists v2, sem_pexprs (p_globs p2) (with_vm s vm) e2 = ok v2 /\
               List.Forall2 value_uincl v1 v2.
  Proof.
    rewrite -eq_globs;case: s => sscs sm svm.
    rewrite /check_es; elim: e1 e2 r => [ | e1 es1 Hrec] [ | e2 es2] r //=.
    + by move=> [] <- ?;split=>// -[] //= ?;exists [::].
    move=> H Hea;apply: rbindP H => r' /(check_eP gd) /(_ Hea) [] Hea' He.
    move=> /Hrec /(_ Hea') [] Hre Hes;split=> // v1.
    rewrite /sem_pexprs;apply: rbindP => ve1 h. 
    have [{h}ve2 /=[-> Hve]]:= He _ _ _ h.
    apply:rbindP => ev2 /Hes [ves2 []];rewrite /sem_pexprs => -> Hves [] <- /=.
    by exists (ve2 :: ves2);split => //;constructor.
  Qed.

  Lemma check_lvalsP gd xs1 xs2 vs1 vs2 r1 r2 s1 s2 vm1 :
    check_lvals xs1 xs2 r1 = ok r2 ->
    eq_alloc r1 s1.(evm) vm1 ->
    List.Forall2 value_uincl vs1 vs2 ->
    write_lvals gd s1 xs1 vs1 = ok s2 ->
    exists vm2,
      write_lvals gd (with_vm s1 vm1) xs2 vs2 = ok (with_vm s2 vm2) /\
      eq_alloc r2 s2.(evm) vm2.
  Proof.
    elim: xs1 xs2 vs1 vs2 r1 r2 s1 s2 vm1 => [ | x1 xs1 Hrec] [ | x2 xs2] //=
      vs1 vs2 r1 r2 s1 s2 vm1.
    + by move=> [<-] Hvm1 [] //= [<-];exists vm1.
    apply: rbindP => r3 Hx Hcxs Hvm1 [] //= {vs1 vs2}.
    move=> v1 v2 vs1 vs2 Hv Hvs;apply: rbindP => s3 Hw Hws.
    have [ //| vm3 [->/= Hvm3]] := check_lvalP (e2:= None) Hx Hvm1 Hv _ Hw.
    apply: Hrec Hcxs Hvm3 Hvs Hws.
  Qed.

  Local Lemma Hopn : sem_Ind_opn p1 Pi_r.
  Proof.
    move => s1 s2 t o xs es.
    rewrite /sem_sopn; t_xrbindP => v ves He Ho Hw r1 [] //= xs2 t' o2 es2 r2 vm1 Hvm1.
    rewrite /check_i.
    case:ifPn => //= /eqP <-.
    t_xrbindP => r1' /check_esP -/(_ _ _ Hvm1) [Hr1'] /(_ _ He) [v2 [He2 Hu2]].
    have [v' Ho' Hv Hcxs]:= vuincl_exec_opn Hu2 Ho.
    have /(_ _ Hr1') [vm2 [Hwv Hvm2]]:= check_lvalsP Hcxs _ Hv Hw.
    by exists vm2;split=>//;constructor;rewrite /sem_sopn He2 /= Ho' -eq_globs.
  Qed.

  Local Lemma Hsyscall : sem_Ind_syscall p1 Pi_r.
  Proof.
    move => s1 scs m s2 o xs es ves vs hes hsys hw r1 [] //= xs2 o2 es2 r2 vm1 Hvm1.
    rewrite /check_i.
    case:ifPn => //= /eqP <-.
    t_xrbindP => r1' /check_esP -/(_ _ _ Hvm1) [Hr1'] /(_ _ hes) [v2 [He2 Hu2]] Hcxs.
    have  [vs' Ho' Hv] := exec_syscallP hsys Hu2.
    have /(_ _ Hr1') [vm2 [Hwv Hvm2]]:= check_lvalsP Hcxs _ Hv hw.
    by exists vm2;split=>//; econstructor; eauto; rewrite -eq_globs.
  Qed.

  Local Lemma Hif_true : sem_Ind_if_true p1 ev Pc Pi_r.
  Proof.
    move => s1 s2 e c1 c2.
    case: s1 => scs1 sm1 svm1 Hve _ Hc1 r1 [] //= e' c1' c2' r2 vm1 Hvm1.
    rewrite /check_i.
    t_xrbindP => r1' /check_eP -/(_ gd _ _ Hvm1) [] Hr1'.
    move=> /(_ _ _ _ Hve) [ve' [Hve' /value_uinclE ?]];subst ve'.
    move => r3 Hr3 r4 Hr4 <-.
    have [vm2 [Hvm2 Hsem]]:= Hc1 _ _ _ _ Hr1' Hr3;exists vm2;split.
    + by eapply eq_alloc_incl;eauto;apply M.merge_incl_l.
    by apply Eif_true => //;rewrite -eq_globs Hve'.
  Qed.

  Local Lemma Hif_false : sem_Ind_if_false p1 ev Pc Pi_r.
  Proof.
    move => s1 s2 e c1 c2.
    case: s1 => scs1 sm1 svm1 Hve _ Hc1 r1 [] //= e' c1' c2' r2 vm1 Hvm1.
    rewrite /check_i.
    t_xrbindP => r1' /check_eP -/(_ gd _ _ Hvm1) [] Hr1'.
    move=> /(_ _ _ _ Hve) [ve' [Hve' /value_uinclE ?]];subst ve'.
    move => r3 Hr3 r4 Hr4 <-.
    have [vm2 [Hvm2 Hsem]]:= Hc1 _ _ _ _ Hr1' Hr4;exists vm2;split.
    + by eapply eq_alloc_incl;eauto;apply M.merge_incl_r.
    by apply Eif_false => //;rewrite -eq_globs Hve'.
  Qed.

  Local Lemma loop2P check_c n r1 r2:
    loop2 check_c n r1 = ok r2 ->
      exists r2' r3,
      [/\ check_c r2' = ok (r2, r3), M.incl r2' r1 & M.incl r2' r3].
  Proof.
    elim: n r1 r2 => //= n Hrec r1 r2.
    apply: rbindP => -[r2_1 r2_2] Hc;case:ifPn => [? [] <- | _ /Hrec].
    + exists r1, r2_2;split=>//;apply M.incl_refl.
    move=> [r2' [r3 [H1 H2 H3]]];exists r2', r3;split=>//.
    apply: (M.incl_trans H2); apply M.merge_incl_l.
  Qed.

  Local Lemma Hwhile_true : sem_Ind_while_true p1 ev Pc Pi_r.
  Proof.
    move => s1 s2 s3 s4 a c e c'.
    case: s2 => scs2 sm2 svm2 _ Hc Hse _ Hc' _ Hw r1 [] //= a2 c2 e2 c2' r2 vm1 Hvm1.
    rewrite /check_i -/check_I.
    apply: rbindP => r /loop2P [r2' [r3 [H Hir1 Hir3]]] [?];subst r.
    have Hvmr2' := eq_alloc_incl Hir1 Hvm1.
    move: H; t_xrbindP => r0 Cc2; move /Hc: (Hvmr2') (Cc2) => H /H {H} [vm2 [Hvm2 /= Hc2]] re Hre.
    have /= [Hrevm2 /(_ _ _ _ Hse) [vb' [Hse2 /value_uinclE ?]]]:= check_eP gd Hre Hvm2.
    subst vb' => r' Cc2' ??;subst r2 r3.
    move /Hc': (Hrevm2) (Cc2')=> H /H {H} [vm3 [Hvm3 /= Hc2']].
    have /Hw {Hw} Hw:= eq_alloc_incl Hir3 Hvm3.
    have : check_i (Cwhile a c e c') (Cwhile a2 c2 e2 c2') r2' = ok re.
    + by rewrite /check_i -/check_I Loop.nbP /= Cc2 /= Hre /= Cc2' /= Hir3 /=.
    move=> /Hw [vm4 [Hvm4 Hsw]];exists vm4;split => //.
    by apply: Ewhile_true Hsw;eauto;rewrite -eq_globs Hse2.
  Qed.

  Local Lemma Hwhile_false : sem_Ind_while_false p1 ev Pc Pi_r.
  Proof.
    move => s1 s2 a c e c'.
    case: s2 => scs2 sm2 svm2 _ Hc Hse r1 [] //= a2 c2 e2 c2' r2 vm1 Hvm1.
    rewrite /check_i -/check_I.
    t_xrbindP => r /loop2P [r2' [r3 [H Hir1 Hir3]]] ?;subst r.
    have Hvmr2' := eq_alloc_incl Hir1 Hvm1.
    move: H; t_xrbindP=> r0 Cc2; move /Hc: (Hvmr2') (Cc2) => H /H {H} [vm2 [Hvm2 /= Hc2]] re Hre.
    have /= [Hrevm2 /(_ _ _ _ Hse) [vb' [Hse2 /value_uinclE ?]]]:= check_eP gd Hre Hvm2.
    subst vb' => r' Cc2' ??;subst r2 r3.
    exists vm2;split => //.
    by apply: Ewhile_false;rewrite // -eq_globs Hse2.
  Qed.

  Local Lemma loopP check_c n r1 r2:
    loop check_c n r1 = ok r2 ->
      exists r2',
      [/\ check_c r2 = ok r2', M.incl r2 r1 & M.incl r2 r2'].
  Proof.
    elim: n r1 r2 => //= n Hrec r1 r2.
    apply: rbindP => r2' Hc;case:ifPn => [? [] <- | _ /Hrec].
    + exists r2';split=>//;apply M.incl_refl.
    move=> [r2'' [H1 H2 H3]];exists r2'';split=>//.
    apply: (M.incl_trans H2); apply M.merge_incl_l.
  Qed.

  Local Lemma Hfor : sem_Ind_for p1 ev Pi_r Pfor.
  Proof.
    move => s1 s2 i d lo hi c vlo vhi.
    case: s1 => scs1 sm1 svm1.
    move=> Hlo Hhi Hc Hfor r1 [] //= i2 [[d2 lo2] hi2] c2 r2 vm1 Hvm1.
    rewrite /check_i -/check_I.
    case: eqP => //= ?;subst d2.
    t_xrbindP => r1' r1'' /check_eP -/(_ gd _ _ Hvm1) [Hr1'' Heqlo].
    have [vlo'' [Hlo2 /value_uinclE Hvlo']] := Heqlo _ _ _ Hlo.
    subst vlo'' => /check_eP -/(_ gd _ _ Hr1'') [Hr1' Heqhi].
    have [vhi'' [Hhi2 /value_uinclE Hhi']] := Heqhi _ _ _ Hhi.
    subst vhi'' => /loopP [r2'] []; t_xrbindP=> r2'' Hcv Hcc Hr2r1 Hr2r2.
    have := Hfor _ _ _ _ _ _ (eq_alloc_incl Hr2r1 Hr1') Hcv Hcc Hr2r2.
    move=> [vm2 [Hvm2 Hsem2]];exists vm2;split=> //.
    econstructor; rewrite -?eq_globs ?Hlo2 ?Hhi2 /= ;eauto.
  Qed.

  Local Lemma Hfor_nil : sem_Ind_for_nil Pfor.
  Proof.
    by move=> s i c i2 r1 r1' c2 r2 vm1 Ha ???;exists vm1;split=> //;constructor.
  Qed.

  Local Lemma Hfor_cons : sem_Ind_for_cons p1 ev Pc Pfor.
  Proof.
    move=> s1 s1' s2 s3 i w ws c Hwi _ Hc _ Hfor i2 r1 r1' c2 r2 vm2 Heq Hr1' Hcc Hincl.
    have [//|vm3 [Hwi2 Hvm3]] := check_lvalP (gd := gd) Hr1' Heq (value_uincl_refl _) _ Hwi.
    have [vm4 [Hvm4 Hsc]] := Hc _ _ _ _ Hvm3 Hcc.
    have [vm5 [Hvm5 Hsf]] := Hfor _ _ _ _ _ _ (eq_alloc_incl Hincl Hvm4) Hr1' Hcc Hincl.
    by exists vm5;split=>//;econstructor;eauto.
  Qed.

  Local Lemma Hcall : sem_Ind_call p1 ev Pi_r Pfun.
  Proof.
    move=> s1 scs2 m2 s2 ii xs fn args vargs vs Hes Hsc Hfun Hw r1 [] //= ii2 xs2 fn2 args2 r2 vm1 Hr1.
    rewrite /check_i.
    case: eqP => //= ?;subst fn2.
    apply: rbindP => r1' Hca Hcxs.
    have [Hr1' /(_ _ Hes) [vargs2 [Hargs2 Hvargs]]] := check_esP Hca Hr1.
    have [v' [Hs2 Hvs]]:= Hfun _ Hvargs.
    have /(_ _ Hr1') [vm2 [Hw2 Hr2]]:= check_lvalsP Hcxs _ Hvs Hw.
    exists vm2;split=>//. by econstructor;eauto;rewrite -?eq_globs.
  Qed.

  Section REFL.

    Hypothesis eq_prog : p1 = p2.

    Local Lemma Hproc_eq scs1 m1 scs2 m2 fn f vargs vargs' s0 s1 s2 vres vres':
      get_fundef (p_funcs p1) fn = Some f ->
      mapM2 ErrType truncate_val f.(f_tyin) vargs' = ok vargs ->
      init_state f.(f_extra) (p_extra p1) ev (Estate scs1 m1 vmap0) = ok s0 ->
      write_vars (f_params f) vargs s0 = ok s1 ->
      sem p1 ev s1 (f_body f) s2 ->
      Pc s1 (f_body f) s2 ->
      mapM (fun x : var_i => get_var s2.(evm) x) (f_res f) = ok vres ->
      mapM2 ErrType truncate_val f.(f_tyout) vres = ok vres' ->
      scs2 = s2.(escs) ->
      m2 = finalize f.(f_extra) s2.(emem) ->
      Pfun scs1 m1 fn vargs' scs2 m2 vres'.
    Proof.
      move=> Hget Hca Hi Hw Hsem _ Hres Hcr hscs Hfi vargs2 Hvargs2; rewrite -eq_prog.
      have: sem_call p1 ev scs1 m1 fn vargs' scs2 m2 vres' by econstructor;eauto.
      by apply: sem_call_uincl.
    Qed.

    Lemma alloc_funP_eq_aux fn f f' scs1 m1 scs2 m2 vargs vargs' vres s0 s1 s2 vres':
      check_fundef ep1 ep2 (fn, f) (fn, f') tt = ok tt ->
      mapM2 ErrType truncate_val f.(f_tyin) vargs' = ok vargs ->
      init_state f.(f_extra) (p_extra p1) ev (Estate scs1 m1 vmap0) = ok s0 ->
      write_vars (f_params f) vargs s0 = ok s1 ->
      sem p1 ev s1 (f_body f) s2 ->
      mapM (fun x : var_i => get_var (evm s2) x) (f_res f) = ok vres ->
      mapM2 ErrType truncate_val f.(f_tyout) vres = ok vres' ->
      scs2 = s2.(escs) ->
      m2 = finalize f.(f_extra) s2.(emem) ->
      exists vm0' vm1' vm2' vres1 vres1',
       [ /\ mapM2 ErrType truncate_val f'.(f_tyin) vargs' = ok vargs,
            init_state f'.(f_extra) (p_extra p2) ev (Estate scs1 m1 vmap0) = ok (with_vm s0 vm0') /\
            write_vars (f_params f') vargs (with_vm s0 vm0') = ok (with_vm s1 vm1'),
            sem p2 ev (with_vm s1 vm1') (f_body f') (with_vm s2 vm2'),
            [ /\ mapM (fun x : var_i => get_var (evm (with_vm s2 vm2')) x) (f_res f') = ok vres1, 
                 List.Forall2 value_uincl vres' vres1' &
                mapM2 ErrType truncate_val f'.(f_tyout) vres1 = ok vres1'] &
            scs2 = s2.(escs) /\ m2 = finalize f'.(f_extra) s2.(emem) ].
    Proof.
      rewrite /check_fundef eq_refl => /=.
      case: ifP => // /andP[]/andP[]/eqP htyin /eqP htyout /eqP hextra.
      t_xrbindP => r0 Hcinit r1 Hcparams r2 Hcc r3 Hcres _ Hca.
      move=> /(init_allocP Hcinit) [vm0 [Hi0 Hvm0]].
      rewrite (write_vars_lvals gd)=> /(check_lvalsP Hcparams).
      move=> /(_ vargs _ Hvm0) [ | vm3 /= [Hw2 Hvm3]].
      + by apply: List_Forall2_refl.
      move=> /(sem_Ind Hskip Hcons HmkI Hassgn Hopn Hsyscall Hif_true Hif_false
                Hwhile_true Hwhile_false Hfor Hfor_nil Hfor_cons Hcall Hproc_eq) Hc.
      have [vm4 /= [Hvm4 Hsc2] Hres Hcr]:= Hc _ _ _ _ Hvm3 Hcc.
      have := check_esP Hcres Hvm4.
      move=> [Hr3];rewrite sem_pexprs_get_var => /(_ _ Hres) [vres1' /= []].
      rewrite sem_pexprs_get_var => hmap huincl ??.
      have [vres2' ??]:= mapM2_truncate_val Hcr huincl.
      do 5 eexists;split;eauto.
      + by rewrite -htyin.
      + rewrite -hextra; split; first by eauto.
        by rewrite (write_vars_lvals gd).
      + by rewrite -htyout;split;eauto.
      by rewrite -hextra.
    Qed.

  End REFL.

  Local Lemma Hproc : sem_Ind_proc p1 ev Pc Pfun.
  Proof.
    move=> scs1 m1 scs2 m2 fn f vargs vargs' s0 s1 s2 vres vres' Hget Hca Hi Hw _ Hc Hres Hcr Hscs Hfi.
    have [fd2 [Hget2 /=]]:= all_checked Hget.
    rewrite eq_refl /=;case: ifP => // /andP[]/andP[] /eqP htyin /eqP htyout /eqP hextra.
    t_xrbindP => r0 Hcinit r1 Hcparams r2 Hcc r3 Hcres _.
    move=> vargs2 Hvargs2.
    have [vm0 [Hi0 Hvm0]]:= init_allocP Hcinit Hi.
    have [vs2 htr hall2]:= mapM2_truncate_val Hca Hvargs2.
    move: Hw;rewrite (write_vars_lvals gd)=> /(check_lvalsP Hcparams).
    move=> /(_ _ _ Hvm0 hall2) [vm3 /= [Hw2 Hvm3]].
    have [vm4 /= [Hvm4 Hsc2]]:= Hc _ _ _ _ Hvm3 Hcc.
    have := check_esP Hcres Hvm4.
    move=> [Hr3];rewrite sem_pexprs_get_var => /(_ _ Hres) [vres1' /= []].
    rewrite sem_pexprs_get_var => H1 H2.
    have [vs3 ??]:= mapM2_truncate_val Hcr H2.
    econstructor;split;eauto.
    econstructor;eauto.
    + by rewrite -htyin; eauto.
    + by rewrite -hextra; eauto.
    + by rewrite (write_vars_lvals gd).
    + by rewrite -htyout.
    by rewrite -hextra.
  Qed.

  Lemma alloc_callP_aux f scs mem scs' mem' va vr:
    sem_call p1 ev scs mem f va scs' mem' vr ->
    exists vr', sem_call p2 ev scs mem f va scs' mem' vr' /\ List.Forall2 value_uincl vr vr'.
  Proof.
    move=>
      /(@sem_call_Ind _ _ _ _ _ _ p1 ev Pc Pi_r Pi Pfor Pfun Hskip Hcons HmkI Hassgn Hopn Hsyscall
            Hif_true Hif_false Hwhile_true Hwhile_false Hfor Hfor_nil Hfor_cons Hcall Hproc).
    move=> H;apply H.
    by apply List_Forall2_refl.
  Qed.

End PROOF.

Lemma alloc_callP ev gd ep1 p1 ep2 p2 (H: check_prog ep1 p1 ep2 p2 = ok tt) f scs mem scs' mem' va vr:
    sem_call {|p_globs := gd; p_funcs := p1; p_extra := ep1; |} ev scs mem f va scs' mem' vr ->
    exists vr', 
     sem_call {|p_globs := gd; p_funcs := p2; p_extra := ep2; |} ev scs mem f va scs' mem' vr' /\
                List.Forall2 value_uincl vr vr'.
Proof.
  by apply alloc_callP_aux.
Qed.

Lemma alloc_funP_eq p ev fn f f' scs1 m1 scs2 m2 vargs vargs' vres vres' s0 s1 s2:
  check_fundef (p_extra p) (p_extra p) (fn, f) (fn, f') tt = ok tt ->
  mapM2 ErrType truncate_val f.(f_tyin) vargs' = ok vargs ->
  init_state (f_extra f) (p_extra p) ev (Estate scs1 m1 vmap0) = ok s0 ->
  write_vars (f_params f) vargs s0 = ok s1 ->
  sem p ev s1 (f_body f) s2 ->
  mapM (fun x : var_i => get_var (evm s2) x) (f_res f) = ok vres ->
  mapM2 ErrType truncate_val f.(f_tyout) vres = ok vres' ->
  scs2 = s2.(escs) ->
  m2 = finalize f.(f_extra) s2.(emem) ->
  exists vm0' vm1' vm2' vres1 vres1',
       [ /\ mapM2 ErrType truncate_val f'.(f_tyin) vargs' = ok vargs,
            init_state f'.(f_extra) (p_extra p) ev (Estate scs1 m1 vmap0) = ok (with_vm s0 vm0') /\
            write_vars (f_params f') vargs (with_vm s0 vm0') = ok (with_vm s1 vm1'),
            sem p ev (with_vm s1 vm1') (f_body f') (with_vm s2 vm2'),
            [ /\ mapM (fun x : var_i => get_var (evm (with_vm s2 vm2')) x) (f_res f') = ok vres1, 
                 List.Forall2 value_uincl vres' vres1' &
                mapM2 ErrType truncate_val f'.(f_tyout) vres1 = ok vres1'] &
            scs2 = s2.(escs) /\ m2 = finalize f'.(f_extra) s2.(emem) ].
  Proof. by apply alloc_funP_eq_aux. Qed.

End PROG.

Section UPROG.

#[local]
Existing Instance progUnit.

Lemma init_alloc_uprogP :
  forall (ef: extra_fun_t) (ep1 ep2: extra_prog_t) ev s1 scs m r,
    init_alloc_uprog ef ep1 ep2 = ok r ->
    init_state ef ep1 ev (Estate scs m vmap0) = ok s1 ->
    exists vm2,
      init_state ef ep2 ev (Estate scs m vmap0) = ok (with_vm s1 vm2) /\
      eq_alloc r s1.(evm) vm2.
Proof.
  by move=> /= ??? _ ???? [<-] [<-]; exists vmap0; split => //=; apply eq_alloc_empty.
Qed.

Lemma alloc_call_uprogP ev gd ep1 p1 ep2 p2
  (H: check_prog init_alloc_uprog ep1 p1 ep2 p2 = ok tt) f scs mem scs' mem' va vr:
    sem_call {|p_globs := gd; p_funcs := p1; p_extra := ep1; |} ev scs mem f va scs' mem' vr ->
    exists vr', 
     sem_call {|p_globs := gd; p_funcs := p2; p_extra := ep2; |} ev scs mem f va scs' mem' vr' /\
                List.Forall2 value_uincl vr vr'.
Proof. by apply: (alloc_callP init_alloc_uprogP). Qed.

Lemma alloc_fun_uprogP_eq p ev fn f f' scs1 m1 scs2 m2 vargs vargs' vres vres' s0 s1 s2:
  check_fundef init_alloc_uprog (p_extra p) (p_extra p) (fn, f) (fn, f') tt = ok tt ->
  mapM2 ErrType truncate_val f.(f_tyin) vargs' = ok vargs ->
  init_state (f_extra f) (p_extra p) ev (Estate scs1 m1 vmap0) = ok s0 ->
  write_vars (f_params f) vargs s0 = ok s1 ->
  sem p ev s1 (f_body f) s2 ->
  mapM (fun x : var_i => get_var (evm s2) x) (f_res f) = ok vres ->
  mapM2 ErrType truncate_val f.(f_tyout) vres = ok vres' ->
  scs2 = s2.(escs) ->
  m2 = finalize f.(f_extra) s2.(emem) ->
  exists vm0' vm1' vm2' vres1 vres1',
       [ /\ mapM2 ErrType truncate_val f'.(f_tyin) vargs' = ok vargs,
            init_state f'.(f_extra) (p_extra p) ev (Estate scs1 m1 vmap0) = ok (with_vm s0 vm0') /\
            write_vars (f_params f') vargs (with_vm s0 vm0') = ok (with_vm s1 vm1'),
            sem p ev (with_vm s1 vm1') (f_body f') (with_vm s2 vm2'),
            [ /\ mapM (fun x : var_i => get_var (evm (with_vm s2 vm2')) x) (f_res f') = ok vres1, 
                 List.Forall2 value_uincl vres' vres1' &
                mapM2 ErrType truncate_val f'.(f_tyout) vres1 = ok vres1'] &
            scs2 = s2.(escs) /\ m2 = finalize f'.(f_extra) s2.(emem) ].
Proof. by apply (alloc_funP_eq_aux init_alloc_uprogP). Qed.

End UPROG.

Section SPROG.

#[local]
Existing Instance progStack.

Lemma init_alloc_sprogP :
  forall (ef: extra_fun_t) (ep1 ep2: extra_prog_t) ev s1 scs m r,
    init_alloc_sprog ef ep1 ep2 = ok r ->
    init_state ef ep1 ev (Estate scs m vmap0) = ok s1 ->
    exists vm2,
      init_state ef ep2 ev (Estate scs m vmap0) = ok (with_vm s1 vm2) /\
      eq_alloc r s1.(evm) vm2.
Proof.
  rewrite /init_alloc_sprog /init_state /= /init_stk_state /check_vars.
  t_xrbindP => ef ep1 ep2 ev s1 scs m r hc m' ha; rewrite (@write_vars_lvals _ _ _ [::]) => hw.
  have [ vm2 [] ]:= check_lvalsP (s1 := (Estate scs m' vmap0)) hc eq_alloc_empty
                         (List_Forall2_refl _ (@value_uincl_refl)) hw.
  rewrite ha -write_vars_lvals => ??.
  by exists vm2.
Qed.

Lemma alloc_call_sprogP ev gd ep1 p1 ep2 p2
  (H: check_prog init_alloc_sprog ep1 p1 ep2 p2 = ok tt) f scs mem scs' mem' va vr:
    sem_call {|p_globs := gd; p_funcs := p1; p_extra := ep1; |} ev scs mem f va scs' mem' vr ->
    exists vr', 
     sem_call {|p_globs := gd; p_funcs := p2; p_extra := ep2; |} ev scs mem f va scs' mem' vr' /\
                List.Forall2 value_uincl vr vr'.
Proof. by apply: (alloc_callP init_alloc_sprogP). Qed.

End SPROG.

End WITH_PARAMS.