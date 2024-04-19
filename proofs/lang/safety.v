From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import word_ssrZ.
Require Import psem_defs typing typing_proof.

Section Safety_conditions.

Context
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {wsw : WithSubWord}
  (wdb : bool)
  (gd : glob_decls).

(*Safety checker in Ocaml -> SC
SG(P) -> s 
SC(s, P) -> True 
P |= s /\ P type checks. 

/\ P reaches ok state /\ SC is formally correct *)

(* x/y pos safe_div (x : int, y : pos) *)

(* can be used to check that an expression does not evaluate to 0 *) 
Definition not_zero_pexpr (e : pexpr) (s : @estate nosubword syscall_state ep) :=
forall v sz n, 
sem_pexpr (wsw:= nosubword) false gd s e = ok v -> 
to_word sz v = ok n -> 
(n == 0%R) = false.

(* -128/-1 = 128 which will lead to overflow *)
Definition not_overflow_pexpr (e1 e2: pexpr) (s : @estate nosubword syscall_state ep) :=
forall v1 v2 sz n n',
sem_pexpr (wsw:= nosubword) false gd s e1 = ok v1 -> 
sem_pexpr (wsw:= nosubword) false gd s e2 = ok v2 -> 
to_word sz v1 = ok n ->
to_word sz v2 = ok n' ->
(wsigned n == wmin_signed sz) && (n' == (-1)%R) = false.

(* checks that a variable is defined in the memory *)
Definition defined_var (x : var_i) (s : @estate nosubword syscall_state ep) : bool :=
is_defined (evm s).[x].

Definition get_len_stype (t : stype) : positive :=
match t with 
| sbool => xH
| sint => xH 
| sarr n => n
| sword w => xH
end.

(* Here len is the array length which is obtained from get_gvar *)
(*Definition is_align_check (aa : arr_access) (ws : wsize) (e : pexpr) 
(s : @estate nosubword syscall_state ep) :=
forall v i, sem_pexpr (wsw:= nosubword) false gd s e = ok v -> 
            to_int v = ok i -> 
is_align (i * mk_scale aa ws)%Z ws. *)

Definition is_align_check_array (e : pexpr) (ws : wsize) (s : @estate nosubword syscall_state ep) :=
forall v vp, sem_pexpr (wsw:= nosubword) false gd s e = ok v ->  
to_int v = ok vp ->
is_align vp ws.

Definition is_align_check_memory (e : pexpr) (ws : wsize) (s : @estate nosubword syscall_state ep) :=
forall v vp, sem_pexpr (wsw:= nosubword) false gd s e = ok v ->  
to_pointer v = ok vp ->
is_align vp ws.

Definition in_range_check (aa : arr_access) (ws : wsize) (x : var_i) (e : pexpr) 
(s : @estate nosubword syscall_state ep) :=
forall v i, sem_pexpr (wsw:= nosubword) false gd s e = ok v -> 
            to_int v = ok i -> 
WArray.in_range (get_len_stype x.(v_var).(vtype)) (i * mk_scale aa ws)%Z ws. 

(* Here len is the array length which is obtained from get_gvar *)

Definition in_sub_range_check (aa : arr_access) (ws : wsize) (slen : positive) (x : var_i) (e : pexpr) 
(s : @estate nosubword syscall_state ep) :=
forall v i, sem_pexpr (wsw:= nosubword) false gd s e = ok v -> 
                to_int v = ok i -> 
((0 <=? (i * mk_scale aa ws))%Z && ((i * mk_scale aa ws + arr_size ws slen) <=? (get_len_stype x.(v_var).(vtype)))%Z).

(* checks if the address is valid or not *) 
Definition addr_check (x : var_i) (ws : wsize) (e : pexpr) (s : @estate nosubword syscall_state ep) :=
forall ve w1 w2, defined_var x s ->
              sem_pexpr (wsw:= nosubword) false gd s e = ok ve ->
              to_pointer (evm s).[x] = ok w1 ->
              to_pointer ve = ok w2 ->
exists vr, read (emem s) (w1 + w2)%R ws = vr /\ 
if (is_ok vr) then (exists v, vr = ok v) else vr = Error ErrType. 

Inductive safe_cond : Type :=
| Defined_var : var_i -> safe_cond
| Not_zero : pexpr -> pexpr -> safe_cond
| No_overflow : pexpr -> pexpr -> safe_cond
| Is_align : bool -> pexpr -> wsize -> safe_cond
| In_range : pexpr -> arr_access -> wsize -> var_i -> safe_cond
| In_sub_range : pexpr -> arr_access -> wsize -> positive -> var_i -> safe_cond
| Is_valid_addr : pexpr -> var_i -> wsize -> safe_cond.


(* checks the safety condition for operations: except division and modulo, rest of the operations are safe without any 
   explicit condition *)
Definition gen_safe_cond_op2 (op : sop2) (e1 e2 : pexpr) : seq safe_cond :=
match op with 
| Odiv ck => match ck with 
             | Cmp_w u sz => [:: Not_zero e1 e2; No_overflow e1 e2]
             | Cmp_int => [::]
             end
| Omod ck => match ck with 
             | Cmp_w u sz => [:: Not_zero e1 e2; No_overflow e1 e2]
             | Cmp_int => [::]
             end
| _ => [::]
end.

Definition interp_safe_cond_op2 (s : @estate nosubword syscall_state ep) (op : sop2) (e1 e2 : pexpr) (sc: seq safe_cond) :=
match sc with 
| [::] => True 
| [:: sc1; sc2] => not_zero_pexpr e2 s /\ not_overflow_pexpr e1 e2 s
| _ => False
end. 

Section gen_safe_conds. 

Variable gen_safe_cond : pexpr -> seq safe_cond.

Fixpoint gen_safe_conds (es : seq pexpr) : seq (seq safe_cond) := 
match es with
| [::] => [::]
| e :: es => gen_safe_cond e :: gen_safe_conds es
end. 

End gen_safe_conds. 


Definition Pmul := Papp2 (Omul Op_int).
Definition Padd := Papp2 (Oadd (Op_w Uptr)).
 
Fixpoint gen_safe_cond (e : pexpr) : seq safe_cond :=
match e with   
| Pconst _ | Pbool _ | Parr_init _ => [::] 
| Pvar x => [:: Defined_var (gv x)]
| Pget aa ws x e => [:: Defined_var (gv x); 
                        Is_align true (Pmul e (Pconst (mk_scale aa ws))) ws; 
                        In_range e aa ws (gv x)] 
                     ++ gen_safe_cond e 
| Psub aa ws p x e => [:: Defined_var (gv x);
                          Is_align true (Pmul e (Pconst (mk_scale aa ws))) ws; 
                          In_sub_range e aa ws p (gv x)] 
                       ++ gen_safe_cond e 
| Pload ws x e => [:: Defined_var x;
                      Is_align false (Padd (Pvar (mk_lvar x)) e) ws;
                      Is_valid_addr e x ws] 
                   ++ gen_safe_cond e 
| Papp1 op e => gen_safe_cond e
| Papp2 op e1 e2 => gen_safe_cond e1 ++ gen_safe_cond e2 ++ gen_safe_cond_op2 op e1 e2
| PappN op es => flatten (gen_safe_conds (gen_safe_cond) es)
| Pif t e1 e2 e3 => gen_safe_cond e1 ++ gen_safe_cond e2 ++ gen_safe_cond e3
end.

Section safe_pexprs.

Variable safe_pexpr : @estate nosubword syscall_state ep -> pexpr -> seq safe_cond -> Prop.

End safe_pexprs. 

Definition interp_safe_cond (sc : safe_cond) (s : @estate nosubword syscall_state ep) : Prop :=
match sc with 
| Defined_var x => defined_var x s
| Not_zero e1 e2 => not_zero_pexpr e2 s
| No_overflow e1 e2 => not_overflow_pexpr e1 e2 s
| Is_align b e ws => if b then is_align_check_array e ws s else is_align_check_memory e ws s
| In_range e aa ws x => in_range_check aa ws x e s
| In_sub_range e aa ws len x => in_sub_range_check aa ws len x e s
| Is_valid_addr e x ws => addr_check x ws e s
end.

Fixpoint interp_safe_conds (sc : seq safe_cond) (s : @estate nosubword syscall_state ep) : Prop :=
match sc with 
| [::] => True 
| sc1 :: sc2 => interp_safe_cond sc1 s /\ interp_safe_conds sc2 s
end.

Lemma interp_safe_concat : forall sc1 sc2 s,
interp_safe_conds (sc1 ++ sc2) s ->
interp_safe_conds sc1 s /\ interp_safe_conds sc2 s.
Proof.
move=> sc1 sc2 s /=. elim: sc1=> [h | s1 s2] //=.
move=> ht [] hs1 hs2. move: (ht hs2)=> [] hs3 hs4.
by split=> //=.
Qed.

Lemma wt_safe_get_gvar_not_undef : forall x s t i ty,
vtype (gv x) = ty ->
defined_var (gv x) s ->
get_gvar false gd (evm s) x <> ok (Vundef t i).
Proof.
move=> x s t i ty ht hd hg.
rewrite /defined_var /is_defined in hd.
rewrite /get_gvar /= in hg. move: hg. case: ifP=> //= hl.
+ rewrite /get_var /=. move=> [] hg. by rewrite hg in hd.
move=> /get_globalI [gv [hg hg'' hg']]. by case: gv hg hd hg''=> //=.
Qed.

Lemma wt_safe_get_gvar_not_error : forall x s ty err,
vtype (gv x) = ty ->
defined_var (gv x) s ->
get_gvar false gd (evm s) x <> Error err.
Proof.
move=> x s ty err ht hd hg.
have hter := @get_gvar_not_tyerr asm_op syscall_state ep spp wsw wdb gd x ty s err ht hg.
rewrite /get_gvar in hg. move: hg. case: ifP=> //= hl.
rewrite /get_global. case hv: (get_global_value gd (gv x)) ht=> [a | ] //=.
+ case: ifP=> //= /eqP hty ht [] h. by rewrite h in hter.
move=> ht [] h. by rewrite h in hter.
Qed.

Lemma safe_not_undef : forall e s t he,
interp_safe_conds (gen_safe_cond e) s ->
sem_pexpr false gd s e <> ok (Vundef t he).
Proof.
move=> e s t u. elim: e=> //=.
(* Pvar *)
+ move=> x [] hd _ hg. rewrite /defined_var /is_defined in hd.
  rewrite /get_gvar /= in hg. move: hg. case: ifP=> //= hl.
  + rewrite /get_var /=. move=> [] hg. by rewrite hg in hd.
  move=> /get_globalI [gv [hg hg'' hg']]. by case: gv hg hd hg''=> //=.
(* Pget *)
+ move=> aa sz x e hin [] hs1 [] hs2 [] hs3 hs4. rewrite /on_arr_var /=.
  case hg: get_gvar=> [vg | er] //=. case: vg hg=> //= len a hg /=.
  move: (hin hs4)=> he. case he': sem_pexpr=> [ve | err] //=.
  case hi: to_int=> [vi | vrr] //=. by case ha : WArray.get=> [va | err] //=.
(* Psub *)
+ move=> aa sz len x e hin [] hs1 [] hs2 [] hs3 hs4. rewrite /on_arr_var /=.
  case hg: get_gvar=> [vg | er] //=. case: vg hg=> //= len' a hg /=.
  move: (hin hs4)=> he. case he': sem_pexpr=> [ve | err] //=.
  case hi: to_int=> [vi | vrr] //=. by case ha : WArray.get_sub=> [va | err] //=.
(* Pload *)
+ move=> sz x e hin [] hs1 [] hs2 [] hs3 hs4. case hp: to_pointer=> [vp | verr] //=.
  move: (hin hs4)=> he. case he': sem_pexpr=> [ve | verr] //=.
  case hp': to_pointer=> [vp' | verr'] //=. by case hr: read=> [vr | verr] //=.
(* Papp1 *)
+ move=> op e hin hs. move: (hin hs)=> he. case he': sem_pexpr=> [ve | verr] //=.
  rewrite /sem_sop1 /=. case hv: of_val=> [vv | verr] //=. case ht: to_val=> //= [t' ti].
  by have := to_valI ht.
(* Papp2 *)
+ move=> op e1 hin e2 hin' hs. 
  have [hs1 {hs} hs] := interp_safe_concat (gen_safe_cond e1) 
                        (gen_safe_cond e2 ++ gen_safe_cond_op2 op e1 e2) s hs.
  have [hs2 hs3] := interp_safe_concat (gen_safe_cond e2) (gen_safe_cond_op2 op e1 e2) s hs.
  move: (hin hs1)=> her1. move: (hin' hs2)=> her2. case he1 : sem_pexpr=> [ve1| ver1] //=.
  + case he2 : sem_pexpr=> [ve2| ver2] //=. rewrite /sem_sop2 /=. case hv : of_val=> [vv | ver] //=.
    + case hv' : of_val=> [vv' | ver'] //=. case ho: sem_sop2_typed=> [vo | vor] //=.
      case ht: to_val=> //= [t' ti]. by have := to_valI ht.
    by case hv' : of_val=> [vv | vvr] //=.
  by case he1': sem_pexpr=> [ve | ver] //=.
(* PappN *)
+ move=> op es hin hs. case hm: mapM=> [vm | vmr] //=. rewrite /sem_opN /=.
  case ha: app_sopn=> [va | var] //=. case ht: to_val=> //= [t' ti]. by have := to_valI ht.
(* Pif *)
move=> ty e hin e1 hin1 e2 hin2 hs.
have [hs1 hs2] := interp_safe_concat (gen_safe_cond e) (gen_safe_cond e1 ++ gen_safe_cond e2) s hs.
have [hs3 hs4] := interp_safe_concat (gen_safe_cond e1) (gen_safe_cond e2) s hs2.
move: (hin hs1)=> he1. move: (hin1 hs3)=> he2. move: (hin2 hs4)=> he3.
case h1: sem_pexpr=> [ve | ver] //=.
+ case h2: sem_pexpr=> [ve1 | ver1] //=.
  + case h3: sem_pexpr=> [ve2 | ver2] //=. case hb : to_bool=> [vb | vbr] //=.
    case ht: truncate_val=> [vt | vtr] //=.
    + case ht': truncate_val=> [vt' | vtr'] //=. case: ifP=> //= h; subst.
      + move: ht'. rewrite /truncate_val /=. case hv: of_val=> [vv | vvr] //=.
        move=> [] hv'. have := to_valI hv'. by case: vt' hv hv'=> //=.
      move: ht. rewrite /truncate_val /=. case hv: of_val=> [vv | vvr] //=.
      move=> [] hv'. have := to_valI hv'. by case: vt hv hv'=> //=.
    by case ht': truncate_val=> [vee | vtr1] //=.
  case he: sem_pexpr=> [vee | ver] //=. by case hb: to_bool=> [vb | vbr] //=.
case he1': sem_pexpr=> [ve1 | veer1] //=.  
+ case he': sem_pexpr=> [ve | vee] //=. case hb: to_bool=> [vb | vbr] //=.
  by case ht: truncate_val=> [vt | vtr] //=.  
case he' : sem_pexpr=> [ve | veer] //=. by case hb: to_bool=> [vb | vbr] //=.  
Qed.

Lemma wt_safe_to_bool_not_error : forall pd e (s: @estate nosubword syscall_state ep) ve err,
ty_pexpr pd e = ok sbool ->
interp_safe_conds (gen_safe_cond e) s ->
sem_pexpr false gd s e = ok ve ->
to_bool ve <> Error err.
Proof.
move=> pd e s ve err ht hs he. 
have htve := @sem_pexpr_well_typed asm_op syscall_state ep spp wsw wdb gd pd sbool e s ve ht he.
rewrite /to_bool /=. case: ve he htve=> //= t i he hte; subst.
by have := safe_not_undef e s sbool i hs he.
Qed.

Lemma wt_safe_to_int_not_error : forall pd e (s: @estate nosubword syscall_state ep) ve err,
ty_pexpr pd e = ok sint ->
interp_safe_conds (gen_safe_cond e) s ->
sem_pexpr false gd s e = ok ve ->
to_int ve <> Error err.
Proof.
move=> pd e s ve err ht hs he. 
have htve := @sem_pexpr_well_typed asm_op syscall_state ep spp wsw wdb gd pd sint e s ve ht he.
rewrite /to_int /=. case: ve he htve=> //= t i he hte; subst.
by have := safe_not_undef e s sint i hs he.
Qed.

Lemma wt_safe_to_arr_not_error : forall pd e (s: @estate nosubword syscall_state ep) p ve err,
ty_pexpr pd e = ok (sarr p) ->
interp_safe_conds (gen_safe_cond e) s ->
sem_pexpr false gd s e = ok ve ->
to_arr p ve <> Error err.
Proof.
move=> pd e s p ve err ht hs he. 
have htve := @sem_pexpr_well_typed asm_op syscall_state ep spp wsw wdb gd pd (sarr p) e s ve ht he.
rewrite /to_arr /=. case: ve he htve=> //= t i he hte; subst. case: hte=> hte'; subst.
+ rewrite /WArray.cast /=. by case: ifP=> //= /eqP.
by have := safe_not_undef e s (sarr p) i hs he.
Qed.

Lemma wt_safe_to_word_not_error : forall pd e (s: @estate nosubword syscall_state ep) sz sz' ve err,
ty_pexpr pd e = ok (sword sz') ->
(sz <= sz')%CMP ->
interp_safe_conds (gen_safe_cond e) s ->
sem_pexpr false gd s e = ok ve ->
to_word sz ve <> Error err.
Proof.
move=> pd e s sz sz' ve err ht hcmp hs he. 
have htve := @sem_pexpr_well_typed asm_op syscall_state ep spp wsw wdb gd pd (sword sz') e s ve ht he.
rewrite /to_word /=. case: ve he htve=> //= t i he hte; subst. case: hte=> hte'; subst.
+ have htr := truncate_word_le i hcmp. move=> htr'. by rewrite htr' in htr.
by have := safe_not_undef e s (sword sz') i hs he.
Qed.

Lemma wt_safe_truncate_not_error : forall pd e s v t ty err,
interp_safe_conds (gen_safe_cond e) s ->
ty_pexpr pd e = ok t ->
sem_pexpr false gd s e = ok v ->
subtype ty t ->
truncate_val ty v <> Error err.
Proof.
move=> pd e s v t ty err hs hte he hsub. rewrite /truncate_val /=.
case hv : of_val=> [vo | vor] //=.
case: ty hsub hv=> //=.
+ move=> /eqP hb hbv; subst. 
  by have hbv' := wt_safe_to_bool_not_error pd e s v vor hte hs he.
+ move=> /eqP hi hiv; subst.
  by have hbv' := wt_safe_to_int_not_error pd e s v vor hte hs he.
+ move=> p /eqP ht; subst.
  by have hbv' := wt_safe_to_arr_not_error pd e s p v vor hte hs he.
move=> sz. case: t hte=> //= sz' hte hcmp hw.
by have hw' := wt_safe_to_word_not_error pd e s sz sz' v vor hte hcmp hs he.
Qed.

Lemma sem_op1_val_ty : forall tin tout op v vo,
type_of_op1 op = (tin, tout) ->
sem_sop1 op v = ok vo ->
type_of_val vo = tout.
Proof.
move=> tin tout op v vo ht ho.
rewrite /sem_sop1 /= in ho.  move: ho. 
t_xrbindP=> z h1 h2. have := to_valI h2. case: vo h2=> //=.
+ move=> b /= hb [] b' heq; subst. by rewrite -b' /= ht /=. 
+ move=> zi /= hi [] zi' heq; subst. by rewrite -zi' /= ht /=.
+ move=> len a ha [] len' heq; subst. by rewrite -len' /= ht /=.
move=> w w' hw [] wt heq; subst. by rewrite -wt /= ht /=.
Qed.

Lemma wt_safe_of_val_not_error : forall pd s e t ty ve err,
ty_pexpr pd e = ok t ->
subtype ty t ->
interp_safe_conds (gen_safe_cond e) s ->
sem_pexpr false gd s e = ok ve ->
of_val ty ve <> Error err.
Proof.
move=> pd s e t ty v err hte hsub hs he.
case: ty hsub=> //=.
+ move=> /eqP hb hbv; subst. 
  by have hbv' := wt_safe_to_bool_not_error pd e s v err hte hs he.
+ move=> /eqP hi hiv; subst.
  by have hbv' := wt_safe_to_int_not_error pd e s v err hte hs he.
+ move=> p /eqP ht; subst.
  by have hbv' := wt_safe_to_arr_not_error pd e s p v err hte hs he.
move=> sz. case: t hte=> //= sz' hte hcmp hw.
by have hw' := wt_safe_to_word_not_error pd e s sz sz' v err hte hcmp hs he.
Qed.
           
Lemma wt_safe_sem_op1_not_error : forall pd op tin tout t1 e s v err,
type_of_op1 op = (tin, tout) ->
subtype tin t1 ->
ty_pexpr pd e = ok t1 ->
interp_safe_conds (gen_safe_cond e) s ->
sem_pexpr false gd s e = ok v ->
sem_sop1 op v <> Error err.
Proof.
move=> pd op tin tout t e s ve err htop hsub hte hse hs. 
rewrite /sem_sop1 /=.
case hvo: of_val=> [vo | vor] //=.  rewrite htop /= in hvo.
by have := wt_safe_of_val_not_error pd s e t tin ve vor hte hsub hse hs.
Qed.

Lemma wt_safe_sem_sop2_not_error : forall pd op t1 e1 t2 e2 s ve1 ve2 err,
subtype (type_of_op2 op).1.1 t1 ->
ty_pexpr pd e1 = ok t1 ->
subtype (type_of_op2 op).1.2 t2 ->
ty_pexpr pd e2 = ok t2 ->
interp_safe_conds (gen_safe_cond e1) s ->
interp_safe_conds (gen_safe_cond e2) s ->
interp_safe_conds (gen_safe_cond_op2 op e1 e2) s ->
sem_pexpr false gd s e1 = ok ve1 ->
sem_pexpr false gd s e2 = ok ve2 ->
sem_sop2 op ve1 ve2 <> Error err.
Proof.
move=> pd op t1 e1 t2 e2 s ve1 ve2 err hsub1 ht1 hsub2 ht2 hs1 hs2 hs3 he1 he2.
rewrite /sem_sop2 /=. case hvo : of_val=> [vo | vor] //=.
+ case hvo': of_val=> [vo' | vor'] //=.
  + case hso : sem_sop2_typed=> [so | sor] //=. rewrite /gen_safe_cond_op2 in hs3.
    case: op hsub1 hsub2 hs3 vo hvo vo' hvo' hso=> //=.
    + move=> o. by case: o=> //=.
    + move=> o. by case: o=> //=.
    + move=> o. by case: o=> //=.
    + move=> o. case: o=> //= sig sz.
      case: t1 ht1=> //= sz' ht1 hcmp. case: t2 ht2=> //= sz'' ht2 hcmp' [] hnz [] hnz' _ w' hw' w hw /=.
      rewrite /mk_sem_divmod /=. case: ifP=> //=. rewrite /not_zero_pexpr in hnz.
      move: (hnz ve2 sz w' he2 hw')=> hnw heq [] h'; subst. rewrite /not_overflow_pexpr in hnz'.
      move: (hnz' ve1 ve2 sz w w' he1 he2 hw hw') => hnw'. 
      have heq'' := Bool.orb_false_intro (w' == 0%R) ((wsigned w == wmin_signed sz) && (w' == (-1)%R)) hnw hnw'.
      by rewrite heq'' in heq. 
    + move=> o. case: o=> //= sig sz.
      case: t1 ht1=> //= sz' ht1 hcmp. case: t2 ht2=> //= sz'' ht2 hcmp' [] hnz [] hnz' _ w' hw' w hw /=.
      rewrite /mk_sem_divmod /=. case: ifP=> //=. rewrite /not_zero_pexpr in hnz.
      move: (hnz ve2 sz w' he2 hw')=> hnw heq [] h'; subst. rewrite /not_overflow_pexpr in hnz'.
      move: (hnz' ve1 ve2 sz w w' he1 he2 hw hw') => hnw'. 
      have heq'' := Bool.orb_false_intro (w' == 0%R) ((wsigned w == wmin_signed sz) && (w' == (-1)%R)) hnw hnw'.
      by rewrite heq'' in heq.  
    + move=> o. by case: o=> //=.
    + move=> o. by case: o=> //=.
    + move=> o. by case: o=> //=.
    + move=> o. by case: o=> //=.
    + move=> o. by case: o=> //=.
    + move=> o. by case: o=> //=.
    + move=> o. by case: o=> //=.
    move=> o. by case: o=> //=.
  by have hvo'':= wt_safe_of_val_not_error pd s e1 t1 (type_of_op2 op).1.1 ve1 vor' ht1 hsub1 hs1 he1.
by have hvo':= wt_safe_of_val_not_error pd s e2 t2 (type_of_op2 op).1.2 ve2 vor ht2 hsub2 hs2 he2.
Qed.

Lemma wt_safe_read_not_error : forall pd e t (x:var_i) s w ve vp vp' err,
subtype (sword pd) t ->
ty_pexpr pd e = ok t ->
defined_var x s ->
is_align_check_memory (Padd (mk_lvar x) e) w s ->
addr_check x w e s ->
interp_safe_conds (gen_safe_cond e) s ->
sem_pexpr false gd s e = ok ve ->
to_pointer ve = ok vp ->
to_pointer (evm s).[x] = ok vp' ->
read (emem s) (vp' + vp)%R w <> Error err.
Proof.
move=> pd e t x s w ve vp vp' err hsub hte hd ha haddr hs he hp hp'.
rewrite /addr_check /= in haddr. move: (haddr ve vp' vp hd he hp' hp)=> [] vr [] hr.
case: ifP=> //=.
+ move=> hok [] v heq; subst. by rewrite heq.
move=> hnok hvr; subst.
case: t hsub hte=> //= w' hsub hte.
by have := @read_ptr_not_tyerr asm_op syscall_state ep spp wsw 
        wdb gd pd s e ve w' x vp' vp ErrType w he hte hp' hp hvr.
Qed.

Lemma wt_safe_to_pointer_error : forall pd wr (x: var_i) s err,
vtype x = sword wr ->
(pd ≤ wr)%CMP ->
defined_var x s ->
to_pointer (evm s).[x] <> Error err.
Proof.
move=> pd wr x s err ht hsub hd hp. 
have htr := @to_pointer_not_tyerr_var asm_op syscall_state ep spp wsw 
            wdb gd s x wr err ht hp.
case hv : ((evm s).[x]) hd hp=> [ b | z| arr a| w sz| i u] //=.
+ move=> hd [] hr. have hg : get_var false (evm s) x = ok (Vbool b).
  + by rewrite /get_var /= hv. 
  have /= /eqP hsub' := type_of_get_var hg. by rewrite -hsub' in ht.
+ move=> hd [] hr. have hg : get_var false (evm s) x = ok (Vint z).
  + by rewrite /get_var /= hv. 
  have /= /eqP hsub' := type_of_get_var hg. by rewrite -hsub' in ht.
+ move=> hd [] hr. have hg : get_var false (evm s) x = ok (Varr a).
  + by rewrite /get_var /= hv. 
  have /= /eqP hsub' := type_of_get_var hg. by rewrite -hsub' in ht.
+ move=> hd hr. have hg : get_var false (evm s) x = ok (Vword (s:=w) sz).
  + by rewrite /get_var /= hv. 
  have /= /eqP hsub' := type_of_get_var hg. rewrite ht /eqP in hsub'. 
  move: hsub'. move=> /eqP hsub'. by have [hter hter'] := truncate_word_errP hr; subst.
by rewrite /defined_var /is_defined hv /=.
Qed.

Lemma wt_safe_exp_to_pointer_error : forall pd e t (x:var_i) s ve err,
ty_pexpr pd e = ok t ->
subtype (sword pd) t ->
interp_safe_conds (gen_safe_cond e) s ->
sem_pexpr false gd s e = ok ve ->
to_pointer ve <> Error err.
Proof.
move=> pd e t x s ve err ht hsub hs he. case: t ht hsub=> //= w ht hsub hp.
have htve := @sem_pexpr_well_typed asm_op syscall_state ep spp wsw wdb gd pd (sword w) e s ve ht he.
have htr := @to_pointer_not_tyerr asm_op syscall_state ep spp wsw 
            wdb gd pd s e ve w err ht he hsub hp.
case hve: ve he htve hp=> [ b | z | arr a | sz wsz | u i ] //=; subst.
+ move=> he htve htp; subst. by have [hter hter'] := truncate_word_errP htp; subst.
move=> he htve hu; subst. by have := safe_not_undef e s (sword w) i hs he.
Qed.

Lemma wt_safe_read_arr_not_error : forall pd e x p aa sz s arr (p':WArray.array arr) ve vi err,
ty_pexpr pd e = ok sint ->
vtype (gv x) = sarr p ->
defined_var (gv x) s ->
is_align_check_array (Pmul e (mk_scale aa sz)) sz s ->
in_range_check aa sz (gv x) e s ->
interp_safe_conds (gen_safe_cond e) s ->
get_gvar false gd (evm s) x = ok (Varr p') ->
sem_pexpr false gd s e = ok ve ->
to_int ve = ok vi ->
read p' (vi * mk_scale aa sz)%Z sz <> Error err.
Proof.
move=> pd e x p aa sz s p' arr ve vi err hte htx hd ha hr hs hg he hi.
rewrite /is_align_check_array /= he /sem_sop2 /= hi /= in ha.
move: (ha (vi * mk_scale aa sz)%Z (vi * mk_scale aa sz)%Z erefl erefl)=> {ha} ha.
rewrite /in_range_check in hr. move: (hr ve vi he hi)=> {hr} hr hread.
rewrite /read ha in hread. 
case hm: mapM hread=> [vm | vmr] //=. move=> [] heq; subst. 
move: err hm. elim : (ziota 0 (wsize_size sz))=> [ | n ns] //= hin err.
case hwr: WArray.get8=> [wv | wvr] //=.
+ case hm: mapM=> [vm | vmr] //= [] heq; subst. by move: (hin err hm).
move=> [] heq; subst. 
have htr := array_get8_not_tyerr p' arr (add (vi * mk_scale aa sz)%Z n) err hwr.
rewrite /WArray.get8 in hwr. move: hwr.
case has: assert=> [va | var] //=.
+ case has': assert=> [va' | var'] //= [] heq1. 
  rewrite /assert in has'. move: has'. case: ifP=> //= has' [] heq2.
  rewrite heq1 in heq2. rewrite /WArray.in_bound /= in has'. 
  move: has'. rewrite /andb /=. case: ifP=> //= h h'.  
  + rewrite /WArray.in_range in hr. move: hr. rewrite /andb. case: ifP=> //= h1 h2.
    rewrite /get_len_stype htx in h2. 
    have hvt := @type_of_get_gvar_eq asm_op syscall_state ep spp wsw wdb gd (evm s) x (Varr arr) hg.
    rewrite htx /type_of_val in hvt. case: hvt=> hvt'; subst. rewrite WArray.addE in h'.
    have [hl hr] := Z.ltb_ge (vi * mk_scale aa sz + n) p. move: (hl h')=> hl'.
    admit.
  subst. admit.
case has': assert=> [va' | var'] //=. 
+ move=>[] heq; subst. rewrite /assert in has. 
  move: has. case: ifP=> //= has [] heq; subst. rewrite /WArray.is_init in has.
  move: has. admit.
move=> [] heq; subst. admit.
Admitted.

Lemma wt_safe_sem_opN_not_error : forall pd es op vm vma s err,
mapM2 ErrType (check_expr ty_pexpr pd) es (type_of_opN op).1 = ok vm ->
interp_safe_conds (flatten (gen_safe_conds gen_safe_cond es)) s ->
mapM (sem_pexpr false gd s) es = ok vma ->
sem_opN op vma <> Error err.
Proof.
move=> pd es op. case hteq: (type_of_opN op).1=> [ | t ts] //=; subst.
+ admit.
move: (t :: ts). elim: es=> //=.
+ admit.
move=> e es hin. move=> sts sts' vs s err. 
case heq': sts=> [ | t' ts'] //=; subst.
case hc: check_expr=> [vc | vcr] //=.
case hm: mapM2=> [vm | vmr] //= [] heq hs; subst.
case he: sem_pexpr=> [ve | ver] //=. 
case hes: mapM=> [ves | vesr] //= [] heq; subst.
have [hs1 hs2] := interp_safe_concat (gen_safe_cond e)
(flatten (gen_safe_conds gen_safe_cond es)) s hs.
move: (hin ts' vm ves s err hm hs2 hes)=> hoer.
rewrite /sem_opN /=. case h: app_sopn => [r | er] //=.
move=> [] heq; subst. 
Admitted.

Lemma type_of_get_gvar_eq : forall x (vm : @Vm.t nosubword) v,
is_defined v ->
get_gvar false gd vm x = ok v ->
(type_of_val v) = (vtype x.(gv)).
Proof.
move=> x vm v. rewrite /get_gvar. case: ifP=> //= hl hd hg.
+ have /= [_ h]:= get_var_compat hg. rewrite /compat_val /= /compat_type in h.
  move: h. case: ifP=> //=.
  + move=> hd'. by rewrite hd in hd'.
  by move=> hd' /eqP ->.
by have := type_of_get_global hg.
Qed.

Theorem sem_pexpr_safe : forall pd e s ty,
ty_pexpr pd e = ok ty ->
interp_safe_conds (gen_safe_cond e) s ->
exists v, sem_pexpr (wsw := nosubword) false gd s e = ok v /\ type_of_val v = ty.
Proof.
move=> pd e s. elim: e=> //=.
(* Pconst *)
+ move=> z ty [] ht _; subst. by exists z. 
(* Pbool *)
+ move=> b ty [] ht _; subst. by exists b. 
(* Parr_init *)
+ move=> n ty [] ht _; subst. by exists (Varr (WArray.empty n)).
(* Pvar *)
+ move=> x ty [] ht [] hd _. case hg: get_gvar=> [vg | vgr] //=.
  + exists vg. split=> //=. have hvg : is_defined vg. 
    + rewrite /is_defined /=. 
      case: vg hg=> //= t i hg. 
      by have := wt_safe_get_gvar_not_undef x s t i ty ht hd. 
    have hsub := type_of_get_gvar_eq x (evm s) vg hvg hg.
    by rewrite ht /= in hsub. 
  by have := wt_safe_get_gvar_not_error x s ty vgr ht hd hg.
(* Pget *)
+ move=> aa sz x e hin ty. rewrite /ty_get_set /check_array /=. 
  t_xrbindP=> t hte t'. case ht: (vtype (gv x))=> [  | | p |] //= [] heq; subst.
  rewrite /check_int /check_type /=. case: ifP=> //= /eqP hteq t2 [] hteq' hteq''; subst. 
  move=> [] hs1 [] hs2 [] hs3 hs4.
  rewrite /on_arr_var /=. case hg: get_gvar=> [vg | vgr] //=.
  + case hvg: vg=> [b | z | p' arr| w wsz| t i] //=; subst.
    + have hdb : is_defined b. + by rewrite /is_defined. 
      have ht' := type_of_get_gvar_eq x (evm s) b hdb hg. by rewrite ht /= in ht'.
    + have hdb : is_defined z. + by rewrite /is_defined. 
      have ht' := type_of_get_gvar_eq x (evm s) z hdb hg. by rewrite ht /= in ht'.
    + move: (hin sint hte hs4) => [] ve [] he htve. rewrite he /=. 
      case hi : to_int=> [vi | vr] //=.
      + case hw : WArray.get=> [vw | vwr] //=.
        + exists (Vword (s:=sz) vw). by split=> //=.
        rewrite /WArray.get /= in hw.
        by have := wt_safe_read_arr_not_error pd e x p aa sz s p' arr ve vi vwr
                   hte ht hs1 hs2 hs3 hs4 hg he hi.
      by have := wt_safe_to_int_not_error pd e s ve vr hte hs4 he. 
    + have hdb : is_defined (Vword (s:=w) wsz). + by rewrite /is_defined. 
      have ht' := type_of_get_gvar_eq x (evm s) (Vword (s:=w) wsz) hdb hg. by rewrite ht /= in ht'.
    by have := wt_safe_get_gvar_not_undef x s t i (sarr p) ht hs1. 
  by have := wt_safe_get_gvar_not_error x s (sarr p) vgr ht hs1.
(* Psub *)
+ move=> aa sz len x e hin ty. rewrite /ty_get_set_sub /check_array /= /check_int /= /check_type /=.
  t_xrbindP => t hte t'. case ht: (vtype (gv x))=> [  | | p|] //= [] heq; subst.
  move=>ti. case: ifP=> //= /eqP hteq [] hteq' hteq''; subst. move=> [] hs1 [] hs2 [] hs3 hs4.   
  rewrite /on_arr_var /=. case hg: get_gvar=> [vg | vgr] //=.
  + case hvg: vg=> [b | z | p' arr| w wsz| t i] //=; subst.
    + have hdb : is_defined b. + by rewrite /is_defined. 
      have ht' := type_of_get_gvar_eq x (evm s) b hdb hg. by rewrite ht /= in ht'.
    + have hdb : is_defined z. + by rewrite /is_defined. 
      have ht' := type_of_get_gvar_eq x (evm s) z hdb hg. by rewrite ht /= in ht'.
    + move: (hin sint hte hs4) => [] ve [] he htve. rewrite he /=. 
      case hi : to_int=> [vi | vr] //=.
      + case hw : WArray.get_sub=> [vw | vwr] //=.
        + exists (Varr vw). by split=> //=.
        rewrite /WArray.get_sub /= in hw. move: hw. case: ifP=> //= /andP [].
        rewrite /in_sub_range_check /= ht /= in hs3.
        have hd : is_defined (Varr arr).
        + by rewrite /is_defined.
        move: (hs3 ve vi he hi)=> /andP. have hsub' := type_of_get_gvar_eq x (evm s) (Varr arr) hd hg. 
        rewrite ht /= in hsub'. by move: hsub'=> [] heq'; subst.
      by have := wt_safe_to_int_not_error pd e s ve vr hte hs4 he. 
    + have hdb : is_defined (Vword (s:=w) wsz). + by rewrite /is_defined. 
      have ht' := type_of_get_gvar_eq x (evm s) (Vword (s:=w) wsz) hdb hg. by rewrite ht /= in ht'.
    by have := wt_safe_get_gvar_not_undef x s t i (sarr p) ht hs1.
  by have := wt_safe_get_gvar_not_error x s (sarr p) vgr ht hs1.
(* Pload *)
+ move=> w x e hin ty. rewrite /ty_load_store /= /check_ptr /check_type.
  t_xrbindP=> te hte t1. case: ifP=> //= hsub [] heq t2; subst. 
  case: ifP=> //= hsub' heq' t3 hs; subst. case: heq'=> heq'; subst.
  move:hs=> [] hs1 [] hs2 [] hs3 hs4.
  move: (hin t2 hte hs4)=> [] ve [] he htve. rewrite he /=.
  case hp: to_pointer=> [vp | vpr] //=.
  + case hp': to_pointer=> [vp' | vpr'] //=.
    + case hr: read=> [vr | vrr] //=.
      + exists (Vword (s:=w) vr). by split=> //=.
      by have /= := wt_safe_read_not_error pd e t2 x s w ve vp vp' vrr hsub' hte hs1 hs2 hs3 hs4 he hp hp'.
    case hsub : (vtype x) hsub=> //= [wr] hsub''.
    by have //= := wt_safe_to_pointer_error pd wr x s vpr' hsub hsub'' hs1. 
  by have //= := wt_safe_exp_to_pointer_error pd e t2 x s ve vpr hte hsub' hs4 he.
(* Papp1 *)
+ move=> op e hin ty. case hto: type_of_op1=> [tin tout]. rewrite /check_expr /= /check_type.
  t_xrbindP=> t1 t2 hte. case: ifP=> //= hsub [] heq heq'; subst. 
  move=> hs. move: (hin t1 hte hs)=> [] v [] he ht. rewrite he /=.
  case ho: sem_sop1=> [ vo | vor] //=.
  + exists vo. split=> //=.
    by have := sem_op1_val_ty tin ty op v vo hto ho.
  by have //= := wt_safe_sem_op1_not_error pd op tin ty t1 e s v vor hto hsub hte hs he.
(* Papp2 *)
+ move=> op e1 hin1 e2 hin2 ty. rewrite /check_expr /check_type /=.
  t_xrbindP=> t1 t1' ht1. case: ifP=> //= hsub [] hteq t2 t2' ht2; subst.
  case: ifP=> //= hsub' [] hteq' hteq hs; subst.
  have [hs1 hs2] := interp_safe_concat (gen_safe_cond e1) 
                         ((gen_safe_cond e2) ++ (gen_safe_cond_op2 op e1 e2)) s hs.
  have [hs3 hs4] := interp_safe_concat (gen_safe_cond e2) (gen_safe_cond_op2 op e1 e2) s hs2.
  move: (hin1 t1 ht1 hs1)=> [] ve1 [] he1 hte1.
  move: (hin2 t2 ht2 hs3)=> [] ve2 [] he2 hte2. rewrite he1 /= he2 /=.
  case ho: sem_sop2=> [vo | vor] //=.
  + exists vo. split=> //=. rewrite /sem_sop2 /= in ho.
    move: ho. t_xrbindP=> z h1 z' h2 z1 h3 h4 /=. rewrite -h4 /=. by apply type_of_to_val. 
  by have := wt_safe_sem_sop2_not_error pd op t1 e1 t2 e2 s ve1 ve2 
             vor hsub ht1 hsub' ht2 hs1 hs3 hs4 he1 he2 ho.
(* PappN *)
+ admit.
(* Pif *)
move=> t e hin e1 hin1 e2 hin2 ty hty hs. move: hty.
rewrite /check_expr /= /check_type /=. t_xrbindP=> te te' hte. 
case: ifP=> //= /eqP hte' [] heq; subst.
move=> t1 t2 hte1. case: ifP=> //= hsub [] heq; subst.
move=> t2 t3 hte2. case: ifP=> //= hsub' [] heq' heq''; subst.
have [hs1 hs2]:= interp_safe_concat (gen_safe_cond e) 
                        ((gen_safe_cond e1) ++ (gen_safe_cond e2)) s hs.
have [hs3 hs4]:= interp_safe_concat (gen_safe_cond e1) (gen_safe_cond e2) s hs2.
move: (hin sbool hte hs1)=> [] b [] he hbt.
move: (hin1 t1 hte1 hs3)=> [] v1 [] he1 ht1.
move: (hin2 t2 hte2 hs4)=> [] v2 [] he2 ht2.
rewrite he /= he1 /= he2 /=. 
case: b he hbt=> //= b he hbt /=. 
+ case ht: truncate_val=> [vt | vtr] //=.
  + case ht': truncate_val=> [vt' | vtr'] //=.
    + exists (if b then vt' else vt). split=> //=.
      case hb: b he=> //= he.
      + by have := truncate_val_has_type ht'.
      by have := truncate_val_has_type ht.
    by have //= := wt_safe_truncate_not_error pd e1 s v1 t1 ty vtr' hs3 hte1 he1 hsub.
  by have //= := wt_safe_truncate_not_error pd e2 s v2 t2 ty vtr hs4 hte2 he2 hsub'.
move=> hbeq; subst. by have //= := safe_not_undef e s sbool he hs1 hbt. 
Admitted.


(*Theorem sem_pexpr_safe : forall e s r,
safe_pexpr s e ->
sem_pexpr (wsw:= nosubword) false gd s e = r ->
is_ok r \/ r = Error ErrType.
Proof.
move=> e s r. move: r s. elim: e.
(* Pconst *)
- move=> z r s /= _ <-. by left.
(* Pbool *)
- move=> b r s /= _ <-. by left.
(* Parr_init *)
- move=> n r s /= _ <-. by left.
(* Pvar *)
- move=> x r s /= hd hg. rewrite /defined_var /is_defined /= in hd.
  rewrite /get_gvar /= in hg. move: hg. case: ifP=> //= -[hlval hgob].
  (* lvar *)
  - rewrite /get_var /= in hgob; subst. by left.
  (* glob *)
  rewrite /get_global /= in hgob. move: hgob. case hgobv : get_global_value=> //=. 
  (* some value *)
  + case: ifP=> //= /eqP ht.
    * move=> <- /=. by left.
    move=> <-. by right.
  (* none *)
  move=> <- /=. by right.
(* Pget *)
- move=> aa sz x e /= hin r s [] hv [] he ha.
  rewrite /on_arr_var /=. case hg : get_gvar=> [vg| er]//=.
  (* get_gvar evaluates to ok *)
  + case hg': vg hg=> [ v1 | v2 | l arr | ws w | t ut ] //=; subst; move=> hg ht; subst.
    * by right.
    * by right.
    * case he': sem_pexpr=> [ve | ver] //=. 
      + case hi : to_int=> [vi | vir ] //=. rewrite /WArray.get /=. 
        rewrite /alignment_range_check /= in ha. move: (ha ve vi l he' hi)=> [] h1 h2.
        case hr: read=> [vr | ver] //=.
        + by left.
        right. by have -> := read_ty_error vi aa sz l arr ver h1 h2 hr.
      right. by have -> := to_int_ty_error s e ve vir he' he hi.
    by move: (hin (Error ver) s he he')=> /=.
    * by right.
    * by right.
  have -> := get_gvar_ty_error s x er hv hg. move=> <- /=. by right.
(* Psub *)
- move=> aa sz len x e /= hin r s [] hd [] hs ha. rewrite /on_arr_var /=. 
  case hg : get_gvar=> [vg | vgr] //=.
  + case hg': vg hg=> [ v1 | v2 | l arr | ws w | t ut ] //=; subst; move=> hg ht; subst.
    * by right.
    * by right.
    * case he': sem_pexpr=> [ve | ver] //=.
      + case hi: to_int=> [vi | vir] //=. case hwa : WArray.get_sub=> [wa | war] //=.
        + by left.
        rewrite /WArray.get_sub in hwa. move: hwa. case: ifP=> //= h.
        rewrite /alignment_sub_range_check in ha. move: (ha ve vi l he' hi)=> [] hal hc.
        by rewrite hc in h.
      have -> := to_int_ty_error s e ve vir he' hs hi. by right.
    by move: (hin (Error ver) s hs he') => /=.
    * by right.
    * by right.
  have -> := get_gvar_ty_error s x vgr hd hg. move=> <- /=. by right.   
(* Pload *)
- move=> sz z e hin r s /= [] hs [] hd ha.
  case hp: to_pointer=> [vp | vpr] //=.
  + case he: sem_pexpr=> [ve | ver] //=.
    + case hp': to_pointer=> [vp' | vpr']//=.
      + case hr: read=> [vr | vre] //=.
        + move=> <-. by left.
        move=> h; subst. rewrite /addr_check in ha.
        move: (ha z ve vp vp' hd he hp hp')=> hw. 
        rewrite /validw in hw. move: hw. move=> /andP [] hal hall. 
        have -> := read_mem_ty_error vp vp' sz s vre hal hr. by right.
       move=> h; subst. have -> := to_pointer_ty_error s e ve vpr' he hs hp'. by right.
     move=> hr; subst. by move: (hin (Error ver) s hs he).
  move=> h; subst. have -> := to_pointer_ty_error' s z vpr hd hp. by right.
(* Papp1 *)
- move=> op e hin r s /= hs /=.
  case he: sem_pexpr=> [ve | ver] //=.
  + rewrite /sem_sop1 /=. case hv: of_val=> [vv | vvr] //=.
    + move=> <-. by left.
    move=> h; subst. have -> := of_val_ty_error (type_of_op1 op).1 s e ve vvr he hs hv.
    by right.
  move=> h; subst. by move: (hin (Error ver) s hs he).
(* Papp2 *)
- move=> op e1 hin e2 hin' r s /= [] hs1 [] hs2 hs3.
  case he2: sem_pexpr=> [ve2 | ver2] //=.
  + case he1: sem_pexpr=> [ve1 | ver1] //=.
    + move=> ho. by have := sem_sop2_safe s op e1 ve1 e2 ve2 r hs3 he1 he2 ho.
    move=> h; subst. by move: (hin (Error ver1) s hs1 he1).
  case he1: sem_pexpr=> [ve1 | ver1] //=. 
  + move=> h; subst. by move: (hin' (Error ver2) s hs2 he2).
  move=>h; subst. by move: (hin (Error ver1) s hs1 he1). 
(* PappN *)
- move=> op es hin r s hs /=. 
  case hm: mapM=> [vm | vmr] //= ho. 
  + case hr: r ho=> [vo | vor] //=.
    + subst. by left.
    move=> ho. have -> := sem_opN_safe s es vm vor op hs hm ho. by right.
  subst. case: es hin hs hm=> //= e es hin [] hse hses.
  case h: sem_pexpr=> [ve | ver] //=.
  + case hm: mapM=> [vs | vsr] //=.
    + move=> [] heq; subst. have heq : e = e \/ List.In e es. + by left.
      have -> := sem_pexprs_ty_error s es vmr hses hm. by right.
    have heq : e = e \/ List.In e es. + by left.
    move=> [] h'; subst. by move: (hin e heq (Error vmr) s hse h)=> /=.
move=> t e hie e1 hie1 e2 hie2 r s /= [] hse [] hse1 hse2.
case he2: sem_pexpr=> [ve2 | ver2] /=. 
+ case he1: sem_pexpr=> [ve1 | ver1] /=. 
  + case he: sem_pexpr=> [ve | ver] /=. 
    + case hb: to_bool=> [vb | vbr] /=. 
      + case ht: truncate_val=> [vt | vtr] /=. 
        + case ht': truncate_val=> [vt' | vtr'] /=. 
          + move=> <- /=. by left.
          have -> := truncate_val_ty_error s e1 ve1 vtr' t he1 hse1 ht'. move=> <-. by right.
        case ht'': truncate_val=> [vt'' | vtr''] /= hr; subst.
        + have -> := truncate_val_ty_error s e2 ve2 vtr t he2 hse2 ht. by right.
        have -> := truncate_val_ty_error s e1 ve1 vtr'' t he1 hse1 ht''. by right.
      move=> h; subst. have -> := to_bool_ty_error s e ve vbr he hse hb. by right.
    move=> h; subst. by move: (hie (Error ver) s hse he).  
  case he: sem_pexpr=> [ve | ver] //=.
  + case hb: to_bool=> [vb | vbr] //=.
    + move=> h; subst. by move: (hie1 (Error ver1) s hse1 he1). 
    move=> h; subst. have -> := to_bool_ty_error s e ve vbr he hse hb. by right.
  move=> h; subst. by move: (hie (Error ver) s hse he).
case he1: sem_pexpr=> [ve1 | ver1] //=.
+ case he: sem_pexpr=> [ve | ver] //=.
  + case hb: to_bool=> [vb | vbr] //=.
    + case ht: truncate_val=> [vt | vtr] //=.
      + move=> h; subst. by move: (hie2 (Error ver2) s hse2 he2).
      move=> h; subst. have -> := truncate_val_ty_error s e1 ve1 vtr t he1 hse1 ht. by right.
    move=> h; subst. have -> := to_bool_ty_error s e ve vbr he hse hb. by right.
  move=> h; subst. by move: (hie (Error ver) s hse he).
case he: sem_pexpr=> [ve | ver] //=.
+ case hb: to_bool=> [vb | vbr] //=.
  + move=> h; subst. by move: (hie1 (Error ver1) s hse1 he1).
  have -> := to_bool_ty_error s e ve vbr he hse hb. move=> <-. by right.
move=> h; subst. by move: (hie (Error ver) s hse he).
Qed.*)
          
          
End Safety_conditions.

