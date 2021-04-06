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
From mathcomp Require Import all_ssreflect all_algebra.
From CoqWord Require Import ssrZ.
Require Import Psatz xseq.
Require Export array expr gen_map low_memory warray_ sem_type.
Import Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Delimit Scope leakage_scope with leakage.
Open Scope leakage_scope.

Inductive leak_e :=
| LEmpty : leak_e (* no leak *)
| LIdx : Z -> leak_e (* array access at given index *)
| LAdr : pointer -> leak_e (* memory access at given address *)
| LSub: (seq leak_e) -> leak_e. (* forest of leaks *)

Notation leak_es := (seq leak_e).

Inductive leak_i : Type :=
  | Lopn  : leak_e -> leak_i   (* leak_es -> leak_es -> leak_i *)
  | Lcond  : leak_e -> bool -> seq leak_i -> leak_i                          
  | Lwhile_true : seq leak_i -> leak_e -> seq leak_i -> leak_i -> leak_i     
  | Lwhile_false : seq leak_i -> leak_e -> leak_i
  | Lfor : leak_e -> seq (seq leak_i) -> leak_i                              
  | Lcall : leak_e -> (funname * seq leak_i) -> leak_e -> leak_i.            

Notation leak_c := (seq leak_i).

Notation leak_for := (seq leak_c) (only parsing).

Notation leak_fun := (funname * leak_c)%type.

Section Eq_leak_e.

Variable eq_leak_e : leak_e -> leak_e -> bool.

Fixpoint eq_leak_es (les: seq leak_e) (les': seq leak_e) : bool :=
match les, les' with 
| [::], [::] => true
| x::xs, y::ys=> eq_leak_e x y && eq_leak_es xs ys
| _,_=> false
end.

End Eq_leak_e.

Fixpoint eq_leak_e (le: leak_e) (le' : leak_e) : bool :=
match le, le' with 
 | LEmpty, LEmpty=> true
 | LIdx z, LIdx z'=> z==z'
 | LAdr p, LAdr p'=> p==p'
 | LSub le, LSub le'=> eq_leak_es eq_leak_e le le'
 | _, _=> false
end.

Definition Lopn_ les les' := Lopn (LSub [::LSub les; LSub les']).

Definition destr_Lopn (l: leak_e) := 
  match l with
  | LSub [::LSub l1; LSub l2] => (l1, l2)
  | _ => ([::], [::])
  end.

(*
match l with 
| Lopn_ le => 
  let (les1, les2) := destr_Lopn le in
  ... les1 les2 but not le 
*)

(* ------------------------------------------------------------------------ *)

Definition leak_lea_exp : leak_e :=
  LSub [:: LEmpty; LSub [:: LEmpty; LSub [:: LEmpty; LEmpty]]].
  
Definition get_seq_leak_e (l : leak_e) : seq leak_e := 
  match l with 
  | LSub le => le
  | _ => [::]
  end.

(* FIXME : use this definition: nth LEmpty l n *)
Fixpoint get_nth_leak (l : seq leak_e) n : leak_e := 
  match l with 
  | [::] => LEmpty
  | x :: l => if n == 0 then x else get_nth_leak l (n-1)
  end.

Definition get_leak_e (l : leak_e) : leak_e := 
  match l with 
  | LSub le => if (size le) == 1 then (get_nth_leak le 0) else LEmpty
  | _ => LEmpty
  end.

Fixpoint make_leak_e_sub (l : leak_e) : leak_e :=
  match l with 
  | LSub le => LSub (map make_leak_e_sub le)
  | _ => LSub [:: l]
  end.

(* ------------------------------------------------------------------------ *)
(* Leakage trees and leakage transformations. *)

Inductive leak_tr_p :=
  | LS_const of pointer 
  | LS_stk
  | LS_Add `(leak_tr_p) `(leak_tr_p) 
  | LS_Mul `(leak_tr_p) `(leak_tr_p).

Fixpoint eq_leak_tr_p (ltp : leak_tr_p) (ltp' : leak_tr_p) : bool :=
  match ltp, ltp' with 
  | LS_const p, LS_const p' => if p == p' then true else false
  | LS_stk, LS_stk => true
  | LS_Add l l', LS_Add l1 l1' => andb (eq_leak_tr_p l l1) (eq_leak_tr_p l' l1')
  | LS_Mul l l', LS_Mul l1 l1' => andb (eq_leak_tr_p l l1) (eq_leak_tr_p l' l1')
  | _, _ => false
  end.

(* Leakage transformer for expressions *)
Inductive leak_e_tr :=
  | LT_id (* preserve *)
  | LT_remove (* remove *)
  | LT_const : leak_tr_p -> leak_e_tr
  | LT_subi : nat -> leak_e_tr (* projection *)
  | LT_lidx : (Z -> leak_tr_p) -> leak_e_tr
  | LT_map : seq leak_e_tr -> leak_e_tr (* parallel transformations *)
  | LT_seq : seq leak_e_tr -> leak_e_tr
  | LT_compose: leak_e_tr -> leak_e_tr -> leak_e_tr (* compositon of transformations *)
  (* lowering *)
  | LT_rev : leak_e_tr. (* reverse transformation *)

Inductive leak_e_es_tr :=
  | LT_leseq : leak_e_es_tr
  | LT_emseq : leak_e_es_tr
  | LT_subseq : leak_e_tr -> leak_e_es_tr
  | LT_idseq : leak_e_tr -> leak_e_es_tr
  | LT_dfst : leak_e_es_tr
  | LT_dsnd : leak_e_es_tr.

Definition get_seq_leak_e_tr (l : leak_e_tr) : seq leak_e_tr := 
  match l with 
  | LT_seq le => le
  | _ => [::]
  end.

Fixpoint eval_leak_tr_p stk lp : pointer :=
  match lp with
  | LS_const p => p 
  | LS_stk     => stk
  | LS_Add p1 p2 => (eval_leak_tr_p stk p1 + eval_leak_tr_p stk p2)%R
  | LS_Mul p1 p2 => (eval_leak_tr_p stk p1 * eval_leak_tr_p stk p2)%R
  end.

Fixpoint leak_E (stk:pointer) (lt : leak_e_tr) (l : leak_e) : leak_e :=
  match lt, l with
  | LT_map lts, LSub xs => LSub (map2 (leak_E stk) lts xs)
  | LT_seq lts, _ => LSub (map (fun lt => leak_E stk lt l) lts)
  | LT_lidx f, LIdx i => LAdr (eval_leak_tr_p stk (f i))
  | LT_const f, _     => LAdr (eval_leak_tr_p stk f)
  | LT_id, _ => l
  | LT_remove, _ => LEmpty
  | LT_subi i, LSub xs => nth LEmpty xs i
  | LT_compose lt1 lt2, _ => leak_E stk lt2 (leak_E stk lt1 l)
  | LT_rev, LSub xs => LSub (rev xs)
  | _, _ => LEmpty
  end.

Definition leak_E_S (stk: pointer) (lts: seq leak_e_tr) (ls : seq leak_e) : seq leak_e :=
  map2 (leak_E stk) lts ls.

(* Transformation from leakage to sequence of leakage *)
Definition leak_ES (stk : pointer) (lte : leak_e_es_tr) (le : leak_e) : seq leak_e :=
  match lte with
  | LT_leseq      => [:: le]
  | LT_emseq      => [::]
  | LT_subseq lte => [:: leak_E stk lte le]
  | LT_idseq lte  => get_seq_leak_e (leak_E stk lte le)
  | LT_dfst       => [:: LEmpty; LEmpty; LEmpty; LEmpty; LEmpty; le; LEmpty]
  | LT_dsnd       => [:: LEmpty; LEmpty; LEmpty; LEmpty; LEmpty; LEmpty; le]
  end.  

Inductive leak_e_i_tr :=
  | LT_iconditionl : leak_e_tr -> leak_e_i_tr (* lower condition transformer *)
  | LT_iemptyl : leak_e_i_tr.

Inductive leak_es_i_tr :=
  | LT_iopn5f_large : leak_es_i_tr
  | LT_iopn5f_other : leak_es_i_tr
  | LT_iaddcarryf : leak_es_i_tr -> leak_es_i_tr
  | LT_iaddcarry : leak_es_i_tr -> leak_es_i_tr
  | LT_ianone : leak_es_i_tr
  | LT_imul1 : leak_es_i_tr
  | LT_imul2 : leak_es_i_tr
  | LT_imul3 : leak_es_i_tr
  | LT_imul4 : leak_es_i_tr
  | LT_iemptysl : leak_es_i_tr.

Inductive leak_i_tr_single := 
 | LT_ilmov2_ 
 | LT_ilmov3_
 | LT_ilmov4_
 | LT_ild_
 | LT_ildc_
 | LT_ilea_
 | LT_ilsc_
 | LT_ilds_
 | LT_ildus_
 | LT_ilasgn_
 | LT_ilinc_ of leak_e_es_tr
 | LT_ilcopn_ of leak_e_es_tr
 | LT_ileq_ of leak_e_es_tr
 | LT_illt_ of leak_e_es_tr.


Inductive leak_i_tr_double :=
 | LT_ilmov1_
 | LT_ildcn_.

Inductive leak_i_tr :=
(* structural transformation *)
| LT_ikeep : leak_i_tr             (* same as source *)
| LT_ile : leak_e_tr -> leak_i_tr  (* assign and op *)             
| LT_icond  : leak_e_tr -> seq leak_i_tr -> seq leak_i_tr -> leak_i_tr (* if *)       
| LT_iwhile : seq leak_i_tr -> leak_e_tr -> seq leak_i_tr -> leak_i_tr (* while *)      
| LT_ifor : leak_e_tr -> seq leak_i_tr -> leak_i_tr                  
| LT_icall : funname -> leak_e_tr -> leak_e_tr -> leak_i_tr      

(* modify the control flow *)
| LT_iremove : leak_i_tr                                         
| LT_icond_eval : bool -> seq leak_i_tr -> leak_i_tr    
| LT_ifor_unroll: nat -> seq leak_i_tr -> leak_i_tr
| LT_icall_inline: nat -> funname -> nat -> nat -> leak_i_tr

(* lowering leak transformers *)
| LT_icondl : leak_e_i_tr -> leak_e_tr -> seq leak_i_tr -> seq leak_i_tr -> leak_i_tr
| LT_iwhilel :  leak_e_i_tr -> leak_e_tr -> seq leak_i_tr -> seq leak_i_tr -> leak_i_tr
| LT_icopn : leak_es_i_tr -> leak_i_tr
(* lowering assgn *)
| LT_isingle : leak_i_tr_single -> leak_i_tr 
| LT_idouble : leak_i_tr_double -> leak_i_tr
(*| LT_ilmov1 : leak_i_tr
| LT_ildcn : leak_i_tr*)
| LT_ilmul : leak_es_i_tr -> leak_e_tr -> leak_i_tr
| LT_ilif : leak_e_i_tr -> leak_e_tr -> leak_i_tr
| LT_ilfopn : leak_es_i_tr -> leak_e_es_tr -> leak_i_tr
| LT_ildiv : leak_i_tr -> leak_e_es_tr -> leak_i_tr.

Notation LT_ilmov2 := (LT_isingle LT_ilmov2_).
Notation LT_ilmov3 := (LT_isingle LT_ilmov3_).
Notation LT_ilmov4 := (LT_isingle LT_ilmov4_).
Notation LT_ild := (LT_isingle LT_ild_).
Notation LT_ildc := (LT_isingle LT_ildc_).
Notation LT_ilea := (LT_isingle LT_ilea_).
Notation LT_ilsc := (LT_isingle LT_ilsc_).
Notation LT_ilds := (LT_isingle LT_ilds_).
Notation LT_ildus := (LT_isingle LT_ildus_).
Notation LT_ilasgn := (LT_isingle LT_ilasgn_).
Notation LT_ilinc ltes := (LT_isingle (LT_ilinc_ ltes)).
Notation LT_ilcopn ltes := (LT_isingle (LT_ilcopn_ ltes)).
Notation LT_ileq ltes := (LT_isingle (LT_ileq_ ltes)).
Notation LT_illt ltes := (LT_isingle (LT_illt_ ltes)).

Notation LT_ilmov1 := (LT_idouble LT_ilmov1_).
Notation LT_ildcn := (LT_idouble LT_ildcn_).


Definition is_LT_ilds li := if li is LT_ilds then true else false.

(* Transformation from expression leakage to instruction leakage *)
Definition leak_EI (stk : pointer) (lti : leak_e_i_tr) (le : leak_e) : seq leak_i :=
  match lti with 
  | LT_iconditionl lte => 
    [:: Lopn (LSub [:: leak_E stk lte le; LSub [:: LEmpty; LEmpty; LEmpty; LEmpty; LEmpty]])]
  | LT_iemptyl => 
    [::]
  end.

Definition no_i_leak_EI (lt : leak_e_i_tr) : nat :=
match lt with 
 | LT_iconditionl lte => 1
 | LT_iemptyl => 0
end.

Fixpoint remove_last_leak (ls: seq leak_e) : seq leak_e := 
  match ls with
  | [::] => [::]
  | [:: a] => [::]
  | a :: l => a :: remove_last_leak l
  end.

Fixpoint last_leak (ls : seq leak_e) : leak_e :=
  match ls with 
  | [::] => LEmpty
  | [:: a] => a
  | a :: l => last_leak l
  end.

(* Transformation from expressions (seq of expression) leakage to instruction leakage *)
Fixpoint leak_ESI (stk : pointer) (lti : leak_es_i_tr) (les: seq leak_e) (les': seq leak_e) : seq leak_i :=
  match lti with 
  | LT_iopn5f_large => 
    [:: Lopn (LSub [:: LSub [:: nth LEmpty les 1]; LSub [:: LEmpty]])] ++
    [:: Lopn (LSub [:: LSub [::nth LEmpty les 0, LEmpty & drop 2 les]; LSub les'])]

  | LT_iopn5f_other =>
    [:: Lopn (LSub [:: LSub les ; LSub les'])]

  | LT_iaddcarryf ltes => 
    leak_ESI stk ltes (remove_last_leak les) 
      [:: LEmpty; get_nth_leak les' 0; LEmpty; LEmpty; LEmpty; get_nth_leak les' 1]

  | LT_iaddcarry ltes =>  
    leak_ESI stk ltes les 
      [:: LEmpty; get_nth_leak les' 0; LEmpty; LEmpty; LEmpty; get_nth_leak les' 1]

  | LT_ianone => 
    [:: Lopn (LSub [:: LSub les ; LSub les'])]

  | LT_imul1 => 
    [:: Lopn (LSub [:: LSub [:: nth LEmpty les 0]; LSub [:: LEmpty]])] ++
    [:: Lopn (LSub [:: LSub [:: nth LEmpty les 1; LEmpty]; 
                       LSub [:: LEmpty; LEmpty; LEmpty; LEmpty; LEmpty; nth LEmpty les' 0; nth LEmpty les' 1]])]
  | LT_imul2 => 
    [:: Lopn (LSub [:: LSub [:: nth LEmpty les 1]; LSub [:: LEmpty]])] ++
    [:: Lopn (LSub [:: LSub [:: nth LEmpty les 0; LEmpty]; 
              LSub [:: LEmpty; LEmpty; LEmpty; LEmpty; LEmpty; nth LEmpty les' 0; nth LEmpty les' 1]])]

  | LT_imul3 => 
    [:: Lopn (LSub [:: LSub les; 
                LSub [:: LEmpty; LEmpty; LEmpty; LEmpty; LEmpty; nth LEmpty les' 0; nth LEmpty les' 1]])]

  | LT_imul4 => 
    [:: Lopn (LSub [:: LSub les ; LSub les'])]

  | LT_iemptysl => [::]
  end.

(* computes the number of instructions added in lowering high-level constructs *)
Fixpoint no_i_esi_tr (lt: leak_es_i_tr) : nat :=
  match lt with 
  | LT_iopn5f_large => 2
  | LT_iopn5f_other => 1
  | LT_iaddcarryf ltes => no_i_esi_tr ltes 
  | LT_iaddcarry ltes => no_i_esi_tr ltes
  | LT_ianone => 1
  | LT_imul1 => 2
  | LT_imul2 => 2
  | LT_imul3 => 1
  | LT_imul4 => 1
  | LT_iemptysl => 0
 end.

Section Leak_I.

  Variable leak_I : pointer -> leak_i -> leak_i_tr -> seq leak_i.

  Definition leak_Is (stk : pointer) (lts : seq leak_i_tr) (ls : seq leak_i) : seq leak_i :=
    flatten (map2 (leak_I stk) ls lts).

  Definition leak_Iss (stk: pointer) (ltss : seq leak_i_tr) (ls : seq (seq leak_i)) : seq (seq leak_i) :=
    (map (leak_Is stk ltss) ls). 

End Leak_I.

Section Leak_Call.

Variable leak_Fun : funname -> seq leak_i_tr.

Definition dummy_lit := Lopn LEmpty.

Definition leak_assgn := 
  Lopn (LSub [:: LEmpty ; LEmpty]).

Definition get_empty_leak_seq (l : seq leak_e_tr) :=
  (map (fun x => LEmpty) l).

Fixpoint leak_I (stk:pointer) (l : leak_i) (lt : leak_i_tr) {struct l} : seq leak_i :=
  match lt, l with
  | LT_ikeep, _ => 
    [::l]

  | LT_ile lte, Lopn le => 
    [:: Lopn (leak_E stk lte le) ]

  | LT_icond lte ltt ltf, Lcond le b lti => 
    [:: Lcond (leak_E stk lte le) b (leak_Is leak_I stk (if b then ltt else ltf) lti) ]

  | LT_iwhile ltis lte ltis', Lwhile_true lts le lts' lw => 
    [:: Lwhile_true (leak_Is leak_I stk ltis lts)
                     (leak_E stk lte le)
                     (leak_Is leak_I stk ltis' lts')
                     (head dummy_lit (leak_I stk lw lt))]

  | LT_iwhile ltis lte ltis', Lwhile_false lts le => 
    [::Lwhile_false (leak_Is leak_I stk ltis lts)
                     (leak_E stk lte le)]

  | LT_ifor lte ltiss, Lfor le ltss => 
    [:: Lfor (leak_E stk lte le)
             (leak_Iss leak_I stk ltiss ltss) ]

  | LT_icall _f lte lte', Lcall le (f, lts) le' => 
    (* _f should be equal to f *)
    [:: Lcall (leak_E stk lte le)
              (f, (leak_Is leak_I stk (leak_Fun f) lts))
              (leak_E stk lte' le') ]


  (** Modification of the control flow *)
  | LT_iremove, _ => 
    [::]

  | LT_icond_eval _b lts, Lcond _ b lti => 
    (* _b should be equal b *)
    leak_Is leak_I stk lts lti

  | LT_icond_eval _b lts, Lwhile_false lti le => 
    leak_Is leak_I stk lts lti

  | LT_ifor_unroll _n ltiss, Lfor le ltss => 
    (* _n should be equal to size ltss *)
    flatten (map (fun l => leak_assgn :: l) (leak_Iss leak_I stk ltiss ltss))

  | LT_icall_inline nargs _fn ninit nres, Lcall le (f, lts) le' => 
    (* nargs = size le, _fn = fn, nres = size le') *)
    map (fun x => (Lopn (LSub [:: x; LEmpty]))) (get_seq_leak_e le) ++ 
    nseq ninit (Lopn (LSub [:: LEmpty; LEmpty])) ++ 
    leak_Is leak_I stk (leak_Fun f) lts ++
    map (fun y => (Lopn (LSub [:: LEmpty; y]))) (get_seq_leak_e le')

  (* lowering *)
    (* lti'-> b = [e] (* makes boolean expression as b = [e] *) (* trasforms expression leakage to instruction Copn leakage *)
       lte -> leak_e_tr 
       ltt -> leak_i_tr for true branch 
       ltf -> leak_i_tr for false branch *)
  | LT_icondl lti' lte ltt ltf, Lcond le b lti => 
     (leak_EI stk lti' le) ++ 
     [:: Lcond (leak_E stk lte le) b (leak_Is leak_I stk (if b then ltt else ltf) lti) ]

    (* lti ->  b = [e] (* makes boolean expression as b = [e] *) (* trasforms expression leakage to instruction Copn leakage *)
       lte -> leak_e_tr 
       ltt -> leak_i_tr for true branch 
       ltf -> leak_i_tr for false branch *)
  | LT_iwhilel lti lte ltis ltis', Lwhile_true lts le lts' lw => 
    [:: Lwhile_true ((leak_Is leak_I stk ltis lts) ++ (leak_EI stk lti le))
                     (leak_E stk lte le)
                     (leak_Is leak_I stk ltis' lts')
                     (head dummy_lit (leak_I stk lw lt))]

  | LT_iwhilel lti lte ltis ltis', Lwhile_false lts le => 
    [::Lwhile_false ((leak_Is leak_I stk ltis lts) ++ (leak_EI stk lti le)) (leak_E stk lte le)]


  | LT_icopn ltes, Lopn le => 
    leak_ESI stk ltes (get_seq_leak_e (leak_E stk (LT_subi 0) le)) 
                                      (get_seq_leak_e (leak_E stk (LT_subi 1) le))

  
  | LT_idouble lti, Lopn le => 
    match lti with 
     | LT_ilmov1_ => [:: Lopn (LSub [:: LSub [:: leak_E stk (LT_subi 0) le]; LSub [:: LEmpty]]) ; 
                         Lopn (LSub [:: LSub [:: LEmpty]; LSub [:: leak_E stk (LT_subi 1) le]])]
     | LT_ildcn_ => [:: Lopn (LSub [:: LSub [:: LEmpty]; LSub [:: LEmpty]]);
                        Lopn (LSub [:: LSub [:: LEmpty; LEmpty]; 
                               LSub [:: LEmpty; LEmpty; LEmpty; LEmpty; LEmpty; leak_E stk (LT_subi 1) le]])]
    end

  | LT_isingle lti, Lopn le => 
    let le' := 
      match lti with 
      | LT_ilmov2_ => 
        LSub [:: LSub [::];
                LSub[:: LEmpty; LEmpty; LEmpty; LEmpty; LEmpty; leak_E stk (LT_subi 1) le]]

      | LT_ilmov3_ => 
        LSub [:: LSub [::]; LSub [:: leak_E stk (LT_subi 1) le]]
             
      | LT_ilmov4_ => 
        LSub [:: LSub [:: leak_E stk (LT_subi 0) le]; LSub [:: leak_E stk (LT_subi 1) le]]

      | LT_ild_ => 
        LSub [:: LSub[:: LEmpty]; 
                       LSub [:: LEmpty; LEmpty; LEmpty; LEmpty; leak_E stk (LT_subi 1) le]]
      | LT_ildc_ => 
        LSub [:: LSub[:: LEmpty; LEmpty]; 
                       LSub [:: LEmpty; LEmpty; LEmpty; LEmpty; LEmpty; leak_E stk (LT_subi 1) le]]
      | LT_ilea_ =>
        LSub [:: LSub [:: leak_lea_exp]; LSub [:: leak_E stk (LT_subi 1) le]]
      
      | LT_ilsc_ => 
        LSub [:: leak_E stk (LT_subi 1) (leak_E stk (LT_subi 1) leak_lea_exp); 
                       LSub [:: LEmpty; LEmpty; LEmpty; LEmpty; LEmpty; leak_E stk (LT_subi 1) le]]
      | LT_ilds_ =>
        LSub [:: LSub [:: nth LEmpty (get_seq_leak_e (leak_E stk (LT_subi 0) le)) 0]; 
                       LSub [:: LEmpty]]
      | LT_ildus_ =>
        LSub [:: LSub [:: LEmpty]; LSub[:: LEmpty]]
      
      | LT_ilasgn_ => 
        LSub [:: leak_E stk (LT_subi 0) le;
                       leak_E stk (LT_subi 1) le]
      
      | LT_ilinc_ ltes => 
        (LSub [:: LSub (leak_ES stk ltes (leak_E stk (LT_subi 0) le)); 
                       LSub [:: LEmpty; LEmpty; LEmpty; LEmpty; leak_E stk (LT_subi 1) le]])

      | LT_ilcopn_ ltes => 
        (LSub [:: LSub (leak_ES stk ltes (leak_E stk (LT_subi 0) le));
                       LSub [:: leak_E stk (LT_subi 1) le]])

      | LT_ileq_ ltes => 
        (LSub [:: LSub (leak_ES stk ltes (leak_E stk (LT_subi 0) le));
                       LSub [:: LEmpty; LEmpty; LEmpty; LEmpty; leak_E stk (LT_subi 1) le]])

      | LT_illt_ ltes => 
        (LSub [:: LSub (leak_ES stk ltes (leak_E stk (LT_subi 0) le));
                       LSub [:: LEmpty; leak_E stk (LT_subi 1) le; LEmpty; LEmpty; LEmpty]])
     end in
    [:: Lopn le']

    (* lti converts cond expression to Copn leakage *)
  | LT_ilif lti le', Lopn le => 
    leak_EI stk lti (get_nth_leak (get_seq_leak_e (leak_E stk (LT_subi 0) le)) 0) ++ 
    [:: Lopn (LSub [:: LSub [:: leak_E stk le' (leak_E stk (LT_subi 0) (leak_E stk (LT_subi 0) le));
                                (leak_E stk (LT_subi 1) (leak_E stk (LT_subi 0) le));
                                (leak_E stk (LT_subi 2) (leak_E stk (LT_subi 0) le))]; 
                       LSub [:: leak_E stk (LT_subi 1) le]])]

  | LT_ilmul lest ltes, Lopn le =>  
    leak_ESI stk lest (get_seq_leak_e (leak_E stk ltes (LSub [:: LEmpty; LEmpty])))
              [:: LEmpty; LEmpty; LEmpty; LEmpty; LEmpty; leak_E stk (LT_subi 1) le]

  | LT_ilfopn lest lte, Lopn le => 
    leak_ESI stk lest (leak_ES stk lte (leak_E stk (LT_subi 0) le)) 
              [:: LEmpty; LEmpty; LEmpty; LEmpty; LEmpty; leak_E stk (LT_subi 1) le]

  | LT_ildiv lti ltes, Lopn le =>  
    if is_LT_ilds lti then 
      [:: Lopn (LSub [:: LSub [:: nth LEmpty (get_seq_leak_e (leak_E stk (LT_subi 0) le)) 0]; 
                        LSub[:: LEmpty]])] ++ 
      [:: Lopn (LSub [:: LSub [:: LEmpty; nth LEmpty (get_seq_leak_e (leak_E stk (LT_subi 0) le)) 0; 
                                 nth LEmpty (get_seq_leak_e (leak_E stk (LT_subi 0) le)) 1]; 
                        LSub (leak_ES stk ltes (leak_E stk (LT_subi 1) le))])]
    else [:: Lopn (LSub [:: LSub [:: LEmpty]; LSub[:: LEmpty]])]  ++ 
         [:: Lopn (LSub [:: LSub [:: LEmpty; nth LEmpty (get_seq_leak_e (leak_E stk (LT_subi 0) le)) 0; 
                                    nth LEmpty (get_seq_leak_e (leak_E stk (LT_subi 0) le)) 1]; 
                           LSub (leak_ES stk ltes (leak_E stk (LT_subi 1) le))])]
                                
  | _, _ => [:: l]
  end.

Inductive leak_WF : leak_i_tr -> leak_i -> Prop :=
 | LT_ikeepWF : forall le, leak_WF LT_ikeep (Lopn le)
 | LT_ileWF : forall le lte, leak_WF (LT_ile lte) (Lopn le) 
 | LT_icondtWF : forall lte ltt ltf le lti,
                 leak_WFs ltt lti ->
                 leak_WF (LT_icond lte ltt ltf) (Lcond le true lti)
 | LT_icondfWF : forall lte ltt ltf le lti,
                 leak_WFs ltf lti ->
                 leak_WF (LT_icond lte ltt ltf) (Lcond le false lti)
 | LT_iwhiletWF : forall ltis lte ltis' lts le lts' lw,
                  leak_WFs ltis lts ->
                  leak_WFs ltis' lts' ->
                  leak_WF (LT_iwhile ltis lte ltis') lw ->
                  leak_WF (LT_iwhile ltis lte ltis') (Lwhile_true lts le lts' lw)
 | LT_iwhilefWF : forall ltis lte ltis' lts le,
                  leak_WFs ltis lts ->
                  leak_WF (LT_iwhile ltis lte ltis') (Lwhile_false lts le)
 | LT_iforWF: forall lte ltiss le ltss,
              leak_WFss ltiss ltss ->
              leak_WF (LT_ifor lte ltiss) (Lfor le ltss)
 | LT_icallWF : forall f lte lte' le lts le',
                leak_WFs (leak_Fun f) lts ->
                leak_WF (LT_icall f lte lte') (Lcall le (f, lts) le')
 | LT_iremoveWF : forall l,
                  leak_WF LT_iremove l
 | LT_icond_evalWF : forall b lts le lti,
                     leak_WFs lts lti ->
                     leak_WF (LT_icond_eval b lts) (Lcond le b lti)
 | LT_icond_evalWF' : forall lts lti le,
                      leak_WFs lts lti ->
                      leak_WF (LT_icond_eval false lts) (Lwhile_false lti le)
 | LT_ifor_unrollWF : forall ltiss le ltss,
                      leak_WFss ltiss ltss ->
                      leak_WF (LT_ifor_unroll (size ltss) ltiss) (Lfor le ltss)
 | LT_icall_inlineWF : forall ninit les f lts les',
                       leak_WFs (leak_Fun f) lts ->
                       leak_WF (LT_icall_inline (size les) f ninit (size les')) (Lcall (LSub les) (f, lts) (LSub les'))
 (* Lowering *)
 | LT_icondltWF : forall lti' lte ltt ltf le lti,
                  leak_WFs ltt lti ->
                  leak_WF (LT_icondl lti' lte ltt ltf) (Lcond le true lti)
 | LT_icondlfWF : forall lti' lte ltt ltf le lti,
                  leak_WFs ltf lti ->
                  leak_WF (LT_icondl lti' lte ltt ltf) (Lcond le false lti)
 | LT_iwhilelWF : forall lti lte ltis ltis' lts le lts' lw,
                  leak_WFs ltis lts ->
                  leak_WFs ltis' lts' ->
                  leak_WF (LT_iwhilel lti lte ltis ltis') lw ->
                  leak_WF (LT_iwhilel lti lte ltis ltis') (Lwhile_true lts le lts' lw)  
 | LT_iwhilelWF' : forall lti lte ltis ltis' lts le,
                   leak_WFs ltis lts ->
                   leak_WF (LT_iwhilel lti lte ltis ltis') (Lwhile_false lts le)
 | LT_icopnWF : forall ltes le,
                leak_WF (LT_icopn ltes) (Lopn le)
 | LT_isingleWF : forall lti le, 
                  leak_WF (LT_isingle lti) (Lopn le)
 | LT_idoubleWF : forall lti le,
                  leak_WF (LT_idouble lti) (Lopn le)
 | LT_ilifWF : forall lti le' le,
               leak_WF (LT_ilif lti le') (Lopn le)
 | LT_imulWF : forall lest ltes le,
               leak_WF (LT_ilmul lest ltes) (Lopn le)
 | LT_ilfopnWF : forall lest lte le,
                 leak_WF (LT_ilfopn lest lte) (Lopn le)
 | LT_ildivWF : forall lti ltes le,
                leak_WF (LT_ildiv lti ltes) (Lopn le)

with leak_WFs : seq leak_i_tr -> leak_c -> Prop :=
 | WF_empty : leak_WFs [::] [::]
 | WF_seq : forall li lc lt1 lt1',
            leak_WF lt1 li ->
            leak_WFs lt1' lc ->
            leak_WFs (lt1 :: lt1') (li::lc)

with leak_WFss : seq leak_i_tr -> seq leak_c -> Prop :=
 | WF_empty' : forall lt, leak_WFss lt [::]
 | WF_seq' : forall lc lcs lt,
            leak_WFs lt lc ->
            leak_WFss lt lcs ->
            leak_WFss lt (lc :: lcs).

End Leak_Call.

Notation leak_c_tr := (seq leak_i_tr).

Definition leak_f_tr := seq (funname * leak_c_tr).

Section Leak_Call_Imp.

Variable Fs: leak_f_tr.

Definition leak_Fun (f: funname) : leak_c_tr := odflt [::] (assoc Fs f).

End Leak_Call_Imp.

Fixpoint leak_compile (stk : pointer) (lts: seq leak_f_tr) (lf: leak_fun) := 
  match lts with 
  | [::] => lf.2
  | x :: xs => 
    let r := leak_Is (leak_I (leak_Fun x)) stk (leak_Fun x lf.1) lf.2 in 
    leak_compile stk xs (lf.1, r)
  end.

Fixpoint leak_compiles (stk: pointer) (ltss: seq (seq leak_f_tr)) (lf: leak_fun) :=
  match ltss with 
  | [::] => lf.2
  | x :: xs => 
    let r := leak_compile stk x lf in 
    leak_compiles stk xs (lf.1, r)
  end.

(** Leakage for intermediate-level **)

Inductive leak_il : Type :=
  | Lempty0 : leak_il
  | Lempty : leak_il
  | Lopnl : leak_e -> leak_il
  | Lcondl : leak_e -> bool -> leak_il.

Fixpoint eq_leak_il (li: leak_il) (li': leak_il) : bool :=
match li, li' with 
 | Lempty0, Lempty0 => true 
 | Lempty, Lempty => true
 | Lopnl le, Lopnl le' => if (eq_leak_e le le') then true else false
 | Lcondl le b, Lcondl le' b' => if (eq_leak_e le le') && (b == b') then true else false
 | _, _ => false
end.

Notation leak_funl := (funname * seq leak_il).

Definition leak_cl := seq leak_il.

Inductive leak_i_il_tr : Type :=
  (*| LT_ilremove : leak_i_il_tr*)
  | LT_ilkeep : leak_i_il_tr
  | LT_ilkeepa : leak_i_il_tr
  | LT_ilcond_0 : leak_e_tr -> seq leak_i_il_tr -> leak_i_il_tr (*c1 is empty*)
  | LT_ilcond_0' : leak_e_tr -> seq leak_i_il_tr -> leak_i_il_tr (*c2 is empty*)
  | LT_ilcond : leak_e_tr -> seq leak_i_il_tr -> seq leak_i_il_tr -> leak_i_il_tr (* c1 and c2 are not empty *)
  | LT_ilwhile_c'0 : align -> seq leak_i_il_tr -> leak_i_il_tr
  | LT_ilwhile_f : seq leak_i_il_tr -> leak_i_il_tr
  | LT_ilwhile : seq leak_i_il_tr -> seq leak_i_il_tr -> leak_i_il_tr.

Section Leak_IL.

  Variable leak_i_iL : pointer -> leak_i ->  leak_i_il_tr -> seq leak_il.

  Definition leak_i_iLs (stk : pointer) (lts : seq leak_i_il_tr) (ls : seq leak_i) : seq leak_il :=
    flatten (map2 (leak_i_iL stk) ls lts).

  Fixpoint ilwhile_c'0 (stk: pointer) (lti : seq leak_i_il_tr) (li : leak_i) : seq leak_il :=
    match li with 
    | Lwhile_false lis le => 
      leak_i_iLs stk lti lis ++ [:: Lcondl le false]
    | Lwhile_true lis le lis' li' => 
      leak_i_iLs stk lti lis ++ [:: Lcondl le true] ++ ilwhile_c'0 stk lti li'
    | _ => [::]
    end.

  Fixpoint ilwhile (stk : pointer) (lts : seq leak_i_il_tr) (lts' : seq leak_i_il_tr) (li : leak_i) 
             : seq leak_il :=
    match li with 
    | Lwhile_false lis le => 
      leak_i_iLs stk lts lis ++ [:: Lcondl le false]
    | Lwhile_true lis le lis' li' =>
      leak_i_iLs stk lts lis ++ [:: Lcondl le true] ++ 
      leak_i_iLs stk lts' lis' ++ [:: Lempty0] ++ ilwhile stk lts lts' li'
    | _ => [::]
    end.

End Leak_IL.

(* Computes the leakage depending on alignment *) 
Definition get_align_leak_il a : seq leak_il :=
  match a with 
  | NoAlign => [::]
  | Align => [:: Lempty0]
  end.

Fixpoint leak_i_iL (stk:pointer) (li : leak_i) (l : leak_i_il_tr) {struct li} : seq leak_il :=
  match l, li with 
  (*| LT_ilremove, _ => 
    [:: Lempty]*)

  | LT_ilkeepa, Lopn le => 
    [:: Lopnl (LSub (map (fun x => LSub [:: x]) (get_seq_leak_e le)))]

  | LT_ilkeep, Lopn le => 
    [:: Lopnl le]

  | LT_ilcond_0 lte lti, Lcond le b lis => 
    [:: Lcondl (leak_E stk lte le) b] ++ 
    if b then [::] 
    else leak_i_iLs leak_i_iL stk lti lis ++ [:: Lempty0]

  | LT_ilcond_0' lte lti, Lcond le b lis => 
    [:: Lcondl (leak_E stk lte le) (negb b)] ++ 
    if negb b then [::] 
    else leak_i_iLs leak_i_iL stk lti lis ++ [:: Lempty0]

  | LT_ilcond lte lti lti', Lcond le b lis => 
    [:: Lcondl (leak_E stk lte le) b] ++ 
    if b then leak_i_iLs leak_i_iL stk lti lis ++ [:: Lempty0]
    else leak_i_iLs leak_i_iL stk lti' lis ++ [:: Lempty]

  | LT_ilwhile_c'0 a lti, _ => 
    get_align_leak_il a ++ [:: Lempty0 & ilwhile_c'0 leak_i_iL stk lti li]

  | LT_ilwhile_f lti, Lwhile_false lis le => 
    leak_i_iLs leak_i_iL stk lti lis

  | LT_ilwhile lti lti', _ => 
    [:: Lempty] ++ ilwhile leak_i_iL stk lti lti' li 

  | _, _ => [::]
  end.

Notation leak_c_il_tr := (seq leak_i_il_tr).

Definition leak_f_lf_tr := seq (funname * seq leak_i_il_tr).

Inductive leak_i_WF : leak_i_il_tr -> leak_i -> Prop :=
| LT_ilkeepaWF : forall le, leak_i_WF LT_ilkeepa (Lopn le)
| LT_ilkeepWF : forall le, leak_i_WF LT_ilkeep (Lopn le)
| LT_ilcond_0tWF : forall le lis lte lti,
                  leak_i_WF (LT_ilcond_0 lte lti) (Lcond le true lis)
| LT_ilcond_0fWF : forall le lis lte lti,
                  leak_i_WFs lti lis ->
                  leak_i_WF (LT_ilcond_0 lte lti) (Lcond le false lis)
| LT_icond_0tWF' : forall le lis lte lti,
                  leak_i_WFs lti lis ->
                  leak_i_WF (LT_ilcond_0' lte lti) (Lcond le true lis)
| LT_icond_0fWF' : forall le lis lte lti,
                  leak_i_WF (LT_ilcond_0' lte lti) (Lcond le false lis)
| LT_ilcondtWF : forall lte lti lti' le lis,
                leak_i_WFs lti lis ->
                leak_i_WF (LT_ilcond lte lti lti') (Lcond le true lis)
| LT_ilcondfWF : forall lte lti lti' le lis,
                leak_i_WFs lti' lis ->
                leak_i_WF (LT_ilcond lte lti lti') (Lcond le false lis)
| LT_ilwhile_fWF : forall lis le lti,
                   leak_i_WFs lti lis ->
                   leak_i_WF (LT_ilwhile_f lti) (Lwhile_false lis le)
(* Fix needed *)
| LT_ilwhile_c'0WF : forall li a lti,
                     leak_i_WF (LT_ilwhile_c'0 a lti) li
(* Fix needed *)
| LT_ilwhileWF : forall li lti lti',
                 leak_i_WF (LT_ilwhile lti lti') li

with leak_i_WFs : seq leak_i_il_tr -> leak_c -> Prop :=
 | WF_i_empty : leak_i_WFs [::] [::]
 | WF_i_seq : forall li lc lt1 lt1',
            leak_i_WF lt1 li ->
            leak_i_WFs lt1' lc ->
            leak_i_WFs (lt1 :: lt1') (li::lc).


Section Leak_Call_Imp_L.

Variable Fs: leak_f_lf_tr.

Definition leak_Fun_L (f: funname) : seq leak_i_il_tr := odflt [::] (assoc Fs f).

End Leak_Call_Imp_L.

(** Leakage for assembly-level **)

Inductive leak_asm : Type :=
  | Laempty
  | Lacond of bool (* bool represents the condition in conditional jump *)
  | Laop of seq pointer.

(* Extracts the sequence of pointers from leak_e *)
Fixpoint leak_e_asm (l : leak_e) : seq pointer :=
  match l with 
  | LEmpty => [::]
  | LIdx i => [::]
  | LAdr p => [:: p]
  | LSub l => flatten (map leak_e_asm l)
  end.

(* Transforms leakage for intermediate langauge to leakage for assembly *)
Definition leak_i_asm (l : leak_il) : leak_asm :=
  match l with 
  | Lempty0 => Laempty
  | Lempty => Laempty
  | Lopnl le => Laop (leak_e_asm le)
  | Lcondl le b => Lacond b
  end.

Definition leak_compile_prog
   (stk: pointer)
   (ltss: leak_f_tr * seq (seq leak_f_tr) * seq leak_f_tr * leak_f_lf_tr)
   (lf: leak_fun) : seq leak_il :=
  let r  := leak_compile stk [:: ltss.1.1.1 ] lf in
  let rs := leak_compiles stk ltss.1.1.2 (lf.1, r) in
  leak_i_iLs leak_i_iL stk (leak_Fun_L ltss.2 lf.1) (leak_compile stk ltss.1.2 (lf.1, rs)).

Definition leak_compile_x86
   (stk: pointer)
   (ltss: leak_f_tr * seq (seq leak_f_tr) * seq leak_f_tr * leak_f_lf_tr)
   (lf: leak_fun) : seq leak_asm :=
  let r := leak_compile_prog stk ltss lf in
  map (fun x=> leak_i_asm x) r.