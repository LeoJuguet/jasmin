(* Clear (ovewrite) the stack before returning from export functions. *)

(* The strategies are:
- Loop: Overwrite with a simple one-instruction loop.
- LoopSCT: Overwrite with a simple one-instruction loop, and put an LFENCE before the return.
- Unrolled: Overwrite with a sequence of instructions (no loop).

Implemented in [compiler/clear_stack.v]. *)

From mathcomp Require Import
  all_ssreflect
  all_algebra.
Require Import ZArith.
Require Import utils.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Variant cs_strategy :=
| CSSloop
| CSSloopSCT
| CSSunrolled.

Scheme Equality for cs_strategy.

Lemma cs_strategy_eq_axiom : Equality.axiom cs_strategy_beq.
Proof.
  exact:
    (eq_axiom_of_scheme
       internal_cs_strategy_dec_bl
       internal_cs_strategy_dec_lb).
Qed.

Definition cs_strategy_eqMixin := Equality.Mixin cs_strategy_eq_axiom.
Canonical cs_strategy_eqType :=
  Eval hnf in EqType cs_strategy cs_strategy_eqMixin.
