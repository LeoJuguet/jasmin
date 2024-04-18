From mathcomp Require Import
  all_ssreflect
  all_algebra.
From mathcomp Require Import word_ssrZ.

Require Import
  compiler_util
  expr
  lowering
  pseudo_operator
  shift_kind.
Require Import
  arch_decl
  arch_extra.
Require Import
  riscv_decl
  riscv_instr_decl
  riscv_extra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Section.
Context {atoI : arch_toIdent}.

(* TODO : Review *)
Definition chk_ws_reg (ws : wsize) : option unit :=
  oassert (ws == reg_size)%CMP.

Definition is_load (e: pexpr) : bool :=
  match e with
  | Pconst _ | Pbool _ | Parr_init _
  | Psub _ _ _ _ _
  | Papp1 _ _ | Papp2 _ _ _ | PappN _ _ | Pif _ _ _ _
    => false
  | Pvar {| gs := Sglob |}
  | Pget _ _ _ _ _
  | Pload _ _ _ _
    => true
  | Pvar {| gs := Slocal ; gv := x |}
    => is_var_in_memory x
  end.

Definition lower_Papp1 (ws : wsize) (op : sop1) (e : pexpr) : option(riscv_extended_op * pexprs) :=
  let%opt _ := chk_ws_reg ws in
  match op with
  | Oword_of_int _ =>
    if is_const e is Some _
      then  Some(BaseOp (None, LI), [:: Papp1 (Oword_of_int U32) e])
    else None
  | Osignext U32 ws' =>
      let%opt _ := oassert (is_load e) in
      Some (BaseOp(None, LOAD Signed ws'), [:: e ])
  | Ozeroext U32 ws' =>
      let%opt _ := oassert (is_load e) in
      Some (BaseOp(None, LOAD Unsigned ws'), [:: e ])    
  | Olnot U32 =>
      Some(BaseOp (None, NOT), [:: e])
  | Oneg (Op_w U32) =>
      Some(BaseOp (None, NEG), [:: e])
  | _ =>
      None
  end.

Definition lower_Papp2
  (ws : wsize) (op : sop2) (e0 e1 : pexpr) :
  option (riscv_extended_op * pexprs) :=
  let%opt _ := chk_ws_reg ws in
  match op with
  | Oadd (Op_w _) =>
    let op := if is_wconst U32 e1 then ADDI else ADD in
    Some (BaseOp (None, op), [:: e0; e1])
  | Osub (Op_w _) =>
    let op := if is_wconst U32 e1 then ExtOp SUBI else BaseOp(None, SUB) in
    Some (op, [:: e0; e1])
  | Oland _ =>
    let op := if is_wconst U32 e1 then ANDI else AND in
    Some (BaseOp (None, op), [:: e0; e1])
  | Olor _ =>
    let op := if is_wconst U32 e1 then ORI else OR in
    Some (BaseOp (None, op), [:: e0; e1])
  | Olxor _ =>
    let op := if is_wconst U32 e1 then XORI else XOR in
    Some (BaseOp (None, op), [:: e0; e1])
  | Omul (Op_w _) => Some (BaseOp (None, MUL), [:: e0; e1])
  | Olsr _  =>
    let op := if is_wconst U32 e1 then SRLI else SRL in
    Some (BaseOp (None, op), [:: e0; e1])
  | Olsl (Op_w U32) =>
    let op := if is_wconst U8 e1 then SLLI else SLL in
    Some (BaseOp (None, op), [:: e0; e1])
  (* | Oasr (Op_w U32) =>
      if is_zero U8 e1 then Some (MOV, e0, [::])
      else Some (ASR, e0, [:: e1 ])
  | Oror U32 =>
      if is_zero U8 e1 then Some (MOV, e0, [::])
      else Some (ROR, e0, [:: e1 ])
  | Orol U32 =>
      let%opt c := is_wconst U8 e1 in
      if c == 0%R then Some (MOV, e0, [::])
      else Some (ROR, e0, [:: wconst (32 - c) ]) *)
  | _ =>
      None
  end.

(* Lower an expression of the form [(ws)[v + e]] or [tab[ws e]]. *)
Definition lower_load (ws: wsize) (e: pexpr) : option(riscv_extended_op * pexprs) :=
  let%opt _ := chk_ws_reg ws in
  Some (BaseOp (None, LOAD Signed U32), [:: e ]).

(* Lower an expression of the form [v].
   Precondition:
   - [v] is a one of the following:
     + a register.
     + a stack variable. *)
Definition lower_Pvar (ws : wsize) (v : gvar) : option(riscv_extended_op * pexprs) :=
    (* For now, only 32 bits can be read from memory or upon move, signed / unsigned has no effect on load or move *)
    if ws != U32 
        then None 
    else
        let op := if is_var_in_memory (gv v) then LOAD Signed U32 else MV in
        Some (BaseOp (None, op), [:: Pvar v ]).

(* Convert an assignment into an architecture-specific operation. *)
Definition lower_cassgn
  (lv : lval) (ws : wsize) (e : pexpr) : option (copn_args) :=
  if is_lval_in_memory lv
    then 
      if (ws <= U32)%CMP
        then
          Some ([:: lv], Oriscv (STORE ws), [:: e])
        else
          None
  else
  let%opt (op, e) :=
    match e with
    | Pvar v => lower_Pvar ws v
    | Pget _ _ _ _ _
    | Pload _ _ _ _ => lower_load ws e
    | Papp1 op e => lower_Papp1 ws op e
    | Papp2 op a b => lower_Papp2 ws op a b
    | _ => None
    end
    in Some ([:: lv], Oasm op, e).

Definition lower_swap ty lvs es : option (seq copn_args) := 
  match ty with
  | sword sz => 
    if (sz <= U32)%CMP then 
      Some([:: (lvs, Oasm (ExtOp (SWAP sz)), es)])
    else None
  | sarr _ => 
      Some([:: (lvs, Opseudo_op (Oswap ty), es)])
  | _ => None
  end.

Definition lower_mulu (lvs : seq lval) (es : seq pexpr) : option (seq copn_args):=
  match lvs, es with
  | [:: r1; r2 ], [:: x ; y ] =>
    (* Arbitrary choice : r1 computed before r2*)
    Some [::
      ([:: r1], Oasm(BaseOp (None, MULHU)), es);
      ([:: r2], Oasm(BaseOp (None, MUL)), es)]
  | _, _ => None
  end.

Definition lower_pseudo_operator
  (lvs : seq lval) (op : pseudo_operator) (es : seq pexpr) : option (seq copn_args) :=
  match op with
  | Oswap ty => lower_swap ty lvs es
  | Omulu ws => lower_mulu lvs es
  | _ => None
  end.

Definition lower_copn
  (lvs : seq lval) (op : sopn) (es : seq pexpr) : option (seq copn_args) :=
  match op with
  | Opseudo_op pop => lower_pseudo_operator lvs pop es
  | _ => None
  end.

(* -------------------------------------------------------------------- *)

Definition lowering_options := unit.

(* Applied to every jasmin lines, cmd is a list of instructions *)
Fixpoint lower_i (i : instr) : cmd :=
(* ii : instruction info, ir : instruction itself *)
  let '(MkI ii ir) := i in
  match ir with
  (* ty is the type of the assign, lv and e *)
  | Cassgn lv tg ty e =>
      let oirs :=
        match ty with
        | sword ws =>
            let%opt (lvs, op, es) := lower_cassgn lv ws e in
            Some ([:: Copn lvs tg op es ])
        | _ => None
        end
      in
      let irs := if oirs is Some irs then irs else [:: ir ] in
      (* Reintroduce information instruction *)
      map (MkI ii) irs

 (* Copn : "assembly" instruction pattern matching, required for pseudo instructions or extra instructions *)
  | Copn lvs tag op es =>
      let seq_ir :=
        if lower_copn lvs op es is Some l
        then map (fun '(lvs', op', es') => Copn lvs' tag op' es') l
        else [:: ir]
      in map (MkI ii) seq_ir
      
  | Cif e c1 c2  =>
      let c1' := conc_map lower_i c1 in
      let c2' := conc_map lower_i c2 in
        [:: MkI ii (Cif e c1' c2')]

  | Cfor v r c =>
      let c' := conc_map lower_i c in
      [:: MkI ii (Cfor v r c') ]

  | Cwhile a c0 e c1 =>
      let c0' := conc_map lower_i c0 in
      let c1' := conc_map lower_i c1 in
      [:: MkI ii (Cwhile a c0' e c1')]

  | _ =>
      [:: i ]
  end.

End Section.