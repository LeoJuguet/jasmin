module X86_64 = X86_64


open Jasmin
module type ArchCoreWithAbstraction = sig
  module Arch : Arch_full.Arch

  val eval_opn : Mopsa.expr list
        -> (
          Arch.reg, Arch.regx, Arch.xreg, Arch.rflag, Arch.cond, Arch.asm_op,
          Arch.extra_op
        ) Arch_extra.extended_op
          Sopn.sopn
        -> Mopsa.expr list
        -> Mopsa.range
        -> ('a,'b) Mopsa.man
        -> 'a Mopsa.flow
        -> 'a Core.Post.post option

  val eval_base_op :
      Mopsa.expr list
      -> Wsize.wsize option
      -> Arch.asm_op
      -> Mopsa.expr list
      -> Mopsa.range
      -> ('a,'b) Mopsa.man
      -> 'a Mopsa.flow
      -> 'a Core.Post.post option
      
  val eval_ext_op :
      Mopsa.expr list
      -> Arch.extra_op
      -> Mopsa.expr list
      -> Mopsa.range
      -> ('a,'b) Mopsa.man
      -> 'a Mopsa.flow
      -> 'a Core.Post.post option
  
end


let get_arch_abstraction target : (module ArchCoreWithAbstraction) =
  let (module P: ArchCoreWithAbstraction) =
  match target with
  | "x86-64" -> (module X86_64.ArchCoreWithAbstraction)
  | _arch -> failwith "This arch doesn't have any abstraction available for the moment"
  in (module P)

open Mopsa
open Ast
open Abstraction.Stateless 
module StatelessDomain = struct

  include GenStatelessDomainId (
    struct
      let name = "jasmin.arch.specific"
    end
  )

  let checks = []

  let init _ _ _ = None


  let exec_pseudo_op lvals pseudo_op args range man flow =
      match pseudo_op, lvals, args with
      | Pseudo_operator.Ospill (Spill, _), _,_ 
      | Pseudo_operator.Ospill (Unspill, _), _,_
      | Pseudo_operator.Ocopy (_, _), _,_ -> None
      | Pseudo_operator.Oaddcarry _, expr1 :: expr2::q , arg1:: arg2::t 
      | Pseudo_operator.Osubcarry _, expr1 :: expr2::q , arg1:: arg2::t
      | Pseudo_operator.Omulu _, expr1 :: expr2::q, arg1:: arg2::t ->
        let open Initialized in
        man.eval arg1 ~translate:"Universal" flow >>$? fun arg1 flow ->
        man.eval arg2 ~translate:"Universal" flow >>$? fun arg2 flow ->
        let aval_arg1 = mk_avalue_query arg1 V_jasmin_scalar_initialized in
        let aval_arg2 = mk_avalue_query arg2 V_jasmin_scalar_initialized in
        let (is_init_1 : Init.t) = ask_and_reduce man.ask aval_arg1 flow in
        let (is_init_2 : Init.t) = ask_and_reduce man.ask aval_arg2 flow in
        let is_init = Init.meet is_init_1 is_init_2 in
        (
        match is_init with
        | Nb is_init ->
          let open Universal.Ast in
          let cst = mk_constant ~etyp:T_int (C_int_interval (ItvUtils.IntBound.MINF, ItvUtils.IntBound.PINF)) range in
          man.exec (mk_assign expr1 cst range) flow
          >>%
          man.exec (mk_assign expr2 cst range)
          |> OptionExt.return
        | _ -> failwith "bottom"
      )
      | Pseudo_operator.Omulu _, _, _ -> failwith "other mult not supported this one"
      | Pseudo_operator.Oaddcarry _, _, _ -> failwith "other addcarry not supported"  
      | Pseudo_operator.Osubcarry _, _, _ -> failwith "other subcarry not supported"
      | Pseudo_operator.Oswap _, _,_ -> None
      | Pseudo_operator.Onop, _ , _ ->
        Post.return flow
        |> OptionExt.return

  
  let exec stmt man flow =
    let range = srange stmt in
    match skind stmt with
    | S_J_opn (lvals, assgn_tag, Opseudo_op pseudo_op, expr) ->
      exec_pseudo_op lvals pseudo_op expr range man flow
    | S_J_opn (lvals, assgn_tag, Oslh slh_op, expr) ->
      None
    | S_J_opn (lvals, assgn_tag, Oasm (BaseOp (wsize,asm_op)), expr) ->
      X86_64.ArchCoreWithAbstraction.eval_base_op lvals wsize asm_op expr range man flow
    | S_J_opn (lvals, assgn_tag, Oasm (ExtOp asm_op), expr) ->
      X86_64.ArchCoreWithAbstraction.eval_ext_op lvals asm_op expr range man flow
    | _ -> None


  
  let eval expr man flow =
    match ekind expr with
    | _ -> None 

  let ask _ _ _ = None
  let print_expr man flow printer exp = ()
end

let () =
  register_stateless_domain (module StatelessDomain)
