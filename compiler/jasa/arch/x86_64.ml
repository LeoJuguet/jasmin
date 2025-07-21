open Jasmin
open Mopsa
open Ast




open X86_decl

type reg = register
type regx = register_ext
type xreg = xmm_register
type cond = condt
type asm_op = X86_instr_decl.x86_op
type extra_op = X86_extra.x86_extra_op

module ArchCoreWithAbstraction = struct
  module Arch =
    (val let use_set0 = true and use_lea = true in
         let call_conv = Glob_options.Linux in
         let module Arch =
           (val CoreArchFactory.core_arch_x86 ~use_lea ~use_set0 call_conv)
        in
        (module Arch_full.Arch_from_Core_arch (Arch): Arch_full.Arch
          with 
            type reg = register
            and type asm_op = X86_instr_decl.x86_op
            and type extra_op = X86_extra.x86_extra_op            
        )
    )
  
  let eval_base_op lvars wsize op args range man flow =
    let open X86_instr_decl in
    match op, lvars, args with
    | MOV _, [lval], [arg] ->
      man.exec (mk_assign lval arg range) flow
      |> OptionExt.return
    | _ -> failwith "todo"

  let eval_ext_op lvars op args range man flow =
    let open X86_extra in
    let open Universal.Ast in
    let range = erange (List.hd lvars) in
    match op with
    | Oset0 wsize ->
        man.exec
          (mk_assign
            (List.hd lvars)
            (mk_int 0 range)
            range
          )
        flow
      |> OptionExt.return
    | _ -> failwith "todo"

  let eval_opn lvars opn args range man flow =
    let open Sopn in 
    match opn with
    | Opseudo_op pseudo_op -> failwith "todo"
    | Oslh slh -> failwith "todo"
    | Oasm asm_op -> (
      let open Arch_extra in
        match asm_op with
        | BaseOp (wsize,op) -> eval_base_op lvars wsize op args range man flow
        | ExtOp op -> eval_ext_op lvars op args range man flow
      )

end


