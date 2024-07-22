open Jasmin
open Format

module Arch =
  (val let use_set0 = true and use_lea = true in
       let call_conv = Glob_options.Linux in
       let module C : Arch_full.Core_arch =
         (val CoreArchFactory.core_arch_x86 ~use_lea ~use_set0 call_conv)
       in
       (module Arch_full.Arch_from_Core_arch (C) : Arch_full.Arch))

let load_file name =
  let open Pretyping in
  try
    name
    |> tt_file Arch.arch_info Env.empty None None
    |> fst |> Env.decls
    |> Compile.preprocess Arch.reg_size Arch.asmOp
  with
  | TyError (loc, e) ->
      Format.eprintf "%a: %a@." Location.pp_loc loc pp_tyerror e;
      assert false
  | Syntax.ParseError (loc, None) ->
      Format.eprintf "Parse error: %a@." Location.pp_loc loc;
      assert false

(* ======================================================================  *)
(*                             MOPSA defs                                  *)
(* ======================================================================  *)
open Mopsa
open Universal
open Ast

let universal = "Universal"

(* Define Jasmin types *)
type typ +=
  | T_J_Bool
  | T_J_Int
  | T_J_U of Wsize.wsize
  | T_J_Array of Wsize.wsize * int
  | T_J_Return of typ list (* Special type for return statement, useful to be able to use default MOPSA stub comportment*)

let compare_wsize wsize1 wsize2 =
  match Wsize.wsize_cmp wsize1 wsize2 with Eq -> 0 | Gt -> 1 | Lt -> -1

let () =
  register_typ
    {
      compare =
        (fun next t1 t2 ->
          match (t1, t2) with
          | T_J_U size1, T_J_U size2 -> compare_wsize size1 size2
          | T_J_Array (wsize1, size1), T_J_Array (wsize2, size2) ->
              Compare.compose
                [
                  (fun () -> compare_wsize wsize1 wsize2);
                  (fun () -> compare size1 size2);
                ]
          | _ -> next t1 t2);
      print =
        (fun default fmt t ->
          match t with
          | T_J_U wsize ->
              fprintf fmt "T_J_U%s"
                (String.of_seq
                   (List.to_seq (Jasmin.Wsize.string_of_wsize wsize)))
          | T_J_Array (wsize, len) ->
              fprintf fmt "T_J_Array(U%s,%i)"
                (String.of_seq
                   (List.to_seq (Jasmin.Wsize.string_of_wsize wsize)))
                len
          | T_J_Return ltyp ->
              fprintf fmt "return_t(%a)"
              (Jasmin.Utils.pp_list ", " pp_typ) ltyp
          | _ -> default fmt t);
    }

let string_of_wsize wsize=
          (String.of_seq
                   (List.to_seq (Jasmin.Wsize.string_of_wsize wsize)))


(** Builtin abstract expression *)
type jasmin_abstract_builtin =
      Init_array

(* Define Jasmin expr *)
type expr_kind +=
  | E_J_arr_init of int
  | E_J_get of Warray_.arr_access * Wsize.wsize * var * expr
  | E_J_sub of Warray_.arr_access * Wsize.wsize * int * var * expr
  | E_J_load of Wsize.wsize * var * expr
  | E_J_app1 of Jasmin.Expr.sop1 * expr
  | E_J_appN of Jasmin.Expr.opN * expr list
  | E_J_if of typ * expr * expr * expr
  | E_J_Lnone of typ
  | E_J_Lvar of var
  | E_J_Lmem of Wsize.wsize * var * expr
  | E_J_Laset of Warray_.arr_access * Wsize.wsize * var * expr
  | E_J_Lasub of Warray_.arr_access * Wsize.wsize * int * var * expr
  | E_J_return_vars of var list
  | E_stub_J_abstract of jasmin_abstract_builtin * expr list

let is_left_value = function
  | E_J_Lvar _ | E_J_Laset _ | E_J_Lnone _ | E_J_Lmem _ | E_J_Lasub _ -> true
  | _ -> false

let () =
  register_expr_with_visitor
    {
      compare =
        (fun next e1 e2 -> match (ekind e1, ekind e2) with _ -> next e1 e2);
      print =
        (fun next fmt e ->
          match ekind e with
          | E_J_arr_init len -> fprintf fmt "ArrayInit(%i)" len
          | E_J_get (arr_access, wsize, var, expr) ->
              fprintf fmt "@[get(%a, %a)@]" pp_var var pp_expr expr
          | E_J_sub (arr_access, wsize, len, var, expr) ->
              fprintf fmt "@[sub(%s, %s, %d, %a,%a)@]" (match arr_access with Warray_.AAdirect -> "AAdirect" | _ -> "AAscale") (string_of_wsize wsize) len pp_var var pp_expr expr
          | E_J_load (wsize, var, expr) ->
              fprintf fmt "@[load(%a, %a)@]" pp_var var pp_expr expr
          | E_J_if (typ, cond, expr1, expr2) ->
              fprintf fmt "@[(%a : %a ? %a : %a)@]" pp_expr cond pp_typ typ
                pp_expr expr1 pp_expr expr2
          | E_J_app1 (op, expr) ->
              fprintf fmt "@[op1(%s, %a)@]"
                (Jasmin.PrintCommon.string_of_op1 op)
                pp_expr expr
          | E_J_appN (opn, exprn) ->
              fprintf fmt "@[opN(%a)@]"
                (Jasmin.Utils.pp_list ", " pp_expr)
                exprn
          | E_J_Lnone typ -> fprintf fmt "Lnone(%a)" pp_typ typ
          | E_J_Lvar var -> fprintf fmt "Lvar(%a)" pp_var var
          | E_J_Lmem (wsize, var, expr) ->
              fprintf fmt "Lmem(%a,%a)" pp_var var pp_expr expr
          | E_J_Laset (arr_access, wsize, var, expr) ->
              fprintf fmt "Laset(%s, %s,%a,%a)" (match arr_access with Warray_.AAdirect -> "AAdirect" | _ -> "AAscale") (string_of_wsize wsize) pp_var var pp_expr expr
          | E_J_Lasub (arr_access, wsize, len, var, expr) ->
              fprintf fmt "Lasub(%s, %s, %d,%a,%a)" (match arr_access with Warray_.AAdirect -> "AAdirect" | _ -> "AAscale") (string_of_wsize wsize) len pp_var var pp_expr expr
          | E_J_return_vars vars ->
              fprintf fmt "ret_vars(%a)" (Jasmin.Utils.pp_list ", " pp_var) vars
          | E_stub_J_abstract (builtin, exprs) ->
              let builtin_s = match builtin with Init_array -> "init_array" in
              fprintf fmt "%s(%a)" builtin_s (Jasmin.Utils.pp_list ", " pp_expr) exprs
          | _ -> next fmt e);
      visit =
        (fun default expr ->
          match ekind expr with
          | E_J_get (arr_access, wsize, var, index) ->
              ( { exprs = [ index ]; stmts = [] },
                function
                | { exprs = [ index ]; stmts = [] } ->
                    {
                      expr with
                      ekind = E_J_get (arr_access, wsize, var, index);
                    }
                | _ -> assert false )
          | E_J_if (typ, cond, expr1, expr2) ->
              ( { exprs = [ cond; expr1; expr2 ]; stmts = [] },
                function
                | { exprs = [ cond; expr1; expr2 ]; stmts = [] } ->
                    { expr with ekind = E_J_if (typ, cond, expr1, expr2) }
                | _ -> assert false )
          | E_J_app1 (op, expr1) ->
              ( { exprs = [ expr1 ]; stmts = [] },
                function
                | { exprs = [ expr1 ]; stmts = [] } ->
                    { expr with ekind = E_J_app1 (op, expr1) }
                | _ -> assert false )
          | E_J_appN (op, exprN) ->
              ( { exprs = exprN; stmts = [] },
                function
                | { exprs = exprN; stmts = [] } ->
                    { expr with ekind = E_J_appN (op, exprN) }
                | _ -> assert false )
          | E_J_Laset (arr, wsize, var, expr) ->
              ( { exprs = [ expr ]; stmts = [] },
                function
                | { exprs = [ expr ]; stmts = [] } ->
                    { expr with ekind = E_J_Laset (arr, wsize, var, expr) }
                | _ -> assert false )
          | E_J_arr_init len -> leaf expr

          | E_stub_J_abstract (builtin, args) ->
              ( { exprs = args ; stmts = [] },
                function
                | { exprs = args ; stmts = [] } ->
                    { expr with ekind = E_stub_J_abstract (builtin,args) }
                | _ -> assert false )
          | _ ->
              default expr);
    }

type for_range = Jasmin.Expr.dir * expr * expr




(* stmt of jasmin (correspond to instr) *)
type stmt_kind +=
  | S_J_assgn of expr (** lval *) * Jasmin.Expr.assgn_tag * typ * expr
    (* turn 'asm Sopn.sopn into 'sopn? could be useful to ensure that we remove things statically *)
  | S_J_opn of
      expr list (** lvals *)
      * Jasmin.Expr.assgn_tag (* 'asm Sopn.sopn *)
      * expr list
  | S_J_syscall of
      expr list (** lvals *) * BinNums.positive Syscall_t.syscall_t * expr list
  | S_J_if of expr * stmt * stmt
  | S_J_for of var * for_range * stmt
  | S_J_while of (* E.align * *) stmt * expr * stmt
  | S_J_call of expr list (** lvals *) * Jasmin.Prog.funname * expr list
  | S_J_declare of var
        (** Declare the existence of a variable (useful for declare arguments)*)
  | S_J_return of var list (** returns values *)

let () =
  register_stmt
    {
      compare =
        (fun next s1 s2 ->
          match (skind s1, skind s2) with
          | S_J_assgn _, S_J_assgn _
          | S_J_if _, S_J_if _
          | S_J_for _, S_J_for _
          | S_J_while _, S_J_while _
          | S_J_declare _, S_J_declare _ ->
              0
          | S_J_return _, S_J_return _ -> 0
          | _ -> next s1 s2);
      print =
        (fun next fmt e ->
          match skind e with
          | S_J_assgn (lval, assgn_tag, typ, expr) ->
              fprintf fmt "@[assign(%a, %a , %a)@]" pp_typ typ pp_expr lval
                pp_expr expr
          | S_J_opn (lvals, assgn_tag, exprs) ->
              fprintf fmt "@[opn_statement(@[%a@], @[%a@])@]"
                (Jasmin.Utils.pp_list ", " pp_expr)
                lvals
                (Jasmin.Utils.pp_list ", " pp_expr)
                exprs
          | S_J_syscall (lvals, syscall, exprs) ->
              fprintf fmt "@[syscall(@[%a@], @[%a@])@]"
                (Jasmin.Utils.pp_list ", " pp_expr)
                lvals
                (Jasmin.Utils.pp_list ", " pp_expr)
                exprs
          | S_J_for (var, (dir, start, last), stmt) ->
              fprintf fmt "@[for(%a, %a to %a){@\n@ @ %a@\n}@]" pp_var var
                pp_expr start pp_expr last pp_stmt stmt
          | S_J_if (cond, expr_true, expr_false) ->
              fprintf fmt "@[if(%a){@\n@ @ %a@\n}else{@\n@ @ %a@\n}@]" pp_expr
                cond pp_stmt expr_true pp_stmt expr_false
          | S_J_while(pre,cond,loop) -> fprintf fmt "@[while(%a){@\n@ @ %a@\n}(%a)@]" pp_expr cond pp_stmt loop pp_stmt pre
          | S_J_call (lvals, call, exprs) ->
              fprintf fmt "@[call(@[%a@], %s ,@[%a@])@]"
                (Jasmin.Utils.pp_list ", " pp_expr)
                lvals call.fn_name
                (Jasmin.Utils.pp_list ", " pp_expr)
                exprs
          | S_J_declare vars -> fprintf fmt "@[declare(@[%a@])@]" pp_var vars
          | S_J_return vars ->
            fprintf fmt "@[return @[%a@]@]"
              (Jasmin.Utils.pp_list ", " pp_var) vars
          | _ -> next fmt e);
    }


type operator +=
  (* Unary operator *)
  | O_J_word_of_int of Wsize.wsize
  | O_J_int_of_word of Wsize.wsize
  | O_J_signext of Wsize.wsize * Wsize.wsize
  | O_J_zeroext of Wsize.wsize * Wsize.wsize
  | O_J_not
  | O_J_lnot of Wsize.wsize
  | O_J_neg of typ

let () = register_operator {
    compare = (fun next op1 op2 ->
        let open Wsize in
        match op1, op2 with
        | O_J_word_of_int wsize1, O_J_word_of_int wsize2 ->
          compare_wsize wsize1 wsize2
        | O_J_int_of_word  wsize1,O_J_int_of_word  wsize2 ->
          compare_wsize wsize1 wsize2
        | O_J_signext (wsize1 , wsize2),O_J_signext (wsize3 , wsize4) ->
          Compare.compose [
            (fun () -> compare_wsize wsize1 wsize3);
            (fun () -> compare_wsize wsize2 wsize4)
          ]
        | O_J_zeroext  (wsize1 , wsize2),O_J_zeroext  (wsize3 , wsize4) ->
          Compare.compose [
            (fun () -> compare_wsize wsize1 wsize3);
            (fun () -> compare_wsize wsize2 wsize4)
          ]
        | O_J_lnot  wsize1,O_J_lnot  wsize2 ->
          compare_wsize wsize1 wsize2
        | O_J_neg  typ1,O_J_neg  typ2 ->
          compare_typ typ1 typ2
        | _ -> next op1 op2
      );
    print = (fun default fmt op ->
      match op with
        | O_J_word_of_int wsize -> Format.fprintf fmt "word%s_of_int" (string_of_wsize wsize)
        | O_J_int_of_word wsize -> Format.fprintf fmt "int_of_word%s" (string_of_wsize wsize)
        | O_J_signext (wsize,wsize2) -> Format.fprintf fmt "signext"
        | O_J_zeroext (wsize,wsize2) -> Format.fprintf fmt "zeroext"
        | O_J_not -> Format.fprintf fmt "J_not"
        | O_J_lnot wsize -> Format.fprintf fmt "J_lnot"
        | O_J_neg typ -> Format.fprintf fmt "J_neg(%a)" pp_typ typ
        | _ -> default fmt op)
  }

(** {1 Translate Jasmin Ast in a MOPSA Ast} *)
let jasmin_to_mopsa_type typ =
  let open Prog in
  let open CoreIdent in
  let open Universal.Ast in
  match typ with
  | Bty Bool -> T_bool
  | Bty Int -> T_int
  | Bty (U wsize) -> T_J_U wsize
  | Arr (wsize, len) -> T_J_Array (wsize, len)
  | _ -> panic ~loc:__LOC__ "type is not supported"

let jasmin_mopsa_to_universal typ =
  let open Universal.Ast in
  match typ with
  | T_J_U wsize -> T_J_U wsize
  | T_J_Array (wsize, len) -> T_array T_int
  | _ -> typ

let jasmin_to_mopsa_var var =
  let open CoreIdent in
  let open Prog in
  mkv (var.v_name^":"^string_of_uid var.v_id)
    (* FIXME add vkind type*)
    (V_uniq (var.v_name, hash_of_uid var.v_id))
    (* FIXME *)
    (jasmin_to_mopsa_type var.v_ty)

let jasmin_to_mopsa_op_kind =
  let open Universal.Ast in
  let open Jasmin.Expr in
  function Op_int -> T_int | Op_w wsize -> T_J_U wsize

let jasmin_to_mopsa_op1 op =
  let open Universal.Ast in
  let open Jasmin.Expr in
  match op with
  | Oword_of_int wsize -> O_J_word_of_int wsize,T_J_U wsize
  | Oint_of_word wsize -> O_J_int_of_word wsize,T_int
  | Osignext (wsize1, wsize2) -> O_J_signext (wsize1,wsize2),T_J_U wsize2
  | Onot -> O_J_not,T_bool
  | Olnot wsize -> O_J_lnot wsize,T_J_U wsize
  | Ozeroext (wsize1, wsize2) -> O_J_zeroext (wsize1, wsize2),T_J_U wsize2
  | Oneg op_kind -> O_J_neg (jasmin_to_mopsa_op_kind op_kind),jasmin_to_mopsa_op_kind op_kind

let jasmin_to_mopsa_cmp_kind cmp =
  let open Universal.Ast in
  let open Jasmin.Expr in
  match cmp with
  | Cmp_int -> T_int
  | Cmp_w (signe, wsize) -> T_J_U wsize

let jasmin_to_mopsa_op2 op =
  let open Universal.Ast in
  let open Jasmin.Expr in
  match op with
  (* Logical *)
  | Obeq -> (O_eq, T_bool)
  | Oand -> (O_log_and, T_bool)
  | Oor -> (O_log_or, T_bool)
  (* Arithmetic *)
  | Oadd op_kind -> (O_plus, jasmin_to_mopsa_op_kind op_kind)
  | Omul op_kind -> (O_mult, jasmin_to_mopsa_op_kind op_kind)
  | Osub op_kind -> (O_minus, jasmin_to_mopsa_op_kind op_kind)
  | Odiv cmp_kind -> (O_div, jasmin_to_mopsa_cmp_kind cmp_kind)
  | Omod cmp_kind -> (O_mod, jasmin_to_mopsa_cmp_kind cmp_kind)
  | Oland wsize -> (O_bit_and, T_J_U wsize)
  | Olor wsize -> (O_bit_or, T_J_U wsize)
  | Olxor wsize -> (O_bit_xor, T_J_U wsize)
  | Olsr wsize -> (O_bit_rshift, T_J_U wsize)
  | Olsl op_kind -> (O_bit_lshift, jasmin_to_mopsa_op_kind op_kind)
  | Oasr op_kind -> (O_bit_rshift, jasmin_to_mopsa_op_kind op_kind)
  | Oror wsize -> failwith "todo trad op with wsize"
  | Orol wsize -> failwith "todo trad op with wsize"
  (* Comparison *)
  | Oeq op_kind ->  (O_eq, T_bool)
  | Oneq op_kind -> (O_ne, T_bool)
  | Olt cmp_kind -> (O_lt, T_bool)
  | Ole cmp_kind -> (O_le, T_bool)
  | Ogt cmp_kind -> (O_gt, T_bool)
  | Oge cmp_kind -> (O_ge, T_bool)
  (* Array expr *)
  | Ovadd (velem, wsize) -> failwith "todo trad op with velem wsize"
  | Ovsub (velem, wsize) -> failwith "todo trad op with velem wsize"
  | Ovmul (velem, wsize) -> failwith "todo trad op with velem wsize"
  | Ovlsr (velem, wsize) -> failwith "todo trad op with velem wsize"
  | Ovlsl (velem, wsize) -> failwith "todo trad op with velem wsize"
  | Ovasr (velem, wsize) -> failwith "todo trad op with velem wsize"

let sub_pos_to_var expr vars =
  let open Prog in
  match expr with
  | Pconst z -> (match List.nth_opt vars (Z.to_int z) with
      | Some v -> v
      | None -> panic ~loc:__LOC__ "invalid argument position")
  | _ -> panic ~loc:__LOC__ "the abstract pos is incorrect"

type translate_info = {
    args : var list;
    return_var : var list;
}


let rec jasmin_to_mopsa_expr ?(range = mk_program_range [ "dummy location" ]) ?(translate_info = {args = []; return_var = []})
    expr =
  let open Prog in
  let open Universal.Ast in
  match expr with
  | Pconst const -> mk_z const range
  | Pbool bool -> mk_bool bool range
  | Parr_init len -> mk_expr (E_J_arr_init len) range
  | Pvar var -> mk_var (jasmin_to_mopsa_var var.gv.pl_desc) range
  | Pget (warray, wsize, var, expr) ->
      mk_expr
        ~etyp:(T_J_U wsize)
        (E_J_get
           ( warray,
             wsize,
             jasmin_to_mopsa_var var.gv.pl_desc,
             jasmin_to_mopsa_expr ~translate_info ~range expr ))
        range
  | Psub (warray, wsize, len, var, expr) ->
    mk_expr
      (E_J_sub
      (warray,
      wsize,
      len,
      jasmin_to_mopsa_var var.gv.pl_desc,
      jasmin_to_mopsa_expr ~translate_info expr ~range)) range
  | Pload (wsize, var, expr) ->
      mk_expr
        (E_J_load
           ( wsize,
             jasmin_to_mopsa_var var.pl_desc,
             jasmin_to_mopsa_expr ~translate_info ~range expr ))
        range
  | Papp1 (sop1, expr) ->
    let new_op, new_typ = jasmin_to_mopsa_op1 sop1 in
    mk_unop ~etyp:new_typ new_op (jasmin_to_mopsa_expr ~translate_info expr ~range) range
  | Papp2 (sop2, expr1, expr2) ->
      let new_op, typ = jasmin_to_mopsa_op2 sop2 in
        mk_binop ~etyp:typ
          (jasmin_to_mopsa_expr ~translate_info ~range expr1)
          new_op
          (jasmin_to_mopsa_expr ~translate_info ~range expr2)
          range
  | PappN (sopn, exprn) ->
      mk_expr
        (E_J_appN (sopn, List.map (jasmin_to_mopsa_expr ~translate_info ~range) exprn))
        range
  | Pif (typ, cond, expr_true, expr_false) ->
      mk_expr ~etyp:(jasmin_to_mopsa_type typ)
        (E_J_if
           ( jasmin_to_mopsa_type typ,
             jasmin_to_mopsa_expr ~translate_info ~range cond,
             jasmin_to_mopsa_expr ~translate_info ~range expr_true,
             jasmin_to_mopsa_expr ~translate_info ~range expr_false ))
        range
  | Pabstract (pred, args) -> (
    let open Stubs.Ast in
    match pred.name, args with
    | "init_array", [pos;i1;i2] when List.length args == 3 ->
      mk_expr (
        E_stub_J_abstract (Init_array,
        [
          mk_var (sub_pos_to_var pos translate_info.args) range;
          jasmin_to_mopsa_expr ~translate_info ~range i1;
          jasmin_to_mopsa_expr ~translate_info ~range i2
        ]
        )
      ) range
    | "assigns_array", [pos; i1;i2] when List.length args == 3 ->
      mk_expr (
        E_stub_J_abstract (Init_array,
          [
            mk_stub_primed (mk_var (sub_pos_to_var pos translate_info.return_var) range) range;
            jasmin_to_mopsa_expr ~translate_info ~range i1;
            jasmin_to_mopsa_expr ~translate_info ~range i2
          ]
        )
      ) range
    | pred_name,_ -> 
      warn_at range "abstract %s is not yet supported" pred_name;
      mk_true range
      )
  | Pfvar _ -> 
    warn_at range "expr Pfvar not yet supported";
    mk_true range
  | Pbig _ -> 
    warn_at range "expr Pbig not yet supported";
    mk_true range
  | Presult _ -> 
    warn_at range "expr Presult not yet supported";
    mk_true range
  | Presultget _ -> 
    warn_at range "expr Presultget not yet supported";
    mk_true range
  | _ -> failwith "expr not yet supported"




and jasmin_lval_to_mopsa_expr ?(range = mk_program_range [ "dummy location" ]) ?(translate_info = {args = []; return_var = []})
    lval =
  let open Prog in
  match lval with
  | Lnone (loc, typ) -> mk_expr (E_J_Lnone (jasmin_to_mopsa_type typ)) range
  | Lvar var -> (* mk_expr (E_J_Lvar (jasmin_to_mopsa_var var.pl_desc)) range *)
    mk_var (jasmin_to_mopsa_var var.pl_desc) range
  | Lmem (wsize, var, expr) ->
      mk_expr
        (E_J_Lmem
           ( wsize,
             jasmin_to_mopsa_var var.pl_desc,
             jasmin_to_mopsa_expr ~translate_info ~range expr ))
        range
  | Laset (arr_access, wsize, var, expr) ->
      mk_expr
        (E_J_Laset
           ( arr_access,
             wsize,
             jasmin_to_mopsa_var var.pl_desc,
             jasmin_to_mopsa_expr ~translate_info ~range expr ))
        range
  | Lasub (arr_access, wsize, len, var, expr) ->
      mk_expr
        (E_J_Lasub
           ( arr_access,
             wsize,
             len,
             jasmin_to_mopsa_var var.pl_desc,
             jasmin_to_mopsa_expr ~translate_info ~range expr ))
        range

(* Jasmin location to MOPSA location*)
let jasmin_to_mopsa_loc location =
  let open Jasmin.Location in
  let start_line, start_col = location.loc_start in
  let end_line, end_col = location.loc_end in
  mk_orig_range
    (mk_pos location.loc_fname start_line start_col)
    (mk_pos location.loc_fname end_line end_col)

(** Translate jasmin instruction to MOPSA  stmt (instr in Jasmin is the equivalent of stmt in MOPSA)*)
let rec jasmin_to_mopsa_stmt ?(translate_info = {args = []; return_var = []}) instr  =
  let open Prog in
  let open Universal.Ast in
  let range = jasmin_to_mopsa_loc instr.i_loc.base_loc in
  match instr.i_desc with
  | Cassgn (lval, assgn_tag, typ, expr) ->
    mk_assign (jasmin_lval_to_mopsa_expr ~range lval) (jasmin_to_mopsa_expr ~translate_info ~range expr) range
  | Cif (cond, stmt_true, stmt_false) ->
    mk_if (jasmin_to_mopsa_expr ~translate_info ~range cond)
      (mk_block (List.map jasmin_to_mopsa_stmt stmt_true) range)
      (mk_block (List.map jasmin_to_mopsa_stmt stmt_false) range)
      range
  | Cfor (var, (dir, start, last), loop) ->
      mk_stmt
        (S_J_for
           ( jasmin_to_mopsa_var var.pl_desc,
             ( dir,
               jasmin_to_mopsa_expr ~translate_info ~range start,
               jasmin_to_mopsa_expr ~translate_info ~range last ),
             Lang.Ast.mk_block (List.map jasmin_to_mopsa_stmt loop) range ))
        range
  | Cwhile (align, loop, cond, after_loop) ->
      mk_stmt
        (S_J_while
           ( Lang.Ast.mk_block (List.map jasmin_to_mopsa_stmt loop) range,
             jasmin_to_mopsa_expr ~translate_info ~range cond,
             Lang.Ast.mk_block (List.map jasmin_to_mopsa_stmt after_loop) range
           ))
        range
  | Copn (lvals, assgn_tag, opn, exprs) ->
      mk_stmt
        (S_J_opn
           ( List.map (jasmin_lval_to_mopsa_expr ~range) lvals,
             assgn_tag,
             List.map (jasmin_to_mopsa_expr ~translate_info ~range) exprs ))
        range
  | Csyscall (lvals, syscall, exprs) ->
      mk_stmt
        (S_J_syscall
           ( List.map (jasmin_lval_to_mopsa_expr ~range) lvals,
             syscall,
             List.map (jasmin_to_mopsa_expr ~translate_info ~range) exprs ))
        range
  | Ccall (lvals, name, exprs) ->
      mk_stmt
        (S_J_call
           ( List.map (jasmin_lval_to_mopsa_expr ~range) lvals,
             name,
             List.map (jasmin_to_mopsa_expr ~translate_info ~range) exprs ))
        range
  | _ -> panic "this instruction is not yet translate in MOPSA stmt"

(* TODO translate fields commented *)

type j_func = {
  f_loc : range;
  (* f_annot *)
  (* f_contra *)
  f_stub : Stubs.Ast.stub_func;
  (* f_cc not useful for the analysis ? *)
  f_name : Prog.funname;
  f_tyin : typ list;
  f_args : var list;
  f_body : stmt;
  f_tyout : typ option;
  (* f_outannot *)
  f_ret : var list;
}
(** Similar to the jasmin gfunc type but with MOPSA types *)

let declare_args ?(range = mk_program_range ["dummy range"]) args =
  let open Universal.Ast in
  if List.compare_length_with args 0 = 0 then mk_nop range
  else mk_block (List.map (fun v -> mk_stmt (S_J_declare v) range) args) range


let jasmin_stub_to_universal fname vars stub return range translate_info =
  let open Prog in
  let open Stubs.Ast in
  let pre = stub.f_pre in
  let post = stub.f_post in
  let pre = List.map (fun e -> S_leaf (S_requires (with_range (with_range (F_expr (jasmin_to_mopsa_expr ~translate_info ~range (snd e))) range ) range ))) pre in
  let post = List.map (fun e -> S_leaf (S_ensures (with_range (with_range (F_expr (jasmin_to_mopsa_expr ~translate_info ~range (snd e))) range ) range))) post in
  {
    stub_func_name = fname;
    stub_func_body = pre @ post;
    stub_func_params = vars;
    stub_func_locals = [];
    stub_func_assigns = [];
    stub_func_return_type = return;
    stub_func_range = range
  }


let jasmin_to_mopsa_func func =
  let open Prog in
  let open CoreIdent in
  let open Universal.Ast in
  let args = List.map jasmin_to_mopsa_var func.f_args in
  let range = jasmin_to_mopsa_loc func.f_loc in
  let return_range = mk_tagged_range (String_tag ("return expression of "^func.f_name.fn_name)) (mk_program_range [func.f_loc.loc_fname]) in
  let declare_range = mk_tagged_range (String_tag ("declaration of arguments for function "^func.f_name.fn_name)) (mk_program_range [func.f_loc.loc_fname]) in
  let ret =
      List.map
        (fun var -> jasmin_to_mopsa_var (Jasmin.Location.unloc var))
        func.f_ret
  in
  let body =
      Lang.Ast.mk_block
        (declare_args args ~range:declare_range :: List.map jasmin_to_mopsa_stmt func.f_body @ if List.length ret = 0 then [] else [mk_stmt (S_J_return ret) return_range] )
        range
  in
  let return_typ = Some (T_J_Return (List.map jasmin_to_mopsa_type func.f_tyout)) in
  {
    f_loc = range ;
    f_name = func.f_name;
    f_stub = jasmin_stub_to_universal func.f_name.fn_name args func.f_contra return_typ range { args ; return_var = ret };
    f_tyin = List.map jasmin_to_mopsa_type func.f_tyin;
    f_args = args;
    f_body = body;
    f_tyout = return_typ;
    f_ret = ret
  }

(** Pretty printer for j_func type*)
let pp_function fmt func =
  fprintf fmt
    "@[<v>%s{@\n\
     @[@ args : @[%a@] @\n\
     @ body : @\n\
     @ @ @ @[%a@]@\n\
     @ ret : @\n\
     @ @ @ @[%a@]@\n\
     @ stubs : @\n\
     @ @ @ @[%a@]@]@\n\
     }@]@\n"
    func.f_name.fn_name
    (Jasmin.Utils.pp_list ", " pp_var)
    func.f_args pp_stmt func.f_body
    (Jasmin.Utils.pp_list ", " pp_var)
    func.f_ret
    (Stubs.Ast.pp_stub_func)
    func.f_stub

type jasmin_program = {
  global_decl : (var * Jasmin.Global.glob_value) list;
  functions : j_func list;
}
(** Describe a Jasmin program with MOPSA types *)

(** Make a jasmin program with the output of `load_file`*)
let mk_jasmin_program (global_decl, funcs) =
  {
    global_decl =
      List.map
        (fun (var, value) -> (jasmin_to_mopsa_var var, value))
        global_decl;
    functions = List.map jasmin_to_mopsa_func funcs;
  }

(** Define Jasmin prog kind *)
type prog_kind += Jasmin_Program of jasmin_program

(* Register the program *)

let () =
  register_program
    {
      compare = (fun next -> next);
      print =
        (fun default fmt prog ->
          match prog.prog_kind with
          | Jasmin_Program prog ->
              fprintf fmt
                "@[Jasmin Program : @\n\
                \ Globals : @\n\
                \ [%a] @\n\
                \ Functions : @\n\
                \ @[<v>%a@]@]"
                (Jasmin.Utils.pp_list ";@ " pp_var)
                (List.map fst prog.global_decl)
                (Jasmin.Utils.pp_list "@\n" pp_function)
                prog.functions
          | _ -> default fmt prog);
    }

(* ======================================================================= *)
(** Program key  *)
(* ======================================================================= *)

module JasminProgramKey = GenContextKey (struct
  type 'a t = jasmin_program

  let print pp fmt prog = Format.fprintf fmt "Jasmin Program"
end)

let jasmin_program_ctx = JasminProgramKey.key

let set_jasmin_program prog flow =
  Flow.set_ctx (Flow.get_ctx flow |> add_ctx jasmin_program_ctx prog) flow

let get_jasmin_program flow = Flow.get_ctx flow |> find_ctx jasmin_program_ctx

(* ======================================================================= *)
(** Target information *)
(* ======================================================================= *)

module TargetCtx = GenContextKey (struct
  type 'a t = (module Jasmin.Arch_full.Arch)

  let print _ fmt _ = Format.fprintf fmt "target information"
end)

let set_target_info info flow =
  Flow.set_ctx (Flow.get_ctx flow |> add_ctx TargetCtx.key info) flow

let get_jasmin_info flow = Flow.get_ctx flow |> find_ctx TargetCtx.key


(* ======================================================================  *)
(*                              Locals vars                                *)
(* ======================================================================  *)

let find_function prog call =
  List.find (fun e -> e.f_name = call) prog.functions

let get_locals_var prog =
  let rec locals_stmt stmt vars=
    match skind stmt with
    | S_assign(v1,exp) -> (locals_expr exp (locals_expr v1 vars))
    | S_block(stmt, block) -> List.fold_right locals_stmt stmt (List.fold_right VarSet.add block vars)
    | S_J_for(v,_,body) -> locals_stmt body (VarSet.add v vars)
    | S_J_while(s1,cond,body) -> locals_stmt body @@ locals_expr cond @@ locals_stmt s1 vars
    | S_J_if(c,strue,sfalse) -> locals_stmt sfalse (locals_stmt strue (locals_expr c vars))
    | S_if (c,strue,sfalse) -> locals_stmt sfalse (locals_stmt strue (locals_expr c vars))
    | S_J_call(lval,_,args) -> List.fold_right locals_expr lval (List.fold_right locals_expr args vars)
    | S_J_return return_var -> List.fold_right VarSet.add return_var vars
    | _ -> vars
  and locals_expr expr vars =
    match ekind expr with
    | E_binop(_,e1,e2) -> locals_expr e2 (locals_expr e1 vars)
    | E_unop(_,e1) -> locals_expr e1 vars
    | E_var(v,_) -> VarSet.add v vars
    | E_J_Laset(_,_,var,expr)
    | E_J_get(_,_,var,expr)
    | E_J_sub(_,_,_,var,expr)
    | E_J_Lasub(_,_,_,var,expr) ->  locals_expr expr (VarSet.add var vars)
    | _ -> vars
  in locals_stmt prog VarSet.empty


(* ======================================================================  *)
(*                              Utils                                      *)
(* ======================================================================  *)



let is_jasmin_scalar typ = match typ with
  | T_bool | T_int | T_J_U _ -> true
  | _ -> false

let is_jasmin_array_type typ = match typ with
  | T_J_Array _ -> true
  | _ -> false

let is_jasmin_type typ = match typ with
  | T_J_Array _ | T_J_U _ | T_J_Bool | T_J_Int -> true
  | _ -> false

let is_jasmin_numeric_type typ = match typ with
  | T_J_U _ | T_J_Bool | T_J_Int -> true
  | _ -> false

let get_array_type_len typ = match typ with
  | T_J_Array (_, len) -> len
  | _ -> panic ~loc:__FILE__ "%a is not a T_J_Array type" pp_typ typ

let get_array_type_wsize typ = match typ with
  | T_J_Array (wsize, len) -> wsize
  | _ -> panic ~loc:__FILE__ "%a is not a T_J_Array type" pp_typ typ
