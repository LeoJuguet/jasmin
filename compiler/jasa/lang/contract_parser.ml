module Parse = struct
    open Angstrom

    type bin_op = Add | Subtract | Multiply | Divide

    type bin_op_cond = Eq | Neq | Lt | Gt | Le | Ge

    type log_bin_op = bin_op_cond

    type constant = 
      | CstBool of bool
      | CstInt of int

    type atom = 
      | Constant of constant
      | Var of string

    type expr = 
      | Atom of atom
      | BinOp of expr * bin_op * expr
      | LogBinOp of expr * log_bin_op * expr 
      | ArrayAccess of string * atom

    type expr_cond = expr * bin_op_cond * expr

    type arg = 
      | LabeledArg of string * expr
      | ExprArg of expr

    type array_predicate = arg list

    type condition = expr_cond * unit

    type predicate =
      | ExprPredicate of expr
      | ArrayPredicate of array_predicate

    type contract_ensures = 
      | Condition of condition
      | ArrayPredicate of array_predicate

    type contract_requires = array_predicate

    let whitespace = char ' '
    let ws = skip_many whitespace

    let comment = 
      string "/*"
      *> take_till (function '*' -> true | _ -> false)
      *> string "*/"
      *> return ()

    let skip_ws_and_comments = skip_many (whitespace *> return () <|> comment)

    
    let integer = 
      take_while1 (function '0'..'9' -> true | _ -> false) >>| int_of_string

    let ident = 
      peek_char >>= function
      | Some c when ('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z') ->
          take_while1 (function 
            | 'a'..'z' | 'A'..'Z' | '0'..'9' | '_' -> true 
            | _ -> false)
      | _ -> fail "Expected identifier"

    let add = char '+' *> return Add
    let subtract = char '-' *> return Subtract  
    let multiply = char '*' *> return Multiply
    let divide = char '/' *> return Divide

    let bin_op = choice [add; subtract; multiply; divide]

    let eq = char '=' *> return Eq
    let neq = string "!=" *> return Neq
    let le = string "=<" *> return Le
    let ge = string ">=" *> return Ge
    let lt = char '<' *> return Lt
    let gt = char '>' *> return Gt

    let bin_op_cond = choice [neq; le; ge; eq; lt; gt]

    let cst_true = string "true" *> return (CstBool true)
    let cst_false = string "false" *> return (CstBool false)
    let cst_int = integer >>| fun i -> CstInt i

    let constant = choice [cst_true; cst_false; cst_int]

    let var = ident >>| fun id -> id

    let atom = choice [
      constant >>| (fun c -> Constant c);
      var >>| (fun v -> Var v);
    ]

    let array_access = 
      var >>= fun v ->
      skip_ws_and_comments *> char '[' *> skip_ws_and_comments *>
      atom >>= fun idx ->
      skip_ws_and_comments *> char ']' *> return (ArrayAccess (v, idx))

    let expr = 
      let rec expr_parser () =
        choice [
          array_access >>| (fun aa -> aa);
          term_parser ();
          (* term_parser () >>= fun first -> *)
          (* many (skip_ws_and_comments *> bin_op >>= fun op -> *) 
                (* skip_ws_and_comments *> term_parser () >>| fun t -> (op, t)) >>= fun rest -> *)
          (* return (List.fold_left (fun acc (op, t) -> BinOp (acc, op, t)) first rest) *)
        ]
      and term_parser () =
        choice [
          atom >>| (fun a -> Atom a);
          (* skip_ws_and_comments *> char '(' *> skip_ws_and_comments *> *)
          (* expr_parser () >>= fun e -> *)
          (* skip_ws_and_comments *> char ')' *> return e *)
        ]
      in
      expr_parser ()

    let expr_cond = 
      expr >>= fun e1 ->
      skip_ws_and_comments *> bin_op_cond >>= fun op ->
      skip_ws_and_comments *> expr >>| fun e2 ->
      (e1, op, e2)


    let labeled_arg = 
      ident >>= fun id ->
      skip_ws_and_comments *> char '=' *> skip_ws_and_comments *>
      expr >>| fun e ->
      LabeledArg (id, e)

    let arg = choice [
      labeled_arg;
      (expr >>| fun e -> ExprArg e);
    ]

    let array_predicate = 
      string "Array" *> skip_ws_and_comments *> char '(' *> skip_ws_and_comments *>
      arg >>= fun first_arg ->
      many (skip_ws_and_comments *> char ',' *> skip_ws_and_comments *> arg) >>= fun rest_args ->
      skip_ws_and_comments *> char ')' *> return (first_arg :: rest_args)

    let success = string "Success" *> return ()

    let condition = 
      expr_cond >>= fun cond ->
      skip_ws_and_comments *> string "=>" *> skip_ws_and_comments *>
      success >>| fun s ->
      (cond, s)

    let contract_ensures = choice [
      condition >>| (fun c -> Condition c);
      array_predicate >>| (fun ap -> ArrayPredicate ap);
    ]

    let contract_requires = array_predicate

    let parse_with parser input = 
      match parse_string ~consume:All parser input with
      | Ok result -> result
      | Error msg -> failwith ("Parse error: " ^ msg)

    let parse_expr = parse_with expr
    let parse_contract_ensures = parse_with contract_ensures  
    let parse_contract_requires = parse_with contract_requires


end


