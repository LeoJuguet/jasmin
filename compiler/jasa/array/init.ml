open Mopsa
open Sig.Abstraction.Simplified_value
open Universal.Ast
open Stubs.Ast
open Ast
open Bot
open Array_common
module I = Mopsa.ItvUtils.IntItv
module B = Mopsa.ItvUtils.IntBound

(** Module to represent range of index not initialized in a Jasmin Array *)
module ArrayNotInit = struct
  type t = I.t_with_bot with_bot (* interval with empty *)

  let bottom = BOT
  let top = Nb BOT (* empty set *)

  let mk_array_not_init wsize len =
    let wsize = Utils.wsize_to_int wsize in
    Nb (Nb (B.zero, B.of_int ((wsize * len) - 1)))

  let mk_array_init = top
  let is_bottom a = a = BOT
  let subset a1 a2 = bot_included I.included_bot a1 a2
  let join a1 a2 = bot_neutral2 I.join_bot a1 a2
  let meet a1 a2 = bot_absorb2 (fun a1 a2 -> Nb (I.meet_bot a1 a2)) a1 a2
  let widen ctx a1 a2 = join a1 a2
  let fprint = bot_fprint I.fprint_bot
  let print printer a = unformat fprint printer a
end

module SimplifiedValue = struct
  include ArrayNotInit

  include GenValueId (struct
    type nonrec t = ArrayNotInit.t

    let name = "jasmin.array.values.init"
    let display = "array init"
  end)

  let accept_type typ =
    Debug.debug ~channel:name "LE type est %a" pp_typ typ;
    is_jasmin_array_type typ

  include DefaultValueFunctions

  let constant c t =
    Debug.debug ~channel:name "constant";
    match c with _ -> top

  let unop op t a tr = match op with _ -> top
  let binop op t1 a1 t2 a2 tr = match op with _ -> top
end

let () = register_simplified_value_abstraction (module SimplifiedValue)

open Sig.Abstraction.Stateless

module Domain = struct
  include GenStatelessDomainId (struct
    let name = "jasmin.array.init"
  end)

  let mk_init_array ?(mode = STRONG) s =
    mk_attr_var ~mode s "no_init_range" T_int

  let checks = [ CHK_J_NOT_INIT_ARRAY ]
  let init prog man flow = None

  let eval expr man flow =
    let range = erange expr in
    let open Universal.Numeric.Common in
    match ekind expr with
    | E_J_get (access, wsize, var, index) ->
        man.eval ~translate:"Universal" index flow >>$? fun index_univ flow ->
        let index_interval =
          ask_and_reduce man.ask
            (mk_int_interval_query ~fast:false index_univ)
            flow
        in
        let array_init = mk_var (mk_init_array var) range in
        let array_no_init_interval =
          ask_and_reduce man.ask
            (mk_int_interval_query ~fast:false array_init)
            flow
        in
        let wsize = B.of_int @@ Utils.wsize_to_int wsize in
        let scale_index_interval =
          match index_interval with
          | BOT -> BOT
          | Nb (li, hi) -> Nb (B.mul li wsize, B.mul hi wsize)
        in
        (if I.intersect_bot scale_index_interval array_no_init_interval then (
           Debug.debug ~channel:name "ALARM";
           let cs = Flow.get_callstack flow in
           let alarm =
             mk_alarm (A_J_NOT_INIT_ARRAY (var, index_interval)) cs range
           in
           Flow.add_alarm ~warning:true alarm man.lattice flow)
         else Flow.add_safe_check CHK_J_NOT_INIT_ARRAY range flow)
        |> man.eval expr ~route:(Below name)
        |> OptionExt.return
    | E_stub_J_abstract (Init_array, [ evar; i1; i2 ]) -> (
        match ekind evar with
        | E_var (var, mode) ->
            man.eval ~translate:"Universal" i1 flow >>$? fun i1_univ flow ->
            let i1_interval =
              ask_and_reduce man.ask
                (mk_int_interval_query ~fast:false i1_univ)
                flow
            in
            man.eval ~translate:"Universal" i2 flow >>$? fun i2_univ flow ->
            let i2_interval =
              ask_and_reduce man.ask
                (mk_int_interval_query ~fast:false i2_univ)
                flow
            in
            let array_init = mk_var (mk_init_array var) range in
            let array_no_init_interval =
              ask_and_reduce man.ask
                (mk_int_interval_query ~fast:false array_init)
                flow
            in
            let wsize =
              B.of_int @@ Utils.wsize_to_int @@ get_array_type_wsize @@ vtyp var
            in
            let scale_index_interval =
              match (i1_interval, i2_interval) with
              | Nb (li, hi), Nb (li2, hi2) ->
                  Nb (B.mul (B.min li li2) wsize, B.mul (B.max hi hi2) wsize)
              | _ -> BOT
            in
            let is_init_expr =
              mk_bool
                (I.intersect_bot scale_index_interval array_no_init_interval)
                range
            in
            Eval.singleton is_init_expr flow |> OptionExt.return
        | _ ->
            Debug.debug ~channel:name "problem HERE HERE";
            None)
    | _ ->
        Debug.debug ~channel:name "%a" pp_expr expr;
        None

  let update_is_init is_init wsize ?(len = 1) var index value range man flow =
    let open Universal.Numeric.Common in
    man.eval index ~translate:"Universal" flow >>$? fun index_univ flow ->
    let index_interval =
      ask_and_reduce man.ask (mk_int_interval_query ~fast:false index_univ) flow
    in
    let array_init = mk_var (mk_init_array var) range in
    let array_no_init_interval =
      ask_and_reduce man.ask (mk_int_interval_query ~fast:false array_init) flow
    in
    let wsize_B = B.of_int @@ Utils.wsize_to_int wsize in
    let scale_index_interval =
      match index_interval with
      | BOT -> BOT
      | Nb (li, hi) -> Nb (B.mul li wsize_B, B.mul hi wsize_B)
    in
    match scale_index_interval with
    (* No index found *)
    | BOT -> None
    (* Index can take only one value *)
    | Nb ((index_value, _) as index) when I.is_singleton index ->
        if I.intersect_bot scale_index_interval array_no_init_interval then
          match array_no_init_interval with
          | Nb (la, ha) when B.equal la index_value ->
              (* new interval of uninitialized values is (la + len * wisze) *)
              let a, b =
                (B.add la (B.of_int (len * Utils.wsize_to_int wsize)), ha)
              in
              man.exec
                (mk_assign
                   (mk_var (mk_init_array var) range)
                   (mk_constant ~etyp:T_int (C_int_interval (a, b)) range)
                   range)
                flow
              |> OptionExt.return
          | Nb (la, ha) when B.equal ha index_value -> None
          | _ -> None
        else None
    (* Index can take different values, we can not say which cell is correctly initialized *)
    | _ -> None

  let exec stmt man flow =
    let range = srange stmt in
    match skind stmt with
    | S_assign ({ ekind = E_var (var, mode) }, { ekind = E_J_arr_init len }) ->
        let wsize = Utils.wsize_to_int @@ get_array_type_wsize (vtyp var) in
        man.exec
          (mk_assign
             (mk_var (mk_init_array var) range)
             (mk_int_interval 0 (len * 8) range)
             range)
          flow
        |> OptionExt.return
    | S_assign ({ ekind = E_J_Laset (access, wsize, var, index) }, expr)
      when is_jasmin_scalar @@ etyp expr ->
        Debug.debug ~channel:name "assign init array";
        man.eval ~translate:"Universal" expr flow >>$? fun value flow ->
        Debug.debug ~channel:name "assign init array after trad";
        let query = Initialized.mk_scalar_is_init_query value in
        let is_init = ask_and_reduce man.ask query flow in
        if Initialized.Init.is_init is_init then
          update_is_init is_init wsize var index expr range man flow
        else Post.return flow |> OptionExt.return
    | S_assign ({ ekind = E_J_Laset (access, wsize, var, index) }, t) -> None
    | S_assign ({ ekind = E_J_Lasub (access, wsize, len, var, index) }, t) ->
        None
    | S_add ({ ekind = E_var (var, mode) } as v)
      when is_jasmin_array_type @@ etyp v ->
        let len = get_array_type_len (vtyp var) in
        let wsize = Utils.wsize_to_int @@ get_array_type_wsize (vtyp var) in
        man.exec
          (mk_assign
             (mk_var (mk_init_array var) range)
             (mk_int_interval 0 (len * wsize) range)
             range)
          flow
        |> OptionExt.return
    | S_assume { ekind = E_stub_J_abstract (Init_array, args) } ->
        Debug.debug "%a" pp_stmt stmt;
        Post.return flow |> OptionExt.return
    (* | S_assume { ekind = E_unop (O_log_not, { ekind = E_stub_J_abstract (Init_array, args)}) } -> *)
    (*   Post.return flow *)
    (*   |> OptionExt.return *)
    | S_remove ({ ekind = E_var (var, mode) } as v)
      when is_jasmin_array_type @@ etyp v ->
        man.exec (mk_remove_var (mk_init_array var) range) flow
        |> OptionExt.return
    | _ ->
        Debug.debug "%a" pp_stmt stmt;
        None

  let ask : type r. ('a, r) query -> _ man -> _ flow -> ('a, r) cases option =
   fun query man flow ->
    match query with
    (* return if array access is well initialized *)
    | Q_avalue
        ( ({ ekind = E_J_get (access, wsize, var, index) } as expr),
          Integer.Initialized.V_jasmin_scalar_initialized ) ->
        let open Universal.Numeric.Common in
        let range = erange expr in
        let index_interval =
          ask_and_reduce man.ask (mk_int_interval_query ~fast:false index) flow
        in
        let array_init = mk_var (mk_init_array var) range in
        let array_no_init_interval =
          ask_and_reduce man.ask
            (mk_int_interval_query ~fast:false array_init)
            flow
        in
        let wsize_B = B.of_int @@ Utils.wsize_to_int wsize in
        let scale_index_interval =
          match index_interval with
          | BOT -> BOT
          | Nb (li, hi) -> Nb (B.mul li wsize_B, B.mul hi wsize_B)
        in
        let is_init =
          if I.included_bot scale_index_interval array_no_init_interval then
            Integer.Initialized.Init.not_init
          else if I.intersect_bot scale_index_interval array_no_init_interval
          then Integer.Initialized.Init.maybe
          else Integer.Initialized.Init.init
        in
        Cases.singleton is_init flow |> OptionExt.return
    | _ -> None

  let print_expr man flow printer expr = ()
end

let () = register_stateless_domain (module Domain)
