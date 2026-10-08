(*   
     ********* Forward Iterator ************
   Copyright (C) 2012-2014 by Caterina Urban. All rights reserved.
*)

open Typed_syntax
open InvMap
open Apron
open Sig
open Sig.Ranking
open Sig.Domain
open Config
open Semantics
open Utils.Datatypes
open VarSet
open Domains.Taint

module ForwardIterator (B : PARTITION) = struct
  let fwdTaintMap_print fmt m =
    InvMap.iter
      (fun l a ->
        Format.fprintf fmt "%a: %s\n" label_print l
          (VarSet.fold (fun v acc -> v.var_name ^ " -- " ^ acc) a ""))
      m

  let fwdInvMap_print fmt m iter printkey =
    iter (fun l a -> Format.fprintf fmt "%a: %a\n" printkey l B.print a) m

  let fwdInvMap = ref InvMap.empty
  let fwdSummaryMap : B.t StringMap.t ref = ref StringMap.empty
  let addFwdInv l (a : B.t) = fwdInvMap := InvMap.add l a !fwdInvMap

  let blockLabel b =
    match b with T_empty (l, _) -> l | T_stat ((l, _), _, _) -> l

  type ctx = {
    env : B.env;
    global : Typed_syntax.block;
    funcs : func StringMap.t;
    prog : Typed_syntax.prog;
    f_cur : func;
    summary : bool;
    cp : string list;
  }
  (* compute invariant map based on forward analysis *)

  let rec fwdStm ctx p s =
    let fwd_assign, join, filter, is_leq =
      (B.fwd_assign, B.join COMPUTATIONAL, B.fwd_filter, B.is_leq COMPUTATIONAL)
    in
    match s with
    | T_label _ | T_print _ | T_add_var (_, None) | T_del_var _ -> p
    | T_RETURN ->
        (* if ctx.summary then
          if not (StringMap.mem ctx.f_cur.func_name !fwdSummaryMap) then
            fwdSummaryMap := StringMap.add ctx.f_cur.func_name p !fwdSummaryMap
          else
            fwdSummaryMap :=
              StringMap.update ctx.f_cur.func_name
                (Option.map (fun (prev : B.t) -> B.join prev p))
                !fwdSummaryMap; *)
        B.bot ctx.env
    | T_add_var (v, Some (e, t, ext)) ->
        fwd_assign p ((T_var v, v.var_typ, ext), (e, t, ext))
    | T_assign (lval, rval) -> (
        match lval with
        | T_var v, typ, ext -> fwd_assign p ((T_var v, v.var_typ, ext), rval)
        | T_deref (T_var v, typ, ext), _, _ ->
            let v =
              {
                v with
                var_name = Printf.sprintf "*%s" v.var_name;
                var_typ = Typed_syntax.deref_typ v.var_typ;
              }
            in
            fwd_assign p ((T_var v, v.var_typ, ext), rval)
        | _ -> failwith "nyi")
    | T_assert (b, l) -> filter p b
    | T_expr _ | T_assume _ -> p
    | T_if (b, s1, s2) ->
        let p1 = fwdBlk ctx (filter p b) s1 in
        let p2 = fwdBlk ctx (filter p (neg_bexp b)) s2 in
        if ctx.summary then (
          Format.fprintf !fmt "neg b: %a\n" Typed_syntax.pp_expr_ext
            (neg_bexp b);
          Format.fprintf !fmt "p: %a\n" B.print p;
          Format.fprintf !fmt "p1: %a\n" B.print p1;
          Format.fprintf !fmt "p2: %a\n" B.print p2;
          Format.fprintf !fmt "join p1 p2: %a\n" B.print (join p1 p2));
        join p1 p2
    | T_while ((l, _), b, s) ->
        let rec aux i p2 n =
          let i' = join p p2 in
          if !tracefwd && not !minimal then (
            Format.fprintf !fmt "### %a:%i ###:\n" label_print l n;
            Format.fprintf !fmt "p: %a\n" B.print p;
            Format.fprintf !fmt "i: %a\n" B.print i;
            Format.fprintf !fmt "p2: %a\n" B.print p2;
            Format.fprintf !fmt "i': %a\n" B.print i');
          if is_leq i' i then i
          else
            let i'' = if n <= !joinfwd then i' else B.widen i i' in
            if !tracefwd && not !minimal then
              Format.fprintf !fmt "i'': %a\n" B.print i'';
            aux i'' (fwdBlk ctx (B.fwd_filter i'' b) s) (n + 1)
        in
        let i = B.bot ctx.env in
        let p2 = fwdBlk ctx (filter i b) s in
        let p = aux i p2 1 in
        addFwdInv l p;
        filter p (neg_bexp b)
    | T_call (f, ss) -> fwdBlk ctx p f.func_body
    | T_BREAK -> raise (Invalid_argument "bwdStm:T_BREAK")

  and fwdBlk ctx (p : B.t) (b : block) : B.t =
    match b with
    | T_empty (l, _) ->
        if !tracefwd && not !minimal then
          Format.fprintf !fmt "### %a ###: %a\n" label_print l B.print p;
        if not ctx.summary then addFwdInv l p;
        p
    | T_stat ((l, _), (s, _), b) ->
        if !tracefwd && not !minimal then
          Format.fprintf !fmt "### %a ###: %a\n" label_print l B.print p;
        if not ctx.summary then addFwdInv l p;
        fwdBlk ctx (fwdStm ctx p s) b

  (* Assgined block: return set of variables assigned in a block (only syntactic) *)
  (* let rec fwdTStm funcs p s =
    let open Taint in
    match s with
    | A_label _ -> p
    | A_return -> p
    | A_assign ((A_var x, _), (A_INPUT, _)) -> add x p
    | A_assign ((A_var x, _), (A_RANDOM, _)) ->
        filter (fun v -> String.compare v.varId x.varId != 0) p
    | A_assign ((A_var x, _), (e, l)) ->
        let e_vars = avars (e, l) in
        if is_bot (meet e_vars p) then add x p
        else filter (fun v -> String.compare v.varId x.varId != 0) p
    | A_assign (_, _) -> p
    | A_assert _ -> p
    | A_if ((b, ba), s1, s2) ->
        let assigned_vars = join (assigned s1) (assigned s2) in
        let r1 = fwdTBlk funcs p s1 in
        let r2 = fwdTBlk funcs p s2 in
        let iflow = if taint_b (b, ba) p then assigned_vars else VarSet.empty in
        join (join (snd r1) (snd r2)) iflow
    | A_while (l, (b, ba), s) ->
        let rec aux i p2 =
          if VarSet.subset i p2 then i
          else aux p2 (fwdTStm funcs p2 (A_if ((b, ba), s, A_empty l)))
        in
        let i = p in
        let p2 = fwdTStm funcs i (A_if ((b, ba), s, A_empty l)) in
        let p = aux i p2 in
        addFwdTaint l p;
        p
    | A_call (f, ss) ->
        let f = StringMap.find f funcs in
        let p = List.fold_left (fun ap (s, _) -> fwdTStm funcs p s) p ss in
        snd (fwdTBlk funcs p f.funcBody)
    | A_recall (f, ss) -> raise (Invalid_argument "fwdStm:A_recall")

  and fwdTBlk funcs p (b : block) =
    match b with
    | A_empty l ->
        addFwdTaint l p;
        (!fwdTaintMap, p)
    | A_block (l, (s, _), b) ->
        Format.printf "%a: %s\n" label_print l
          (VarSet.fold (fun x acc -> acc ^ "-" ^ x.varName) p "");
        let p' = fwdTStm funcs p s in
        addFwdTaint l p;
        fwdTBlk funcs p' b *)

  (* Detect an input source possibly wrapped in casts, e.g. the rhs of
     `char x = (char) input(id)` is T_unary (A_cast _, (T_INPUT id, ...)). *)
  let rec input_of_expr (e : Typed_syntax.expr) : string option =
    match e with
    | T_input (id, _) -> Some id
    | _ -> (
        match unbox_cast e with
        | Some (e', _) -> input_of_expr e'
        | None -> None)

  let rec fwdTStm ctx p s =
    let open Taint in
    match s with
    | T_label _ | T_print _ | T_add_var (_, None) | T_del_var _ -> p
    | T_RETURN ->
        (* if ctx.summary then
                if not (StringMap.mem ctx.f_cur.func_name !fwdSummaryMap) then
                  fwdSummaryMap := StringMap.add ctx.f_cur.func_name p !fwdSummaryMap
                else
                  fwdSummaryMap :=
                    StringMap.update ctx.f_cur.func_name
                      (Option.map (fun (prev : B.t) -> B.join prev p))
                      !fwdSummaryMap; *)
        p
    | T_add_var (v, Some (e, t, ext)) -> (
        (* x = input(id), possibly through casts, e.g. (char) input(id) *)
        match input_of_expr e with
        | Some id -> if not (List.mem id ctx.cp) then add v p else p
        | None ->
            let e_vars = vars_in_expr e in
            if not (is_bot (meet e_vars p)) then add v p
            else filter (fun x -> Z.compare v.var_id x.var_id != 0) p)
    | T_assign (lval, rval) -> (
        match lval with
        | T_var v, typ, ext -> (
            let e, _, _ = rval in
            let e_vars = vars_in_expr e in
            if not (is_bot (meet e_vars p)) then add v p
            else
              (* x = input(id), possibly through casts, e.g. (char) input(id) *)
              match input_of_expr e with
              | Some id -> if not (List.mem id ctx.cp) then add v p else p
              | None -> filter (fun x -> Z.compare v.var_id x.var_id != 0) p)
        | _ -> failwith "nyi")
    | T_assert (b, l) -> p
    | T_expr _ | T_assume _ -> p
    | T_if ((b, _, _), s1, s2) ->
        let assigned_vars = join (assigned s1) (assigned s2) in
        let r1 = fwdTBlk ctx p s1 in
        let r2 = fwdTBlk ctx p s2 in
        let iflow = if is_tainted b p then assigned_vars else VarSet.empty in
        join (join r1 r2) iflow
    | T_while (l, b, s) ->
        let rec aux i p2 =
          if VarSet.subset i p2 then i
          else aux p2 (fwdTStm ctx p2 (T_if (b, s, T_empty l)))
        in
        let i = p in
        let p2 = fwdTStm ctx i (T_if (b, s, T_empty l)) in
        let p = aux i p2 in
        addFwdTaint l p;
        p
    | T_call (f, ss) -> fwdTBlk ctx p f.func_body
    | T_BREAK -> raise (Invalid_argument "bwdStm:T_BREAK")

  and fwdTBlk ctx p (b : block) : VarSet.t =
    match b with
    | T_empty l ->
        if not ctx.summary then addFwdTaint l p;
        p
    | T_stat (l, (s, _), b) ->
        if not ctx.summary then addFwdTaint l p;
        fwdTBlk ctx (fwdTStm ctx p s) b

  and fwdTaintMap : VarSet.t InvMap.t ref = ref InvMap.empty

  and addFwdTaint (l, _) (a : VarSet.t) =
    fwdTaintMap := InvMap.add l a !fwdTaintMap

  let analyze ?(reachability = true) ?(precondition = Some dummy_precond)
      ?(cp = []) ?(env = B.init_env ()) prog =
    let block, funcmap, varmap = prog in
    let f = StringMap.find !Config.main funcmap in
    let s = f.func_body in
    (* dumb but temporary *)
    let module Init = EnvInit.Make (B) in
    let f_env, vars = Init.env prog in
    if !tracefwd && not !minimal then
      Format.fprintf !fmt "\nForward Analysis Trace:\n";
    let startfwd = Sys.time () in
    let ctx =
      {
        env;
        global = block;
        funcs = funcmap;
        prog;
        f_cur = f;
        summary = true;
        cp;
      }
    in
    (* StringMap.iter
      (fun _ f ->
        Printf.printf "\n iter f.func_name %s <> %s %b \n" f.func_name
          !Config.main
          (f.func_name <> !Config.main);
        if f.func_name <> !Config.main then
          let _ = fwdBlk { ctx with f_cur = f } (B.top env v1) f.func_body in
          ())
      ctx.funcs; *)
    let ctx = { ctx with summary = false } in
    if reachability then (
      let pre =
        match precondition with
        | Some precondition -> B.fwd_filter (B.top env) precondition
        | None -> B.top env
      in
      let _ = fwdBlk ctx (fwdBlk ctx pre block) s in
      let stopfwd = Sys.time () in
      Format.fprintf !fmt "\nForward Summary :\n";
      if not !minimal then
        if !timefwd then
          Format.fprintf !fmt "\nForward Analysis (Time: %f s):\n"
            (stopfwd -. startfwd)
        else Format.fprintf !fmt "\nForward Analysis numerical:\n";
      fwdInvMap_print !fmt !fwdInvMap InvMap.iter label_print);
    let _ = fwdTBlk ctx (VarSet.of_list vars) s in
    let stopfwd = Sys.time () in
    Format.fprintf !fmt "\nForward Taint Summary :\n";
    if not !minimal then
      if !timefwd then
        Format.fprintf !fmt "\nForward Taint Analysis (Time: %f s):\n"
          (stopfwd -. startfwd)
      else Format.fprintf !fmt "\nForward Analysis numerical:\n";
    fwdTaintMap_print !fmt !fwdTaintMap;

    ()
end
