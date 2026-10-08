open InvMap
open Semantics
open Typed_syntax
open Domains
open Sig
open Decision_Tree
open Apron
open ForwardIterator
open AP_Partition
open Config
open VarSet
open Utils
open InvMap
open Datatypes

module type CDA_ITERATOR = sig
  val analyze :
    ?precondition:expr typed option ->
    ?property:'a p ->
    Typed_syntax.prog ->
    bool
end

module Make (S : SEMANTIC) : sig
  include CDA_ITERATOR
end = struct
  module D = S.D
  module B = S.D.B

  (* Bundle commonly used values (AST, Apron env. variable list) to one struct *)

  type env = S.D.B.env

  let fwdMap_print fmt m =
    InvMap.iter
      (fun l a -> Format.fprintf fmt "%a: %a\n" label_print l B.print a)
      m

  module ForwardIteratorB = ForwardIterator (B)

  let bwdMap_print fmt m =
    if !Config.compress then
      InvMap.iter
        (fun l a ->
          Format.fprintf fmt "%a:\n%a\n" label_print l D.print (D.compress a))
        m
    else
      InvMap.iter
        (fun l a -> Format.fprintf fmt "%a:\n%a\n" label_print l D.print a)
        m

  let rec analyze ?(precondition = Some dummy_precond)
      ?(property = S.dummy_prop) prog =
    let module Init = EnvInit.Make (B) in
    let f_env, vars = Init.env prog in
    let env = f_env |> D.lift_fenv in

    let precondition =
      Option.bind precondition (fun e ->
          Some (Typed_syntax.expr_prop_handler e vars))
    in
    (* Conflict driven analysis result *)
    let block, funcmap, elt = prog in
    let f = StringMap.find !Config.main funcmap in
    let i = cda_recursive ~property funcmap env vars block main elt f in
    let block_label block =
      match block with T_empty l -> fst l | T_stat (l, _, _) -> fst l
    in
    if not !minimal then
      Format.fprintf !fmt "\n Final Analysis Result: %a@." D.print i;
    let ret = D.defined ~condition:(Option.get precondition) i in
    Format.fprintf !fmt "Final Analysis Result: ";
    let result = if ret then "TRUE" else "UNKNOWN" in
    Format.fprintf !fmt "%s\n" result;
    S.bwdInvMap :=
      InvMap.update (block_label f.func_body) (fun _ -> Some i) !S.bwdInvMap;
    ret

  and cda_recursive ?(property : 'a p = S.dummy_prop) funcmap env vars block
      main elt f =
    let open S in
    let s = f.func_body in
    let compress () =
      S.bwdInvMap := InvMap.map (fun a -> D.compress a) !S.bwdInvMap
    in
    let reinit () =
      S.bwdInvMap := InvMap.map (fun a -> D.reinit a) !S.bwdInvMap
    in
    let rec aux (b : S.D.B.t) p n =
      (* Forward Analysis *)
      if !tracefwd && not !minimal then
        Format.fprintf !fmt "\nForward Analysis[%i] Trace:\n" n;
      let startfwd = Sys.time () in
      (* Compute the forward analysis starting from the environment b (top at the begining) *)
      let b_env = S.D.B.env b in
      ForwardIteratorB.analyze ~env:b_env (block, funcmap, elt);
      fwdInvMap := !ForwardIteratorB.fwdInvMap;
      (* fwdBlk funcs env vars (fwdBlk funcs env vars b stmts) s in *)
      let stopfwd = Sys.time () in
      if not !minimal then (
        if !timefwd then
          Format.fprintf !fmt "\nForward Analysis[%i] (Time: %f s):\n" n
            (stopfwd -. startfwd)
        else Format.fprintf !fmt "\nForward Analysis[%i]:\n" n;
        fwdMap_print !fmt !S.fwdInvMap);
      (* Backward Analysis *)
      if !tracebwd && not !minimal then
        Format.fprintf !fmt "\nBackward Analysis[%i] Trace:\n" n;
      start := Sys.time ();
      let startbwd = Sys.time () in
      (* 
          Compute the backward analysis for the given Semantic. 
          Refine option is always activated for cda 
      *)
      let tree0 =
        if !analysis = "termination" then S.D.zero env else S.D.bot env
      in
      let i =
        bwdRec ~property funcmap env vars
          (bwdRec ~property funcmap env vars tree0 s)
          block
      in
      let stopbwd = Sys.time () in
      if not !minimal then (
        if !timebwd then
          Format.fprintf !fmt "\nBackward Analysis[%i] (Time: %f s):\n" n
            (stopbwd -. startbwd)
        else Format.fprintf !fmt "\nBackward Analysis[%i]:\n" n;
        bwdMap_print !fmt !S.bwdInvMap);
      if not !minimal then
        if S.D.defined i then
          Format.fprintf !fmt "Analysis[%i] Result: TRUE\n" n
        else Format.fprintf !fmt "Analysis[%i] Result: UNKNOWN\n" n;
      if S.D.defined i || n > !size then
        (* 
          Return if we can already infer the property or if the maximum number of
          iteration is reached 
        *)
        D.learn p (D.compress i)
      else (
        learn := true;
        (* 
          Cumulate the constraints along the path to an undefined piece of
          the ranking function i.e. the conflicts
        *)
        let bs = S.D.conflict i in
        if not !minimal then (
          Format.fprintf !fmt "CONFLICTS: { ";
          List.iter (fun b -> Format.fprintf !fmt "%a; " D.B.print b) bs;
          Format.fprintf !fmt "}\n");
        let i =
          List.fold_left
            (fun (ai : S.D.t) (ab : S.D.B.t) ->
              (* 
                [ai] is a tree,
                [ab] is a contraint toward an undefined leaf the tree
              *)
              if
                S.D.B.is_leq APPROXIMATION b ab
                (* If the current domain [b] from which we start is smaller that the one define by the constraint [ab]
                   we need to split [ab]. 
                   Needed to divide the domain if after one iteration we cannot infer the property
                *)
              then (
                (*
                  [b1] \cup [b2] == ab
                *)
                let b1, b2 = S.D.B.split ~pow:(float_of_int n) ab in
                (* We reinit the leaf that are at top *)
                assert (
                  S.D.B.is_leq APPROXIMATION ab (S.D.B.join APPROXIMATION b1 b2));
                assert (
                  S.D.B.is_leq APPROXIMATION (S.D.B.join APPROXIMATION b1 b2) ab);
                assert (not (S.D.B.is_bot b1));
                assert (not (S.D.B.is_bot b2));
                reinit ();
                compress ();
                if not !minimal then
                  Format.fprintf !fmt "\nASSUME-1: %a\n" S.D.B.print b1;
                (* restart with b1 *)
                let i = aux b1 ai (n + 1) in
                reinit ();
                compress ();
                if not !minimal then
                  Format.fprintf !fmt "\nASSUME-2: %a\n" S.D.B.print b2;
                (* continue with b2*)
                aux b2 i (n + 1))
              else (
                reinit ();
                compress ();
                if not !minimal then
                  Format.fprintf !fmt "\nASSUME: %a\n" S.D.B.print ab;
                aux ab ai (n + 1)))
            i bs
        in
        (* We learn from the cda analysis new part of the domain where the property of interest holds *)
        S.D.learn p (S.D.compress i))
    in
    (* We start from the numerical domain top and decision tree bot *)
    let bot = S.D.bot env in
    aux (S.D.B.top (S.D.f_env bot)) bot 1
end
