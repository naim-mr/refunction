(*
   ********* Affine Ranking Functions Abstract Domain ************
   Copyright (C) 2012-2014 by Caterina Urban. All rights reserved.
*)

open Typed_syntax
open Apron
open Sig.Ranking
open Tast_to_texpr
open Utils
open Apron_utils
open Sig
open Sig.Domain
open AP_Partition

module AP_Affine (B : AP_PARTITION) : FUNCTION with module B = B = struct
  module B = B
  module N = B.N

  (** [manager]: Apron manager used in the numerical domain [N]*)
  let manager : N.lib Manager.t = N.manager

  (** [rank]: [Bot] undefined function, [Top] undefined function due to
      precision losses, [Fun of Linexpr1.t] Affine function*)
  type rank = Bot | Fun of Linexpr1.t | Top

  type env = B.env
  type t = { ranking : rank; env : env }
  type dim = B.dim

  (* Getter and setter functions *)
  let ranking f = f.ranking
  let env f = f.env
  let set_env env f = { f with env }
  let ap_env env = B.ap_env env
  let vars f = (env f).vars

  let reinit f =
    match f.ranking with Top -> { ranking = Bot; env = env f } | _ -> f

  let bot e = { ranking = Bot; env = e }

  (** [extra_dim]: Apron variable used to extend [env] by one dimension *)
  let extra_dim = Var.of_string "#"

  (** [ap_env_ext env]: APRON environment of [env] extended with [extra_dim] *)
  let ap_env_ext env = Environment.add (ap_env env) [| extra_dim |] [||]

  let zero e = { ranking = Fun (Linexpr1.make (ap_env_ext e)); env = e }
  let top e = { ranking = Top; env = e }
  let init_env () = B.init_env ()

  let add_dim_to_env f dim =
    let b = B.bot f.env in
    let env = B.add_dim_to_env b dim |> B.env in
    match f.ranking with
    | Bot | Top -> { f with env }
    | Fun flin ->
        {
          ranking = Fun (Linexpr1.extend_environment flin (ap_env_ext env));
          env;
        }

  let remove_dim_of_env f dim =
    let b = B.bot f.env in
    let env = B.remove_dim_of_env b dim |> B.env in
    match f.ranking with Bot | Top -> { f with env } | Fun _ -> { f with env }

  (*  Boolean predicates on function *)
  let is_bot f = match f.ranking with Bot -> true | _ -> false
  let defined f = match f.ranking with Fun _ -> true | _ -> false
  let is_top f = match f.ranking with Top -> true | _ -> false

  (** [graph_constraints b fs]: constraints of [b] extended with [#], plus
      [f - # typ 0] for each [(typ, f)] in [fs], and the extended environment *)
  let graph_constraints b fs =
    let env = ap_env_ext (B.env b) in
    let cs = B.ap_constraints b in
    let n = List.length cs in
    let a = Lincons1.array_make env (n + List.length fs) in
    List.iteri
      (fun i c -> Lincons1.array_set a i (Lincons1.extend_environment c env))
      cs;
    List.iteri
      (fun i (typ, f) ->
        let f = Linexpr1.extend_environment f env in
        Linexpr1.set_coeff f extra_dim (Coeff.s_of_int (-1));
        Lincons1.array_set a (n + i) (Lincons1.make f typ))
      fs;
    (a, env)

  (** [abstract1_of_graph b fs]: abstraction of [graph_constraints b fs] *)
  let abstract1_of_graph b fs =
    let a, env = graph_constraints b fs in
    Abstract1.of_lincons_array manager env a

  (** [abstract1_of_hypograph f b]: abstraction of the hypograph of [f] on [b] *)
  let abstract1_of_hypograph f b = abstract1_of_graph b [ (Lincons1.SUPEQ, f) ]

  (** [abstract1_binop op f1 f2 b]: [op] applied to the hypographs of [f1] and
      [f2] on [b] *)
  let abstract1_binop op f1 f2 b =
    let p1 = abstract1_of_hypograph f1 b in
    let p2 = abstract1_of_hypograph f2 b in
    op p1 p2

  (** [filter_constraints p var] returns the list of constraints in [p] where
      [var] appears *)
  let filter_constraints p var =
    let f = ref [] in
    for i = 0 to Lincons1.array_length p - 1 do
      let c = Lincons1.array_get p i in
      if not (Coeff.is_zero (Lincons1.get_coeff c var)) then f := c :: !f
    done;
    !f

  (** [ranking_of_abstract1 p]: the affine function bounding [#] in [p], if [#]
      has a single upper bound in [p] *)
  let ranking_of_abstract1 p cmp =
    match
      filter_constraints (Abstract1.to_lincons_array manager p) extra_dim
    with
    | [ c ] ->
        let f = Lincons1.get_linexpr1 c in
        Linexpr1.set_coeff f extra_dim (Coeff.s_of_int 0);
        Fun f
    | _ -> Top

  let is_eq b f1 f2 =
    (* b = domain of first/second function, f1/f2 = value of first/second function *)
    match (f1.ranking, f2.ranking) with
    | Fun f1, Fun f2 -> abstract1_binop (Abstract1.is_eq manager) f1 f2 b
    | Bot, Bot | Top, Top -> true
    | _ -> false

  let domain_eq b f1 f2 =
    (* b = domain of first/second function, f1/f2 = value of first/second function *)
    match (f1.ranking, f2.ranking) with
    | Fun f1, Fun f2 ->
        let p = abstract1_of_graph b [ (Lincons1.EQ, f1); (Lincons1.EQ, f2) ] in
        let p =
          Abstract1.change_environment manager p (B.env b |> B.ap_env) false
        in
        let cc = Abstract1.to_lincons_array manager p in
        let f = ref [] in
        for i = 0 to Lincons1.array_length cc - 1 do
          f := Lincons1.array_get cc i :: !f
        done;
        B.ap_inner (B.env b) !f
    | Bot, Bot | Top, Top -> b
    | _ -> B.bot (B.env b)

  let is_leq k b f1 f2 =
    (* k = kind of test, b = domain of first/second function, f1/f2 = value of first/second function *)
    match (f1.ranking, f2.ranking) with
    | Fun f1, Fun f2 -> abstract1_binop (Abstract1.is_leq manager) f1 f2 b
    | Bot, Fun _ -> (
        match k with
        | APPROXIMATION -> false
        | COMPUTATIONAL -> true
        | RESILIENCE -> true)
    | Fun _, Bot -> (
        match k with
        | APPROXIMATION -> true
        | COMPUTATIONAL -> false
        | RESILIENCE -> false)
    | Fun _, Top -> (
        match k with
        | APPROXIMATION -> true
        | COMPUTATIONAL -> true
        | RESILIENCE -> false)
    | Top, Fun _ -> (
        match k with
        | APPROXIMATION -> false
        | COMPUTATIONAL -> false
        | RESILIENCE -> true)
    | Bot, _ | _, Top -> true
    | _ -> false

  (** Binary operators on functions *)
  let join_ranking k b f1 f2 =
    (* k = kind of join, b = domain of first/second function, f1/f2 = value of first/second function *)
    match (f1, f2) with
    | Bot, _ -> (
        match k with
        | RESILIENCE -> f2
        | APPROXIMATION -> Bot
        | COMPUTATIONAL -> f2)
    | _, Bot -> (
        match k with
        | RESILIENCE -> f1
        | APPROXIMATION -> Bot
        | COMPUTATIONAL -> f1)
    | Fun f, Top | Top, Fun f -> (
        match k with
        | RESILIENCE -> Fun f
        | APPROXIMATION -> Top
        | COMPUTATIONAL -> Top)
    | Fun f1, Fun f2 -> (
        let p1 = abstract1_of_hypograph f1 b in
        let p2 = abstract1_of_hypograph f2 b in
        match k with
        | RESILIENCE ->
            (* resilience join: overapproximate min(f1,f2) *)
            if Abstract1.is_leq manager p1 p2 then Fun f1
            else if Abstract1.is_leq manager p2 p1 then Fun f2
            else
              let p = Abstract1.meet manager p1 p2 in
              (* p = hypo(f1) inter hypo(f2) =  hypo(min(f1,f2)) *)
              let itv = Abstract1.bound_variable manager p extra_dim in
              if Scalar.is_infty itv.sup = 0 then (
                let f = Linexpr1.make (ap_env_ext (B.env b)) in
                Linexpr1.set_cst f (Coeff.Scalar (ceil_scalar itv.sup));
                Fun f)
              else Top (* otherwise *)
        | APPROXIMATION | COMPUTATIONAL ->
            let p = Abstract1.join manager p1 p2 in
            (* Lemma: hypo(f1) U hypo(f2) =  hypo(max(f1,f2) *)
            (* p = convex hull of hypo(f1) and  hypo(f2) overapproximating hypo(max(f1,f2)) *)
            ranking_of_abstract1 p (fun n -> n = 1))
    | _ -> Top

  let join k b f1 f2 =
    { ranking = join_ranking k b f1.ranking f2.ranking; env = f1.env }

  let meet _ = failwith "nyi"

  let learn_ranking b f1 f2 =
    (* b = domain of first/second function, f1/f2 = value of first/second
       function *)
    match (f1, f2) with
    | Bot, _ | Top, _ | _, Top -> f2
    | _, Bot -> f1
    | Fun f1, Fun f2 ->
        let p = abstract1_binop (Abstract1.join manager) f1 f2 b in
        (* p = convex-hull *)
        ranking_of_abstract1 p (fun n -> n = 1)

  let learn b f1 f2 =
    { ranking = learn_ranking b f1.ranking f2.ranking; env = f1.env }

  let widen_ranking b f1 f2 =
    (* b = domain of first/second function, f1/f2 = value of first/second function *)
    match (f1, f2) with
    | Bot, _ -> f2
    | _, Bot -> f1
    | Fun f1, Fun f2 ->
        let p = abstract1_binop (Abstract1.widening manager) f1 f2 b in
        (* p = widening *)
        ranking_of_abstract1 p (fun n -> n = 1)
    | _ -> Top

  let widen ?(jokers = 0) b f1 f2 =
    { ranking = widen_ranking b f1.ranking f2.ranking; env = f1.env }

  let extend_ranking b1 b2 f1 f2 =
    match (f1, f2) with
    | Fun f1, Fun f2 ->
        let env = ap_env_ext (B.env b1) in
        (* adding special variable # to environment of b *)
        let l1 = List.length (B.ap_constraints b1) + 1 in
        (* l1 = |b1| + 1 *)
        let l2 = List.length (B.ap_constraints b2) + 1 in
        (* l2 = |b2| + 1 *)
        let a1 = Lincons1.array_make env l1
        and a2 = Lincons1.array_make env l2 in
        let i = ref 0 and j = ref 0 in
        List.iter
          (fun c ->
            Lincons1.array_set a1 !i (Lincons1.extend_environment c env);
            i := !i + 1)
          (B.ap_constraints b1);
        (* copying constraints from b1 to a1 *)
        List.iter
          (fun c ->
            Lincons1.array_set a2 !j (Lincons1.extend_environment c env);
            j := !j + 1)
          (B.ap_constraints b2);
        (* copying constraints from b2 to a2 *)
        let f1 = Linexpr1.extend_environment f1 env
        and f2 = Linexpr1.extend_environment f2 env in
        (* extending f1 and f2 with # (fresh copies) *)
        Linexpr1.set_coeff f1 extra_dim (Coeff.s_of_int (-1));
        Lincons1.array_set a1 (l1 - 1) (Lincons1.make f1 Lincons1.SUPEQ);
        (* adding constraint # <= f1 to a1 *)
        Linexpr1.set_coeff f2 extra_dim (Coeff.s_of_int (-1));
        Lincons1.array_set a2 (l2 - 1) (Lincons1.make f2 Lincons1.SUPEQ);
        (* adding constraint # <= f2 to a2 *)
        let p1 = Abstract1.of_lincons_array manager env a1 in
        (* p1 = polyhedra represented by a1 *)
        let p2 = Abstract1.of_lincons_array manager env a2 in
        (* p2 = polyhedra represented by a2 *)
        let p = Abstract1.join manager p1 p2 in
        (* p = convex-hull *)
        let p = Abstract1.to_lincons_array manager p in
        (* converting p into set of constraints *)
        let f = ref [] in
        for i = 0 to Lincons1.array_length p - 1 do
          let c = Lincons1.array_get p i in
          try
            if not (Coeff.is_zero (Lincons1.get_coeff c extra_dim)) then
              f := c :: !f
          with _ -> ()
        done;
        (* f = # *)
        if
          1 <= List.length !f
          (* if there list of constraints on special variable is at least one constraint on # *)
        then
          let f =
            List.map
              (fun c ->
                let c = Lincons1.get_linexpr1 c in
                (* let k = Linexpr1.get_coeff c extra_dim in
               if Coeff.is_scalar k && (Coeff.cmp k (Coeff.s_of_int 0)) < 0 then
               Linexpr1.set_cst c (Linexpr1.get_cst c);
               if Coeff.is_scalar k && (Coeff.cmp k (Coeff.s_of_int 0)) < 0 then
               Linexpr1.iter (fun k x -> Linexpr1.set_coeff c x (Coeff.neg k)) c; *)
                Linexpr1.set_coeff c extra_dim (Coeff.s_of_int 0);
                Fun c)
              !f
          in
          List.fold_left (join_ranking COMPUTATIONAL b2) (List.hd f) (List.tl f)
        else Top (* otherwise *)
    | _ -> f2

  let extend b1 b2 f1 f2 =
    { ranking = extend_ranking b1 b2 f1.ranking f2.ranking; env = f1.env }

  (**)

  let reset f = zero f.env

  let increment_n f n =
    match f with
    | Fun f ->
        let f = Linexpr1.copy f in
        Linexpr1.set_cst f (add_coeff (Linexpr1.get_cst f) (Coeff.s_of_int n));
        Fun f
    | _ -> f

  let predecessor_ranking f = increment_n f (-1)
  let predecessor f = { ranking = predecessor_ranking f.ranking; env = f.env }
  let successor_ranking f = increment_n f 1
  let successor f = { ranking = successor_ranking f.ranking; env = f.env }

  let plus_ranking b f1 f2 =
    (* b = domain of first/second function, f1/f2 = value of first/second
           function *)
    match (f1, f2) with
    | Fun f1, Fun f2 ->
        let env = ap_env_ext (B.env b) in
        let f1 = Linexpr1.extend_environment f1 env
        and f2 = Linexpr1.extend_environment f2 env in
        (* coefficients read from f1/f2 are summed right away and never kept:
           a value read from an APRON expression may not stay valid *)
        let f = Linexpr1.make env in
        let sum x =
          Linexpr1.set_coeff f x
            (add_coeff (Linexpr1.get_coeff f1 x) (Linexpr1.get_coeff f2 x))
        in
        let ivars, rvars = Environment.vars env in
        Array.iter sum ivars;
        Array.iter sum rvars;
        Linexpr1.set_cst f
          (add_coeff (Linexpr1.get_cst f1) (Linexpr1.get_cst f2));
        successor_ranking @@ Fun f
    | _, Bot | Bot, _ -> Bot
    | _, Top | Top, _ -> Top

  let plus b f1 f2 =
    { ranking = plus_ranking b f1.ranking f2.ranking; env = f1.env }

  let bwd_assign_ranking f ((x, t, ext), e) =
    match x with
    | T_var x -> (
        match f with
        | Fun f ->
            let env = Linexpr1.get_env f in
            let e = Texpr1.of_expr env (exp_to_apron e) in
            let f = Linexpr1.copy f in
            let a = Lincons1.array_make env 1 in
            Linexpr1.set_coeff f extra_dim (Coeff.s_of_int (-1));
            Lincons1.array_set a 0 (Lincons1.make f Lincons1.SUPEQ);
            let p = Abstract1.of_lincons_array manager env a in
            let p =
              Abstract1.substitute_texpr manager p (apron_of_var x) e None
            in
            let a = Abstract1.to_lincons_array manager p in
            if 1 = Lincons1.array_length a then (
              let f = Lincons1.get_linexpr1 (Lincons1.array_get a 0) in
              Linexpr1.set_coeff f extra_dim (Coeff.s_of_int 0);
              Linexpr1.set_cst f
                (add_coeff (Linexpr1.get_cst f) (Coeff.s_of_int 1));
              Fun f)
            else Top
        | _ -> f)
    | _ -> raise (Invalid_argument "Box.fwd_assign: unexpected lvalue")

  let bwd_assign f (x, e) =
    { ranking = bwd_assign_ranking f.ranking (x, e); env = f.env }

  let filter f _ = successor f

  (**)

  let print fmt f =
    let first = ref true in
    let rec aux c v =
      match c with
      | Coeff.Scalar s ->
          if v <> "" && Scalar.sgn s = 0 then ()
          else (
            if Scalar.sgn s < 0 then
              if v <> "" && Scalar.equal_int s (-1) then Format.fprintf fmt "-"
              else Format.fprintf fmt "-%s" (Scalar.to_string (Scalar.neg s))
            else if !first then
              if v <> "" && Scalar.equal_int s 1 then ()
              else Format.fprintf fmt "%s" (Scalar.to_string s)
            else if v <> "" && Scalar.equal_int s 1 then Format.fprintf fmt "+"
            else Format.fprintf fmt "+%s" (Scalar.to_string s);
            if v <> "" then Format.fprintf fmt "%s" v;
            first := false)
      | Coeff.Interval i ->
          if Scalar.equal i.Interval.inf i.Interval.sup then
            aux (Coeff.Scalar i.Interval.inf) v
          else (
            if not !first then Format.fprintf fmt "+";
            Format.fprintf fmt "[%s,%s]"
              (Scalar.to_string i.Interval.inf)
              (Scalar.to_string i.Interval.sup);
            if v <> "" then Format.fprintf fmt "%s" v);
          first := false
    in
    let vars = vars f in
    match f.ranking with
    | Fun f ->
        Linexpr1.iter
          (fun v x ->
            try
              let x =
                List.find
                  (fun y ->
                    String.compare (Var.to_string x)
                      (apron_of_var y |> Var.to_string)
                    = 0)
                  vars
              in
              Format.fprintf Format.str_formatter "$%s{%s}"
                (Z.to_string x.var_id) x.var_name;
              aux v (Format.flush_str_formatter ())
            with Not_found -> ())
          f;
        aux (Linexpr1.get_cst f) ""
    | Bot -> Format.fprintf fmt "bottom"
    | Top -> Format.fprintf fmt "top"
end

module AB = AP_Affine (B)
module AO = AP_Affine (O)
module AP = AP_Affine (P)
