(***************************************************)
(*                                                 *)
(*   Ranking Function Numerical Domain Partition   *)
(*                                                 *)
(*                  Caterina Urban                 *)
(*     École Normale Supérieure, Paris, France     *)
(*                   2012 - 2015                   *)
(*                                                 *)
(***************************************************)

open Typed_syntax
open Apron
open Tast_to_texpr
open Sig.Constraints
open Sig.Ranking
open Sig.Domain
open AP_LinearConstraint
open Utils.Apron_utils

(** Single partition of the domain of a ranking function represented by an APRON
    numerical abstract domain. *)
module AP_Partition (N : AP_NUMERICAL) (C : AP_CONSTRAINT) : AP_PARTITION =
struct
  module C = C
  module N = N
  module BanalApron = Banal_apron_domain.ApronDomain (N)

  type env = C.env
  type dim = var

  type t = {
    constraints : C.t list; (* representation as list of constraints *)
    env : C.env; (* environements over which the constraints are defined *)
  }

  type apron_t = N.lib Abstract1.t
  (** An element of the numerical abstract domain. *)

  let conjunction t =
    List.fold_right
      (fun c cs ->
        (* warning: fold_left impacts speed and result of the analysis *)
        try
          (* equality constraints are turned into pairs of inequalities *)
          let c1, c2 = C.expand c in
          c1 :: c2 :: cs
        with Invalid_argument _ -> c :: cs)
      t.constraints []

  (* the node-constraint domain is already linear, so the APRON projection is
     just the raw constraints of the conjunction *)
  let ap_constraints t = List.map (fun (c : C.t) -> c.cons) (conjunction t)
  let env t = t.env
  let set_env env t = { t with env }

  (** The current underlying APRON environment. *)
  let ap_env env = env.ap_env

  (** The current list of variables used by the constraints i.e bind in the
      APRON environment. *)
  let vars t = t.env.vars

  (** Creates an APRON manager depending on the numerical abstract domain. *)

  let manager = N.manager
  (**)

  (** Converts t into an apron_t *)
  let to_apron_t (t : t) : apron_t =
    let ap_env = env t |> ap_env in
    let a = Lincons1.array_make ap_env (List.length t.constraints) in
    let i = ref 0 in
    List.iter
      (fun (c : C.t) ->
        Lincons1.array_set a !i c.cons;
        i := !i + 1)
      t.constraints;
    Abstract1.of_lincons_array manager ap_env a

  (** Converts apront_t into t *)
  let of_apron_t env (a : apron_t) : t =
    let a = Abstract1.to_lincons_array manager a in
    let (cs : C.t list ref) = ref [] in
    for i = 0 to Lincons1.array_length a - 1 do
      cs := { cons = Lincons1.array_get a i; env } :: !cs
      (*TODO: normalization *)
    done;
    { constraints = !cs; env }

  (** Returns the bottom elements: a singleton of an unsat constraint*)

  let bot e = { constraints = [ C.make_unsat e ]; env = e }
  let inner e cs = { constraints = cs; env = e }

  let ap_inner e cs =
    inner e (List.map (fun c -> ({ cons = c; env = e } : C.t)) cs)

  (** Returns the top elements: an empty list <-> no constraints*)
  let top e = { constraints = []; env = e }

  let init_env () = C.init_env ()
  let remove_dim_of_env t dim = { t with env = C.remove_dim_of_env t.env dim }

  let dim_in_env t dim =
    vars t |> List.exists (fun v -> Z.compare v.var_id dim.var_id = 0)

  let print fmt b =
    let env = env b in
    let b = to_apron_t b in
    let a = Abstract1.to_lincons_array manager b in
    let cs = ref [] in
    for i = 0 to Lincons1.array_length a - 1 do
      cs := Lincons1.array_get a i :: !cs
    done;
    match !cs with
    | [] -> Format.fprintf fmt "top"
    | x :: _ ->
        if C.is_bot { cons = x; env } then Format.fprintf fmt "bottom"
        else
          let i = ref 1 and l = List.length !cs in
          List.iter
            (fun c ->
              C.print fmt { cons = c; env };
              if !i = l then () else Format.fprintf fmt " && ";
              i := !i + 1)
            !cs

  let add_dim_to_env t dim = { t with env = C.add_dim_to_env t.env dim }
  (**)

  let lift1_apron op b = to_apron_t b |> op manager
  let is_bot = lift1_apron Abstract1.is_bottom

  let is_leq kind b1 b2 =
    let b1 = to_apron_t b1 in
    let b2 = to_apron_t b2 in
    Abstract1.is_leq manager b1 b2

  (**)

  let rec split ?(pow = 5.) b =
    let env = b.env in
    (* count occurrences of variables within the polyhedral constraints *)
    let blookup =
      let filter_equality =
        List.filter
          (fun (c : C.t) -> not (Lincons1.get_typ c.cons = Lincons1.EQ))
          b.constraints
      in
      match filter_equality with
      | [] -> b
      | _ -> { b with constraints = filter_equality }
    in
    let occ =
      List.map
        (fun x ->
          let o =
            List.fold_left
              (fun ao c -> if C.var x c then ao + 1 else ao)
              0 blookup.constraints
          in
          (x, o))
        (vars b)
    in
    (* selecting the variable with less occurrences *)
    let x =
      fst
        (List.hd
           (List.sort
              (fun (x1, o1) (x2, o2) ->
                if
                  x1.var_name = Z.to_string x1.var_id
                  && x2.var_name != Z.to_string x2.var_id
                then 1
                else if
                  x1.var_name = Z.to_string x1.var_id
                  && x2.var_name = Z.to_string x2.var_id
                then -1
                else compare o1 o2)
              occ))
    in
    (* creating an APRON variable *)
    let v = apron_of_var x in
    (* creating an APRON polyhedra *)
    let ap_env = ap_env env in
    let a = Lincons1.array_make ap_env (List.length b.constraints) in
    let i = ref 0 in
    List.iter
      (fun (c : C.t) ->
        Lincons1.array_set a !i c.cons;
        i := !i + 1)
      b.constraints;
    let p = Abstract1.of_lincons_array manager ap_env a in
    (* creating an APRON polyhedra *)
    (* getting the interval of variation of the variable in the polyhedra *)
    let i = Abstract1.bound_variable manager p v in
    (* splitting the interval making assumtions *)
    let inf = i.Interval.inf in
    let sup = i.Interval.sup in
    if 1 = Scalar.is_infty sup then (
      if -1 = Scalar.is_infty inf then (
        (* infinite domain: for -inf <= v <= +oo*)
        let e = Linexpr1.make ap_env in
        Linexpr1.set_coeff e v (Coeff.s_of_int 1);
        Linexpr1.set_cst e (Coeff.s_of_int (-1));
        let c = Lincons1.make e Lincons1.SUPEQ in
        (* split on : c = v >= -1 *)
        assert (
          not (is_bot { constraints = { cons = c; env } :: b.constraints; env }));
        assert (
          not
            (is_bot
               {
                 constraints = C.negate { cons = c; env } :: b.constraints;
                 env;
               }));
        ( { constraints = { cons = c; env } :: b.constraints; env },
          { constraints = C.negate { cons = c; env } :: b.constraints; env } ))
      else if
        (*  m <= v <= +oo *)
        pow > 30.
      then (
        assert (not (is_bot { constraints = b.constraints; env }));
        ( { constraints = b.constraints; env },
          { constraints = b.constraints; env } ))
      else
        let p2 = 2. ** pow in
        if Scalar.cmp inf (Scalar.of_float p2) > 0 then
          split ~pow:(2. ** (pow +. 1.)) b
        else
          let mid = int_of_float p2 in
          let e = Linexpr1.make ap_env in
          Linexpr1.set_coeff e v (Coeff.s_of_int 1);
          Linexpr1.set_cst e
            (Coeff.Scalar (mul_scalar (Scalar.of_int (-1)) inf));
          let c = Lincons1.make e Lincons1.SUPEQ in
          (*  c =  v  >= m  *)
          let e1 = Linexpr1.make ap_env in
          Linexpr1.set_coeff e1 v (Coeff.s_of_int (-1));
          Linexpr1.set_cst e1 (Coeff.s_of_int mid);
          let c1 = Lincons1.make e1 Lincons1.SUPEQ in
          let e3 = Linexpr1.make ap_env in
          Linexpr1.set_coeff e3 v (Coeff.s_of_int 1);
          Linexpr1.set_cst e3 (Coeff.s_of_int (-mid));
          let c3 = Lincons1.make e3 Lincons1.SUPEQ in
          (* c3 =  v >= 2 ^ n *)
          (* split on: 
                a- c && c1 ==  m <= v <= 2^n
                b- c3      ==  2^n <= v <= +oo
              
              *)
          assert (
            not
              (is_bot
                 {
                   constraints =
                     { cons = c; env } :: { cons = c1; env } :: b.constraints;
                   env;
                 }));
          assert (
            not
              (is_bot
                 { constraints = { cons = c3; env } :: b.constraints; env }));
          ( {
              constraints =
                { cons = c; env } :: { cons = c1; env } :: b.constraints;
              env;
            },
            { constraints = { cons = c3; env } :: b.constraints; env } ))
    else if -1 = Scalar.is_infty inf then (
      (* -oo <= v <= M*)
      let mid =
        if Scalar.cmp sup (Scalar.of_int 0) >= 0 then
          div_scalar sup (Scalar.of_int 2)
        else mul_scalar sup (Scalar.of_int 2)
      in
      let e = Linexpr1.make ap_env in
      Linexpr1.set_coeff e v (Coeff.s_of_int (-1));
      Linexpr1.set_cst e (Coeff.Scalar sup);
      let c = Lincons1.make e Lincons1.SUPEQ in
      (* c ==  v <= (M ) *)
      let e1 = Linexpr1.make ap_env in
      Linexpr1.set_coeff e1 v (Coeff.s_of_int 1);
      Linexpr1.set_cst e1 (Coeff.Scalar (Scalar.neg mid));
      let c1 = Lincons1.make e1 Lincons1.SUPEQ in
      (* c1 ==  v >= M/2 *)
      let e2 = Linexpr1.make ap_env in
      Linexpr1.set_coeff e2 v (Coeff.s_of_int (-1));
      Linexpr1.set_cst e2 (Coeff.Scalar mid);
      let c2 = Lincons1.make e2 Lincons1.SUPEQ in
      (* c2 ==   M/2 >= v   *)
      (* split on: 
             a- c1 && c2 ==  M/2 <= v <= M -1 
             b- c        ==  -oo<= v <= M/2
        *)
      assert (
        not
          (is_bot
             {
               constraints =
                 { cons = c; env } :: { cons = c1; env } :: b.constraints;
               env;
             }));
      assert (
        not (is_bot { constraints = { cons = c2; env } :: b.constraints; env }));
      ( {
          constraints = { cons = c; env } :: { cons = c1; env } :: b.constraints;
          env;
        },
        { constraints = { cons = c2; env } :: b.constraints; env } ))
    else if Scalar.equal inf sup then (
      (* -m <= v <= m : v == m *)
      (* let e = Linexpr1.make env in
        Linexpr1.set_coeff e v (Coeff.s_of_int 1) ;
        Linexpr1.set_cst e (Coeff.Scalar (mulScalar (Scalar.of_int (-1)) inf));
        let c = Lincons1.make e Lincons1.SUPEQ in *)
      (* split on: 
             c == v >= m && v<=m
        *)
      assert (not (is_bot { constraints = b.constraints; env }));
      assert (not (is_bot { constraints = b.constraints; env }));
      ( { constraints = b.constraints; env },
        { constraints = b.constraints; env } ))
    else
      (* m <= v <= M *)
      let e = Linexpr1.make ap_env in
      Linexpr1.set_coeff e v (Coeff.s_of_int 1);
      let s = add_scalar sup inf in
      let s = div_scalar s (Scalar.of_int 2) in
      (* s = ((m + M) / 2 *)
      Linexpr1.set_cst e (Coeff.Scalar (Scalar.neg s));
      let c = Lincons1.make e Lincons1.SUPEQ in
      (* c = x >= ((m + M) / 2)   *)
      let e2 = Linexpr1.make ap_env in
      Linexpr1.set_coeff e2 v (Coeff.s_of_int (-1));
      Linexpr1.set_cst e2 (Coeff.Scalar sup);
      let c2 = Lincons1.make e2 Lincons1.SUPEQ in
      (* c2 = x <= M *)
      let e3 = Linexpr1.make ap_env in
      Linexpr1.set_coeff e3 v (Coeff.s_of_int (-1));
      Linexpr1.set_cst e3 (Coeff.Scalar s);
      let c3 = Lincons1.make e3 Lincons1.SUPEQ in
      (* c3 = x <= ((m + M / 2) + 1) *)
      let e4 = Linexpr1.make ap_env in
      Linexpr1.set_coeff e4 v (Coeff.s_of_int 1);
      Linexpr1.set_cst e4 (Coeff.Scalar inf);
      let c4 = Lincons1.make e2 Lincons1.SUPEQ in
      (* c4 = x >= m *)
      (* split on: 
             a- c && c2   == ((m + M / 2) + 1) <= v <= M 
             b- c3 && c4  ==  m <= v <= ((m + M / 2) ) 
        *)
      assert (
        not
          (is_bot
             {
               constraints =
                 { cons = c; env } :: { cons = c2; env } :: b.constraints;
               env;
             }));
      assert (
        not
          (is_bot
             {
               constraints =
                 { cons = c3; env } :: { cons = c4; env } :: b.constraints;
               env;
             }));
      ( {
          constraints = { cons = c; env } :: { cons = c2; env } :: b.constraints;
          env;
        },
        {
          constraints =
            { cons = c3; env } :: { cons = c4; env } :: b.constraints;
          env;
        } )

  let lift2_apron op b1 b2 =
    let env = env b1 in
    let b1 = to_apron_t b1 in
    let b2 = to_apron_t b2 in
    let b = op manager b1 b2 in
    of_apron_t env b

  let join kind = lift2_apron Abstract1.join
  let widen ?(jokers = 2) = lift2_apron Abstract1.widening
  let meet kind = lift2_apron Abstract1.meet

  (**)

  let add_var_to_env =
   fun env id ->
    { env with ap_env = Environment.add env.ap_env [| Var.of_string id |] [||] }

  let mem_var env id = Environment.mem_var env.ap_env (Var.of_string id)

  let remove_var_of_env =
   fun env id ->
    { env with ap_env = Environment.remove env.ap_env [| Var.of_string id |] }

  let fwd_assign b ((x, t, ext), e) =
    match x with
    | T_var x when String.starts_with ~prefix:"nondet_" x.var_name -> b
    | T_var x ->
        let env = env b in
        let ap_env = ap_env env in
        let e = Texpr1.of_expr ap_env (exp_to_apron e) in
        let b =
          Abstract1.assign_texpr manager (to_apron_t b) (apron_of_var x) e None
        in
        of_apron_t env b
    | _ -> raise (Invalid_argument "fwd_assign: unexpected lvalue")

  let ubwd_assign (t : t) ((x, typ, ext), e) =
    match x with
    | T_var x ->
        if not N.supports_underapproximation then
          raise
            (Invalid_argument
               "Underapproximation not supported by this abstract domain, use \
                polyhedra instead");
        let env = env t in
        let at = to_apron_t t in
        let top = Abstract1.top manager (Abstract1.env at) in
        let pre = top in
        (* use top as pre environment *)
        let assigned = BanalApron.bwd_assign at () (STRONG x) e pre in
        of_apron_t env assigned
    | _ -> raise (Invalid_argument "ubwd_assign: unexpected lvalue")

  let bwd_assign ?(controllable = false) b (lv, e) =
    let (x, t, ext) : expr typed = lv in
    match x with
    | T_var x ->
        let f manager b (x, e) : t =
          let env = env b in
          let ap_env = ap_env env in
          let e = Texpr1.of_expr ap_env (exp_to_apron e) in
          let b =
            Abstract1.substitute_texpr manager (to_apron_t b) (apron_of_var x) e
              None
          in
          of_apron_t env b
        in
        let b1 = f manager b (x, e) in
        (* A-controlled assignment on polyhedra: dedicated treatment of the
           redundant constraints. [controllable] is only set by the ATL
           iterator. *)
        if controllable && N.kind = Polyhedra then
          let env = env b in
          let ap_env = ap_env env in
          let p = to_apron_t b1 in
          let box_constraints : C.t list =
            List.concat_map
              (fun (var : var) ->
                let v = apron_of_var var in
                let itv = Abstract1.bound_variable manager p v in
                let inf = itv.Interval.inf in
                let sup = itv.Interval.sup in
                let lower =
                  if Scalar.is_infty inf = 0 then (
                    let e = Linexpr1.make ap_env in
                    Linexpr1.set_coeff e v (Coeff.s_of_int 1);
                    Linexpr1.set_cst e (Coeff.Scalar (Scalar.neg inf));
                    [ ({ cons = Lincons1.make e Lincons1.SUPEQ; env } : C.t) ])
                  else []
                and upper =
                  if Scalar.is_infty sup = 0 then (
                    let e = Linexpr1.make ap_env in
                    Linexpr1.set_coeff e v (Coeff.s_of_int (-1));
                    Linexpr1.set_cst e (Coeff.Scalar sup);
                    [ ({ cons = Lincons1.make e Lincons1.SUPEQ; env } : C.t) ])
                  else []
                in
                lower @ upper)
              (vars b1)
          in

          { b1 with constraints = b1.constraints @ box_constraints }
        else b1
    | _ -> raise (Invalid_argument "bwd_assign: unexpected lvalue")

  let ubwd_filter (t : t) (e : expr typed) : t =
    if not N.supports_underapproximation then
      raise
        (Invalid_argument
           "Underapproximation not supported by this abstract domain, use \
            polyhedra instead");
    let env = env t in
    let at = to_apron_t t in
    let top = Abstract1.top manager (Abstract1.env at) in
    let bot = Abstract1.bottom manager (Abstract1.env at) in
    let pre = top in
    (* use top as pre environment *)
    let filtered = BanalApron.bwd_filter at bot () e () pre in
    of_apron_t env filtered

  let fwd_filter ?(controllable = false) b (e, t, ext) =
    let rec f (manager : 'a Manager.t) b (e, t, ext) =
      match e with
      | T_bool_const True -> b
      | T_bool_const Maybe -> b
      | T_bool_const False -> bot (env b)
      | T_binary (op, (T_var v, _, _), e2)
        when String.starts_with ~prefix:"nondet_" v.var_name ->
          f manager b (T_binary (op, e2, (T_bool_const Maybe, t, ext)), t, ext)
      | T_binary (op, e1, (T_var v, _, ext))
        when String.starts_with ~prefix:"nondet_" v.var_name ->
          f manager b (T_binary (op, e1, (T_bool_const Maybe, t, ext)), t, ext)
      | T_int_const _ | T_var _ ->
          let env = env b in
          let ap_env = ap_env env in
          let e = exp_to_apron (e, t, ext) in
          let e1 = Texpr1.of_expr ap_env e in
          let b = to_apron_t b in
          let c1 = Tcons1.make e1 Tcons1.SUPEQ in
          let eneg =
            Texpr1.of_expr ap_env
              (Texpr1.Unop (Texpr1.Neg, e, Texpr1.Int, Texpr1.Zero))
          in
          let c2 = Tcons1.make eneg Tcons1.SUPEQ in
          let a = Tcons1.array_make ap_env 2 in
          Tcons1.array_set a 0 c1;
          Tcons1.array_set a 1 c2;
          Abstract1.meet_tcons_array manager b a |> of_apron_t env
      | T_unary (A_cast (t, _), e) -> f manager b e
      | T_unary (A_NOT, e) -> neg_bexp e |> f manager b
      | T_unary (A_UNARY_PLUS, e) -> f manager b e
      | T_unary (A_UNARY_MINUS, e) ->
          let env = env b in
          let ap_env = ap_env env in
          let e = exp_to_apron e in
          let b = to_apron_t b in
          let eneg =
            Texpr1.of_expr ap_env
              (Texpr1.Unop (Texpr1.Neg, e, Texpr1.Int, Texpr1.Zero))
          in
          let c = Tcons1.make eneg Tcons1.SUPEQ in
          let a = Tcons1.array_make ap_env 1 in
          Tcons1.array_set a 0 c;
          Abstract1.meet_tcons_array manager b a |> of_apron_t env
      | T_binary (o, e1, e2) -> (
          match o with
          | A_MODULO -> top (env b)
          | A_AND ->
              let b1 = f manager b e1 and b2 = f manager b e2 in
              meet APPROXIMATION b1 b2
          | A_OR ->
              let b1 = f manager b e1 and b2 = f manager b e2 in
              join APPROXIMATION b1 b2
          | A_EQUAL ->
              let bop =
                T_binary
                  ( A_AND,
                    (T_binary (A_GREATER_EQUAL, e1, e2), t, ext),
                    (T_binary (A_GREATER_EQUAL, e2, e1), t, ext) )
              in
              f manager b (bop, t, ext)
          | A_NOT_EQUAL ->
              let bop =
                T_binary
                  ( A_OR,
                    (T_binary (A_GREATER, e1, e2), t, ext),
                    (T_binary (A_LESS, e1, e2), t, ext) )
              in
              f manager b (bop, t, ext)
          | o -> (
              let env = env b in
              let ap_env = ap_env env in
              let b = to_apron_t b in
              match o with
              | A_LESS ->
                  let e =
                    Texpr1.of_expr ap_env
                      (exp_to_apron (T_binary (A_MINUS, e2, e1), t, ext))
                  in
                  let c = Tcons1.make e Tcons1.SUP in
                  let a = Tcons1.array_make ap_env 1 in
                  Tcons1.array_set a 0 c;
                  Abstract1.meet_tcons_array manager b a |> of_apron_t env
              | A_LESS_EQUAL ->
                  let e =
                    Texpr1.of_expr ap_env
                      (exp_to_apron (T_binary (A_MINUS, e2, e1), t, ext))
                  in
                  let c = Tcons1.make e Tcons1.SUPEQ in
                  let a = Tcons1.array_make ap_env 1 in
                  Tcons1.array_set a 0 c;
                  Abstract1.meet_tcons_array manager b a |> of_apron_t env
              | A_GREATER ->
                  let e =
                    Texpr1.of_expr ap_env
                      (exp_to_apron (T_binary (A_MINUS, e1, e2), t, ext))
                  in
                  let c = Tcons1.make e Tcons1.SUP in
                  let a = Tcons1.array_make ap_env 1 in
                  Tcons1.array_set a 0 c;
                  Abstract1.meet_tcons_array manager b a |> of_apron_t env
              | A_GREATER_EQUAL ->
                  let e =
                    Texpr1.of_expr ap_env
                      (exp_to_apron (T_binary (A_MINUS, e1, e2), t, ext))
                  in
                  let c = Tcons1.make e Tcons1.SUPEQ in
                  let a = Tcons1.array_make ap_env 1 in
                  Tcons1.array_set a 0 c;
                  Abstract1.meet_tcons_array manager b a |> of_apron_t env
              | _ -> raise (Invalid_argument "Filter only boolean expression")))
      | _ -> raise (Invalid_argument "Unsupported float")
    in
    let b1 = f manager b (e, t, ext) in
    if !Config.resilience && N.kind = Polyhedra && false then
      let env = env b in
      let ap_env = ap_env env in
      let p = to_apron_t b1 in
      let box_constraints : C.t list =
        List.concat_map
          (fun (var : var) ->
            let v = apron_of_var var in
            let itv = Abstract1.bound_variable manager p v in
            let inf = itv.Interval.inf in
            let sup = itv.Interval.sup in
            let lower =
              if Scalar.is_infty inf = 0 then (
                let e = Linexpr1.make ap_env in
                Linexpr1.set_coeff e v (Coeff.s_of_int 1);
                Linexpr1.set_cst e (Coeff.Scalar (Scalar.neg inf));
                [ ({ cons = Lincons1.make e Lincons1.SUPEQ; env } : C.t) ])
              else []
            and upper =
              if Scalar.is_infty sup = 0 then (
                let e = Linexpr1.make ap_env in
                Linexpr1.set_coeff e v (Coeff.s_of_int (-1));
                Linexpr1.set_cst e (Coeff.Scalar sup);
                [ ({ cons = Lincons1.make e Lincons1.SUPEQ; env } : C.t) ])
              else []
            in
            lower @ upper)
          (vars b1)
      in
      { b1 with constraints = b1.constraints @ box_constraints }
    else b1

  let is_representable = N.is_representable
  (**)
end

module AP_Box : AP_NUMERICAL = struct
  type lib = Box.t

  let kind = Boxes
  let is_representable = Typed_syntax.expr_is_univariate
  let manager = Box.manager_alloc ()
  let supports_underapproximation = false
end

module AP_Oct : AP_NUMERICAL = struct
  type lib = Oct.t

  let kind = Octagons
  let is_representable = Typed_syntax.expr_is_octagonal
  let manager = Oct.manager_alloc ()
  let supports_underapproximation = false
end

module AP_Poly : AP_NUMERICAL = struct
  type lib = Polka.loose Polka.t (* ou Pkgrid.loose Pkgrid.t selon strictness *)

  let kind = Polyhedra

  type t = lib Abstract1.t

  let is_representable = Typed_syntax.expr_is_linear
  let manager : lib Manager.t = Polka.manager_alloc_loose ()
  let supports_underapproximation = true
end

module B = AP_Partition (AP_Box) (AP_LinearConstraint)
(** Single partition of the domain of a ranking function represented by the
    boxes numerical abstract domain. *)

module O = AP_Partition (AP_Oct) (AP_LinearConstraint)
(** Single partition of the domain of a ranking function represented by the
    octagons abstract domain. *)

module P = AP_Partition (AP_Poly) (AP_LinearConstraint)
(** Single partition of the domain of a ranking function represented by the
    polyhedra abstract domain. *)
