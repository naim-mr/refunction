(***************************************************)
(*                                                 *)
(*      The Ranking Functions Abstract Domain      *)
(*                                                 *)
(*                 Caterina Urban                  *)
(*     École Normale Supérieure, Paris, France     *)
(*                   2012 - 2015                   *)
(*          ETH Zurich, Zurich, Switzerland        *)
(*                      2016                       *)
(*                                                 *)
(*              with contributions of              *)
(*                Nathanaël Courant                *)
(*     École Normale Supérieure, Paris, France     *)
(*                      2016                       *)
(*                                                 *)
(***************************************************)

open Typed_syntax
open AP_Affines
open Sig.Domain
open Sig
open Sig.Ranking
open Config
open AP_Ordinals

(** The ranking functions abstract domain is an abstract domain functor T. It is
    parameterized by an auxiliary abstract domain for linear constraints C, and
    an auxiliary abstract domains for functions F, both parameterized by an
    auxiliary numerical abstract domain B. *)

module Decision_Tree (F : FUNCTION) : RANKING_FUNCTION = struct
  module B = F.B (* auxiliary parition abstract domain *)
  module C = B.C (* auxiliary constraints abstract domain *)

  module CMap = Map.Make (struct
    type t = C.t

    let compare = C.compare
  end)

  module L = struct
    type t = C.t * C.t

    let compare (c1, nc1) (c2, nc2) =
      if C.is_leq nc1 c1 then
        if C.is_leq nc2 c2 then C.compare c1 c2 else C.compare c1 nc2
      else if C.is_leq nc2 c2 then C.compare nc1 c2
      else C.compare nc1 nc2
  end

  module LSet = Set.Make (L)

  (** [type tree] The abstract domain manipulates piecewise-defined partial
      functions. These are represented by decision trees, where the decision
      nodes are labeled by linear constraints over the program variables, and
      the leaf nodes are labeled by functions of the program variables. The
      decision nodes recursively partition the space of possible values of the
      program variables and the functions at the leaves provide the
      corresponding upper bounds on the number of program execution steps to
      termination. *)
  type tree = Bot | Leaf of F.t | Node of L.t * tree * tree

  type env = {
    f_env : F.env;
    domain : B.t option; (* current reachable program states *)
  }

  type t = {
    tree : tree; (* current piecewise-defined ranking function *)
    env : env;
  }

  type dim = B.dim

  (** [tree t] returns the current decision tree. *)
  let tree t = t.tree

  let env t = t.env
  let f_env t = t.env.f_env
  let lift_fenv f_env = { f_env; domain = None }

  let print_tree fmt t =
    let rec aux ind fmt t =
      match t with
      | Bot -> Format.fprintf fmt "\n%sNIL" ind
      | Leaf f -> Format.fprintf fmt "\n%sLEAF %a" ind F.print f
      | Node ((c, _), l, r) ->
          Format.fprintf fmt "\n%sNODE %a%a%a" ind C.print c
            (aux (ind ^ "  "))
            l
            (aux (ind ^ "  "))
            r
    in
    aux "" fmt t

  let output_json vars t : Yojson.Safe.t =
    let rec aux t =
      match t with
      | Bot -> `String "BOT"
      | Leaf f -> `Assoc [ ("Leaf", `String (Format.asprintf "%a" F.print f)) ]
      | Node ((c, _), l, r) ->
          `Assoc
            [
              ( "Node",
                `Assoc
                  [
                    ("constraint", `String (Format.asprintf "%a" C.print c));
                    ("left", aux l);
                    ("right", aux r);
                  ] );
            ]
    in
    aux t.tree

  (** [print_graphviz_dot fmt t] Prints a tree in graphviz 'dot' format for
      visualization. http://www.graphviz.org/content/dot-language *)
  let print_graphviz_dot fmt t =
    let nodeId = ref 0 in
    let nextNodeId () =
      let id = !nodeId in
      nodeId := id + 1;
      Printf.sprintf "node%d" id
    in
    let rec aux id fmt t =
      match t with
      | Bot -> Format.fprintf fmt "%s[shape=box,label=\"Nil\"]" id
      | Leaf f -> Format.fprintf fmt "%s[shape=box,label=\"%a\"]" id F.print f
      | Node ((c, _), l, r) ->
          let leftId = nextNodeId () in
          let hiddenId = nextNodeId () in
          let rightId = nextNodeId () in
          Format.fprintf fmt
            "%s[shape=box,style=rounded,label=\"%a\"] ; %s \
             [label=\"\",width=.1,style=invis] ; %s -- %s ; %s -- %s \
             [style=invis] ; %s -- %s [style=dashed] {rank=same %s -- %s -- %s \
             [style=invis]} ; %a; %a"
            id C.print c hiddenId id leftId id hiddenId id rightId leftId
            hiddenId rightId (aux leftId) l (aux rightId) r
    in
    Format.fprintf fmt "graph G { %a }" (aux (nextNodeId ())) t.tree

  (** [tree_labels t] collects the constraints labeling the current decision
      tree. *)
  let tree_labels t =
    let ls = ref LSet.empty in
    let rec aux t =
      match t with
      | Bot | Leaf _ -> ()
      | Node (c, l, r) ->
          aux l;
          aux r;
          ls := LSet.add c !ls
    in
    aux t;
    !ls

  (** [tree_map f_bot f_leaf t] map function for decision tree *)
  let tree_map f_bot f_leaf t : t =
    let rec aux (tree : tree) : tree =
      match tree with
      | Bot -> f_bot
      | Leaf f -> f_leaf f
      | Node (c, l, r) -> Node (c, aux l, aux r)
    in
    { t with tree = aux t.tree }

  (** Sorts (and normalizes the constraints within) a decision tree `t`.

      Let x_1,...,x_k be program variables. We consider all linear constraints
      in a decision tree to have the following normal form: m_1*x_1 + ... +
      m_k*x_k + q >= 0 where m_1,...,m_k,q are integer coefficients. Moreover,
      in order to ensure a canonical representation of the linear constraints,
      we require gcd(|m_1|,...,|m_k|,|q|) = 1 We then impose a total order on
      the linear constraints. In particular, we define such order to be the
      lexicographic order on the coefficients m_1,...,m_k and constant q of the
      linear constraints. *)
  let rec sort_tree t =
    let rec swap_tree t =
      match t with
      | Node ((c, nc), l, r) -> (
          let sl = swap_tree l in
          let sr = swap_tree r in
          if C.is_leq nc c then (* t is normalized *)
            match (sl, sr) with
            | Node ((c1, nc1), l1, r1), Node ((c2, nc2), l2, r2)
              when C.is_eq c1 c2 (* c1 = c2 *) ->
                if C.is_leq c c1 then (* c <= c1 = c2 *)
                  if C.is_eq c c1 then (* c = c1 = c2 *) Node ((c, nc), l1, r2)
                  else (* c < c1 = c2 *) Node ((c, nc), sl, sr)
                else if
                  (* c > c1 = c2 *)
                  C.similar c c1
                then Node ((c1, nc1), l1, Node ((c, nc), r1, r2))
                else
                  let rt = (c, nc) in
                  Node ((c1, nc1), Node (rt, l1, l2), Node (rt, r1, r2))
            | Node ((c1, nc1), l1, r1), Node ((c2, nc2), l2, r2)
              when C.is_leq c1 c2 (* c1 < c2 *) ->
                if C.is_leq c c1 then (* c <= c1 < c2 *)
                  if C.is_eq c c1 then (* c = c1 < c2 *) Node ((c, nc), l1, sr)
                  else (* c < c1 < c2 *) Node ((c, nc), sl, sr)
                else if
                  (* c > c1 < c2 *)
                  C.is_leq c c2
                then
                  (* c1 < c <= c2 *)
                  if C.is_eq c c2 then (* c1 < c = c2 *)
                    if C.similar c c1 then
                      Node ((c1, nc1), l1, Node ((c, nc), r1, r2))
                    else
                      let rt = (c, nc) in
                      let rt1 = (c1, nc1) in
                      Node (rt1, Node (rt, l1, r2), Node (rt, r1, r2))
                  else if
                    (* c1 < c < c2 *)
                    C.similar c2 c && C.similar c c1
                  then Node ((c1, nc1), l1, Node ((c, nc), r1, sr))
                  else
                    let rt = (c, nc) in
                    let rt1 = (c1, nc1) in
                    Node (rt1, Node (rt, l1, sr), Node (rt, r1, sr))
                else if
                  (* c1 < c2 < c *)
                  C.similar c c2 && C.similar c2 c1
                then Node ((c1, nc1), l1, Node ((c, nc), r1, r2))
                else
                  let rt = (c, nc) in
                  let rt2 = (c2, nc2) in
                  Node
                    ( (c1, nc1),
                      Node (rt2, Node (rt, l1, l2), Node (rt, l1, r2)),
                      Node (rt2, Node (rt, r1, l2), Node (rt, r1, r2)) )
            | Node ((c1, nc1), l1, r1), Node ((c2, nc2), l2, r2)
              when C.is_leq c2 c1 (* c1 > c2 *) ->
                if C.is_leq c c2 then (* c <= c2 < c1 *)
                  if C.is_eq c c2 then (* c = c2 < c1 *) Node ((c, nc), sl, r2)
                  else (* c < c2 < c1 *) Node ((c, nc), sl, sr)
                else if
                  (* c > c2 < c1 *)
                  C.is_leq c c1
                then
                  (* c2 < c <= c1 *)
                  if C.is_eq c c1 then (* c2 < c = c1 *)
                    if C.similar c c2 then Node ((c, nc), l1, r2)
                    else
                      let rt = (c, nc) in
                      let rt2 = (c2, nc2) in
                      Node (rt2, Node (rt, l1, l2), Node (rt, l1, r2))
                  else if
                    (* c2 < c < c1 *)
                    C.similar c1 c && C.similar c c2
                  then Node ((c, nc), l1, r2)
                  else
                    let rt = (c, nc) in
                    let rt2 = (c2, nc2) in
                    Node (rt2, Node (rt, sl, l2), Node (rt, sl, r2))
                else if
                  (* c2 < c1 < c *)
                  C.similar c c1 && C.similar c1 c2
                then Node ((c1, nc1), l1, Node ((c, nc), r1, r2))
                else
                  let rt = (c, nc) in
                  let rt1 = (c1, nc1) in
                  Node
                    ( (c2, nc2),
                      Node (rt1, Node (rt, l1, l2), Node (rt, r1, l2)),
                      Node (rt1, Node (rt, l1, r2), Node (rt, r1, r2)) )
            | Node ((c1, nc1), l1, r1), _ ->
                if C.is_leq c c1 then (* c <= c1 *)
                  if C.is_eq c c1 then (* c = c1 *) Node ((c, nc), l1, sr)
                  else (* c < c1 *) Node ((c, nc), sl, sr)
                else if
                  (* c > c1 *)
                  C.similar c c1
                then Node ((c1, nc1), l1, Node ((c, nc), r1, sr))
                else
                  let rt = (c, nc) in
                  Node ((c1, nc1), Node (rt, l1, sr), Node (rt, r1, sr))
            | _, Node ((c2, nc2), l2, r2) ->
                if C.is_leq c c2 then (* c <= c2 *)
                  if C.is_eq c c2 then (* c = c2 *) Node ((c, nc), sl, r2)
                  else (* c < c2 *) Node ((c, nc), sl, sr)
                else if
                  (* c > c2 *)
                  C.similar c c2
                then Node ((c, nc), sl, r2)
                else
                  let rt = (c, nc) in
                  Node ((c2, nc2), Node (rt, sl, l2), Node (rt, sl, r2))
            | _ -> Node ((c, nc), sl, sr) (* same *)
          else (* t is not normalized *)
            match (sl, sr) with
            | Node ((c1, nc1), l1, r1), Node ((c2, nc2), l2, r2)
              when C.is_eq c1 c2 (* c1 = c2 *) ->
                if C.is_leq nc c1 then (* nc <= c1 = c2 *)
                  if C.is_eq nc c1 then (* nc = c1 = c2 *) Node ((nc, c), l2, r1)
                  else (* nc < c1 = c2 *) Node ((nc, c), sr, sl)
                else if
                  (* nc > c1 = c2 *)
                  C.similar nc c1
                then Node ((c1, nc1), l2, Node ((nc, c), r2, r1))
                else
                  let rt = (nc, c) in
                  let rt1 = (c1, nc1) in
                  Node (rt1, Node (rt, l2, l1), Node (rt, r2, r1))
            | Node ((c1, nc1), l1, r1), Node ((c2, nc2), l2, r2)
              when C.is_leq c1 c2 (* c1 < c2 *) ->
                if C.is_leq nc c1 then (* nc <= c1 < c2 *)
                  if C.is_eq nc c1 then (* nc = c1 < c2 *) Node ((nc, c), sr, r1)
                  else (* nc < c1 < c2 *) Node ((nc, c), sr, sl)
                else if
                  (* nc > c1 < c2 *)
                  C.is_leq nc c2
                then
                  (* c1 < nc <= c2 *)
                  if C.is_eq nc c2 then (* c1 < nc = c2 *)
                    if C.similar nc c1 then Node ((nc, c), l2, r1)
                    else
                      let rt = (nc, c) in
                      let rt1 = (c1, nc1) in
                      Node (rt1, Node (rt, l2, l1), Node (rt, l2, r1))
                  else if
                    (* c1 < nc < c2 *)
                    C.similar c2 nc && C.similar nc c1
                  then Node ((nc, c), l2, r1)
                  else
                    let rt = (nc, c) in
                    let rt1 = (c1, nc1) in
                    Node (rt1, Node (rt, sr, l1), Node (rt, sr, r1))
                else if
                  (* c1 < c2 < nc *)
                  C.similar nc c2 && C.similar c2 c1
                then Node ((c2, nc2), l2, Node ((nc, c), r2, r1))
                else
                  let rt = (nc, c) in
                  let rt2 = (c2, nc2) in
                  Node
                    ( (c1, nc1),
                      Node (rt2, Node (rt, l2, l1), Node (rt, r2, l1)),
                      Node (rt2, Node (rt, l2, r1), Node (rt, r2, r1)) )
            | Node ((c1, nc1), l1, r1), Node ((c2, nc2), l2, r2)
              when C.is_leq c2 c1 (* c1 > c2 *) ->
                if C.is_leq nc c2 then (* nc <= c2 < c1 *)
                  if C.is_eq nc c2 then (* nc = c2 < c1 *) Node ((nc, c), l2, sl)
                  else (* nc < c2 < c1 *) Node ((nc, c), sr, sl)
                else if
                  (* nc > c2 < c1 *)
                  C.is_leq nc c1
                then
                  (* c2 < nc <= c1 *)
                  if C.is_eq nc c1 then (* c2 < nc = c1 *)
                    if C.similar nc c2 then
                      Node ((c2, nc2), l2, Node ((nc, c), r2, r1))
                    else
                      let rt = (nc, c) in
                      let rt2 = (c2, nc2) in
                      Node (rt2, Node (rt, l2, r1), Node (rt, r2, r1))
                  else if
                    (* c2 < nc < c1 *)
                    C.similar c1 nc && C.similar nc c2
                  then Node ((c2, nc2), l2, Node ((nc, c), r2, sl))
                  else
                    let rt = (nc, c) in
                    let rt2 = (c2, nc2) in
                    Node (rt2, Node (rt, l2, sl), Node (rt, r2, sl))
                else if
                  (* c2 < c1 < nc *)
                  C.similar nc c1 && C.similar c1 c2
                then Node ((c2, nc2), l2, Node ((nc, c), r2, r1))
                else
                  let rt = (nc, c) in
                  let rt1 = (c1, nc1) in
                  Node
                    ( (c2, nc2),
                      Node (rt1, Node (rt, l2, l1), Node (rt, l2, r1)),
                      Node (rt1, Node (rt, r2, l1), Node (rt, r2, r1)) )
            | Node ((c1, nc1), l1, r1), _ ->
                if C.is_leq nc c1 then (* nc <= c1 *)
                  if C.is_eq nc c1 then (* nc = c1 *) Node ((nc, c), sr, r1)
                  else (* nc < c1 *) Node ((nc, c), sr, sl)
                else if
                  (* nc > c1 *)
                  C.similar nc c1
                then Node ((nc, c), sr, r1)
                else
                  let rt = (nc, c) in
                  Node ((c1, nc1), Node (rt, sr, l1), Node (rt, sr, r1))
            | _, Node ((c2, nc2), l2, r2) ->
                if C.is_leq nc c2 then (* nc <= c2 *)
                  if C.is_eq nc c2 then (* nc = c2 *) Node ((nc, c), l2, sl)
                  else (* nc < c2 *) Node ((nc, c), sr, sl)
                else if
                  (* nc > c2 *)
                  C.similar nc c2
                then Node ((c2, nc2), l2, Node ((nc, c), r2, sl))
                else
                  let rt = (nc, c) in
                  Node ((c2, nc2), Node (rt, l2, sl), Node (rt, r2, sl))
            | _ -> Node ((nc, c), sr, sl)
          (* it stays the same *))
      | _ -> t
    in
    let st = swap_tree t in
    (* root(st) is the smallest constraint in t *)
    match st with
    | Node (c, l, r) ->
        let sl = sort_tree l in
        let sr = sort_tree r in
        Node (c, sl, sr)
    | _ -> st

  let update_dom b env = { env with domain = b }
  let is_bot t = match t.tree with Leaf f when F.is_bot f -> true | _ -> false

  (** The bottom element of the abstract domain. The totally undefined function,
      i.e., a decision tree with a single `bottom` leaf. *)
  let bot e = { tree = Leaf (F.bot e.f_env); env = e }

  (** The total function equal to zero, i.e., a decision tree with a single leaf
      with value zero. *)
  let zero e = { tree = Leaf (F.zero e.f_env); env = e }

  (** The top element of the abstract domain. The totally unknown function,
      i.e., a decision tree with a single `top` leaf. *)
  let top e = { tree = Leaf (F.top e.f_env); env = e }

  (* BINARY OPERATORS *)
  let tree_unification_aux t1 t2 f_env cs =
    let rec aux (t1, t2) cs =
      match (t1, t2) with
      | Bot, Bot -> (t1, t2)
      | Bot, Leaf _ | Leaf _, Bot | Leaf _, Leaf _ ->
          if B.is_bot (B.inner f_env cs) then (Bot, Bot) else (t1, t2)
      | Node ((c1, nc1), l1, r1), Node ((c2, nc2), l2, r2)
        when C.is_eq c1 c2 (* c1 = c2 *) ->
          let ul1, ul2 = aux (l1, l2) (c1 :: cs) in
          let ur1, ur2 = aux (r1, r2) (nc1 :: cs) in
          (Node ((c1, nc1), ul1, ur1), Node ((c2, nc2), ul2, ur2))
      | Node ((c1, nc1), l1, r1), Node ((c2, nc2), l2, r2)
        when C.is_leq c1 c2 (* c1 < c2 *) ->
          let bcs = B.inner f_env cs in
          let bc1 = B.inner f_env [ c1 ] in
          if B.is_leq COMPUTATIONAL bcs bc1 then (* c1 is redundant *)
            aux (l1, t2) cs
          else (* c1 is not redundant *)
            let bnc1 = B.inner f_env [ nc1 ] in
            if B.is_leq COMPUTATIONAL bcs bnc1 then (* nc1 is redundant *)
              aux (r1, t2) cs
            else (* nc1 is not redundant *)
              let ul1, ul2 = aux (l1, t2) (c1 :: cs) in
              let ur1, ur2 = aux (r1, t2) (nc1 :: cs) in
              (Node ((c1, nc1), ul1, ur1), Node ((c1, nc1), ul2, ur2))
      | Node ((c1, nc1), l1, r1), Node ((c2, nc2), l2, r2)
        when C.is_leq c2 c1 (* c1 > c2 *) ->
          let bcs = B.inner f_env cs in
          let bc2 = B.inner f_env [ c2 ] in
          if B.is_leq COMPUTATIONAL bcs bc2 then (* c2 is redundant *)
            aux (t1, l2) cs
          else (* c2 is not redundant *)
            let bnc2 = B.inner f_env [ nc2 ] in
            if B.is_leq COMPUTATIONAL bcs bnc2 then (* nc2 is redundant *)
              aux (t1, r2) cs
            else (* nc2 is not redundant *)
              let ul1, ul2 = aux (t1, l2) (c2 :: cs) in
              let ur1, ur2 = aux (t1, r2) (nc2 :: cs) in
              (Node ((c2, nc2), ul1, ur1), Node ((c2, nc2), ul2, ur2))
      | Node ((c1, nc1), l1, r1), _ ->
          let bcs = B.inner f_env cs in
          let bc1 = B.inner f_env [ c1 ] in
          if B.is_leq COMPUTATIONAL bcs bc1 then (* c1 is redundant *)
            aux (l1, t2) cs
          else (* c1 is not redundant *)
            let bnc1 = B.inner f_env [ nc1 ] in
            if B.is_leq COMPUTATIONAL bcs bnc1 then (* nc1 is redundant *)
              aux (r1, t2) cs
            else (* nc1 is not redundant *)
              let ul1, ul2 = aux (l1, t2) (c1 :: cs) in
              let ur1, ur2 = aux (r1, t2) (nc1 :: cs) in
              (Node ((c1, nc1), ul1, ur1), Node ((c1, nc1), ul2, ur2))
      | _, Node ((c2, nc2), l2, r2) ->
          let bcs = B.inner f_env cs in
          let bc2 = B.inner f_env [ c2 ] in
          if B.is_leq COMPUTATIONAL bcs bc2 then (* c2 is redundant *)
            aux (t1, l2) cs
          else (* c2 is not redundant *)
            let bnc2 = B.inner f_env [ nc2 ] in
            if B.is_leq COMPUTATIONAL bcs bnc2 then (* nc2 is redundant *)
              aux (t1, r2) cs
            else (* nc2 is not redundant *)
              let ul1, ul2 = aux (t1, l2) (c2 :: cs) in
              let ur1, ur2 = aux (t1, r2) (nc2 :: cs) in
              (Node ((c2, nc2), ul1, ur1), Node ((c2, nc2), ul2, ur2))
    in
    aux (t1, t2) cs

  (** The decision tree orderings and binary operators rely on tree unification
      to find a common labeling for the decision trees. Given two decision trees
      t1 and t2 the unification accumulates into a set `cs` the linear
      constraints encountered along the paths of the decision trees, possibly
      adding decision nodes or removing constraints that are redundant or whose
      negation is redundant with respect to `cs`.

      The implementation assumes that t1 and t2 are sorted and normalized. *)
  let tree_unification t1 t2 env = tree_unification_aux t1 t2 env.f_env []

  (** The decision tree ordering is parameterized by the choice of the ordering
      `k` between leaf nodes, i.e., approximation or computational ordering.
      Given two decision trees t1 and t2, the ordering accumulates into a set
      `cs` the linear constraints encountered along the paths of the decision
      tree up to the leaf nodes, which are compared by means of the chosen leaf
      node ordering `k`.

      The implementation assumes that t1 and t2 are defined over the same
      reachable states, the same APRON envorinment and the same list of program
      variables. *)
  let is_leq k t1 t2 =
    (* assuming t1.domain = t2.domain *)
    let env = t1.env in
    let f_env = env.f_env in
    (* assuming t1.f_env = t2.f_env *)
    let rec aux (t1, t2) cs =
      match (t1, t2) with
      | Bot, Bot -> true
      | Bot, _ | _, Bot ->
          let b =
            match env.domain with
            | None -> B.inner f_env cs
            | Some domain -> B.meet COMPUTATIONAL (B.inner f_env cs) domain
          in
          B.is_bot b
      | Leaf f1, Leaf f2 -> (
          let b =
            match env.domain with
            | None -> B.inner f_env cs
            | Some domain -> B.meet COMPUTATIONAL (B.inner f_env cs) domain
          in
          if B.is_bot b then true
          else
            match k with
            | APPROXIMATION | RESILIENCE ->
                if (not (F.defined f2)) || F.defined f1 then
                  (* dom(f1) \supseteq dom(f2) *)
                  if F.defined f1 && F.defined f2 then
                    (* forall x: f1(x) <= f2(x) *)
                    F.is_leq k b f1 f2
                  else true
                else false
            | COMPUTATIONAL -> F.is_leq k b f1 f2 (* forall x: f1(x) <= f2(x) *)
          )
      | Node ((c1, nc1), l1, r1), Node ((c2, nc2), l2, r2) when C.is_eq c1 c2 ->
          aux (l1, l2) (c1 :: cs) && aux (r1, r2) (nc1 :: cs)
      | _ -> raise (Invalid_argument "is_leq:")
    in
    aux (tree_unification t1.tree t2.tree env) []

  (*
    The 'tree_join_helper' function can be used to generalize the joining of two trees.
    It applies tree_unification to the two input trees 'tree1' and 'tree2' and uses 
    the given functions 'fBotLeft', 'fBotRight' and 'fBotLeaf' to produce the new leaf nodes in the resulting tree.

     - fBotRight: is called when the left node is a leaf and the right node is NIL
     - fBotLeft: is called when the right node is a leaf and the left node is NIL
     - fLeaf: is called if both nodes are leafs

    All of the above take the set of constraints 'cs' leading up to that tree node and the corresponding leaf value(s) as argument.
  *)
  let tree_join_helper (fBotLeft : C.t list -> F.t -> tree)
      (fBotRight : C.t list -> F.t -> tree)
      (fLeaf : C.t list -> F.t -> F.t -> tree) (tree1 : tree) (tree2 : tree) env
      =
    let rec aux (t1, t2) cs =
      match (t1, t2) with
      | Bot, Bot -> Bot
      | Leaf f, Bot -> fBotRight cs f
      | Bot, Leaf f -> fBotLeft cs f
      | Leaf f1, Leaf f2 -> fLeaf cs f1 f2
      | Node ((c1, nc1), l1, r1), Node ((c2, nc2), l2, r2) ->
          (* if not (C.is_eq c1 c2) then raise (Invalid_argument "tree_join_helper: invalid tree structure, constraints don't match"); *)
          let l = aux (l1, l2) (c1 :: cs) in
          let r = aux (r1, r2) (nc1 :: cs) in
          Node ((c1, nc1), l, r)
      | _ -> raise (Invalid_argument "tree_join_helper: invalid tree structure")
    in
    aux (tree_unification tree1 tree2 env) []

  (** The decision tree join is parameterized by the choice of the join `k`
      between leaf nodes, i.e., approximation or computational join. Given two
      decision trees t1 and t2, the join accumulates into a set `cs` the linear
      constraints encountered along the paths of the decision tree up to the
      leaf nodes, which are joined by means of the chosen leaf node join `k`.

      The implementation assumes that t1 and t2 are defined over the same
      reachable states, the same APRON envorinment and the same list of program
      variables. *)
  let tree_join k (t1, t2) env =
    let f_env = env.f_env in
    let domain = env.domain in
    let fBotLeftRight cs f =
      let b =
        match domain with
        | None -> B.inner f_env cs
        | Some domain -> B.meet COMPUTATIONAL (B.inner f_env cs) domain
      in
      if B.is_bot b then Bot else Leaf f
    in
    let fLeaf cs f1 f2 =
      let b =
        match domain with
        | None -> B.inner f_env cs
        | Some domain -> B.meet COMPUTATIONAL (B.inner f_env cs) domain
      in
      if B.is_bot b then Bot else Leaf (F.join k b f1 f2)
    in
    tree_join_helper fBotLeftRight fBotLeftRight fLeaf t1 t2 env

  let tree_plus (t1, t2) env =
    let f_env = env.f_env in
    let domain = env.domain in
    let fBotLeftRight cs f =
      let b =
        match domain with
        | None -> B.inner f_env cs
        | Some domain -> B.meet COMPUTATIONAL (B.inner f_env cs) domain
      in
      if B.is_bot b then Bot else Leaf f
    in
    let fLeaf cs f1 f2 =
      let b =
        match domain with
        | None -> B.inner f_env cs
        | Some domain -> B.meet COMPUTATIONAL (B.inner f_env cs) domain
      in
      if B.is_bot b then Bot else Leaf (F.plus b f1 f2)
    in
    tree_join_helper fBotLeftRight fBotLeftRight fLeaf t1 t2 env

  let join k t1 t2 =
    let t = tree_join k (t1.tree, t2.tree) t1.env in
    {
      (* tree = tree_join k (t1.tree,t2.tree) t1.domain t1.env ; *)
      tree = t;
      env = t1.env;
      (* assuming t1.env = t2.env *)
    }

  let plus t1 t2 =
    let t = tree_plus (t1.tree, t2.tree) t1.env in
    {
      (* tree = tree_join k (t1.tree,t2.tree) t1.domain t1.env ; *)
      tree = t;
      env = t1.env;
      (* assuming t1.env = t2.env *)
    }

  (** Given two decision trees t1 and t2, the decision tree meet accumulates
      into a set `cs` the linear constraints encountered along the paths of the
      decision tree up to the leaf nodes, which are joined by means of the leaf
      node meet.

      The implementation assumes that t1 and t2 are defined over the same
      reachable states, the same APRON envorinment and the same list of program
      variables.

      The following two versions of meet exists:

      COMPUTATIONAL: In this versions, all parts of the resuling decision tree
      that are undefined i.e. not part of t1 and t2 are set to bottom leafs.

      APPROXIMATION: In this versions, all parts of the resuling decision tree
      that are undefined i.e. not part of t1 and t2 are replaced with NIL nodes.
      Using this version of the meet can lead to NIL nodes in the resulting
      tree. *)
  let meet (k : kind) (t1 : t) (t2 : t) =
    let f_env = t1.env.f_env in
    let domain = t1.env.domain in
    (* assuming t1.env = t2.env *)
    let botLeaf = Leaf (F.bot f_env) in
    let fBotLeftRight =
      match k with
      | APPROXIMATION ->
          fun _ _ -> Bot (* use NIL if at least one leaf is NIL *)
      | RESILIENCE -> fun _ _ -> Bot (* use NIL if at least one leaf is NIL *)
      | COMPUTATIONAL ->
          fun _ _ -> botLeaf (* use bottom leaf if at least one leaf is nil*)
    in
    let fLeaf cs f1 f2 =
      let b =
        match domain with
        | None -> B.inner f_env cs
        | Some domain -> B.meet COMPUTATIONAL (B.inner f_env cs) domain
      in
      if B.is_bot b then Bot else Leaf (F.join APPROXIMATION b f1 f2)
      (* join leaf values using APPROXIMATION join *)
    in
    {
      tree =
        tree_join_helper fBotLeftRight fBotLeftRight fLeaf t1.tree t2.tree
          t1.env;
      env = t1.env;
    }

  let left_unification ?(join_kind = COMPUTATIONAL) t1 t2 domain env =
    let ls1 = tree_labels t1 in
    let ls2 = tree_labels t2 in
    let ls = LSet.diff ls2 ls1 in
    let f_env = env.f_env in
    (* Checks whether constraint c is redundant, given the constraints cs *)
    let is_redundant c cs =
      let bcs = B.inner f_env cs in
      let bc = B.inner f_env [ c ] in
      B.is_leq COMPUTATIONAL bcs bc
    in
    (* Compare l1 and l2, with labels not in t1 being greater
     * than all others, and thus will go to the bottom of the
     * tree
     *)
    let cmp l1 l2 =
      match (LSet.mem l1 ls, LSet.mem l2 ls) with
      | false, false -> L.compare l1 l2
      | true, true -> L.compare l1 l2
      | false, true -> -1
      | true, false -> 1
    in
    (* Removes redundant constraints in t *)
    let rec remove_redundant t cs =
      match t with
      | Bot | Leaf _ -> t
      | Node ((c, nc), l, r) ->
          if is_redundant c cs then remove_redundant l cs
          else if is_redundant nc cs then remove_redundant r cs
          else
            let ll = remove_redundant l (c :: cs) in
            let rr = remove_redundant r (nc :: cs) in
            Node ((c, nc), ll, rr)
    in
    let add_node (c, nc) (l, r) cs =
      if is_redundant c cs then l
      else if is_redundant nc cs then r
      else Node ((c, nc), l, r)
    in
    (* Creates a node, putting it in the right place so the tree
     * stays sorted
     *)
    let rec make_node (c, nc) (l, r) cs =
      let smallest t cc =
        match t with
        | Bot | Leaf _ -> cc
        | Node (cc1, l1, r1) -> if cmp cc cc1 > 0 then cc1 else cc
      in
      if is_redundant c cs then l
      else if is_redundant nc cs then r
      else
        let sc = smallest l (smallest r (c, nc)) in
        match (l, r) with
        | Node ((cl, ncl), ll, rl), Node ((cr, ncr), lr, rr)
          when cmp (cl, ncl) sc = 0 && cmp (cr, ncr) sc = 0 ->
            Node
              ( (cl, ncl),
                make_node (c, nc) (ll, lr) (cl :: cs),
                make_node (c, nc) (rl, rr) (ncl :: cs) )
        | Node ((cl, ncl), ll, rl), _ when cmp (cl, ncl) sc = 0 ->
            Node
              ( (cl, ncl),
                make_node (c, nc) (ll, r) (cl :: cs),
                make_node (c, nc) (rl, r) (ncl :: cs) )
        | _, Node ((cr, ncr), lr, rr) when cmp (cr, ncr) sc = 0 ->
            Node
              ( (cr, ncr),
                make_node (c, nc) (l, lr) (cr :: cs),
                make_node (c, nc) (l, rr) (ncr :: cs) )
        | _, _ -> Node ((c, nc), l, r)
    in
    (* Sort the tree completely; adding the new nodes *)
    let rec rebalance_tree t cs =
      match t with
      | Bot | Leaf _ -> t
      | Node ((c, nc), l, r) ->
          let ll = rebalance_tree l (c :: cs) in
          let rr = rebalance_tree r (nc :: cs) in
          make_node (c, nc) (ll, rr) cs
    in
    (* Collapse all leaves of t into a single one, making sure
     * all labels that are to be removed are deleted
     *)
    let rec collapse t cs =
      match t with
      | Bot | Leaf _ -> t
      | Node ((c, nc), l, r) -> (
          assert (LSet.mem (c, nc) ls);
          if is_redundant c cs then collapse l cs
          else if is_redundant nc cs then collapse r cs
          else
            let ll = collapse l (c :: cs) in
            let rr = collapse r (nc :: cs) in
            match (ll, rr) with
            | _, Bot -> ll
            | Bot, _ -> rr
            | Leaf f1, Leaf f2 ->
                let b =
                  match domain with
                  | None -> B.inner f_env cs
                  | Some domain ->
                      B.meet COMPUTATIONAL (B.inner f_env cs) domain
                in
                Leaf (F.join join_kind b f1 f2)
            | _, _ -> assert false)
    in
    (* Finish t1 and t2 unification by doing a tree unification step
     * for labels that are in t1, and collapsing the others.
     *)
    let rec lunify t1 t2 cs =
      match (t1, t2) with
      | (Bot | Leaf _), (Bot | Leaf _) -> t2
      | Node ((c1, nc1), l1, r1), (Bot | Leaf _) ->
          add_node (c1, nc1)
            (lunify l1 t2 (c1 :: cs), lunify r1 t2 (nc1 :: cs))
            cs
      | (Bot | Leaf _), Node ((c2, nc2), l2, r2) ->
          if LSet.mem (c2, nc2) ls then collapse t2 cs
          else
            add_node (c2, nc2)
              (lunify t1 l2 (c2 :: cs), lunify t1 r2 (nc2 :: cs))
              cs
      | Node ((c1, nc1), l1, r1), Node ((c2, nc2), l2, r2) ->
          let w = cmp (c1, nc1) (c2, nc2) in
          if w = 0 then
            add_node (c1, nc1)
              (lunify l1 l2 (c1 :: cs), lunify r1 r2 (nc1 :: cs))
              cs
          else if w < 0 then
            add_node (c1, nc1)
              (lunify l1 t2 (c1 :: cs), lunify r1 t2 (nc1 :: cs))
              cs
          else (
            assert (not (LSet.mem (c2, nc2) ls));
            add_node (c2, nc2)
              (lunify t1 l2 (c2 :: cs), lunify t1 r2 (nc2 :: cs))
              cs)
    in
    lunify t1 (remove_redundant (rebalance_tree t2 []) []) []

  let widen ?(jokers = 0) t1 t2 =
    let env = t1.env in
    let domain = env.domain in
    let f_env = env.f_env in
    let t1 = t1.tree and t2 = t2.tree in
    let rec widen_right (t1, t2) cs =
      match (t1, t2) with
      | Leaf f1, Leaf f2 ->
          let b =
            match domain with
            | None -> B.inner f_env cs
            | Some domain -> B.meet COMPUTATIONAL (B.inner f_env cs) domain
          in
          if F.is_leq COMPUTATIONAL b f1 f2 then t2 else Leaf (F.top f_env)
      | Node ((c1, nc1), l1, r1), Node ((c2, nc2), l2, r2)
        when C.is_eq c1 c2 (* c1 = c2 *) ->
          let l = widen_right (l1, l2) (c1 :: cs) in
          let r = widen_right (r1, r2) (nc1 :: cs) in
          Node ((c2, nc2), l, r)
      | Node ((c1, nc1), l1, r1), Node ((c2, _), _, _)
        when C.is_leq c1 c2 (* c1 < c2 *) ->
          let bcs = B.inner f_env cs in
          let bc1 = B.inner f_env [ c1 ] in
          if B.is_leq COMPUTATIONAL bcs bc1 then (* c1 is redundant *)
            widen_right (l1, t2) cs
          else (* c1 is not redundant *)
            let bnc1 = B.inner f_env [ nc1 ] in
            if B.is_leq COMPUTATIONAL bcs bnc1 then (* nc1 is redundant *)
              widen_right (r1, t2) cs
            else (* nc1 is not redundant *)
              let l = widen_right (l1, t2) (c1 :: cs) in
              let r = widen_right (r1, t2) (nc1 :: cs) in
              Node ((c1, nc1), l, r)
      | Node ((c1, _), _, _), Node ((c2, nc2), l2, r2)
        when C.is_leq c2 c1 (* c1 > c2 *) ->
          let l = widen_right (t1, l2) (c2 :: cs) in
          let r = widen_right (t1, r2) (nc2 :: cs) in
          Node ((c2, nc2), l, r)
      | Node ((c1, nc1), l1, r1), _ ->
          let bcs = B.inner f_env cs in
          let bc1 = B.inner f_env [ c1 ] in
          if B.is_leq COMPUTATIONAL bcs bc1 then (* c1 is redundant *)
            widen_right (l1, t2) cs
          else (* c1 is not redundant *)
            let bnc1 = B.inner f_env [ nc1 ] in
            if B.is_leq COMPUTATIONAL bcs bnc1 then (* nc1 is redundant *)
              widen_right (r1, t2) cs
            else (* nc1 is not redundant *)
              let l = widen_right (l1, t2) (c1 :: cs) in
              let r = widen_right (r1, t2) (nc1 :: cs) in
              Node ((c1, nc1), l, r)
      | _, Node ((c2, nc2), l2, r2) ->
          let l = widen_right (t1, l2) (c2 :: cs) in
          let r = widen_right (t1, r2) (nc2 :: cs) in
          Node ((c2, nc2), l, r)
      | _ -> t2
    in
    let rec widen_up (t1, t2) cs =
      match (t1, t2) with
      | Bot, Bot -> Bot
      | Leaf f1, Leaf f2 ->
          let b =
            match domain with
            | None -> B.inner f_env cs
            | Some domain -> B.meet COMPUTATIONAL (B.inner f_env cs) domain
          in
          Leaf
            (F.widen
               ~jokers:
                 (if !retrybwd > 0 then (jokers + !retrybwd - 1) / !retrybwd
                  else 0)
               b f1 f2)
      | Node ((c1, nc1), l1, r1), Node ((c2, nc2), l2, r2)
        when C.is_eq c1 c2 (* c1 = c2 *) ->
          Node
            ( (c1, nc1),
              widen_up (l1, l2) (c1 :: cs),
              widen_up (r1, r2) (nc1 :: cs) )
      | Node ((c1, nc1), l1, r1), Node ((c2, _), _, _)
        when C.is_leq c1 c2 (* c1 < c2 *) ->
          let bcs = B.inner f_env cs in
          let bc1 = B.inner f_env [ c1 ] in
          if B.is_leq COMPUTATIONAL bcs bc1 then (* c1 is redundant *)
            widen_up (l1, t2) cs
          else (* c1 is not redundant *)
            let bnc1 = B.inner f_env [ nc1 ] in
            if B.is_leq COMPUTATIONAL bcs bnc1 then (* nc1 is redundant *)
              widen_up (r1, t2) cs
            else (* nc1 is not redundant *)
              Node
                ( (c1, nc1),
                  widen_up (l1, t2) (c1 :: cs),
                  widen_up (r1, t2) (nc1 :: cs) )
      | Node ((c1, _), _, _), Node ((c2, nc2), l2, r2)
        when C.is_leq c2 c1 (* c1 > c2 *) ->
          Node
            ( (c2, nc2),
              widen_up (t1, l2) (c2 :: cs),
              widen_up (t1, r2) (nc2 :: cs) )
      | Node ((c1, nc1), l1, r1), _ ->
          let bcs = B.inner f_env cs in
          let bc1 = B.inner f_env [ c1 ] in
          if B.is_leq COMPUTATIONAL bcs bc1 then (* c1 is redundant *)
            widen_up (l1, t2) cs
          else (* c1 is not redundant *)
            let bnc1 = B.inner f_env [ nc1 ] in
            if B.is_leq COMPUTATIONAL bcs bnc1 then (* nc1 is redundant *)
              widen_up (r1, t2) cs
            else (* nc1 is not redundant *)
              Node
                ( (c1, nc1),
                  widen_up (l1, t2) (c1 :: cs),
                  widen_up (r1, t2) (nc1 :: cs) )
      | _, Node ((c2, nc2), l2, r2) ->
          Node
            ( (c2, nc2),
              widen_up (t1, l2) (c2 :: cs),
              widen_up (t1, r2) (nc2 :: cs) )
      | Bot, _ | _, Bot -> Bot
    in
    let widen (t1, t2) =
      let prev = t1 in
      let lbl = LSet.elements (tree_labels t2) in
      let inner_b cs =
        match domain with
        | None -> B.inner f_env cs
        | Some domain -> B.meet COMPUTATIONAL (B.inner f_env cs) domain
      in
      let extend1 b2 f20 f2 (b1, f1) =
        if !tracebwd then (
          Format.fprintf Format.std_formatter "EXTEND\n";
          Format.fprintf Format.std_formatter "%a? %a\n" B.print b1 F.print f1;
          Format.fprintf Format.std_formatter "%a? %a\n" B.print b2 F.print f20;
          Format.fprintf Format.std_formatter "%a? %a\n\n" B.print b2 F.print
            (F.extend b1 b2 f1 f20));
        F.join COMPUTATIONAL b2 (F.extend b1 b2 f1 f20) f2
      in
      let rec leaf p (* labels + path *) t leafcs cs =
        let select ((c, nc), (h, _)) cs = if h then c :: cs else nc :: cs in
        match t with
        | Bot -> None
        | Leaf f ->
            let cs =
              let rec inner p cs =
                match p with [] -> cs | h :: p -> inner p (select h cs)
              in
              inner p cs
            in
            let leafb = inner_b leafcs in
            let b = inner_b cs in
            if
              F.defined f && (not (B.is_bot b)) && not (F.is_eq b f (F.reset f))
            then Some (leafb, f)
            else None
        | Node ((c1, _), l1, r1) -> (
            match p with
            | [] -> raise (Invalid_argument "widen:leaf:")
            | (((c, _), (s, _)) as h) :: p ->
                if C.is_eq c1 c then
                  leaf p (if s then l1 else r1) (select h leafcs) (select h cs)
                else leaf p t leafcs (select h cs))
      in
      let rec adjacent leafb f2 p1 p2 acc =
        match p2 with
        | [] -> acc
        | (p, (b, true)) :: ps ->
            adjacent leafb f2 ((p, (b, true)) :: p1) ps acc
        | (p, (b, false)) :: ps ->
            let acc =
              match
                leaf (List.rev_append p1 ((p, (not b, false)) :: ps)) prev [] []
              with
              | None -> acc
              | Some (b, l) -> extend1 leafb f2 acc (b, l)
            in
            adjacent leafb f2 ((p, (b, false)) :: p1) ps acc
      in
      let rec merge (t1, t2) cs =
        match (t1, t2) with
        | _, Bot -> t1
        | Bot, _ -> t2
        | Leaf f1, Leaf f2 -> Leaf (F.join COMPUTATIONAL (inner_b cs) f1 f2)
        | Node ((c1, nc1), l1, r1), Node ((c2, nc2), l2, r2)
          when C.is_eq c1 c2 (* c1 = c2 *) ->
            let l = merge (l1, l2) (c1 :: cs) in
            let r = merge (r1, r2) (nc1 :: cs) in
            Node ((c1, nc1), l, r)
        | _ -> raise (Invalid_argument "widen:merge:")
      in
      let rec aux p (* path *) ls (* labels *) (t1, t2) leafcs cs =
        (* The path also contains the associated label *)
        match (t1, t2) with
        | Bot, _ | _, Bot -> Bot
        | Leaf _, Node _ | Node _, Leaf _ ->
            raise (Invalid_argument "widen:aux:")
        | Leaf f1, Leaf f2 ->
            let leafb = inner_b leafcs in
            let b = inner_b cs in
            if B.is_bot b then Bot
            else if F.is_eq b f1 f2 then t2
            else
              let rec aux2 p ls cs acc =
                match ls with
                (* finish the path, then extend *)
                | [] ->
                    adjacent leafb f2 [] (List.rev p) acc (* path finished *)
                | (c, nc) :: ls ->
                    (* extend the path *)
                    let bcs = B.inner f_env cs in
                    let bc = B.inner f_env [ c ] in
                    let bnc = B.inner f_env [ nc ] in
                    let leqc = B.is_leq COMPUTATIONAL bcs bc in
                    let leqnc = B.is_leq COMPUTATIONAL bcs bnc in
                    if leqc then (* c is redundant *)
                      aux2 (((c, nc), (true, true)) :: p) ls cs acc
                    else if leqnc then (* nc is redundant *)
                      aux2 (((c, nc), (false, true)) :: p) ls cs acc
                    else
                      (* c and nc are not redundant; mark them as such anyway to avoid taking the current leaf *)
                      aux2
                        (((c, nc), (false, true)) :: p)
                        ls (nc :: cs)
                        (aux2 (((c, nc), (true, true)) :: p) ls (c :: cs) acc)
              in
              Leaf (aux2 p ls cs f2)
        | Node ((c1, _), l1, r1), Node ((c2, _), l2, r2) -> (
            if not (C.is_eq c1 c2) then raise (Invalid_argument "widen:aux:")
            else
              match ls with
              | [] -> raise (Invalid_argument "widen:aux:")
              | (c, nc) :: ls ->
                  if C.is_eq c1 c then
                    let l =
                      aux
                        (((c, nc), (true, false)) :: p)
                        ls (l1, l2) (c :: leafcs) (c :: cs)
                    in
                    let r =
                      aux
                        (((c, nc), (false, false)) :: p)
                        ls (r1, r2) (nc :: leafcs) (nc :: cs)
                    in
                    Node ((c, nc), l, r)
                  else if C.is_leq c c1 then
                    let bcs = B.inner f_env cs in
                    let bc = B.inner f_env [ c ] in
                    let bnc = B.inner f_env [ nc ] in
                    let leqc = B.is_leq COMPUTATIONAL bcs bc in
                    let leqnc = B.is_leq COMPUTATIONAL bcs bnc in
                    if leqc then (* c is redundant *)
                      aux (((c, nc), (true, true)) :: p) ls (t1, t2) leafcs cs
                    else if leqnc then (* nc is redundant *)
                      aux (((c, nc), (false, true)) :: p) ls (t1, t2) leafcs cs
                    else (* c and nc are not redundant *)
                      merge
                        ( aux
                            (((c, nc), (true, true)) :: p)
                            ls (t1, t2) leafcs (c :: cs),
                          aux
                            (((c, nc), (false, true)) :: p)
                            ls (t1, t2) leafcs (nc :: cs) )
                        cs
                  else raise (Invalid_argument "widen:aux:"))
      in
      aux [] lbl (t1, t2) [] []
    in
    if !tracebwd then (
      Format.fprintf !Config.fmt "WIDENING\n";
      Format.fprintf !Config.fmt "t1: %a\n" print_tree t1;
      Format.fprintf !Config.fmt "\nt2: %a\n" print_tree t2);
    let t2 = widen_right (t1, t2) [] in
    if !tracebwd then
      Format.fprintf !Config.fmt "\nt2[widen_right]: %a\n" print_tree t2;
    let t2 = left_unification t1 t2 domain env in
    if !tracebwd then
      Format.fprintf !Config.fmt "\nt2[left_unification]: %a\n" print_tree t2;
    let t1, t2 = tree_unification t1 t2 env in
    if !tracebwd then (
      Format.fprintf !Config.fmt "\nt1[tree_unification]: %a\n" print_tree t1;
      Format.fprintf !Config.fmt "\nt2[tree_unification]: %a\n" print_tree t2);
    let t2 = widen_up (t1, t2) [] in
    if !tracebwd then
      Format.fprintf !Config.fmt "\nt2[widen_up]: %a\n" print_tree t2;
    { tree = widen (t1, t2); env }

  let dual_widen t1 t2 =
    let env = t1.env in
    let f_env = env.f_env in
    let domain = env.domain in
    let rec aux (tree1, tree2) cs =
      match (tree1, tree2) with
      | Bot, _ | _, Bot -> Bot
      | Leaf f1, Leaf f2 ->
          let b =
            match domain with
            | None -> B.inner f_env cs
            | Some domain -> B.meet COMPUTATIONAL (B.inner f_env cs) domain
          in
          if B.is_bot b then Bot
          else if F.is_leq COMPUTATIONAL b f2 f1 then Leaf f2
          else Leaf (F.bot f_env)
      | Node ((c1, nc1), l1, r1), Node ((c2, nc2), l2, r2) ->
          let l = aux (l1, l2) (c2 :: cs) in
          let r = aux (r1, r2) (nc2 :: cs) in
          Node ((c2, nc2), l, r)
      | _ -> raise (Invalid_argument "dual_widen: invalid tree structure")
    in
    let t2_tree =
      left_unification ~join_kind:APPROXIMATION t1.tree t2.tree domain env
    in
    { tree = aux (tree_unification t1.tree t2_tree env) []; env }

  (**)

  let assign ?domain controllable ?(underapprox = false) t e =
    let cache = ref CMap.empty in
    let env = t.env in
    let f_env = env.f_env in
    let pre = domain in
    let post = env.domain in
    let e' : expr typed = snd e in
    let merge t1 t2 cs =
      let rec aux (t1, t2) cs =
        match (t1, t2) with
        | _, Bot -> t1
        | Bot, _ -> t2
        | Leaf f1, Leaf f2 ->
            let b =
              match pre with
              | None -> B.inner f_env cs
              | Some pre -> B.meet COMPUTATIONAL (B.inner f_env cs) pre
            in
            let joinType =
              if underapprox && not !resilience then COMPUTATIONAL
              else APPROXIMATION
            in
            Leaf (F.join ~controllable joinType b f1 f2)
        | Node ((c1, nc1), l1, r1), Node ((c2, nc2), l2, r2) when C.is_eq c1 c2
          ->
            Node ((c1, nc1), aux (l1, l2) (c1 :: cs), aux (r1, r2) (nc1 :: cs))
        | _ -> raise (Invalid_argument "bwd_assign:merge:")
      in
      aux (tree_unification_aux t1 t2 f_env cs) cs
    in
    let rec build t cs =
      match cs with
      | [] -> t
      | x :: xs ->
          let nx = C.negate x in
          if C.is_leq nx x then (* x is normalized *)
            Node ((x, nx), build t xs, Bot)
          else (* x is not normalized *) Node ((nx, x), Bot, build t xs)
    in
    let b_bwd_assign =
      if underapprox then B.ubwd_assign else B.bwd_assign ~controllable
    in
    let rec aux t cs =
      match t with
      | Bot -> Bot
      | Leaf f ->
          if B.is_bot (B.inner f_env cs) then Bot else Leaf (F.bwd_assign f e)
      | Node ((c, nc), l, r) -> (
          match fst e with
          | T_var variable, t, ext ->
              if C.var variable c then
                let filter_constraints cs dom =
                  List.fold_left
                    (fun cs c ->
                      let b = B.inner f_env [ c ] in
                      if
                        (not (C.is_bot c))
                        && (B.is_leq COMPUTATIONAL dom b
                           || B.is_bot (B.meet COMPUTATIONAL dom b))
                      then cs
                      else c :: cs)
                    [] cs
                in
                let c, nc =
                  try CMap.find c !cache
                  with Not_found -> (
                    match (pre, post) with
                    | Some pre, Some post ->
                        let key = c in
                        let c =
                          B.conjunction
                            (b_bwd_assign
                               (B.meet COMPUTATIONAL (B.inner f_env [ c ]) post)
                               e)
                        in
                        let c = filter_constraints c pre in
                        let nc =
                          B.conjunction
                            (b_bwd_assign
                               (B.meet COMPUTATIONAL (B.inner f_env [ nc ]) post)
                               e)
                        in
                        let nc = filter_constraints nc pre in
                        cache := CMap.add key (c, nc) !cache;
                        (c, nc)
                    | _ ->
                        let key = c in
                        let c =
                          B.conjunction (b_bwd_assign (B.inner f_env [ c ]) e)
                        in
                        let nc =
                          B.conjunction (b_bwd_assign (B.inner f_env [ nc ]) e)
                        in
                        cache := CMap.add key (c, nc) !cache;
                        (c, nc))
                in
                match (c, nc) with
                | [], [] -> merge (aux l cs) (aux r cs) cs
                | [], [ y ] when C.is_bot y -> aux l cs
                | [ x ], [] when C.is_bot x -> aux r cs
                | [ x ], [ y ] when C.is_bot x && C.is_bot y ->
                    Leaf (F.bot f_env)
                | [ x ], [ y ] ->
                    let nx = C.negate x in
                    let ny = C.negate y in
                    let ll = aux l (x :: cs) in
                    let rr = aux r (y :: cs) in
                    if C.is_eq nx y then sort_tree (Node ((x, nx), ll, rr))
                    else
                      merge
                        (sort_tree (Node ((x, nx), ll, rr)))
                        (sort_tree (Node ((y, ny), rr, ll)))
                        cs
                | _ ->
                    let ll = aux l (c @ cs) in
                    let rr = aux r (nc @ cs) in
                    merge (sort_tree (build ll c)) (sort_tree (build rr nc)) cs
              else
                let l = aux l (c :: cs) in
                let r = aux r (nc :: cs) in
                Node ((c, nc), l, r)
          | _ ->
              raise
                (Invalid_argument "Decision_Tree.bwd_assign: unexpected lvalue")
          )
    in
    let env = { env with domain = pre } in
    { tree = sort_tree (aux t.tree []); env }

  let bwd_assign ?domain ?(controllable = false) =
    assign ?domain controllable ~underapprox:false

  let ubwd_assign ?domain ?(controllable = false) =
    assign ?domain controllable ~underapprox:true

  let rec filter_helper controllable ?domain ?(underapprox = false) t e =
    let pre = domain in
    let env = t.env in
    let f_env = env.f_env in
    let post = env.domain in
    let b_filter =
      if underapprox then B.ubwd_filter else B.fwd_filter ~controllable
    in
    let rec aux t bs cs =
      let bcs =
        match pre with
        | None -> B.inner f_env cs
        | Some pre -> B.meet COMPUTATIONAL (B.inner f_env cs) pre
      in
      match bs with
      | [] -> (
          match t with
          | Bot -> Bot
          | Leaf f -> Leaf (F.filter f e)
          | Node ((c, nc), l, r) -> (
              let bc = B.inner f_env [ c ] in
              if B.is_leq COMPUTATIONAL bcs bc then (* c is redundant *)
                aux l bs cs
              else (* c is not redundant *)
                (* if (B.is_bot (B.meet COMPUTATIONAL bc bcs))
                then (* c is conflicting *) aux r bs cs
                else *)
                let l = aux l bs (c :: cs) in
                let r = aux r bs (nc :: cs) in
                match (l, r) with
                | Bot, Bot -> Bot
                | Bot, Node (_, Bot, _) -> r
                | _ -> Node ((c, nc), l, r)))
      | (x, nx) :: xs -> (
          let bx = B.inner f_env [ x ] in
          if B.is_leq COMPUTATIONAL bcs bx then (* x is redundant *) aux t xs cs
          else if
            (* x is not redundant *)
            B.is_bot (B.meet COMPUTATIONAL bx bcs)
          then (* x is conflicting *) Bot
            (* This introduces a NIL leaf to the tree *)
          else if C.is_leq nx x then (* x is normalized *)
            match t with
            | Node ((c, nc), l, r) when C.is_eq c x (* c = x *) -> (
                let l = aux l xs (c :: cs) in
                match l with Bot -> Bot | _ -> Node ((c, nc), l, Bot))
            | Node ((c, nc), l, r) when C.is_leq c x (* c < x *) -> (
                let bc = B.inner f_env [ c ] in
                if B.is_leq COMPUTATIONAL bcs bc then (* c is redundant *)
                  aux l bs cs
                else (* c is not redundant *)
                  (* if (B.is_bot (B.meet COMPUTATIONAL bc bcs))
                  then (* c is conflicting *) aux r bs cs
                  else *)
                  let l = aux l bs (c :: cs) in
                  let r = aux r bs (nc :: cs) in
                  match (l, r) with
                  | Bot, Bot -> Bot
                  | Bot, Node (_, Bot, _) -> r
                  | _ -> Node ((c, nc), l, r))
            | _ -> (
                let l = aux t xs (x :: cs) in
                match l with Bot -> Bot | _ -> Node ((x, nx), l, Bot))
          else (* x is not normalized *)
            match t with
            | Node ((c, nc), l, r) when C.is_eq c nx (* c = nx *) -> (
                let r = aux r xs (nc :: cs) in
                match r with Bot -> Bot | _ -> Node ((c, nc), Bot, r))
            | Node ((c, nc), l, r) when C.is_leq c nx (* c < nx *) -> (
                let bc = B.inner f_env [ c ] in
                if B.is_leq COMPUTATIONAL bcs bc then (* c is redundant *)
                  aux l bs cs
                else (* c is not redundant *)
                  (* if (B.is_bot (B.meet COMPUTATIONAL bc bcs))
                  then (* c is conflicting *) aux r bs cs
                  else *)
                  let l = aux l bs (c :: cs) in
                  let r = aux r bs (nc :: cs) in
                  match (l, r) with
                  | Bot, Bot -> Bot
                  | Bot, Node (_, Bot, _) -> r
                  | _ -> Node ((c, nc), l, r))
            | _ -> (
                let r = aux t xs (x :: cs) in
                match r with Bot -> Bot | _ -> Node ((nx, x), Bot, r)))
    in
    let e, typ, ext = e in
    match e with
    | T_bool_const True | T_bool_const Maybe ->
        { tree = aux t.tree [] []; env = { env with domain = pre } }
    | T_binary (_, (T_var v, _, _), _)
      when String.starts_with ~prefix:"nondet_" v.var_name ->
        { tree = aux t.tree [] []; env = { env with domain = pre } }
    | T_binary (_, _, (T_var v, _, _))
      when String.starts_with ~prefix:"nondet_" v.var_name ->
        { tree = aux t.tree [] []; env = { env with domain = pre } }
    | T_binary (A_EQUAL, e1, e2) ->
        let bop =
          T_binary
            ( A_AND,
              (T_binary (A_GREATER_EQUAL, e1, e2), typ, ext),
              (T_binary (A_GREATER_EQUAL, e2, e1), typ, ext) )
        in
        filter_helper controllable ?domain:pre ~underapprox t (bop, typ, ext)
    | T_binary (A_NOT_EQUAL, e1, e2) ->
        let bop =
          T_binary
            ( A_OR,
              (T_binary (A_GREATER, e1, e2), typ, ext),
              (T_binary (A_LESS, e1, e2), typ, ext) )
        in
        filter_helper controllable ?domain:pre ~underapprox t (bop, typ, ext)
    | T_bool_const False -> { tree = Bot; env = { env with domain = pre } }
    | T_unary (A_NOT, e) ->
        let e = neg_bexp e in
        filter_helper controllable ?domain:pre ~underapprox t e
    | T_binary ((A_AND as op), e1, e2) | T_binary ((A_OR as op), e1, e2) -> (
        let t1 = filter_helper controllable ?domain:pre ~underapprox t e1
        and t2 = filter_helper controllable ?domain:pre ~underapprox t e2 in
        match op with
        | A_AND -> meet APPROXIMATION t1 t2
        | A_OR -> join APPROXIMATION t1 t2
        | _ -> raise (Invalid_argument "This cases are impossible to reach"))
    | _ ->
        let bp =
          match post with
          | None -> B.inner f_env []
          | Some post -> B.meet COMPUTATIONAL (B.inner f_env []) post
        in
        let bs =
          List.map
            (fun c ->
              let nc = C.negate c in
              (c, nc))
            (B.conjunction (b_filter bp (e, typ, ext)))
        in
        let bs = List.sort L.compare bs in
        let t = aux t.tree bs [] in
        { tree = t; env = { env with domain = pre } }

  let filter ?(controllable = false) ?domain =
    filter_helper controllable ?domain ~underapprox:false

  let ubwd_filter ?(controllable = false) ?domain =
    filter_helper controllable ?domain ~underapprox:true

  (* 
    Check if all partitions in the decision tree are defined i.e. have a ranking function assigned to them.

    Optionally, a boolean expression condition can be passed to limit the check to only those partitions that 
    satisfy the expression. This can be used to check if a decision tree is defined under a given assumption.
  *)
  let defined ?condition t =
    let env = t.env in
    let f_env = env.f_env in
    let domain = env.domain in
    let rec aux t cs =
      match t with
      | Bot -> (
          match condition with
          | None ->
              let b =
                match domain with
                | None -> B.inner f_env cs
                | Some domain -> B.meet COMPUTATIONAL (B.inner f_env cs) domain
              in
              B.is_bot b
          | Some _ ->
              true
              (* when given a condition, we first filter the tree and ignore NIL leafs *)
          )
      | Leaf f -> (
          match domain with
          | None -> F.defined f || B.is_bot (B.inner f_env cs)
          | Some domain ->
              F.defined f
              || B.is_bot (B.meet COMPUTATIONAL (B.inner f_env cs) domain))
      | Node ((c, nc), l, r) -> aux l (c :: cs) && aux r (nc :: cs)
    in
    let t =
      match condition with
      | Some b ->
          (* replace all NIL leafs with 'bottom' leafs to ensure that we don't confuse actual 
           NIL leafs with NIL leafs introduces by filer *)
          let t' = tree_map (Leaf (F.bot f_env)) (fun f -> Leaf f) t in
          filter t' b (* filte tree with optional condition *)
      | None -> t
    in
    aux t.tree []

  (* 
    Check if at least one partitions in the decision tree is defined i.e. have a ranking function assigned to it.

    Optionally, a boolean expression condition can be passed to limit the check to only those partitions that 
    satisfy the expression. This can be used to check if a decision tree is defined under a given assumption.
  *)
  let partially_defined ?condition t =
    let env = t.env in
    let f_env = env.f_env in
    let domain = env.domain in
    let rec aux t cs =
      match t with
      | Bot -> false
      | Leaf f -> (
          match domain with
          | None -> F.defined f && not (B.is_bot (B.inner f_env cs))
          | Some domain ->
              F.defined f
              && not (B.is_bot (B.meet COMPUTATIONAL (B.inner f_env cs) domain))
          )
      | Node ((c, nc), l, r) -> aux l (c :: cs) || aux r (nc :: cs)
    in
    let t =
      match condition with
      | Some b ->
          (* replace all NIL leafs with 'bottom' leafs to ensure that we don't confuse actual 
           NIL leafs with NIL leafs introduces by filer *)
          let t' = tree_map (Leaf (F.bot f_env)) (fun f -> Leaf f) t in
          filter t' b (* filte tree with optional condition *)
      | None -> t
    in
    aux t.tree []

  (* NOTE: reset underapproximates the filter operation to guarantee soundness. 
     Currently this limits the set of supported domains to polyhedra *)

  let reset ?mask t e =
    let env = t.env in
    let t1 = t.tree in
    let rec reset flag t =
      match t with
      | Bot -> Bot
      | Leaf f -> if flag && F.is_bot f then Leaf f else Leaf (F.reset f)
      | Node (c, l, r) -> Node (c, reset flag l, reset flag r)
    in
    let expr, _, _ = e in
    let filter =
      if B.is_representable expr then filter ~controllable:false
      else ubwd_filter ~controllable:false
    in
    let t2 =
      match mask with
      | None -> reset false (tree (filter t e))
      | Some mask -> reset true (tree (filter mask e))
    in
    let rec aux (t1, t2) =
      match (t1, t2) with
      | _, Bot | Bot, _ -> t1
      | Leaf f1, Leaf f2 -> Leaf f2
      | Node ((c1, nc1), l1, r1), Node ((c2, nc2), l2, r2) when C.is_eq c1 c2 ->
          Node ((c1, nc1), aux (l1, l2), aux (r1, r2))
      | _ -> raise (Invalid_argument "reset:")
    in
    { tree = aux (tree_unification t1 t2 env); env }

  let refine t b = { tree = t.tree; env = { t.env with domain = Some b } }

  (**)

  let compress t =
    let env = t.env in
    let f_env = env.f_env in
    let domain = env.domain in
    let rec aux t cs =
      match t with
      | Bot | Leaf _ -> t
      | Node ((c, nc), l, r) -> (
          let l = aux l (c :: cs) in
          let r = aux r (nc :: cs) in
          match (l, r) with
          | Bot, Bot -> Bot
          | Leaf f1, Leaf f2 when F.is_bot f1 && F.is_bot f2 -> Leaf f1
          | Leaf f1, Leaf f2 when F.defined f1 && F.defined f2 ->
              let b1 =
                match domain with
                | None -> B.inner f_env (c :: cs)
                | Some domain ->
                    B.meet COMPUTATIONAL (B.inner f_env (c :: cs)) domain
              in
              if F.is_eq b1 f1 f2 then Leaf f2
              else
                let b2 =
                  match domain with
                  | None -> B.inner f_env (nc :: cs)
                  | Some domain ->
                      B.meet COMPUTATIONAL (B.inner f_env (nc :: cs)) domain
                in
                if F.is_eq b2 f1 f2 then Leaf f1 else Node ((c, nc), l, r)
          | Leaf f1, Leaf f2 when F.is_top f1 && F.is_top f2 -> Leaf f1
          | Leaf f1, Node ((c2, nc2), Leaf f2, r2)
            when F.is_bot f1 && F.is_bot f2 ->
              aux (Node ((c2, nc2), Leaf f1, r2)) cs
          | Leaf f1, Node ((c2, nc2), Leaf f2, r2)
            when F.defined f1 && F.defined f2 ->
              (* e.g., NODE( y >= 2, LEAF 3y+2, NODE( y >= 1, LEAF 5, LEAF 1 )) *)
              let b2 =
                match domain with
                | None -> B.inner f_env (c2 :: nc :: cs)
                | Some domain ->
                    B.meet COMPUTATIONAL (B.inner f_env (c2 :: nc :: cs)) domain
              in
              if F.is_eq b2 f1 f2 then aux (Node ((c2, nc2), Leaf f1, r2)) cs
              else Node ((c, nc), l, r)
          | Leaf f1, Node ((c2, nc2), Leaf f2, r2)
            when F.is_top f1 && F.is_top f2 ->
              aux (Node ((c2, nc2), Leaf f1, r2)) cs
          | ( Node ((c1, nc1), Leaf f1, Leaf f2),
              Node ((c2, nc2), Node ((c3, nc3), Leaf f3, Leaf f4), r2) )
            when C.is_eq c1 c3 && F.defined f1 && F.defined f2 && F.defined f3
                 && F.defined f4 ->
              (* e.g., NODE( x >= 2, NODE( y >= 1, LEAF 7x+3y-5, LEAF 1 ), NODE( x >= 1, NODE( y >= 1, LEAF 3y+2, LEAF 1 ), LEAF 1 ) *)
              let b3 =
                match domain with
                | None -> B.inner f_env (c3 :: c2 :: nc :: cs)
                | Some domain ->
                    B.meet COMPUTATIONAL
                      (B.inner f_env (c3 :: c2 :: nc :: cs))
                      domain
              in
              let b4 =
                match domain with
                | None -> B.inner f_env (nc3 :: c2 :: nc :: cs)
                | Some domain ->
                    B.meet COMPUTATIONAL
                      (B.inner f_env (nc3 :: c2 :: nc :: cs))
                      domain
              in
              if F.is_eq b3 f1 f3 && F.is_eq b4 f2 f4 then
                aux
                  (Node ((c2, nc2), Node ((c3, nc3), Leaf f1, Leaf f2), r2))
                  cs
              else Node ((c, nc), l, r)
          | _ -> Node ((c, nc), l, r))
    in
    { tree = aux t.tree []; env }

  let reinit t =
    let rec aux t =
      match t with
      | Bot -> Bot
      | Leaf f -> Leaf (F.reinit f)
      | Node (c, l, r) -> Node (c, aux l, aux r)
    in
    { tree = aux t.tree; env = t.env }

  let learn t1 t2 =
    (* t1 learns t2 *)
    let domain1 = t1.env.domain
    and domain2 =
      t2.env.domain
      (*in  t2.domain \subseteq t1.domain *)
    in
    let env = t1.env in
    let f_env = env.f_env in
    let rec aux (t1, t2) cs =
      match (t1, t2) with
      | Bot, Bot -> Bot
      | Leaf _, Bot ->
          let b1 =
            match domain1 with
            | None -> B.inner f_env cs
            | Some domain1 -> B.meet COMPUTATIONAL (B.inner f_env cs) domain1
          in
          if B.is_bot b1 then Bot else t1
      | Bot, Leaf _ ->
          let b2 =
            match domain2 with
            | None -> B.inner f_env cs
            | Some domain2 -> B.meet COMPUTATIONAL (B.inner f_env cs) domain2
          in
          if B.is_bot b2 then t1
          else
            let b1 =
              match domain1 with
              | None -> B.inner f_env cs
              | Some domain1 -> B.meet COMPUTATIONAL (B.inner f_env cs) domain1
            in
            if B.is_bot b1 then Bot else t2
      | Leaf f1, Leaf f2 ->
          let b2 =
            match domain2 with
            | None -> B.inner f_env cs
            | Some domain2 -> B.meet COMPUTATIONAL (B.inner f_env cs) domain2
          in
          if B.is_bot b2 then t1
          else
            let b1 =
              match domain1 with
              | None -> B.inner f_env cs
              | Some domain1 -> B.meet COMPUTATIONAL (B.inner f_env cs) domain1
            in
            if B.is_bot b1 then Bot else Leaf (F.learn b1 f1 f2)
      | Node ((c1, nc1), l1, r1), Node ((c2, nc2), l2, r2)
        when C.is_eq c1 c2 (* c1 = c2 *) ->
          let l = aux (l1, l2) (c1 :: cs) in
          let r = aux (r1, r2) (nc1 :: cs) in
          Node ((c1, nc1), l, r)
      | Node ((c1, nc1), l1, r1), Node ((c2, _), _, _)
        when C.is_leq c1 c2 (* c1 < c2 *) ->
          let l = aux (l1, t2) (c1 :: cs) in
          let r = aux (r1, t2) (nc1 :: cs) in
          Node ((c1, nc1), l, r)
      | Node ((c1, _), _, _), Node ((c2, nc2), l2, r2)
        when C.is_leq c2 c1 (* c1 > c2 *) ->
          let l = aux (t1, l2) (c2 :: cs) in
          let r = aux (t1, r2) (nc2 :: cs) in
          Node ((c2, nc2), l, r)
      | Node ((c1, nc1), l1, r1), _ ->
          let l = aux (l1, t2) (c1 :: cs) in
          let r = aux (r1, t2) (nc1 :: cs) in
          Node ((c1, nc1), l, r)
      | _, Node ((c2, nc2), l2, r2) ->
          let l = aux (t1, l2) (c2 :: cs) in
          let r = aux (t1, r2) (nc2 :: cs) in
          Node ((c2, nc2), l, r)
    in
    (* handling the case when t2.domain is defined by constraints not present in the tree(s) *)
    let ls1 =
      match domain1 with
      | None -> LSet.empty
      | Some domain1 ->
          List.fold_left
            (fun s c ->
              let nc = C.negate c in
              if C.is_leq nc c then (* c is normalized *) LSet.add (c, nc) s
              else (* c is not normalized *) LSet.add (nc, c) s)
            (tree_labels t1.tree) (B.conjunction domain1)
    in
    let ls2 =
      match domain2 with
      | None -> LSet.empty
      | Some domain2 ->
          List.fold_left
            (fun s c ->
              let nc = C.negate c in
              if C.is_leq nc c then (* c is normalized *) LSet.add (c, nc) s
              else (* c is not normalized *) LSet.add (nc, c) s)
            LSet.empty (B.conjunction domain2)
    in
    let ls = LSet.elements (LSet.diff ls2 ls1) in
    (* labels that need to be explicitely added to the tree(s) *)
    let print_domain fmt domain =
      match domain with None -> () | Some domain -> B.print fmt domain
    in
    if !tracebwd && not !minimal then (
      Format.fprintf !Config.fmt "\nLEARN :\n";
      Format.fprintf !Config.fmt "t1: DOMAIN = {%a}%a\n\n" print_domain domain1
        print_tree t1.tree;
      Format.fprintf !Config.fmt "t2: DOMAIN = {%a}%a\n\n" print_domain domain2
        print_tree t2.tree;
      List.iter
        (fun (c, nc) ->
          C.print Format.std_formatter c;
          Format.fprintf !Config.fmt "\n")
        ls;
      Format.fprintf !Config.fmt "\n");
    let add t domain bs =
      (* explicitely adding constraints to t *)
      let rec aux t bs cs =
        match bs with
        | [] -> t
        | (x, nx) :: xs -> (
            let b =
              match domain with None -> B.top f_env | Some domain -> domain
            in
            let bx = B.inner f_env [ x ] in
            if B.is_leq COMPUTATIONAL b bx then (* x is wanted *)
              let bcs = B.inner f_env cs in
              if B.is_bot (B.meet COMPUTATIONAL bx bcs) then
                (* x is conflicting *) Bot
              else (* x is neither redundant nor conflicting *)
                match t with
                | Node ((c, nc), l, r) when C.is_eq c x (* c = x *) -> (
                    let l = aux l xs (c :: cs) in
                    match l with Bot -> Bot | _ -> Node ((c, nc), l, Bot))
                | Node ((c, nc), l, r) when C.is_leq c x (* c < x *) -> (
                    let bc = B.inner f_env [ c ] in
                    if B.is_bot (B.meet COMPUTATIONAL bc bcs) then
                      (* c is conflicting *)
                      aux r bs cs
                    else (* c is neither redundant nor conflicting *)
                      let l = aux l bs (c :: cs) in
                      let r = aux r bs (nc :: cs) in
                      match (l, r) with
                      | Bot, Bot -> Bot
                      | Bot, Node (_, Bot, _) -> r
                      | _ -> Node ((c, nc), l, r))
                | _ -> (
                    let l = aux t xs (x :: cs) in
                    match l with Bot -> Bot | _ -> Node ((x, nx), l, Bot))
            else (* nx is wanted *)
              let bcs = B.inner f_env cs in
              if B.is_bot (B.meet COMPUTATIONAL bx bcs) then
                (* x is conflicting *)
                aux t xs cs
              else (* x is neither redundant nor conflicting *)
                match t with
                | Node ((c, nc), l, r) when C.is_eq c x (* c = x *) -> (
                    let r = aux r xs (nc :: cs) in
                    match r with Bot -> Bot | _ -> Node ((c, nc), Bot, r))
                | Node ((c, nc), l, r) when C.is_leq c x (* c < x *) -> (
                    let bc = B.inner f_env [ c ] in
                    if B.is_bot (B.meet COMPUTATIONAL bc bcs) then
                      (* c is conflicting *)
                      aux r bs cs
                    else (* c is neither redundant nor conflicting *)
                      let l = aux l bs (c :: cs) in
                      let r = aux r bs (nc :: cs) in
                      match (l, r) with
                      | Bot, Bot -> Bot
                      | Bot, Node (_, Bot, _) -> r
                      | _ -> Node ((c, nc), l, r))
                | _ -> (
                    let r = aux t xs (nx :: cs) in
                    match r with Bot -> Bot | _ -> Node ((x, nx), Bot, r)))
      in
      aux t bs []
    in
    let tree2 = match ls with [] -> t2.tree | _ -> add t2.tree domain2 ls in
    if !tracebwd && not !minimal then (
      Format.fprintf !Config.fmt "t0: DOMAIN = {%a}%a\n\n" print_domain domain2
        print_tree t2.tree;
      Format.fprintf !Config.fmt "t2: DOMAIN = {%a}%a\n\n" print_domain domain2
        print_tree tree2;
      Format.fprintf !Config.fmt "t: DOMAIN = {%a}%a\n" print_domain domain1
        print_tree
        (aux (t1.tree, tree2) []));
    { tree = aux (t1.tree, tree2) []; env = t1.env }

  let conflict t =
    let env = t.env in
    let f_env = env.f_env in
    let domain = env.domain in
    let rec aux t cs =
      match t with
      | Bot ->
          let b =
            match domain with
            | None -> B.inner f_env cs
            | Some domain -> B.meet COMPUTATIONAL (B.inner f_env cs) domain
          in
          if B.is_bot b then [] else [ b ]
      | Leaf f ->
          let b =
            match domain with
            | None -> B.inner f_env cs
            | Some domain -> B.meet COMPUTATIONAL (B.inner f_env cs) domain
          in
          if F.defined f || B.is_bot b then [] else [ b ]
      | Node ((c, nc), l, r) -> aux l (c :: cs) @ aux r (nc :: cs)
    in
    aux t.tree []

  let print fmt t =
    let env = t.env in
    let f_env = env.f_env in
    let domain = env.domain in
    (* let print_domain fmt domain =
      match domain with
      | None -> ()
      | Some domain -> B.print fmt domain
    in *)
    let rec aux t cs =
      match t with
      | Bot ->
          let b =
            match domain with
            | None -> B.inner f_env cs
            | Some domain -> B.meet COMPUTATIONAL (B.inner f_env cs) domain
          in
          if B.is_bot b then () else Format.fprintf fmt "%a ? BOT\n" B.print b
      | Leaf f ->
          let b =
            match domain with
            | None -> B.inner f_env cs
            | Some domain -> B.meet COMPUTATIONAL (B.inner f_env cs) domain
          in
          if B.is_bot b then ()
          else Format.fprintf fmt "%a ? %a\n" B.print b F.print f
      | Node ((c, nc), l, r) ->
          aux r (nc :: cs);
          aux l (c :: cs)
      (* in aux t.tree []; Format.fprintf fmt "\nDOMAIN = {%a}%a\n" print_domain domain (print_tree ) t.tree *)
      (* Format.fprintf fmt "\nDOMAIN = {%a}%a\n" print_domain domain (print_tree ) t.tree; *)
    in
    aux t.tree []

  (* 
     Takes 't' and 't_mask' as argument and cuts away all parts of 't'
     that are not part of the domain of 't_mask'.

     This means that if some part of the domain of the 't_mask' is undefined (i.e. bottom, top or NIL)
     then the corresponding part in 't' is replaced with a bottom leaf.

     NOTE: mask is only monotone w.r.t. the APPROXIMATION order
  *)
  let mask t t_mask =
    let env = t.env in
    let f_env = env.f_env in
    let botLeaf = Leaf (F.bot f_env) in
    let isDefined f = not (F.is_bot f || F.is_top f) in
    let fBotLeft _ _ = Bot in
    (* LHS is bottom, keep it that way *)
    let fBotRight _ fLeft = if isDefined fLeft then botLeaf else Leaf fLeft in
    (* if RHS is NIL and LHS is defined then go to bottom *)
    let fLeaf cs l1 l2 =
      if isDefined l2 then Leaf l1 (* don't change if RHS is defined*)
      else if
        (* if RHS is not defined, then go to bottom if LHS is not already top or bottom*)
        isDefined l1
      then botLeaf
      else Leaf l1
    in
    {
      tree = tree_join_helper fBotLeft fBotRight fLeaf t.tree t_mask.tree env;
      env;
    }

  (*
     This function is used to implement the CTL 'until' operator. It takes three arguments 't', 't_keep' and 't_reset'. 
     For a given 'until' formula 'f1 U f2': 
     - 't' is the decision tree that should be modified to satisfy the 'f1 U f2' formula.
     - 't_keep' corresponds to the decision tree representing 'f1' 
     - 't_reset' corresponds to the decision tree representing 'f2'

     The function first filters out all leafs in 't' that are not also part of the domain of 't_keep' and 't_reset'. 
     Then it resets all leafs in 't' that are also part of the domain of 't_reset'. 

     The intuition behind this is to set the ranking function to zero for all partitions that satisfy 'f1' and
     to remove all partitions from the domain of 't' that don't satisfy 'f1' or 'f2' 
     an therefore excluding traces not satisfying the 'f1 U f2' property.
  *)
  let until t t_keep t_reset =
    let env = t.env in
    let f_env = env.f_env in
    let isDefined f = not (F.is_bot f || F.is_top f) in
    let rec filter (t, t_valid) =
      match (t, t_valid) with
      | Bot, _ | _, Bot -> t
      | Leaf f, Leaf f_valid ->
          Leaf (if isDefined f_valid then f else F.bot f_env)
      | Node (c, l1, r1), Node (_, l2, r2) ->
          Node (c, filter (l1, l2), filter (r1, r2))
      | _ -> raise (Invalid_argument "until: Invalid Tree shape")
    in
    let rec reset (t, t_res) =
      match (t, t_res) with
      | Bot, _ | _, Bot -> t
      | Leaf f, Leaf f_reset ->
          Leaf (if isDefined f_reset then F.reset f else f)
      | Node (c, l1, r1), Node (_, l2, r2) ->
          Node (c, reset (l1, l2), reset (r1, r2))
      | _ -> raise (Invalid_argument "until: Invalid Tree shape")
    in
    let t_valid = tree (join COMPUTATIONAL t_keep t_reset) in
    (* join t_reset and t_keep to get the entire domain for which 't' is still defined*)
    let t_filtered = filter (tree_unification t.tree t_valid env) in
    (* filter out all parts of 't' that are not part of the domain of 't_keep' or 't_reset'*)
    let t_reset = reset (tree_unification t_filtered t_reset.tree env) in
    (* reset all parts of the 't' that are defined in 't_reset' *)
    { tree = t_reset; env }

  (*
    Complements the domain of a tree:
    - every leaf that is defined i.e. not top or bottom goes to bottom
    - every bottom leaf is replaced with a 'zero' leaf
    - top stays top

    This function assumes that there are no NIL nodes in the tree
  *)
  let complement t =
    let env = t.env in
    let f_env = env.f_env in
    let zeroLeaf = Leaf (F.zero f_env) in
    let botLeaf = Leaf (F.bot f_env) in
    let rec aux tree =
      match tree with
      | Bot ->
          tree
          (* NIL nodes are unchanged because they represent missing information *)
      | Leaf f when F.is_bot f -> zeroLeaf (* bottom goes to constant zero *)
      | Leaf f when F.is_top f -> tree (* top stays top *)
      | Leaf f -> botLeaf (* everything else goes to bottom *)
      | Node (c, l, r) -> Node (c, aux l, aux r)
    in
    { tree = aux t.tree; env }

  (* Compute the vulnerability analysis, right now the algorithm is naif and doesnot implement the dynamic programming *)
  (* let vulnerable t : Polka.strict Polka.t Vulnerability.t list =
    (* print_tree t.vars Format.std_formatter (compress t).tree ; *)
    let manager = Polka.manager_alloc_strict () in
    Format.print_newline ();
    let forget x = (AbstractSyntax.A_var x, A_RANDOM) in
    let rec unconstraint t cns =
      match t with
      | Bot -> (false, [ cns ])
      | Leaf f when F.is_bot f -> (false, [ cns ])
      | Leaf f when F.is_top f -> (false, [ cns ])
      | Leaf f -> (true, [ cns ])
      | Node ((c, nc), l, r) -> (
          let b, cns1 = unconstraint l (c :: cns) in
          let b2, cns2 = unconstraint r (nc :: cns) in
          match (b, b2) with
          | true, true -> (true, cns1 @ cns2)
          | true, false -> (true, cns1)
          | false, true -> (true, cns2)
          | false, false -> (false, []))
    in
    let v = t.vars in
    let rec aux vars acc t =
      match vars with
      | [] -> []
      | x :: [] ->
          let t' = bwd_assign t (forget x) in
          (* Format.printf "\n Remove last %s \n" x.varName; 
        print_tree t.vars Format.std_formatter t'.tree ;  *)
          let b, cons = unconstraint t'.tree [] in
          let left_sub = if b then [ (x :: acc, cons) ] else [] in
          (* Format.printf "\n Reste last %s \n" x.varName;
        print_tree t.vars Format.std_formatter t.tree ;  *)
          let b, cons = unconstraint t.tree [] in
          let right_sub = if b then [ (acc, cons) ] else [] in
          left_sub @ right_sub
      | x :: q ->
          let t' = bwd_assign t (forget x) in
          (* Format.printf "\nRemove %s \n" x.varName; 
        print_tree t.vars Format.std_formatter t'.tree ;  *)
          let l1 = aux q (x :: acc) t' in
          (* Format.printf "\n Reste %s \n" x.varName;
        print_tree t.vars Format.std_formatter t.tree ; *)
          let l2 = aux q acc t in
          l1 @ l2
    in
    let transform clist arr =
      List.iteri (fun i c -> Lincons1.array_set arr i c) clist
    in
    aux v [] t |> fun uncontrolled ->
    List.map
      (fun (l, c) ->
        ( l,
          Array.of_list
            (List.map (fun c -> Lincons1.array_make t.env (List.length c)) c) ))
      uncontrolled
    |> fun arr ->
    List.iteri
      (fun i (l, ar) ->
        let cons = snd (List.nth uncontrolled i) in
        List.iteri (fun k c -> transform c ar.(k)) cons)
      arr
    |> fun () ->
    List.map
      (fun (l, a) ->
        (l, Array.map (fun a -> Abstract1.of_lincons_array manager t.env a) a))
      arr
    |> fun j ->
    List.fold_left
      (fun (a : (var list * Polka.strict Polka.t Abstract1.t array) list)
           (b, arr) ->
        if
          List.exists
            (fun (l, _) ->
              List.compare_lengths l b > 0
              && List.for_all (fun el -> List.mem el l) b)
            a
        then a
        else (b, arr) :: a)
      [] j
    |> fun j ->
    List.map
      (fun (b, arr) ->
        let nb = List.filter (fun x -> not (List.mem x b)) t.vars in
        { safe = b; vulnerables = nb; cons = arr })
      j *)
end

module TSAB = Decision_Tree (AB)
module TSOB = Decision_Tree (OB)
module TSAO = Decision_Tree (AO)
module TSOO = Decision_Tree (OO)
module TSAP = Decision_Tree (AP)
module TSOP = Decision_Tree (OP)
