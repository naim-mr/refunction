# Plan de route — signatures modulaires, domaine linéaire seul

## 0. Cadre

**Objectif (08/10/2026).** On ne travaille qu'avec les contraintes linéaires
APRON, mais les signatures (`CONSTRAINT`, `PARTITION`, `FUNCTION`) doivent être
*réellement* génériques : rien de propre au linéaire ni à une analyse
particulière, pour pouvoir rebrancher d'autres domaines plus tard (§4) sans
retoucher les interfaces. Aucun nouveau domaine ni combinateur dans ce
périmètre.

Pile actuelle :

```
CONSTRAINT     sig/Constraints.ml   AP_LinearConstraint (seule instance)
 └ PARTITION   sig/Ranking.ml       AP_Partition (N) (C)  → B, O, P (Box/Oct/Poly)
    └ FUNCTION sig/Ranking.ml       AP_Affine (N) (B), AP_OrdinalValued (F)
       └ Decision_Tree (F : FUNCTION) : RANKING_FUNCTION → TSA{B,O,P}, TSO{B,O,P}
```

**Règle** : chaque étape se fait sous régression verte (§3.1), lois vertes dès
qu'elles existent (§3.2).

## 1. Diagnostic — où les signatures ne sont pas génériques

Vérifié dans le code le 08/10/2026.

| # | Où | Problème |
|---|---|---|
| a | `CONSTRAINT.expand` | « égalités → `>=`/`<=` » : linéaire. Utilisé seulement par `AP_Partition`. |
| b | `CONSTRAINT.similar` | « égal à la constante près » : linéaire dans son énoncé, mais **utilisé 18× par `Decision_Tree`** → reste, avec une doc générique (défaut admissible : `is_eq`). |
| c | `CONSTRAINT.t = { cons; env }` | record déclaré dans la signature ⇒ chaque instance crée un **nouveau** `t` : `B.C.t ≠ O.C.t ≠ P.C.t` alors que tous sont des `Lincons1.t`. |
| d | `PARTITION` | porte des détails d'analyse : `?controllable` (ATL), `assume ?pow` (CDA, 1 usage dans `Cda.ml`), `is_representable` (frontend). `constraints` est inutilisé (doublon de `conjunction`). |
| e | `AP_Partition` | lit `!Config.domain = "polyhedra"` et `!Config.analysis = "atl"` (l. 460, 626) : le foncteur sait quelle instance il est. Idem `AP_Affines` avec `!Config.resilience`/`!Config.property` (l. 261–303). |
| f | `AP_CONSTRAINT.linexpr` | inutilisé. |
| g | `AP_NUMERIC` | quasi-doublon de `AP_PARTITION`, n'existait que pour les produits ; seul client : la signature de `AP_Affine`. |
| h | scellement opaque | `AP_Partition … : AP_PARTITION` cache `C = AP_LinearConstraint`, `N = N`. |
| i | `env` | `lincons_env = { vars; ap_env }` duplique l'`Environment.t` de la `Lincons1.t`, et la correspondance `var` ↔ nom APRON est re-dérivée à la main (cause du bug d'affichage du 13/08). |

Ce qui est déjà générique : `Decision_Tree` (n'utilise que `compare`, `negate`,
`similar`, `conjunction` et les opérations de `B`/`F` ; le code APRON vers la
l. 2035 est dans `vulnerable`, commenté) et `AP_OrdinalValued (F : FUNCTION)`.

## 2. Jalons

- [x] **J0** Build vert (13/08/2026).
- [x] **J0.5** Baseline de régression verte + garde-fou CI (13/08/2026) :
      103 rapports, couverture complète, 13 échecs déclarés, 2 régressions
      acceptées (`pending` : P3.c, existential_test4.c).
- [x] **S1 Nettoyer les signatures** (diagnostic a, d, f, g) — petit, mécanique :
      - ~~supprimer `AP_NUMERIC` ; `AP_Affine` prend `B : AP_PARTITION`~~
        (fait le 08/10/2026 — ne pas confondre avec `AP_NUMERICAL`, le
        paramètre `N` Box/Oct/Poly, qui reste) ;
      - ~~`AP_Affine` : un `Fun` vit sur `ap_env` sans `#` ; chaque opération
        étend vers `ap_env_ext` puis `restrict` le résultat~~ (fait le
        08/10/2026). Régression complète verte le 09/10/2026 (103 ok,
        `function-diff` sans régression) ;
      - `AP_Affine` : à partir d'une contrainte `a·x + k·# + c ≥ 0`, on lit `f`
        en mettant juste le coefficient de `#` à 0, ce qui suppose `k = -1`.
        Si les polyèdres renvoient `k ≠ -1`, le rang est faux, sans erreur.
        Ex. : sur `x ∈ [0,3]`, `join` de `f1 = 0` et `f2 = x - 2` donne
        `-3# + x ≥ 0`, lu comme `f = x` au lieu de `x/3`. Et si `k > 0`, la
        contrainte est une borne *inférieure*, lue comme `-f`. Box et Octagon
        restent à ±1 ; le risque concerne surtout les polyèdres. Correction :
        une fonction `of_graph` (`k < 0` → `f = g/(-k)` ; `k > 0` → écarter)
        appelée aux 5 sorties (`join` ×2, `learn`, `widen`, `extend`) à la
        place de `restrict` seul (cf. code commenté dans `extend_ranking`) ;
      - ~~supprimer `PARTITION.constraints`~~ (fait le 08/10/2026 : redondant
        avec `conjunction`, l'accès générique ; `AP_Partition.ap_constraints`
        en dérive) ;
      - ~~supprimer `AP_CONSTRAINT.linexpr`~~ (fait) ;
      - ~~déplacer `expand` de `CONSTRAINT` vers `AP_CONSTRAINT`~~ (fait) ;
      - réécrire la doc de `similar` en termes génériques — reporté : la doc
        reste formulée pour les contraintes affines tant qu'il n'y a qu'elles ;
      - (09/10/2026 : `assume` renommé `split`, contrat documenté ; on garde
        les trois dans `PARTITION`, `controllable` documenté.)
        trancher `?controllable` / `split` / `is_representable` : les garder
        dans `PARTITION` en les documentant comme capacités d'analyse, ou les
        sortir dans une extension (`ATL_PARTITION`…). À décider avant de coder.
- [ ] **S2 Sortir `Config` des domaines** (diagnostic e) : ce qui dépend de
      l'instance (polyèdres ou non) passe par `N` ; ce qui dépend de l'analyse
      (ATL, résilience) passe en paramètre explicite depuis l'itérateur.
      Ex. `AP_Partition.bwd_assign` : `if controllable &&
      N.supports_underapproximation` au lieu de lire `Config.analysis` et
      `Config.domain`. Garder `?(controllable = false)` : le défaut est la
      sur-approximation, donc sûr. (Fait le 08/10/2026 : `~random` de `F.join`
      renommé `~controllable` — c'est le choix formel join de résilience /
      d'approximation de l'assign ; `controllable` documenté dans les
      signatures.) Reste : `F.join` lit encore `Config.resilience` et
      `Config.property` (`AP_Affines.join_ranking`) ; la branche « boîte » de
      `AP_Partition.bwd_assign` ajoute à `b1` ses propres bornes, ce qui ne
      change pas sa valeur — à comprendre (forme de l'arbre ?) avant de
      décider. Au
      passage, trancher le `&& false` de `AP_Partition` l. 626 (code mort ou
      à réactiver ?).
- [ ] **S3 Scellement transparent** (diagnostic c, h) :
      `AP_PARTITION with module C = C and module N = N`, idem `AP_Affine`,
      `AP_OrdinalValued`, `Decision_Tree`. Prérequis de S4 (construire des
      `samples` hors du module).
- [ ] **S4 Lois génériques sous `dune test`** (§3.2), instanciées sur B, O, P.
      Filet de sécurité de S5 et de tout ce qui suit.
- [ ] **S5 Fiabiliser `env`** (diagnostic i) : bijection
      `apron_of_var`/`var_of_apron` exposée une fois, `ap_env` dédupliqué,
      renommage (`scope`/`dims` — c'est un univers de variables, pas un
      liage). Resserrement d'API, pas réécriture.

**Après, hors périmètre actuel** (détails dans git, version du 14/08 de ce
fichier) :
- **Widening en pipeline de passes** : `widen_right → left_unification →
  tree_unification → widen_up → extrapolation` rendu explicite, option CLI
  `-widening`, types `unified`/`canonical` pour rendre les
  `Invalid_argument "widen:aux:"` impossibles. Le **widening angélique** (TODO
  du papier) s'y branche.
- **Perf** : profiler d'abord ; probable point chaud = reconversions APRON
  (`to_apron_t` à chaque `is_leq`/`meet`) → mémo dans `AP_Partition`, puis
  abstrait incrémental dans les récursions de l'arbre ; option
  `-max-partitions k`.
- **Qualité** : réactiver les warnings un par un (`-w -9-27-32-33-35`), `.mli`,
  dédupliquer `AP_Affines` (bloc « copie de b dans un `Lincons1.array` étendu »
  ×7), hygiène du dépôt (`domains/IM`, fichiers parasites).
- **Bugs ouverts** (issues) : segfault `-Dtrue/-Dfalse`, `break` non géré,
  `input(v,lo,hi)` qui casse la linéarisation.

⚠️ Les estimations passées ont été ×2 dépassées (J0.5 : ½ j prévue, 1 j+
réelle) : toucher au code existant révèle des problèmes latents à chaque fois.

## 3. Tests

### 3.1 Régression (en place)

Référence complète : `script/WORKFLOW.md` et `script/README.md`.

```bash
script/harness.py run -o regression_out --layout flat --cover logs
script/function-diff.py logs regression_out --regression
script/harness.py bless <run>.run.json [-n]          # promouvoir un run
script/harness.py compare a.run.json b.run.json      # ablations
```

À retenir :
- `runtest.py` (rendu des tables) et la régression **n'invoquent pas
  l'analyseur pareil** : les options sont encodées dans le nom du rapport, donc
  ne jamais comparer un run de rendu à la baseline.
- La config `.json` est la source de vérité ; la couverture se calcule depuis
  les baselines (toute baseline non reproduite ⇒ rouge).
- `expected` épingle `result` (strict), `suff`/`leaves` (déterministes,
  tolérance 0), `time` (×3, non fatal), `status: FAIL` (échec connu, signalé
  le jour où il se remet à passer).

### 3.2 Lois génériques — un foncteur de test par signature

```
test/
  dune                (test (name test_domains) (libraries domains alcotest))
  Domain_laws.ml      foncteur : lois d'un CONSTRAINT
  Partition_laws.ml   foncteur : lois d'une PARTITION
  Test_domains.ml     instanciations (B, O, P) + runner
```

```ocaml
module Make (C : CONSTRAINT) (S : sig
  val name : string
  val samples : C.t list   (* choisis à la main, pas de QuickCheck au début *)
  val env : C.env
end) : sig val tests : unit Alcotest.test_case list end
```

| Loi (`CONSTRAINT`) | Énoncé |
|---|---|
| ordre total | `compare` réflexif, transitif, antisymétrique (`is_eq`) |
| négation exacte | `negate (negate c) ≡ c` ; `meet c (negate c)` est bot |
| bot | `is_bot (make_unsat env)` |
| `similar` | réflexif, symétrique, impliqué par `is_eq` |
| print | ne lève pas, y compris sur bot/top |

`PARTITION`, en plus : `meet` borne inf, `join` borne sup, `inner env [] =
top`, `widen` extensif, monotonie des transferts (`is_leq a b ⇒ is_leq
(fwd_assign a e) (fwd_assign b e)`), `bwd_assign` sur-approxime `ubwd_assign`.

Coût : ~1 j pour les deux foncteurs + instances ; ~1 h par domaine ajouté
ensuite.

## 4. Pistes — ce qu'on a retiré, pour y revenir

Tout est récupérable via git.

- **Autres domaines de contraintes.** `Congruence.ml` et `Bool_Constraint.ml`
  (supprimé le 08/10/2026, `type t = bool`, dégénéré) ; recette d'ajout : un
  `Foo_Constraint : CONSTRAINT`, sa `PARTITION`, une feuille, un `TS_Foo`, une
  option `-domain foo`, un `.c` témoin minimal (modèle : `tests/j.c`).
  Contrainte dure : **`negate` exact** ⇒ domaine clos par complément (parité
  oui, congruence mod 3 non). Les nœuds actuels sont `SUPEQ` uniquement.
- **`Conj_Partition (C : CONSTRAINT) : PARTITION`** générique (~100 lignes par
  domaine au lieu de ~350). Seulement avec deux vrais clients.
- **Projections** (`Projection.ml`, `Left_projection.ml`, écrits puis retirés
  le 08/10/2026 sans commit) : `project : Src.t -> Dst.t`, lois de correction
  et de monotonie ; `Poly_to_box` exposait les bornes de boîte d'un polyèdre
  comme nœuds supplémentaires (gain de branchement, le meet étant vide puisque
  la boîte est impliquée). Ne typait qu'avec S3.
- **Produits, un combinateur par niveau** (pas de `LATTICE` universelle : les
  opérations de `FUNCTION` sont indexées par `kind`/`B.t`/`jokers`) :
  (a) somme de `CONSTRAINT` = nœuds mixtes ; (b) produit réduit de `PARTITION`
  — le plus utile au papier, renaissance de `Partitions_Union.ml` ;
  (c) produit d'arbres, seulement pour des rangs incomparables. Partitions
  avant feuilles. Tests associés : `is_leq (reduce p) p`, idempotence, et un
  `.c` que ni l'une ni l'autre composante seule ne prouve.
- **`NUM_VIEW`** : remplacer `AP_CONSTRAINT`/`AP_PARTITION` par une vue
  `to_lincons`/`of_lincons` passée à part à la feuille affine. Ne paie qu'avec
  une partition non numérique.
- **`Decision_Tree (C) (L)`** : la feuille reçoit le chemin en argument au
  lieu de posséder sa partition → combinaisons nœuds × feuilles orthogonales.
  Même condition.
- **Passe d'extrapolation LLM** (guess-and-check) : candidats proposés par un
  LLM, acceptés seulement s'ils majorent les itérés et décroissent ;
  `Llm_oracle` derrière une signature, cache disque clé = hash du prompt.
- **Features OCaml** : modules de première classe pour le registre de
  `Main.ml`, effets pour le tracing, `let*` pour bot et pour les constructions
  non supportées du frontend, `ppx_deriving` pour `compare`/`show`. Pas de
  GADTs pour indexer les arbres.
