Require Import VarJ_Syntax.

Open Scope nat_scope.

Set Implicit Arguments.

(** Auxiliaries *)

Fixpoint flatten (A: Type) (ll: list (list A)): list A :=
  match ll with
  | nil => nil
  | hd :: tl => hd ++ (flatten tl)
  end.


(** Opening for types *)
Fixpoint open_t (k:nat) (t:typ) (ts:list typ) {struct t} : typ :=
  let open_t_bound :=
    fun (k:nat) (tbnd:t_bound) (ts:list typ) =>
      let (b, t) := tbnd in (open_b k b ts, open_t k t ts)
  in
  let open_t_bounds :=
    fun (k:nat) (tbnds:t_bounds) (ts:list typ) =>
      List.map (fun tbnd => open_t_bound k tbnd ts) tbnds
  in
  match t with
    | t_ext bounds N =>
        t_ext (open_t_bounds (S k) bounds ts) (open_n (S k) N ts)
    | t_bvar n1 n2 =>
        match (nat_compare n1 k) with
          | Eq => List.nth n2 ts t
          | _  => t
          end
    | t_fvar x => t
  end

with open_b (k:nat) (B:typ_b) (ts:list typ) {struct B} : typ_b :=
  match B with
    | b_typ t => b_typ (open_t k t ts)
    | b_bot   => b_bot
  end

with open_n (k:nat) (N:typ_n) (ts:list typ) {struct N} : typ_n :=
  match N with n_typ C ts' =>
    n_typ C (List.map (fun t => open_t k t ts) ts')
  end.

Definition open_p (k:nat) (p:typ_p) (ts:list typ) : typ_p :=
  match p with
    | p_typ t => p_typ (open_t k t ts)
    | p_inf => p_inf
  end.

Definition open_r (k:nat) (r:typ_r) (ts:list typ) : typ_r :=
  match r with
    | typ_r_n N => typ_r_n (open_n k N ts)
    | typ_r_fvar X => r
  end.

Definition open_ts (k:nat) (ts':list typ) (ts:list typ) : list typ :=
  List.map (fun t => open_t k t ts) ts'.

Definition open_ps (k:nat) (ps:list typ_p) (ts:list typ) : list typ_p :=
  List.map (fun p => open_p k p ts) ps.

Definition open_bs (k:nat) (bs:list typ_b) (ts:list typ) : list typ_b :=
  List.map (fun b => open_b k b ts) bs.

Definition open_ns (k:nat) (ns:list typ_n) (ts:list typ) : list typ_n :=
  List.map (fun n => open_n k n ts) ns.

Definition open_t_bound (k:nat) (tbnd:t_bound) (ts:list typ) : t_bound :=
  let (b, t) := tbnd in (open_b k b ts, open_t k t ts).

Definition open_t_bounds (k:nat) (tbnds:t_bounds) (ts:list typ) : t_bounds :=
  List.map (fun tbnd => open_t_bound k tbnd ts) tbnds.

Definition open_tv_bound (k:nat) (tvbnd:tv_bound) (ts:list typ) : tv_bound :=
  match tvbnd with (v, b, t) => (v, open_b k b ts, open_t k t ts) end.

Definition open_tv_bounds (k:nat) (tvbnds:tv_bounds) (ts:list typ) : tv_bounds :=
  List.map (fun tvbnd => open_tv_bound k tvbnd ts) tvbnds.

Definition open_msig (k:nat) (sig:msig) (ts:list typ) : msig :=
  match sig with (tbnds, ts', t) =>
        (open_t_bounds (S k) tbnds ts, open_ts (S k) ts' ts, open_t (S k) t ts)
  end.

Fixpoint open_e (k:nat) (expr:exp) (es:list exp) {struct expr} : exp :=
  match expr with
    | e_field e f => e_field (open_e k e es) f
    | e_minvk e m ps es' =>
        e_minvk (open_e k e es) m ps
                (List.map (fun e' => open_e k e' es) es')
    | e_new N es' =>
        e_new N (List.map (fun e' => open_e k e' es) es')
    | e_fvar _ => expr
    | e_bvar n => List.nth n es expr
  end.


Fixpoint open_e_t (k:nat) (expr:exp) (ts:list typ) {struct expr} : exp :=
  match expr with
    | e_field e f => e_field (open_e_t k e ts) f
    | e_minvk e m ps es =>
        e_minvk
          (open_e_t k e ts)
          m
          (open_ps k ps ts)
          (List.map (fun e' => open_e_t k e' ts) es)
    | e_new N es =>
        e_new (open_n k N ts) (List.map (fun e' => open_e_t k e' ts) es)
    | _ => expr
  end.


Definition names2fvars_t (names: list tname) : list typ :=
  List.map (fun X => t_fvar X) names.

Definition open_t_with_names (k:nat) (t:typ) (names:list tname) :=
  (open_t k t (names2fvars_t names)).

Definition open_n_with_names (k:nat) (n:typ_n) (names:list tname) :=
  (open_n k n (names2fvars_t names)).

Definition open_b_with_names (k:nat) (b:typ_b) (names:list tname) :=
  (open_b k b (names2fvars_t names)).

Definition open_ts_with_names (k:nat) (ts:list typ) (names:list tname) :=
  (open_ts k ts (names2fvars_t names)).

Definition open_ns_with_names (k:nat) (ns:list typ_n) (names:list tname) :=
  (open_ns k ns (names2fvars_t names)).

Definition open_t_bound_with_names (k:nat) (tbnd:t_bound) (names:list tname) :=
  (open_t_bound k tbnd (names2fvars_t names)).


Definition open_t_bounds_with_names (k:nat) (tbnds:t_bounds) (names:list tname) :=
  (open_t_bounds k tbnds (names2fvars_t names)).

Definition open_e_t_with_names (k:nat) (e:exp) (names:list tname) :=
  (open_e_t k e (names2fvars_t names)).

Definition openToCtxt_tbounds (k:nat) (names : list tname) (tbnds: t_bounds) : cxt_t :=
  combine names (open_t_bounds k tbnds (names2fvars_t names)).

Definition openToCtxt_tvbounds (k:nat) (names : list tname) (tvbnds: tv_bounds) : cxt_t :=
  openToCtxt_tbounds k names (tvbounds_2_tbounds tvbnds).


(** May need to check for locally closed terms *)
(** Don't think the # of binders needs to be specified
  * because it seems it always is equal to the length
  * of some given set of binders *)


Definition tbounds_matches_cxt (tbnds : t_bounds) (tcxt : cxt_t) : Prop :=
  (openToCtxt_tbounds 0 (dom tcxt) tbnds) = tcxt.

Hint Unfold tbounds_matches_cxt.

Inductive boundsOfTyp_matches_cxt : typ -> cxt_t -> Prop :=
| boundsOfTyp_matches_cxt_ext :
    forall tbnds N tcxt,
      tbounds_matches_cxt tbnds tcxt ->
      boundsOfTyp_matches_cxt (t_ext tbnds N) tcxt

| boundsOfTyp_matches_cxt_fvar :
    forall X, boundsOfTyp_matches_cxt (t_fvar X) nil.

Hint Constructors boundsOfTyp_matches_cxt.

Inductive wide_boundsOfTyp_matches_cxt : list typ -> list cxt_t -> Prop :=
| wide_boundsOfTyp_matches_cxt_nil : wide_boundsOfTyp_matches_cxt nil nil
| wide_boundsOfTyp_matches_cxt_cons :
    forall t ts tcxt tcxts,
      boundsOfTyp_matches_cxt t tcxt ->
      wide_boundsOfTyp_matches_cxt ts tcxts ->
      wide_boundsOfTyp_matches_cxt (t::ts) (tcxt::tcxts).

Hint Constructors wide_boundsOfTyp_matches_cxt.

Fixpoint subst_t (xs: list tname) (ts: list typ) (t: typ) : typ :=
  let subst_t_bound :=
    fun (xs: list tname) (ts: list typ) (tbnd: t_bound) =>
      let (b, t) := tbnd in (subst_b xs ts b, subst_t xs ts t)
  in
  let subst_t_bounds :=
    fun (xs: list tname) (ts: list typ) (tbnds: t_bounds) =>
      List.map (fun tbnd => subst_t_bound xs ts tbnd) tbnds
  in
  match t with
    | t_ext tbnds N =>
        t_ext (subst_t_bounds xs ts tbnds) (subst_n xs ts N)
    | t_bvar _ _ => t
    | t_fvar x =>
        match get x (combine xs ts) with
          | Some t' => t'
          | None => t
        end
  end

with subst_b (xs: list tname) (ts: list typ) (b: typ_b) : typ_b :=
  match b with
    | b_typ t => b_typ (subst_t xs ts t)
    | b_bot   => b_bot
  end

with subst_n (xs: list tname) (ts: list typ) (n: typ_n) : typ_n :=
  match n with n_typ C ts' =>
    n_typ C (List.map (fun t => subst_t xs ts t) ts')
  end.


Definition subst_p (xs: list tname) (ts: list typ) (p: typ_p) : typ_p :=
  match p with
    | p_typ t => p_typ (subst_t xs ts t)
    | p_inf => p_inf
  end.

Definition subst_ts (xs: list tname) (ts: list typ) (ts': list typ) : list typ :=
  List.map (fun t => subst_t xs ts t) ts'.

Definition subst_ps (xs: list tname) (ts: list typ) (ps: list typ_p) : list typ_p :=
  List.map (fun p => subst_p xs ts p) ps.

Definition subst_bs (xs: list tname) (ts: list typ) (bs: list typ_b) : list typ_b :=
  List.map (fun b => subst_b xs ts b) bs.

Definition subst_ns (xs: list tname) (ts: list typ) (ns: list typ_n) : list typ_n :=
  List.map (fun n => subst_n xs ts n) ns.

Definition subst_t_bound (xs: list tname) (ts: list typ) (tbnd: t_bound) : t_bound :=
  let (b, t) := tbnd in (subst_b xs ts b, subst_t xs ts t).

Definition subst_t_bounds (xs: list tname) (ts: list typ) (tbnds: t_bounds) : t_bounds :=
 List.map (fun tbnd => subst_t_bound xs ts tbnd) tbnds.


Fixpoint subst_e (xs: list tname) (es: list exp) (expr: exp) : exp :=
  match expr with
    | e_field e f => e_field (subst_e xs es e) f
    | e_minvk e m ps es' =>
        e_minvk (subst_e xs es e) m ps
                (List.map (fun e' => subst_e xs es e') es')
    | e_new N es' =>
        e_new N (List.map (fun e' => subst_e xs es e') es')
    | e_bvar _ => expr
    | e_fvar x =>
        match get x (combine xs es) with
          | Some e' => e'
          | None => expr
        end
  end.

(** Implementing distinct predicate based on its definition
  * in the paper (Arthur Chargueraud, 2012).
  * distinct predicate is used for co-finite quantification.
  *) 
Inductive distinct (A:Type) : list A -> nat -> list A -> Prop :=
| distinct_nil  : forall L, distinct L 0 nil
| distinct_cons : forall L n x xs,
                  ~(In x L) ->
                  distinct (x::L) n xs ->
                  distinct L (S n) (x::xs).

Hint Constructors distinct.

Fixpoint fresh_list (L: list atom) (n: nat) : list atom :=
  match n with
    | 0 => nil
    | (S m) =>
        let (x, _) := atom_fresh_for_list L in
        x::(fresh_list (x::L) m)
  end.


