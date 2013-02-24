Require Import VarJ_Syntax.

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

Definition openToCtxt_tbounds (names : list tname) (tbnds: t_bounds) : cxt_t :=
  combine names (open_t_bounds 0 tbnds (names2fvars_t names)).

Definition openToCtxt_tvbounds (names : list tname) (tvbnds: tv_bounds) : cxt_t :=
  openToCtxt_tbounds names (tvbounds_2_tbounds tvbnds).


Definition tbounds_matches_cxt (tbnds : t_bounds) (tcxt : cxt_t) : Prop :=
  (openToCtxt_tbounds (dom tcxt) tbnds) = tcxt.


Inductive boundsOfTyp_matches_cxt : typ -> cxt_t -> Prop :=
| boundsOfTyp_matches_cxt_ext :
    forall tbnds N tcxt,
      tbounds_matches_cxt tbnds tcxt ->
      boundsOfTyp_matches_cxt (t_ext tbnds N) tcxt

| boundsOfTyp_matches_cxt_fvar :
    forall X, boundsOfTyp_matches_cxt (t_fvar X) nil.


(** Implementing distinct predicate based on its definition
  * in the paper (Arthur Chargueraud, 2012).
  * distinct predicate is used for co-finite quantification.
  *) 
Inductive distinct (A:Type) : list A -> nat -> list A -> Prop :=
| distinct_nil  : forall L, distinct L 0 nil
| distinct_cons : forall L n x xs,
                  ~(In x L) ->
                  distinct (cons x L) n xs ->
                  distinct L (S n) (cons x xs).

(*
Eval simpl in 1::2::nil.

Example distinct_test : (distinct (1::2::nil) 0 nil).
Proof.
apply distinct_nil.
Qed.


Eval simpl in
  combine (combine (1::2::nil) (1::2::nil)) (1::2::nil).
*)


Definition subst_n (xs: list tname) (ts: list typ) (n: typ_n) : typ_n := n.


(** May need to check for locally closed terms *)
(** Don't think the # of binders needs to be specified
  * because it seems it always is equal to the length
  * of some given set of binders *)


