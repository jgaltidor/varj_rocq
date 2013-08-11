(* Variance Predicate Definitions *)

Require Import VarJ_Syntax.

Close Scope nat_scope.

Definition var_lt_op (v1:variance) (v2:variance) : bool :=
  match v1 with
    | bivar => false
    | invar =>
        match v2 with
          | invar => false
          | _ => true
        end
    | covar =>
        match v2 with
          | bivar => true
          | _ => false
        end
    | contravar =>
        match v2 with
          | bivar => true
          | _ => false
        end
    end.

Definition var_lt (v1:variance) (v2:variance) : Prop :=
  (var_lt_op v1 v2) = true.
Reserved Notation "v1 '<' v2" (at level 70, no associativity).
Notation "v1 '<' v2" := (var_lt v1 v2).

Hint Unfold var_lt.

Inductive wide_var_lt : list variance -> list variance -> Prop :=
| wide_var_lt_nil  : wide_var_lt nil nil
| wide_var_lt_cons : forall v vs v' vs',
                      var_lt v v' ->
                      wide_var_lt vs vs' ->
                      wide_var_lt (v::vs) (v'::vs').

Hint Constructors wide_var_lt.

Definition var_leq (v1 v2: variance) : Prop := (v1 < v2) \/ (v1 = v2).
Reserved Notation "v1 '<=' v2" (at level 70, no associativity).
Notation "v1 '<=' v2" := (var_leq v1 v2).

Hint Unfold var_leq.

Inductive wide_var_leq : list variance -> list variance -> Prop :=
| wide_var_leq_nil  : wide_var_leq nil nil
| wide_var_leq_cons : forall v vs v' vs',
                       var_leq v v' ->
                       wide_var_leq vs vs' ->
                       wide_var_leq (v::vs) (v'::vs').

Hint Constructors wide_var_leq.

Definition var_transform_op (v1:variance) (v2:variance) : variance :=
  match v1 with
    | bivar => bivar
    | invar =>
        match v2 with
          | bivar => bivar
          | _ => invar
        end
    | covar => v2
    | contravar =>
        match v2 with
          | covar => contravar
          | contravar => covar
          | _ => v2
        end
    end.

Definition var_transform (v1:variance) (v2:variance)
                         (v3:variance) : Prop :=
  (var_transform_op v1 v2) = v3.

Hint Unfold var_transform.

Definition var_meet_op (v1:variance) (v2:variance) : variance :=
  match v1 with
    | bivar => v1
    | invar => invar
    | covar =>
        match v2 with
          | covar => covar
          | bivar => covar
          | contravar => invar
          | invar => invar
        end
    | contravar =>
        match v2 with
          | contravar => contravar
          | bivar => contravar
          | covar => invar
          | invar => invar
        end
    end.

Definition var_meet (v1:variance) (v2:variance)
                    (v3:variance) : Prop :=
  (var_meet_op v1 v2) = v3.

Hint Unfold var_meet.

Definition var_meet_list_op (vs: list variance) : variance :=
  List.fold_left var_meet_op vs bivar.

Definition var_meet_list (vs: list variance) (v: variance) : Prop :=
 (var_meet_list_op vs) = v.

Hint Unfold var_meet_list.

Definition negateVar (v: variance) : variance :=
  var_transform_op contravar v.

Definition negateVars (vs: list variance) : list variance :=
  List.map negateVar vs.

Definition var_join_op (v1:variance) (v2:variance) : variance :=
  match v1 with
    | bivar => bivar
    | invar => v2
    | covar =>
        match v2 with
          | bivar => bivar
          | contravar => bivar
          | covar => covar
          | invar => covar
        end
    | contravar =>
        match v2 with
          | bivar => bivar
          | covar => bivar
          | contravar => contravar
          | invar => contravar
        end
    end.

Definition var_join (v1:variance) (v2:variance)
                    (v3:variance) : Prop :=
  (var_join_op v1 v2) = v3.

Hint Unfold var_join.

Definition var_join_list_op (vs: list variance) : variance :=
  List.fold_left var_join_op vs bivar.

Definition var_join_list (vs: list variance) (v: variance) : Prop :=
 (var_join_list_op vs) = v.

Hint Unfold var_join_list.

Definition wide_var_transform_op (vs1 vs2: list variance) : list variance :=
  List.map
    (fun (vpair:variance * variance) =>
       let (v1, v2) := vpair in var_transform_op v1 v2)
    (List.combine vs1 vs2).


Example var_neq_ex : invar <> covar.
Proof.
  discriminate.
Qed.

Lemma var_lt_trans : forall (v1 v2 v3:variance), v1 < v2 -> v2 < v3 -> v1 < v3.
Proof.
  intros v1 v2 v3.
  destruct v1;
  destruct v2;
  destruct v3;
  intros H1 H2;
  auto.
Qed.


Lemma var_leq_trans :
  forall (v1 v2 v3:variance), v1 <= v2 -> v2 <= v3 -> v1 <= v3.
Proof.
  intros v1 v2 v3 H1 H2.
  destruct H1.
  destruct H2.
  unfold var_leq.
  left.
  exact (var_lt_trans v1 v2 v3 H H0).

  rewrite -> H0 in *.
  left.
  apply H.

  rewrite <- H in *.
  apply H2.
Qed.


Inductive var_t : tname -> typ -> variance -> Prop :=
| var_t_xx : forall X, var_t X (t_fvar X) covar
| var_t_xy : forall X Y,
             X <> Y -> var_t X (t_fvar Y) bivar
| var_t_bvar : forall X n1 n2,
               var_t X (t_bvar n1 n2) bivar
| var_t_ext : forall X tbnds N v1 v2,
              var_t_bounds X tbnds v1 ->
              var_n X N v2 ->
              var_t X (t_ext tbnds N) (var_meet_op v1 v2)

with var_n : tname -> typ_n -> variance -> Prop :=
| var_n_typ : forall X C ts dvars varsOfActuals,
              VT C dvars ->
              var_ts X ts varsOfActuals ->
              let vs := wide_var_transform_op dvars varsOfActuals in
              var_n X (n_typ C ts) (var_meet_list_op vs)

with var_b : tname -> typ_b -> variance -> Prop :=
| var_b_bot : forall X, var_b X b_bot bivar
| var_b_typ : forall X t v,
              var_t X t v -> var_b X (b_typ t) v

with var_t_bound : tname -> t_bound -> variance -> Prop :=
| var_t_bound_def : forall X b t vb vt,
                    var_b X b vb ->
                    var_t X t vt ->
                    let vb_flip := var_transform_op contravar vb in
                    var_t_bound X (b, t) (var_meet_op vb_flip vt)

with var_t_bounds : tname -> t_bounds -> variance -> Prop :=
| var_t_bounds_nil : forall X, var_t_bounds X nil bivar
| var_t_bounds_cons : forall X tbnd tbnds v1 v2,
                      var_t_bound X tbnd v1 ->
                      var_t_bounds X tbnds v2 ->
                      var_t_bounds X (tbnd::tbnds) (var_meet_op v1 v2)

with var_ts : tname -> list typ -> list variance -> Prop :=
| var_ts_nil : forall X, var_ts X nil nil
| var_ts_cons: forall X t ts v vs,
                     var_t X t v ->
                     var_ts X ts vs ->
                     var_ts X (t::ts) (v::vs).

Inductive var_p : tname -> typ_p -> variance -> Prop :=
| var_p_inf : forall X, var_p X p_inf bivar
| var_p_typ : forall X t v,
              var_t X t v -> var_p X (p_typ t) v.

Hint Constructors var_t
                  var_n
                  var_b
                  var_t_bound
                  var_t_bounds
                  var_ts
                  var_p.

Inductive mono_b : list variance -> list tname -> typ_b -> Prop :=
| mono_b_nil : forall b, mono_b nil nil b
| mono_b_cons :
    forall v vs x xs b w,
      var_b x b w ->
      var_leq v w ->
      mono_b vs xs b ->
      mono_b (v::vs) (x::xs) b.

Hint Constructors mono_b.

Definition mono_t (vs:list variance) (xs: list tname)
                  (t: typ) : Prop :=
  mono_b vs xs (b_typ t).

Hint Unfold mono_t.

Definition mono_n (vs:list variance) (xs: list tname)
                  (N: typ_n) : Prop :=
  mono_t vs xs (t_ext nil N).

Hint Unfold mono_n.

Inductive mono_t_bound : list variance -> list tname -> t_bound -> Prop :=
| mono_t_bound_nil : forall tbnd, mono_t_bound nil nil tbnd
| mono_t_bound_cons :
    forall v vs x xs tbnd w,
      var_t_bound x tbnd w ->
      var_leq v w ->
      mono_t_bound vs xs tbnd ->
      mono_t_bound (v::vs) (x::xs) tbnd.

Hint Constructors mono_t_bound.

Inductive mono_t_bounds (vs: list variance) (xs:list tname): list t_bound -> Prop :=
| mono_t_bounds_nil : mono_t_bounds vs xs nil
| mono_t_bounds_cons :
    forall tbnd tbnds,
      mono_t_bound vs xs tbnd ->
      mono_t_bounds vs xs tbnds ->
      mono_t_bounds vs xs (tbnd::tbnds).

Hint Constructors mono_t_bounds.

Inductive wide_var_b : list tname -> list typ_b -> list variance -> Prop :=
| wide_var_b_nil : wide_var_b nil nil nil
| wide_var_b_cons : forall x xs b bs v vs,
                var_b x b v ->
                wide_var_b xs bs vs ->
                wide_var_b (x::xs) (b::bs) (v::vs).

Hint Constructors wide_var_b.

Inductive wide_var_t : list tname -> list typ -> list variance -> Prop :=
| wide_var_t_nil : wide_var_t nil nil nil
| wide_var_t_cons : forall x xs t ts v vs,
                var_t x t v ->
                wide_var_t xs ts vs ->
                wide_var_t (x::xs) (t::ts) (v::vs).

Hint Constructors wide_var_t.

Inductive wide_var_n : list tname -> list typ_n -> list variance -> Prop :=
| wide_var_n_nil : wide_var_n nil nil nil
| wide_var_n_cons : forall x xs n ns v vs,
                var_n x n v ->
                wide_var_n xs ns vs ->
                wide_var_n (x::xs) (n::ns) (v::vs).

Hint Constructors wide_var_n.

Inductive wide_var_p : list tname -> list typ_p -> list variance -> Prop :=
| wide_var_p_nil : wide_var_p nil nil nil
| wide_var_p_cons : forall x xs p ps v vs,
                var_p x p v ->
                wide_var_p xs ps vs ->
                wide_var_p (x::xs) (p::ps) (v::vs).

Hint Constructors wide_var_p.

