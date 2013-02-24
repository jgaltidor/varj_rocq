(* Contains Subtyping and Variance Predicate Definitions *)

Require Import VarJ_Syntax.
Require Import VarJ_Substitution.

(** Subtyping Relations *)

Inductive subtype_n : cxt_t -> typ_n -> typ_n -> Prop :=
| subtype_n_super :
   forall C tvbnds N fds mds D ts ts' tcxt,
   binds C (C, tvbnds, N, fds, mds) CT ->
   C <> D ->
   subtype_n tcxt (open_n 0 N ts) (n_typ D ts') ->
   subtype_n tcxt (n_typ C ts) (n_typ D ts')

| subtype_n_var:
  forall VT C vars tcxt ts ts',
  VT C vars ->
  (forall v t t',
     In (v, t, t') (combine (combine vars ts) ts') ->
     var_subtype tcxt v t t') ->
  subtype_n tcxt (n_typ C ts) (n_typ C ts')

with subtype_t : cxt_t -> typ -> typ -> Prop :=

(* subtype_t_refl not in VarJ *)
| subtype_t_refl : forall tcxt t, subtype_t tcxt t t

| subtype_t_trans : forall tcxt t1 t2 t3,
                    subtype_t tcxt t1 t2 ->
                    subtype_t tcxt t2 t3 ->
                    subtype_t tcxt t1 t3

| subtype_t_ubound : forall tcxt x b t,
                     binds x (b, t) tcxt ->
                     subtype_t tcxt (t_fvar x) t

(** SE-SD rule in paper violates Barendregt variable convention
  * So using the new SE-SD-left and SE-SD-right.
  *)

| subtype_t_n_left : forall tcxt tbnds N N' L,
                (forall xs,
                   distinct L (length tbnds) xs ->
                   let tcxt' := (openToCtxt_tbounds xs tbnds) in
                   subtype_n (tcxt ++ tcxt') N N') ->
                subtype_t tcxt (t_ext tbnds N) (t_ext nil N')

| subtype_t_n_right : forall tcxt tbnds' N N' L,
                (forall xs,
                   distinct L (length tbnds') xs ->
                   let tcxt' := (openToCtxt_tbounds xs tbnds') in
                   subtype_n (tcxt ++ tcxt') N N') ->
                subtype_t tcxt (t_ext nil N) (t_ext tbnds' N')

| subtype_t_pack : forall tcxt tbnds tbnds' N ts L,
                     (forall xs,
                        distinct L (length tbnds') xs ->
                        let tcxt' := (openToCtxt_tbounds xs tbnds') in
                        (* Need to open ts because they contain binders in tbnds' *)
                        let ts' := (open_ts_with_names 0 ts xs) in
                        let tbnds_opened := (open_t_bounds 0 tbnds ts') in
                        (forall t' b_low t_up,
                           In (t', (b_low, t_up)) (combine ts' tbnds_opened) ->
                           subtype_b (tcxt ++ tcxt') b_low  (b_typ t') /\
                           subtype_t (tcxt ++ tcxt') t' t_up)) ->
             (* -------------------------------------------------------------------- *)
                   subtype_t tcxt (t_ext tbnds' (open_n 0 N ts)) (t_ext tbnds N)

(** Next: Check wellformedness with f-bounds *)

with subtype_b : cxt_t -> typ_b -> typ_b -> Prop :=
| subtype_b_t : forall tcxt t t',
                subtype_t tcxt t t' ->
                subtype_b tcxt (b_typ t) (b_typ t')

| subtype_b_bot : forall tcxt b,
                  subtype_b tcxt b_bot b

| subtype_b_lbound : forall tcxt x b t,
                     binds x (b, t) tcxt ->
                     subtype_b tcxt b (b_typ (t_fvar x))

| subtype_b_refl : forall tcxt b, subtype_b tcxt b b

| subtype_b_trans : forall tcxt b1 b2 b3,
                    subtype_b tcxt b1 b2 ->
                    subtype_b tcxt b2 b3 ->
                    subtype_b tcxt b1 b3

with var_subtype : cxt_t -> variance -> typ -> typ -> Prop :=
| var_subtype_co:
   forall tcxt t t',
   subtype_t tcxt t t' ->
   var_subtype tcxt covar t t'
| var_subtype_contra:
   forall tcxt t t',
   subtype_t tcxt t' t ->
   var_subtype tcxt contravar t t'
| var_subtype_in:
   forall tcxt t t',
   subtype_t tcxt t t' ->
   subtype_t tcxt t' t ->
   var_subtype tcxt invar t t'
| var_subtype_bi:
   forall tcxt t t',
   var_subtype tcxt bivar t t'.


(* Variance reasoning *)

Close Scope nat_scope.

(** Since ordering defined by var_lt is partial, need to
  * use Inductive instead of Definition *)
Inductive var_lt : variance -> variance -> Prop :=
| var_lt_in : forall v2, v2 <> invar -> var_lt invar v2

| var_lt_co : var_lt covar bivar

| var_lt_contra : var_lt contravar bivar.

Hint Constructors var_lt.
Reserved Notation "v1 '<' v2" (at level 70, no associativity).
Notation "v1 '<' v2" := (var_lt v1 v2).


Definition var_leq (v1 v2: variance) := (v1 < v2) \/ (v1 = v2).
Reserved Notation "v1 '<=' v2" (at level 70, no associativity).
Notation "v1 '<=' v2" := (var_leq v1 v2).


Inductive var_transform : variance -> variance -> variance -> Prop :=
| var_transform_co : forall v,  var_transform covar v v

| var_transform_contra_co :     var_transform contravar covar     contravar
| var_transform_contra_contra : var_transform contravar contravar covar
| var_transform_contra_in :     var_transform contravar invar     invar

| var_transform_bi : forall v,  var_transform bivar v bivar

| var_transform_in_co     : var_transform invar covar     invar
| var_transform_in_contra : var_transform invar contravar invar
| var_transform_in_bi     : var_transform invar bivar     bivar
| var_transform_in_in     : var_transform invar invar     invar.


Inductive var_meet : variance -> variance -> variance -> Prop :=
| var_meet_le : forall v1 v2, v1 <= v2 -> var_meet v1 v2 v1
| var_meet_gt : forall v1 v2, v2 < v1  -> var_meet v1 v2 v2
| var_meet_co_contra : var_meet covar contravar invar
| var_meet_contra_co : var_meet contravar covar invar.


Inductive var_join : variance -> variance -> variance -> Prop :=
| var_join_le : forall v1 v2, v1 <= v2 -> var_join v1 v2 v2
| var_join_gt : forall v1 v2, v2 < v1  -> var_join v1 v2 v1
| var_join_co_contra : var_join covar contravar bivar
| var_join_contra_co : var_join contravar covar bivar.


Inductive var_meet_list : list variance -> variance -> Prop :=
| var_meet_list_nil  : var_meet_list nil bivar
| var_meet_list_cons : forall v1 vs v2 v3,
                       var_meet_list vs v2 ->
                       var_meet v1 v2 v3 ->
                       var_meet_list (cons v1 vs) v3.

Inductive var_join_list : list variance -> variance -> Prop :=
| var_join_list_nil  : var_join_list nil invar
| var_join_list_cons : forall v1 vs v2 v3,
                       var_join_list vs v2 ->
                       var_join v1 v2 v3 ->
                       var_join_list (cons v1 vs) v3.


Inductive var_t : tname -> typ -> variance -> Prop :=
| var_t_xx : forall X, var_t X (t_fvar X) covar
| var_t_xy : forall X Y,
             X <> Y -> var_t X (t_fvar Y) bivar
| var_t_bvar : forall X n1 n2,
               var_t X (t_bvar n1 n2) bivar
| var_t_ext : forall X tbnds N v v1 v2,
              var_t_bounds X tbnds v1 ->
              var_n X N v2 ->
              var_meet v1 v2 v ->
              var_t X (t_ext tbnds N) v

with var_n : tname -> typ_n -> variance -> Prop :=
| var_n_typ : forall X C ts v dvars tvars actualVars,
              VT C dvars ->
              (forall dvar t actualVar tvar,
                 In (dvar, t, actualVar, tvar)
                    (combine
                      (combine
                         (combine dvars ts)
                         actualVars)
                      tvars) ->
                 var_t X t actualVar /\
                 var_transform dvar actualVar tvar) ->
              var_meet_list tvars v ->
              var_n X (n_typ C ts) v

with var_b : tname -> typ_b -> variance -> Prop :=
| var_b_bot : forall X, var_b X b_bot bivar
| var_b_typ : forall X t v,
              var_t X t v -> var_b X (b_typ t) v

with var_t_bound : tname -> t_bound -> variance -> Prop :=
| var_t_bound_def : forall X b t vb vt vb_flip v,
                    var_b X b vb ->
                    var_t X t vt ->
                    var_transform contravar vb vb_flip ->
                    var_meet vb_flip vt v ->
                    var_t_bound X (b, t) v

with var_t_bounds : tname -> t_bounds -> variance -> Prop :=
| var_t_bounds_nil : forall X, var_t_bounds X nil bivar
| var_t_bounds_cons : forall X tbnd tbnds v v1 v2,
                      var_t_bound X tbnd v1 ->
                      var_t_bounds X tbnds v2 ->
                      var_meet v1 v2 v ->
                      var_t_bounds X (cons tbnd tbnds) v.


Inductive vars_t : list tname -> typ -> list variance -> Prop :=
| vars_t_nil : forall t, vars_t nil t nil

| vars_t_cons : forall t x xs v vs,
                vars_t xs t vs ->
                var_t x t v ->
                vars_t (cons x xs) t (cons v vs).


Example var_neq_ex : invar <> covar.
Proof.
  discriminate.
Qed.



Lemma var_lt_trans : forall (v1 v2 v3:variance), v1 < v2 -> v2 < v3 -> v1 < v3.
Proof.
  intros v1 v2 v3 H1 H2.
  inversion H1.
  inversion H2.
  clear H1 H2.
  subst.
  contradiction H. (* Proof by contradiction *)
  reflexivity.

  subst.
  apply var_lt_in.
  discriminate.

  subst.
  apply var_lt_in.
  discriminate.

  subst.
  inversion H2.  

  subst.
  inversion H2.
Qed.


Lemma var_le_trans : forall (v1 v2 v3:variance), v1 <= v2 -> v2 <= v3 -> v1 = v3.
Proof.
Admitted.

