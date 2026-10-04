(* Author: John Altidor
 *
 * Rocq Version: 9.2 (originally written for Coq 8.4)
 *
 * This is the full language definition of the VarJ calculus. 
 * I formulate VarJ using the locally-nameless binder representation. 
 * 
 * See: B. Aydemir et al. Engineering formal metatheory. 2008,
 * for more information on the locally-nameless representation. *)

From Stdlib Require Import Arith.
From Stdlib Require Export Arith.

From Stdlib Require Import List.
From Stdlib Require Export List.

From VarJ Require Import Metatheory.
From VarJ Require Export Metatheory.

Set Implicit Arguments.

(** Syntax *)

(* Closing nat_scope so that a * b is interpretted as the
 * product type (prod a b) instead of the multiplication
 * (mult a b)
 *)
Close Scope nat_scope.

Definition cname := atom. (* Class name *)
Definition fname := atom. (* Field name *)
Definition mname := atom. (* Method name *)
Definition tname := atom. (* Type variable name *)
Definition ename := atom. (* Expression variable name *)

(** The names [this] and [Object] are predefined. We simply assume that these
    names exist. *)

Parameter this : ename.
Parameter Object : cname.

Inductive typ : Set :=
| t_ext  : list (typ_b * typ) -> typ_n -> typ   (* Existential type *)
  (* Bound type variables
   * The first index of type variables indicate their level.
   * The second index of type variables refers to the ith
   * type argument in the list of type arguments
   * For example: (t_bvar 0 0) refers to the first type parameter
   * of the innermost enclosing binding.
   * (t_bvar 1 0) refers to the first type parameter of the
   * second innermost binding.
   *)
| t_bvar : nat -> nat -> typ
| t_fvar : tname -> typ  (* Free type variable *)

with typ_n : Set :=
| n_typ : cname -> list typ -> typ_n  (* Parameterized type *)

with typ_b : Set :=
| b_typ : typ -> typ_b
| b_bot : typ_b.

Inductive typ_p : Set :=
| p_typ : typ -> typ_p
| p_inf : typ_p.  (* Infer Type Parameter *)

Inductive typ_r : Set :=
| typ_r_n    : typ_n -> typ_r
| typ_r_fvar : tname -> typ_r.

Abbreviation t_bound := (typ_b * typ).
(** Represents list of lower and upper bounds of type parameters *)
Abbreviation t_bounds := (list t_bound).

Definition t_bound_get_lower_bound (tbnd: t_bound) :=
  let (lower, upper) := tbnd in lower.

Definition t_bound_get_upper_bound (tbnd: t_bound) :=
  let (lower, upper) := tbnd in upper.

Definition t_bounds_get_lower_bounds (tbnds: t_bounds) :=
  List.map t_bound_get_lower_bound tbnds.

Definition t_bounds_get_upper_bounds (tbnds: t_bounds) :=
  List.map t_bound_get_upper_bound tbnds.

Inductive variance : Set :=
| covar : variance
| contravar : variance
| invar : variance
| bivar : variance.

Declare Scope variance_scope.

Notation "+" := covar     (at level 30) : variance_scope.
Notation "-" := contravar (at level 30) : variance_scope.
Notation "*" := bivar     (at level 30) : variance_scope.

(** Represents list of declared variances, lower and upper bounds
  * of class type parameboundsters
  *)
Abbreviation tv_bound := (variance * typ_b * typ).
Abbreviation tv_bounds := (list tv_bound).


Definition tv_bound_get_lower_bound (tvbnd: tv_bound) :=
  match tvbnd with (v, lower, upper) => lower end.

Definition tv_bound_get_upper_bound (tvbnd: tv_bound) :=
  match tvbnd with (v, lower, upper) => upper end.

Definition tv_bounds_get_lower_bounds (tvbnds: tv_bounds) :=
  List.map tv_bound_get_lower_bound tvbnds.

Definition tv_bounds_get_upper_bounds (tvbnds: tv_bounds) :=
  List.map tv_bound_get_upper_bound tvbnds.


Inductive exp : Set :=
| e_field  : exp -> fname -> exp
| e_minvk  : exp -> mname -> list typ_p -> list exp -> exp
| e_new    : typ_n -> list exp -> exp
| e_bvar   : nat -> exp
| e_fvar   : ename -> exp.

(* Values *)
Inductive value : exp -> Prop :=
| value_new :
    forall N es,
      value_wide es ->
 (* ---------------------- *)
      value (e_new N es)

with value_wide : list exp -> Prop :=
| value_wide_nil : value_wide nil
| value_wide_cons :
    forall e es,
      value e ->
      value_wide es ->
 (* ---------------------- *)
      value_wide (e::es).

(* Adding constructors for value to the core hint
 * database.
 *)
#[global] Hint Constructors value value_wide : core.

(* Print HintDb core. *)

Abbreviation fielddef := (fname * typ).

(** A method definition [methdef] is a map entry (a pair)
  * between a method name and 4-tuple of:
  * a list of lower and upper bounds for its type parameter,
  * a return type,
  * a list of argument value types,
  * and an expression representing its method body.
  * Defining a methdef as a pair allows looking up method
  * definitions by name in a list of methdefs.
  * Note that a methdef is a term with binders
  *)
Abbreviation methdef := (mname * (t_bounds * typ * list typ * exp)).

(** Type signature of a method is a list of type bounds,
  * a list of argument types, and
  * a return type.
  * Note that a msig is a term with binders
  *)
Abbreviation msig := (t_bounds * list typ * typ).

Abbreviation fielddefs := (list fielddef).
Abbreviation methdefs  := (list methdef).

(** A class is defined with
  * a name of the class,
  * list of declared variances, lower and upper bounds of class type parameters
  * a parent type,
  * a list of field definitions,
  * and a list of method definitions.
  * Note that a classdef is a term with binders
  *)
Abbreviation classdef := (cname * tv_bounds * typ_n * fielddefs * methdefs).

(** A class table is mapping from names of classes to their definitions. *)

Abbreviation ctable := (list (cname * classdef)).

(** Type Variable Name Context *)

Abbreviation cxt_t := (list (tname * t_bound)).

(** Expression Variable Name Context *)

Abbreviation cxt_e := (list (ename * typ)).


Definition tvbound_var (tvbnd: tv_bound) : variance :=
  match tvbnd with (v, _, _) => v end.

Definition tvbounds_vars(tvbnds: tv_bounds) : list variance :=
  List.map tvbound_var tvbnds.

Definition tvbound_2_tbound (tvbnd:tv_bound) : t_bound :=
  match tvbnd with (v, b, t) => (b, t) end.

Definition tvbounds_2_tbounds (tvbnds:tv_bounds) : t_bounds :=
  List.map tvbound_2_tbound tvbnds.

(** We assume a fixed class table [CT]. *)

Parameter CT : ctable.

Inductive VT : cname -> list variance -> Prop :=
| VT_lookup : forall C tvbnds N fds mds,
              binds C (C, tvbnds, N, fds, mds) CT ->
              VT C (tvbounds_vars tvbnds).

#[global] Hint Constructors VT : core.

Definition fielddef_name (fd:fielddef) : fname :=
  let (f, _) := fd in f.

Definition fieldefs_names (fds:fielddefs) : (list fname) :=
  List.map fielddef_name fds.

Definition methdef_name (md:methdef) : mname :=
  let (m, _) := md in m.

Definition methdefs_names (mds:methdefs) : (list mname) :=
  List.map methdef_name mds.

Definition methdef_msig (md:methdef) : msig :=
  match md with (_, (tbnds, t, ts, _)) => (tbnds, ts, t) end.

Definition cxt_t_entry_name (entry:tname * t_bound) : tname :=
  let (name, bnd) := entry in name.

Definition cxt_e_entry_name (entry:ename * typ) : ename :=
  let (name, t) := entry in name.

Fixpoint fv_t (t: typ) : list tname :=
  let fv_tbnd :=
    fun (tbnd:t_bound) => let (b, t) := tbnd in (fv_b b) ++ (fv_t t)
  in
  let fv_tbnds :=
    fun (tbnds:t_bounds) =>
      List.fold_left
        (fun (names:list tname) (tbnd: t_bound) => names ++ (fv_tbnd tbnd))
        tbnds
        nil
  in
  match t with
    | t_ext tbnds N => (fv_tbnds tbnds) ++ (fv_n N)
    | t_bvar _ _ => nil
    | t_fvar X => X::nil
  end

with fv_b (B: typ_b) : list tname :=
  match B with
    | b_typ t => fv_t t
    | b_bot => nil
  end

with fv_n (N: typ_n) : list tname :=
  let fv_ts :=
    fun ts =>
      List.fold_left (fun (names:list tname) (t: typ) => names ++ (fv_t t)) ts nil
  in
  match N with
    | n_typ C ts => fv_ts ts
  end.

Definition fv_tbnd (tbnd:t_bound) : list tname :=
  let (b, t) := tbnd in (fv_b b) ++ (fv_t t).

Definition fv_tbnds (tbnds:t_bounds) : list tname :=
  List.fold_left
    (fun (names:list tname) (tbnd: t_bound) => names ++ (fv_tbnd tbnd))
    tbnds
    nil.

Definition fv_ts (ts:list typ) : list tname :=
  List.fold_left (fun (names:list tname) (t: typ) => names ++ (fv_t t)) ts nil.

Definition fv_r (r:typ_r) : list tname :=
  match r with
    | typ_r_n N => fv_n N
    | typ_r_fvar X => X::nil
  end.

(** Auxiliaries *)

Fixpoint flatten (A: Type) (ll: list (list A)): list A :=
  match ll with
  | nil => nil
  | hd :: tl => hd ++ (flatten tl)
  end.


(** Going from wide judgment to forall *)

Lemma value_wide_to_forall
  (* If *)
  (es : list exp)
  (H : value_wide es)
  :
  (* Then *)
  (forall e, In e es -> value e).
Proof.
  induction H.
  intros e eInNil.
  simpl in eInNil.
  contradiction.

  intros e0 e0InEs.
  destruct e0InEs.

    (* Case: e = e' *)
    rewrite <- H1.
    apply H.

    (* Case e' \in es *)
    apply IHvalue_wide.
    apply H1.
Qed.

#[global] Hint Resolve value_wide_to_forall : core.

Lemma value_wide_from_forall
  (* If *)
  (es : list exp)
  (H : forall e, In e es -> value e)
  :
  (* Then *)
  value_wide es.
Proof.
  induction es.
  apply value_wide_nil.

  apply value_wide_cons.

  apply H.
  apply in_eq.

  apply IHes.

  intros e eInES.

  apply H.

  apply in_cons.
  apply eInES.
Qed.

(* A more explicit proof of value_wide_iff_forall:
Proof.
  split.
  apply value_wide_to_forall.
  apply value_wide_from_forall.
Qed.
*)

Lemma value_wide_iff_forall :
  forall (es : list exp),
    value_wide es <-> (forall e, In e es -> value e).
Proof.
  split; eauto using value_wide_from_forall.
Qed.


