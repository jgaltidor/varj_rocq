(* Author: John Altidor
 *
 * Coq Version: 8.4
 *
 * This is the full language definition of the VarJ calculus. 
 * I formulate VarJ using the locally-nameless binder representation. 
 * 
 * See: B. Aydemir et al. Engineering formal metatheory. 2008,
 * for more information on the locally-nameless representation. *)

Require Import Arith.
Require Export Arith.

Require Import List.
Require Export List.

Require Import Vector.
Require Export Vector.

Require Import Metatheory.
Require Export Metatheory.

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

Print Vector.t.

Notation Vec := Vector.t.

Inductive typ : Set :=
| t_ext {n} : Vec (typ_b * typ) n -> typ_n -> typ   (* Existential type *)
  (* Bound type variables
   * The first index of type variables indicate their level.
   * The second index of type variables refers to the ith
   * type argument in the list of type arguments
   * Class type variables are always at level 0
   * Method type variables are always at level 1.
   * For example: (t_bvar 0 0) refers to the first type parameter
   * of the enclosing class.
   * (t_bvar 1 0) refers to the first type parameter of the
   * enclosing method.
   *)
| t_bvar : nat -> nat -> typ
| t_fvar : tname -> typ  (* Free type variable *)

with typ_n : Set :=
| n_typ {n} : cname -> Vec typ n -> typ_n  (* Parameterized type *)

with typ_b : Set :=
| b_typ : typ -> typ_b
| b_bot : typ_b.

(** Represents a vector of lower and upper bounds of type parameters *)
with t_bounds : Set :=
| t_bnds {n} : Vec (typ_b * typ) n -> t_bounds.


Inductive typ_p : Set :=
| p_typ : typ -> typ_p
| p_inf : typ_p.  (* Infer Type Parameter *)

Inductive typ_r : Set :=
| typ_r_n    : typ_n -> typ_r
| typ_r_fvar : tname -> typ_r.

Notation t_bound := (typ_b * typ).

Definition t_bound_get_lower_bound (tbnd: t_bound) :=
  let (lower, upper) := tbnd in lower.

Definition t_bound_get_upper_bound (tbnd: t_bound) :=
  let (lower, upper) := tbnd in upper.

Notation vmap := Vector.map.

Definition t_bounds_get_lower_bounds {n} (tbnds: Vec t_bound n) :=
  vmap t_bound_get_lower_bound tbnds.

Definition t_bounds_get_upper_bounds {n} (tbnds: Vec t_bound n) :=
  vmap t_bound_get_upper_bound tbnds.

Inductive variance : Set :=
| covar : variance
| contravar : variance
| invar : variance
| bivar : variance.

Notation "+" := covar     (at level 30) : variance_scope.
Notation "-" := contravar (at level 30) : variance_scope.
Notation "*" := bivar     (at level 30) : variance_scope.

Notation tv_bound := (variance * typ_b * typ).

(** Represents a of declared variances, lower and upper bounds
  * of class type parameters
  *)
Inductive tv_bounds : Set :=
| vt_bnds {n} : Vec tv_bound n -> tv_bounds.

Definition tv_bound_get_lower_bound (tvbnd: tv_bound) :=
  match tvbnd with (v, lower, upper) => lower end.

Definition tv_bound_get_upper_bound (tvbnd: tv_bound) :=
  match tvbnd with (v, lower, upper) => upper end.

Definition tv_bounds_get_lower_bounds {n} (tvbnds: Vec tv_bound n) :=
  vmap tv_bound_get_lower_bound tvbnds.

Definition tv_bounds_get_upper_bounds {n} (tvbnds: Vec tv_bound n) :=
  vmap tv_bound_get_upper_bound tvbnds.

Inductive exp : Set :=
| e_field  : exp -> fname -> exp
| e_minvk {n} {m} :
    exp -> mname -> Vec typ_p n -> Vec exp m -> exp
| e_new {n} : typ_n -> Vec exp n -> exp
| e_bvar   : nat -> exp
| e_fvar   : ename -> exp.

Notation vin := Vector.In.

(* Values *)
Inductive value : exp -> Prop :=
| value_new {n} : forall N (es: Vec exp n),
    (forall e, vin e es -> value e) ->
    value (e_new N es).

(* Adding constructors for value to the core hint
 * database.
 *)
Hint Constructors value.

(* Print HintDb core. *)

Notation fielddef := (fname * typ).

(** A method [method] is a
  * 1) method name
  * 2) a list of lower and upper bounds for its type parameter,
  * 3) a return type,
  * 4) a list of argument value types,
  * 5) an expression representing its method body.
  * Note that a [method] is a term with binders
  *)
Inductive method : Set :=
| methdef {n} {m} :
   mname -> t_bounds -> typ -> Vec typ m -> exp -> method.

(** Type signature of a method is a list of type bounds,
  * a list of argument types, and
  * a return type.
  * Note that a msig is a term with binders
  *)
Definition msig {n} {m} := (@t_bounds n * Vec typ m * typ).

Notation fielddefs := (list fielddef).


(** A method table is mapping from names of methods to their definitions. *)
Notation mtable := (list (mname * method)).

(** A class is defined with
  * a name of the class,
  * list of declared variances, lower and upper bounds of class type parameters
  * a parent type,
  * a list of field definitions,
  * and a list of method definitions.
  * Note that a classdef is a term with binders
  *)
Inductive class : Set :=
| classdef {n} :
  cname -> @tv_bounds n -> typ_n -> fielddefs -> mtable -> class.

(** A class table is mapping from names of classes to their definitions. *)

Notation ctable := (list (cname * class)).

(** Type Variable Name Context *)

Notation cxt_t {n} := Vec (tname * t_bound) n.

(** Expression Variable Name Context *)

Definition cxt_e {n} := Vec (ename * typ) n.


Definition tvbound_var (tvbnd: tv_bound) : variance :=
  match tvbnd with (v, _, _) => v end.

Definition tvbounds_vars {n} (tvbnds: tv_bounds) : Vec variance n :=
  vmap tvbound_var tvbnds.

Definition tvbound_2_tbound (tvbnd:tv_bound) : t_bound :=
  match tvbnd with (v, b, t) => (b, t) end.

Definition tvbounds_2_tbounds {n} (tvbnds:Vec tv_bound n) : Vec t_bound n :=
  vmap tvbound_2_tbound tvbnds.

(** We assume a fixed class table [CT]. *)

Parameter CT : ctable.

Inductive VT {n} : cname -> Vec variance n -> Prop :=
| VT_lookup : forall C tvbnds N fds mds,
              binds C (C, tvbnds, N, fds, mds) CT ->
              VT C (tvbounds_vars tvbnds).

Hint Constructors VT.

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

