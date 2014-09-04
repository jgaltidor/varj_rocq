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

Notation t_bound := (typ_b * typ).
(** Represents list of lower and upper bounds of type parameters *)
Notation t_bounds := (list t_bound).

Print List.nth.


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


Inductive lc_t : typ -> Prop :=
| lc_t_fvar :
    forall X,
      lc_t (t_fvar X)
| lc_t_ext :
    forall bnds N,
      (forall bnd, In bnd bnds -> bodies_bnd (length bnds) bnd) ->
      bodies_n (length bnds) N ->
      lc_t (t_ext bnds N)
(* note no rule for t_bvar *)

with lc_n : typ_n -> Prop :=
| lc_n_typ :
    forall C ts,
      (forall t, In t ts -> lc_t t) ->
      lc_n (n_typ C ts)

with lc_b : typ_b -> Prop :=
| lc_b_typ :
    forall t,
      lc_t ->
      lc_b (b_typ t)
| lc_b_bot : lc_b b_bot

with Definition bodies_t (n:nat) (t: typ) : Prop :=
  exists L,
    forall xs,
      distinct L n xs ->
        lc_t (open_t_with_names 0 t xs)

with bodies_n (n:nat) (N: typ) : Prop :=
  exists L,
    forall xs,
      distinct L n xs ->
        lc_n (open_n_with_names 0 N xs)

with bodies_b (n:nat) (b: typ_b) : Prop :=
  exists L,
    forall xs,
      distinct L n xs ->
        lc_b (open_b_with_names 0 b xs)

with bodies_bnd (n:nat) (bnd: t_bound) : Prop :=
  let (b, t) := tbnd in
  (bodies_b n b /\ bodies_t n t).





Print List.forall.

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

Notation "+" := covar     (at level 30) : variance_scope.
Notation "-" := contravar (at level 30) : variance_scope.
Notation "*" := bivar     (at level 30) : variance_scope.

(** Represents list of declared variances, lower and upper bounds
  * of class type parameboundsters
  *)
Notation tv_bound := (variance * typ_b * typ).
Notation tv_bounds := (list tv_bound).


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
| value_new : forall N es,
    (forall e, In e es -> value e) -> value (e_new N es).

(* Adding constructors for value to the core hint
 * database.
 *)
Hint Constructors value.

(* Print HintDb core. *)

Notation fielddef := (fname * typ).

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
Notation methdef := (mname * (t_bounds * typ * list typ * exp)).

(** Type signature of a method is a list of type bounds,
  * a list of argument types, and
  * a return type.
  * Note that a msig is a term with binders
  *)
Notation msig := (t_bounds * list typ * typ).

Notation fielddefs := (list fielddef).
Notation methdefs  := (list methdef).

(** A class is defined with
  * a name of the class,
  * list of declared variances, lower and upper bounds of class type parameters
  * a parent type,
  * a list of field definitions,
  * and a list of method definitions.
  * Note that a classdef is a term with binders
  *)
Notation classdef := (cname * tv_bounds * typ_n * fielddefs * methdefs).

(** A class table is mapping from names of classes to their definitions. *)

Notation ctable := (list (cname * classdef)).

(** Type Variable Name Context *)

Notation cxt_t := (list (tname * t_bound)).

(** Expression Variable Name Context *)

Notation cxt_e := (list (ename * typ)).


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

