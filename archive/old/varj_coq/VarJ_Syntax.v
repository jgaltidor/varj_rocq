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
| n_typ : cname -> list typ -> typ_n  (* Parameterized type *)

with typ_b : Set :=
| b_typ : typ -> typ_b
| b_bot : typ_b.

Inductive typ_p : Set :=
| p_typ : typ -> typ_p
| p_inf : typ_p.  (* Infer Type Parameter *)

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

Inductive variance : Set :=
| covar : variance
| contravar : variance
| invar : variance
| bivar : variance.

Notation "+" := covar     (at level 30) : variance_scope.
Notation "-" := contravar (at level 30) : variance_scope.
Notation "*" := bivar     (at level 30) : variance_scope.

Notation fielddef := (fname * typ).


Notation t_bound := (typ_b * typ).
(** Represents list of lower and upper bounds of type parameters *)
Notation t_bounds := (list t_bound).

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

(** Represents list of declared variances, lower and upper bounds
  * of class type parameboundsters
  *)
Notation tv_bound := (variance * typ_b * typ).
Notation tv_bounds := (list tv_bound).

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

(* Reopening nat_scope since the syntax definition is complete. *)

Open Scope nat_scope.

(** Auxiliaries *)

(** Opening for types *)
Fixpoint open_t (k:nat) (t:typ) (ts:list typ) {struct t} : typ :=
  match t with
    | t_ext bounds N =>
        t_ext (List.map
                 (fun (bnd:t_bound) =>
                   match bnd with
                     | (b, t') => (open_b (S k) b ts, open_t (S k) t' ts)
                   end)
                 bounds)
              (open_n (S k) N ts)
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
  match N with
    | n_typ C ts' =>
        n_typ C (List.map (fun t => open_t k t ts) ts')
  end.


Definition open_p (k:nat) (p:typ_p) (ts:list typ) : typ_p :=
  match p with
    | p_typ t => p_typ (open_t k t ts)
    | p_inf => p_inf
  end.

Definition open_ts (k:nat) (ts':list typ) (ts:list typ) : list typ :=
  List.map (fun t => open_t k t ts) ts'.

Definition open_ps (k:nat) (ps:list typ_p) (ts:list typ) : list typ_p :=
  List.map (fun p => open_p k p ts) ps.

Definition open_bs (k:nat) (bs:list typ_b) (ts:list typ) : list typ_b :=
  List.map (fun b => open_b k b ts) bs.

Definition open_t_bound (k:nat) (tbnd:t_bound) (ts:list typ) : t_bound :=
  match tbnd with
    | (b, t) => (open_b k b ts, open_t k t ts)
  end.

Definition open_t_bounds (k:nat) (tbnds:t_bounds) (ts:list typ) : t_bounds :=
  List.map (fun tbnd => open_t_bound k tbnd ts) tbnds.


Definition open_tv_bound (k:nat) (tvbnd:tv_bound) (ts:list typ) : tv_bound :=
  match tvbnd with
    | (v, b, t) => (v, open_b k b ts, open_t k t ts)
  end.

Definition open_tv_bounds (k:nat) (tvbnds:tv_bounds) (ts:list typ) : tv_bounds :=
  List.map (fun tvbnd => open_tv_bound k tvbnd ts) tvbnds.


Definition open_msig (k:nat) (sig:msig) (ts:list typ) : msig :=
  match sig with
    | (tbnds, ts', t) =>
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

Definition open_t_bound_with_names (k:nat) (tbnd:t_bound) (names:list tname) :=
  (open_t_bound k tbnd (names2fvars_t names)).


Definition open_t_bounds_with_names (k:nat) (tbnds:t_bounds) (names:list tname) :=
  (open_t_bounds k tbnds (names2fvars_t names)).

Definition open_e_t_with_names (k:nat) (e:exp) (names:list tname) :=
  (open_e_t k e (names2fvars_t names)).


Definition tvbound_var (tvbnd: tv_bound) : variance :=
  match tvbnd with (v, b, t) => v end.

Definition tvbounds_vars(tvbnds: tv_bounds) : list variance :=
  List.map tvbound_var tvbnds.


Definition tvbound_2_tbound (tvbnd:tv_bound) : t_bound :=
  match tvbnd with | (v, b, t) => (b, t) end.

Definition tvbounds_2_tbounds (tvbnds:tv_bounds) : t_bounds :=
  List.map tvbound_2_tbound tvbnds.


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


Definition fielddef_name (fd:fielddef) : fname :=
  match fd with | (f, _) => f end.

Definition fieldefs_names (fds:fielddefs) : (list fname) :=
  List.map fielddef_name fds.

Definition methdef_name (md:methdef) : mname :=
  match md with | (m, _) => m end.

Definition methdefs_names (mds:methdefs) : (list mname) :=
  List.map methdef_name mds.



Definition cxt_t_entry_name (entry:tname * t_bound) : tname :=
  match entry with | (name, bnd) => name end.

Definition cxt_e_entry_name (entry:ename * typ) : tname :=
  match entry with | (name, t) => name end.

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


(** We assume a fixed class table [CT]. *)

Parameter CT : ctable.


Inductive VT : cname -> list variance -> Prop :=
| VT_lookup : forall C tvbnds N fds mds,
              binds C (C, tvbnds, N, fds, mds) CT ->
              VT C (tvbounds_vars tvbnds).

(**  Field lookup *)

Inductive fields : cname -> fielddefs -> Prop :=
| fields_obj : fields Object nil
| fields_super : forall C D tvbnds ts fds fds' ms, 
    binds C (C, tvbnds, (n_typ D ts), fds, ms) CT ->
    fields D fds' ->
    fields C (fds' ++ fds).


(** Need to substitute in type actuals for binders
  * to define ftype
  *)
Inductive ftype : fname -> typ_n -> typ -> Prop :=
| ftype_class :
    forall C tvbnds N fds mds t ts f,
    binds C (C, tvbnds, N, fds, mds) CT ->
    binds f t fds ->
    ftype f (n_typ C ts) (open_t 0 t ts)
| ftype_super :
     forall C tvbnds N fds mds t ts f,
    binds C (C, tvbnds, N, fds, mds) CT ->
    no_binds f fds ->
    ftype f (open_n 0 N ts) t ->
    ftype f (n_typ C ts) t.


(** Method lookup *)

Definition methdef_msig (md:methdef) : msig :=
  match md with
    | (_, (tbnds, t, ts, _)) => (tbnds, ts, t)
  end.


Inductive mtype : mname -> typ_n -> msig -> Prop :=
| mtype_class :
    forall C tvbnds N fds mds ts m tbnds ts' t e,
    binds C (C, tvbnds, N, fds, mds) CT ->
    binds m (tbnds, t, ts', e) mds ->
    mtype m (n_typ C ts) (open_msig 0 (tbnds, ts', t) ts)
| mtype_super :
    forall C tvbnds N fds mds ts m sig,
    binds C (C, tvbnds, N, fds, mds) CT ->
    no_binds m mds ->
    mtype m (open_n 0 N ts) sig ->
    mtype m (n_typ C ts) sig.


Inductive mbody : mname -> typ_n -> exp -> Prop :=
| mbody_class :
    forall C tvbnds N fds mds ts m tbnds ts' t e,
    binds C (C, tvbnds, N, fds, mds) CT ->
    binds m (tbnds, t, ts', e) mds ->
    mbody m (n_typ C ts) (open_e_t 1 e ts)
| mbody_super :
    forall C tvbnds N fds mds ts m e,
    binds C (C, tvbnds, N, fds, mds) CT ->
    no_binds m mds ->
    mbody m (open_n 0 N ts) e ->
    mbody m (n_typ C ts) e.

(** May need to check for locally closed terms *)
(** Don't think the # of binders needs to be specified
  * because it seems it always is equal to the length
  * of some given set of binders *)


