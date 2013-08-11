(* Contains Subtyping and Variance Predicate Definitions *)

Require Import VarJ_Syntax.
Require Import VarJ_Substitution.
Require Import VarJ_Variance.

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
  wide_var_subtype tcxt vars ts ts' ->
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
                   let tcxt' := openToCtxt_tbounds 0 xs tbnds in
                   subtype_n (tcxt ++ tcxt') N N') ->
                subtype_t tcxt (t_ext tbnds N) (t_ext nil N')

| subtype_t_n_right : forall tcxt tbnds' N N' L,
                (forall xs,
                   distinct L (length tbnds') xs ->
                   let tcxt' := openToCtxt_tbounds 0 xs tbnds' in
                   subtype_n (tcxt ++ tcxt') N N') ->
                subtype_t tcxt (t_ext nil N) (t_ext tbnds' N')

| subtype_t_pack :
    forall tcxt tbnds tbnds' N ts L ys,
      (* Need to open subterms in the left type, which
       * contain binders in tbnds'
       *)
      distinct L (length tbnds') ys ->
      let tcxt' := openToCtxt_tbounds 0 ys tbnds' in
      (* Need to open ts because they contain binders in tbnds' *)
      let ts' := open_ts_with_names 0 ts ys in
      (* Instantiating bounds in tbnds with ts' instead of ts
       * because again ts may contain binders
       *)
      let tbnds_opened := open_t_bounds 0 tbnds ts' in
      let lower_bounds := t_bounds_get_lower_bounds tbnds_opened in
      let upper_bounds := t_bounds_get_upper_bounds tbnds_opened in
      let ts'_as_bs    := List.map b_typ ts' in
      wide_subtype_b (tcxt ++ tcxt') lower_bounds ts'_as_bs ->
      wide_subtype_t (tcxt ++ tcxt') ts' upper_bounds ->
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
   var_subtype tcxt bivar t t'


with wide_subtype_t : cxt_t -> list typ -> list typ -> Prop :=
| wide_subtype_t_nil :
    forall tcxt,
      wide_subtype_t tcxt nil nil
| wide_subtype_t_cons :
    forall tcxt t ts t' ts',
      subtype_t tcxt t t' ->
      wide_subtype_t tcxt ts ts' ->
      wide_subtype_t tcxt (t::ts) (t'::ts')

with wide_subtype_b : cxt_t -> list typ_b -> list typ_b -> Prop :=
| wide_subtype_b_nil :
    forall tcxt,
      wide_subtype_b tcxt nil nil
| wide_subtype_b_cons :
    forall tcxt b bs b' bs',
      subtype_b tcxt b b' ->
      wide_subtype_b tcxt bs bs' ->
      wide_subtype_b tcxt (b::bs) (b'::bs')

with wide_subtype_n : cxt_t -> list typ_n -> list typ_n -> Prop :=
| wide_suntype_n_nil :
    forall tcxt,
      wide_subtype_n tcxt nil nil
| wide_suntype_n_cons :
    forall tcxt n ns n' ns',
      subtype_n tcxt n n' ->
      wide_subtype_n tcxt ns ns' ->
      wide_subtype_n tcxt (n::ns) (n'::ns')

with wide_var_subtype :
  cxt_t -> list variance -> list typ -> list typ -> Prop :=
| wide_var_subtype_nil :
    forall tcxt,
      wide_var_subtype tcxt nil nil nil
| wide_var_subtype_cons :
    forall tcxt v vs t ts t' ts',
      var_subtype tcxt v t t' ->
      wide_var_subtype tcxt vs ts ts' ->
      wide_var_subtype tcxt (v::vs) (t::ts) (t'::ts').

(* Adding inductive types without transitive rules/constructor to hints *)
Hint Constructors    subtype_n
                  (* skipping subtype_t because of subtype_t_trans *)
                  (* skipping subtype_b because of subtype_b_trans *)
                     var_subtype
                     wide_subtype_t
                     wide_subtype_b
                     wide_subtype_n
                     wide_var_subtype.

(* Adding non-transitive subtype_t rules *)
Hint Resolve subtype_t_refl
             subtype_t_ubound
             subtype_t_n_left
             subtype_t_n_right
             subtype_t_pack.

Check subtype_t_trans.

(* Using technique from UseAuto chapter of SF book by Pierce et al.
 * to have a hint using a transitive rule without adding significantly
 * slowing auto.
 * Only applying subtype_t_trans when there is some evidence that
 * this application might help.
 *)
Hint Extern 10 (subtype_t ?tcxt ?S ?U) =>
  match goal with 
  | H: subtype_t tcxt S ?T |- _ => apply (subtype_t_trans tcxt S T U)
  | H: subtype_t tcxt ?T U |- _ => apply (subtype_t_trans tcxt S T U)
  end.


(* Adding non-transitive subtype_b rules *)
Hint Resolve subtype_b_t
             subtype_b_bot
             subtype_b_lbound
             subtype_b_refl.

Hint Extern 10 (subtype_b ?tcxt ?S ?U) =>
  match goal with 
  | H: subtype_b tcxt S ?T |- _ => apply (subtype_b_trans tcxt S T U)
  | H: subtype_b tcxt ?T U |- _ => apply (subtype_b_trans tcxt S T U)
  end.


