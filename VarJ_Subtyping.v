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
                   let tcxt' := openToCtxt_tbounds 0 xs tbnds in
                   subtype_n (tcxt ++ tcxt') N N') ->
                subtype_t tcxt (t_ext tbnds N) (t_ext nil N')

| subtype_t_n_right : forall tcxt tbnds' N N' L,
                (forall xs,
                   distinct L (length tbnds') xs ->
                   let tcxt' := openToCtxt_tbounds 0 xs tbnds' in
                   subtype_n (tcxt ++ tcxt') N N') ->
                subtype_t tcxt (t_ext nil N) (t_ext tbnds' N')

| subtype_t_pack : forall tcxt tbnds tbnds' N ts L,
                     (forall xs,
                        distinct L (length tbnds') xs ->
                        let tcxt' := openToCtxt_tbounds 0 xs tbnds' in
                        (* Need to open ts because they contain binders in tbnds' *)
                        let ts' := open_ts_with_names 0 ts xs in
                        let tbnds_opened := open_t_bounds 0 tbnds ts' in
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

