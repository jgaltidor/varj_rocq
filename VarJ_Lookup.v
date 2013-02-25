Require Import VarJ_Syntax.
Require Import VarJ_Substitution.

(**  Field lookup *)

Inductive fields : cname -> fielddefs -> Prop :=
| fields_obj : fields Object nil
| fields_super : forall C D tvbnds ts fds fds' mds, 
    binds C (C, tvbnds, (n_typ D ts), fds, mds) CT ->
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

Inductive methods : cname -> methdefs -> Prop :=
| methods_obj : methods Object nil
| methods_super : forall C D tvbnds ts fds mds mds', 
    binds C (C, tvbnds, (n_typ D ts), fds, mds) CT ->
    methods D mds' ->
    methods C (mds' ++ mds).


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

