From VarJ Require Import VarJ_Syntax.
From VarJ Require Import VarJ_OpenClose.

(**  Field lookup *)

Inductive fields : cname -> fielddefs -> Prop :=
| fields_obj : fields Object nil
| fields_super : forall C D tvbnds ts fds fds' mds, 
    binds C (C, tvbnds, (n_typ D ts), fds, mds) CT ->
    fields D fds' ->
    fields C (fds' ++ fds).

#[global] Hint Constructors fields : core.

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

#[global] Hint Constructors ftype : core.

(** Method lookup *)

Inductive methods : cname -> methdefs -> Prop :=
| methods_obj : methods Object nil
| methods_super : forall C D tvbnds ts fds mds mds', 
    binds C (C, tvbnds, (n_typ D ts), fds, mds) CT ->
    methods D mds' ->
    methods C (mds' ++ mds).

#[global] Hint Constructors methods : core.

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

#[global] Hint Constructors mtype : core.

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

#[global] Hint Constructors mbody : core.

Inductive wide_ftype : typ_n -> list fname -> list typ -> Prop :=
| wide_ftype_nil :
    forall N,
    wide_ftype N nil nil
| wide_ftype_cons :
    forall N f fs t ts,
    ftype f N t ->
    wide_ftype N fs ts ->
    wide_ftype N (f::fs) (t::ts).

#[global] Hint Constructors wide_ftype : core.

Inductive wide_mtype : typ_n -> list mname -> list msig -> Prop :=
| wide_mtype_nil :
    forall N,
    wide_mtype N nil nil
| wide_mtype_cons :
    forall N m ms sig sigs,
    mtype m N sig ->
    wide_mtype N ms sigs ->
    wide_mtype N (m::ms) (sig::sigs).

#[global] Hint Constructors wide_mtype : core.

