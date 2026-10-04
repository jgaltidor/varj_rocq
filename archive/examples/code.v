

Example var_neq_ex : invar <> covar.
Proof.
  discriminate.
Qed.


Lemma trans : forall (v1 v2 v3:variance), v1 < v2 -> v2 < v3 -> v1 < v3.
Proof.
  intros v1 v2 v3 H1 H2.
  inversion H1.
  inversion H2.
  clear H1 H2.
  subst.
  contradiction H. (* Proof by contradiction *)
  reflexivity.

  subst.
  apply var_lt_invar.
  discriminate.

  subst.
  apply var_lt_invar.
  discriminate.

  subst.
  inversion H2.  

  subst.
  inversion H2.
Qed.


(* Alternative proof for trans

Lemma trans : forall (v1 v2 v3:variance), v1 < v2 -> v2 < v3 -> v1 < v3.
Proof.
  intros v1 v2 v3 H1 H2.
  inversion H1.
  inversion H2.
  clear H1 H2.
  subst.
  apply var_lt_invar.
  apply H4.
  
  clear H1 H2.
  subst.
  apply var_lt_invar.
  discriminate.

  clear H1 H2.
  subst.
  apply var_lt_invar.
  discriminate.

  subst.
  inversion H2. (* Reaches contradiction *)

  subst.
  inversion H2.
Qed.
*)


(* Another proof of trans, that is very short:

Lemma trans : forall (v1 v2 v3:variance), v1 < v2 -> v2 < v3 -> v1 < v3.
Proof.
  intros v1 v2 v3 H1 H2.
  inversion H1; inversion H2; subst;
    try (apply var_lt_invar; discriminate); inversion H2; auto.
Qed.
*)

Lemma var_lt_trans : forall (v1 v2 v3:variance), v1 < v2 -> v2 < v3 -> v1 < v3.
Proof.
  intros v1 v2 v3 H1 H2.
  inversion H1.
  inversion H2.
  clear H1 H2.
  inversion H.
  inversion H4.

(*

Definition dom_t (cxt : cxt_t) : list tname :=
  List.map cxt_t_entry_name cxt.

Definition dom_e (cxt : ecxt) : list ename :=
  List.map ecxt_entry_name cxt.

*)


Inductive typing : cxt_t -> cxt_e -> exp -> typ -> t_bounds -> Prop :=

| typing_var : forall tcxt ecxt x t,
               binds x t ecxt ->
               typing tcxt ecxt (e_fvar x) t nil

| typing_new : forall tcxt ecxt C ts es fds,
               ok_n tcxt (n_typ C ts) ->
               fields C fds ->
               (forall f e U,
                  In (f, e) (combine (dom fds) es) ->
                  ftype f (n_typ C ts) U ->
                  typing tcxt ecxt e U nil) ->
               typing tcxt ecxt (e_new (n_typ C ts) es)
                                (t_ext nil (n_typ C ts))
                                nil

| typing_field : forall tcxt ecxt e f tbnds N T,
                 typing tcxt ecxt e (t_ext tbnds N) nil ->
                 ftype f N T ->
                 typing tcxt ecxt (e_field e f) T tbnds

| typing_subs : forall tcxt ecxt e T U tbnds L,
                typing tcxt ecxt e U tbnds ->
                (forall xs tcxt' U_opened,
                   distinct L (length tbnds) xs ->
                   tcxt'    = (openToCtxt_tbounds xs tbnds) ->
                   U_opened = (open_t_with_names 0 U xs) ->
                   subtype_t (tcxt ++ tcxt') U_opened T /\
                   ok_cxt_t tcxt tcxt') ->
                ok_t tcxt T ->
                typing tcxt ecxt e T nil.




