(* Couple Test Lemmas *)

Require Import VarJ_Syntax.
Require Import VarJ_Substitution.
Require Import VarJ_Subtyping.
Require Import VarJ_Lookup.
Require Import VarJ_Wellform.
Require Import VarJ_Typing.
Require Import VarJ_Reduction.

(* Lemma 9 of TameFJ *)
Lemma weakening_subtyping :
  forall tcxt tcxt' tcxt'' T T',
  ok_cxt_t  (tcxt ++ tcxt') tcxt'' ->
  subtype_t (tcxt ++ tcxt') T T' ->
  subtype_t (tcxt ++ tcxt'' ++ tcxt') T T'.
Proof.
  (*
  intros tcxt tcxt' tcxt'' T T' H1 H2.
  induction H2.
  *)
  admit.
Qed.


Lemma context_movement :
  forall tcxt tcxt' tcxt'',
  ok_cxt_t tcxt (tcxt' ++ tcxt'') <->
  ok_cxt_t (tcxt ++ tcxt') tcxt''.
Proof.
  admit.
Qed.

(* Lemma 32 of TameFJ *)
Lemma inversion_field :
  forall tcxt ecxt e f T tcxt',
  typing tcxt ecxt (e_field e f) T tcxt' ->
  ok_cxt_t tcxt tcxt' ->
  (exists tcxt_n tbnds N U,
     ok_cxt_t tcxt (tcxt'++ tcxt_n) /\
     typing tcxt ecxt e (t_ext tbnds N) nil /\
     tbounds_matches_cxt tbnds (tcxt' ++ tcxt_n) /\
     ftype f (open_n_with_names 0 N (dom (tcxt' ++ tcxt_n))) U /\
     subtype_t (tcxt ++ tcxt' ++ tcxt_n) U T).
Proof.
  intros tcxt ecxt e f T tcxt' H1 H2.
  remember (e_field e f) as He.
  induction H1.

  (* Impossible case: typing_var *)
    inversion HeqHe.

  (* Impossible case: typing_new *)
    inversion HeqHe.

  (* Case: typing_field *)
    exists nil, tbnds, N, T.

    (* First simplify hypotheses *)    
    inversion HeqHe.
    rewrite -> H4 in *.
    rewrite -> H5 in *.
    unfold N_open in H0.
    simpl in *.

    (* Simpify conclusion *)
    ssimpl_list.
    (* Remaining steps are simple. *)
    auto.

   (* Case: typing_subs *)
   (* Simpilify goal *)
    simpl.

    (* Apply induction hypothesis *)
    remember (IHtyping HeqHe H0) as H'.

    (* Eliminating existential *)
    inversion H' as
        [tcxt_n'
           [tbnds'
              [N
                 [U' Hu']]]].
    clear - H Hu' H1 H2 H3.

    exists (tcxt' ++ tcxt_n'), tbnds', N, U'.

    split.
    apply Hu'.

    split.
    apply Hu'.

    split.
    apply Hu'.

    split.
    apply Hu'.

    apply subtype_t_trans with (t2 := U).
    apply Hu'.

    assert
      (subtype_t ((tcxt ++ tcxt') ++ tcxt_n' ++ nil) U T)
      as Hweak.

      apply weakening_subtyping with
        (tcxt:=tcxt++tcxt') (tcxt':=nil) (tcxt'':=tcxt_n')
        (T:=U) (T':=T).
      ssimpl_list.

      apply context_movement.
      apply Hu'.

      ssimpl_list.
      apply H.
      (* Proved assertion *)
   
    autorewrite with list in Hweak using simpl.
    assert (((tcxt ++ tcxt') ++ tcxt_n') =
            (tcxt ++ tcxt' ++ tcxt_n')) as Hlisteq.
      symmetry.
      apply app_assoc.

    rewrite -> Hlisteq in Hweak.
    apply Hweak.
    (* Completed T-subs case; the last relevant case *)

  (* Impossible case: typing_invk *)
  inversion HeqHe.
Qed.

Hint Resolve inversion_field.

