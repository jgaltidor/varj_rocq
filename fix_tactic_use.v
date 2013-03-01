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
  fix IH 6.
  intros tcxt ecxt e f T tcxt' H1 H2.
  remember (e_field e f) as He.
  destruct H1.

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

    (* Simpify conclusion *)
    assert (tcxt' ++ nil = tcxt') as H'.
    apply app_nil_r.
    rewrite -> H'.
  
      (* Proving " ok_cxt_t tcxt tcxt' " *)
      split.
      apply H2.

      split.
      apply H1.

      split.
      apply H.

      split.
      apply H0.

      apply subtype_t_refl.

   (* Case: typing_subs *)
      (* First simplify hypotheses *)
      rewrite -> HeqHe in *.
      (* Simpilify goal *)
      simpl.

      inversion H as [U Hu].
      inversion Hu as [tbnds Htbnds].

      remember (fresh_list L (length tbnds)) as ys.

      remember (fresh_and_distinct L (length tbnds) Heqys) as ysDistinct.

      specialize (Htbnds ys ysDistinct).

      inversion Htbnds.
      inversion H3.
      clear - IH H1 H4 H5.

      remember (openToCtxt_tbounds 0 ys tbnds) as tcxt''.
      remember (IH tcxt ecxt e f U tcxt'' H1 H5) as H'.
      inversion H' as [tcxt_n' Htcxt_n'].
      (* Next guard fails because (fresh_list L (length tbnds)) is not a subterm
       * of terms applied to the inductive hypothesis.
       *)
      Guarded.
      inversion Htcxt_n' as [tbnds' Htbnds'].
      inversion Htbnds' as [N Hn].
      inversion Hn as [U' Hu'].
      clear - IH Hu' H1 H4 H5.
      exists (tcxt'' ++ tcxt_n'), tbnds', N, U'.
      split.
      apply Hu'.

      split.
      apply Hu'.

      split.
      apply Hu'.

      split.
      apply Hu'.

      
      assert
        (subtype_t ((tcxt ++ tcxt'') ++ tcxt_n' ++ nil) U T)
        as H4weak.
        apply weakening_subtyping with
          (tcxt:=tcxt++tcxt'') (tcxt':=nil) (tcxt'':=tcxt_n')
          (T:=U) (T':=T).
        ssimpl_list.
        apply context_movement.
        apply Hu'.
        ssimpl_list.
        apply H4.

      assert (tcxt ++ tcxt'' ++ tcxt_n'
              = (tcxt ++ tcxt'') ++ tcxt_n' ++ nil) as Hlisteq.
      ssimpl_list.
      apply app_assoc.
      rewrite <- Hlisteq in H4weak.
      apply subtype_t_trans with (t2:=U).
      apply Hu'.
      apply H4weak.
      (* Completed T-subs case; the last relevant case *)

      repeat inversion HeqHe.
Qed.

