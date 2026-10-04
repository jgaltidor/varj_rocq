(* Typing Judgments *)

Require Import VarJ_Syntax.
Require Import VarJ_Subtyping.
Require Import VarJ_Wellform.
Require Import Metatheory.


Inductive typing : cxt_t -> cxt_e -> exp -> typ -> cxt_t -> Prop :=

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

| typing_field : forall tcxt ecxt e f tbnds N T tcxt',
                 typing tcxt ecxt e (t_ext tbnds N) nil ->
                 tbounds_matches_cxt tbnds tcxt' ->
                 ftype f (open_n_with_names 0 N (dom tcxt')) T ->
                 ok_cxt_t tcxt tcxt' ->
                 typing tcxt ecxt (e_field e f) T tcxt'

| typing_subs : forall tcxt ecxt e T U tcxt',
                typing tcxt ecxt e U tcxt' ->
                subtype_t (tcxt ++ tcxt') U T ->
                ok_cxt_t tcxt tcxt' ->
                ok_t tcxt T ->
                typing tcxt ecxt e T nil

| typing_invk : forall tcxt ecxt e T tcxt',
                typing tcxt ecxt e (t_ext tbnds N) nil ->
                mtype m (open_n_with_names 0 N (dom tcxt')) (tbnds', Us, U) ->
                (forall P, In P Ps -> ok_p tcxt P) ->
                (forall e_i tcxt_i T_i,
                   In (e_i, tcxt_i) (es, tcxts) ->
                   typing tcxt ecxt e' T_i nil /\
                   boundsOfTyp_matches_cxt T_i tcxt_i) ->
                tcxt'' = (tcxt' ++ (join tcxts)) ->
                


  typing tcxt ecxt (e_mink e m Ps es)
                   (open_t 0 U ts)
                   (tcxt' ++ (join tcxts))

