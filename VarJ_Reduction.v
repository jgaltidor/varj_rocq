(* Reduction (Evalution) Semantics *)

Require Import VarJ_Syntax.
Require Import VarJ_Substitution.
Require Import VarJ_Subtyping.
Require Import VarJ_Lookup.
Require Import VarJ_Wellform.
Require Import VarJ_Typing.

Fixpoint getNTypes_exps (es:list exp) : list typ_n :=
  match es with
    | nil => nil
    | e::es =>
        match e with
          | e_new N _ => N :: (getNTypes_exps es)
          | _ => getNTypes_exps es
        end
  end.

Inductive step : exp -> exp -> Prop :=

(* Computation Rules *)

| r_field : forall C ts es f v fds,
            (forall e, In e es -> value e) ->
            fields C fds ->
            binds f v (combine (dom fds) es) ->
      (* --------------------------------------------- *)
            step (e_field (e_new (n_typ C ts) es) f) v

| r_invk : forall N es' m Ps es e_0 Ts methBnds Us U Ns' Us' L,
           (forall e, In e es' -> value e) ->
           (forall e, In e es -> value e) ->
           mbody m N e_0 ->
           mtype m N (methBnds, Us, U) ->
           (forall Ys,
              distinct L (length methBnds) Ys ->
              let Ns := getNTypes_exps es in
              let Us_open := open_ts_with_names 0 Us Ys in
              sift typ_n Ns Us_open Ys Ns' Us' /\
              matching Ns' Us' Ps Ys Ts) ->
     (* ---------------------------------------------------------- *)
           step (e_minvk (e_new N es') m Ps es)
                (let e_0_v  := open_e 0 e_0 es in
                 let e_0_vt := open_e_t 0 e_0_v Ts in
                 (subst_e (this::nil) ((e_new N es')::nil) e_0_vt))


(* Congruence Rules *)

| rc_field : forall e f e',
             step e e' ->
             step (e_field e f) (e_field e' f)

| rc_new : forall es N es',
           wide_step es es' ->
           step (e_new N es) (e_new N es')


| rc_inv_recv : forall e m ps es e',
                step e e' ->
                step (e_minvk e m ps es) (e_minvk e' m ps es)


| rc_inv_arg : forall e m ps es es',
               value e ->
               wide_step es es' ->
               step (e_minvk e m ps es) (e_minvk e m ps es')


with wide_step : list exp -> list exp -> Prop :=

| wide_step_hdstep : forall e e' es,
                     step e e' ->
                     wide_step (e::es) (e'::es)

| wide_step_hdskip : forall e es es',
                     value e ->
                     wide_step es es' ->
                     wide_step (e::es) (e::es').

Hint Constructors step wide_step.

