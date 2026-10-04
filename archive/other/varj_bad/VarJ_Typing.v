(* Typing Judgments *)

Require Import VarJ_Syntax.
Require Import VarJ_Substitution.
Require Import VarJ_Subtyping.
Require Import VarJ_Lookup.
Require Import VarJ_Wellform.

Definition body_fv (t:typ) : list tname :=
  match t with
    | t_ext tbnds N => fv_n N
    | t_bvar _ _ => nil
    | t_fvar X => X::nil
  end.

Fixpoint body_fv_ts (ts:list typ) : list tname :=
  match ts with
    | nil => nil
    | t::ts => (body_fv t) ++ (body_fv_ts ts)
  end.

Fixpoint getBodies (ts:list typ) : list typ_r :=
  match ts with
    | nil => nil
    | t::ts =>
        match t with
          | t_ext tbnds N => (typ_r_n N) :: (getBodies ts)
          | t_fvar X => (typ_r_fvar X) :: (getBodies ts)
          | t_bvar _ _ => getBodies ts
        end
  end.

Fixpoint getNBodies (ts:list typ) : list typ_n :=
  match ts with
    | nil => nil
    | t::ts =>
        match t with
          | t_ext tbnds N => N :: (getNBodies ts)
          | _ => getNBodies ts
        end
  end.

Fixpoint stripRanges (ts:list typ) : list typ :=
  match ts with
    | nil => nil
    | t::ts =>
        match t with
          | t_ext tbnds N =>
              (t_ext nil N)::(stripRanges ts)
          | _ => t::(stripRanges ts)
        end
  end.


Inductive sift (E:Type) : list E -> list typ -> list tname ->
                          list E -> list typ -> Prop :=
| sift_empty : forall ys,
               sift E nil nil ys nil nil

| sift_add : forall e es u us ys es' us',
               (exists y, In y ys /\ In y (fv_t u)) ->
               (forall y, In y ys /\ In y (fv_t u) -> var_t y u invar) ->
               sift E es us ys es' us' ->
               sift E (e::es) (u::us) ys (e::es') (u::us')

| sift_skip_var : forall e es u us ys es' us' v,
                    (exists y, In y ys /\
                               In y (fv_t u) /\
                               var_t y u v /\
                               v <> invar) ->
                    sift E es us ys es' us' ->
                    sift E (e::es) (u::us) ys es' us'

| sift_skip_novar : forall e es u us ys es' us',
                      (forall y, In y ys -> ~(In y (fv_t u))) ->
                      sift E es us ys es' us' ->
                      sift E (e::es) (u::us) ys es' us'.


Definition matching (ns: list typ_n) (us: list typ) (ps: list typ_p)
  (ys: list tname) (ts: list typ) : Prop :=

    (forall p y t,
       In (p, y, t) (combine (combine ps ys) ts) ->
       match p with
         | p_inf => In y (body_fv_ts us)
         | p_typ t' => t = t'
       end)
    /\
    (forall n u,
       In (n, u) (combine ns us) ->
       match u with
         | t_ext _ n' =>
             (exists ts',
                (forall y, In y ys -> ~(In y (fv_ts ts')))
                /\
                let n'_open := (open_n 0 n' ts') in
                subtype_n nil n (subst_n ys ts n'_open))
         | t_bvar _ _ => False
         | t_fvar _ => True
       end)
    /\
    (forall y, In y ys -> ~(In y (fv_ts ts))).


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
                 let N_open := (open_n_with_names 0 N (dom tcxt')) in
                 ftype f N_open T ->
                 typing tcxt ecxt (e_field e f) T tcxt'

| typing_subs : forall tcxt ecxt e T L,
                  (exists U tbnds,
                     (forall xs,
                        distinct L (length tbnds) xs ->
                        let tcxt' := openToCtxt_tbounds 0 xs tbnds in
                        typing tcxt ecxt e U tcxt' /\
                        subtype_t (tcxt ++ tcxt') U T /\
                        ok_cxt_t tcxt tcxt')) ->
                ok_t tcxt T ->
                typing tcxt ecxt e T nil

| typing_invk : forall tcxt ecxt e m Ps es tcxt' tcxts tbnds N
                       methBnds Us U Ts Targs Ns' Us' L,
                typing tcxt ecxt e (t_ext tbnds N) nil ->
                tbounds_matches_cxt tbnds tcxt' ->
                (forall P, In P Ps -> ok_p tcxt P) ->
                (forall e_i Targ_i tcxt_i,
                   In (e_i, Targ_i, tcxt_i) (combine (combine es Targs) tcxts) ->
                   boundsOfTyp_matches_cxt Targ_i tcxt_i ->
                   typing tcxt ecxt e_i Targ_i nil) ->
                (let N_open := (open_n_with_names 0 N (dom tcxt')) in
                  mtype m N_open (methBnds, Us, U)) ->
                (forall Ys,
                   distinct L (length methBnds) Ys ->
                   let Us_open := open_ts_with_names 0 Us Ys in
                   let Nargs := getNBodies Targs in
                   let Nargs_open :=
                     List.map
                       (fun arg : (typ_n * cxt_t) =>
                          let (N_i, tcxt_i) := arg in
                            open_n_with_names 0 N_i (dom tcxt_i))
                       (combine Nargs tcxts)
                   in
                     sift typ_n Nargs_open Us_open Ys Ns' Us' /\
                     matching Ns' Us' Ps Ys Ts) ->
                let tcxt'' := tcxt ++ tcxt' ++ (flatten tcxts) in
                let Targs_NoRng := stripRanges Targs in
                let Targs_NoRng_open :=
                  List.map
                    (fun arg : (typ * cxt_t) =>
                       let (Targs_i, tcxt_i) := arg in
                         open_t_with_names 0 Targs_i (dom tcxt_i))
                    (combine Targs_NoRng tcxts)
                in
                let Us_open := (open_ts 0 Us Ts) in
                let Bs_low_open :=
                    List.map (fun arg : t_bound => let (b, t) := arg in open_b 0 b Ts) methBnds
                in
                let Ts_up_open  :=
                    List.map (fun arg : t_bound => let (b, t) := arg in open_t 0 t Ts) methBnds
                in
                (forall Targ_i U_i B_low T_up T_i,
                   In (Targ_i, U_i, B_low, T_up, T_i)
                      (combine
                         (combine
                            (combine
                               (combine Targs_NoRng_open Us_open)
                               Bs_low_open)
                            Ts_up_open)
                         Ts) ->
                   subtype_t tcxt'' Targ_i U_i ->
                   subtype_b tcxt'' B_low (b_typ T_i) ->
                   subtype_t tcxt'' T_i Targ_i) ->
        (* -------------------------------------------------------------------------- *)
                typing tcxt ecxt (e_minvk e m Ps es) (open_t 0 U Ts)
                                                     (tcxt' ++ (flatten tcxts)).


(* Override Check *)

Inductive override : mname -> typ_n -> msig -> Prop :=

| over_def : forall m N sig,
             mtype m N sig ->
             override m N sig

| over_undef : forall m C ts sig mds,
               methods C mds ->
               no_binds m mds ->
               override m (n_typ C ts) sig.


Inductive method_typing : cxt_t -> methdef -> cname -> Prop :=
| w_meth : forall clsCxt m methBnds T Ts e C clsTVBnds
                  N fds mds L_bnds L_body,
           binds C (C, clsTVBnds, N, fds, mds) CT ->
           tbounds_matches_cxt (tvbounds_2_tbounds clsTVBnds) clsCxt ->
           override m N (methBnds, Ts, T) ->
           let clsVars := tvbounds_vars clsTVBnds in
           let clsVarsNegated := negateVars clsVars in
           let Xs := dom clsCxt in
           mono_t clsVars Xs T ->
           (forall T_i, In T_i Ts -> mono_t clsVarsNegated Xs T_i) ->
           mono_t_bounds clsVarsNegated Xs methBnds  ->
           (forall Ys,
              distinct L_bnds (length methBnds) Ys ->
              let methCxt  := openToCtxt_tbounds 0 Ys methBnds in
              let Ts_open  := open_ts_with_names 0 Ts Ys in
              let T_open   := open_t_with_names 0 T Ys in
              let tcxt     := clsCxt ++ methCxt in
              ok_cxt_t clsCxt methCxt ->
              ok_t tcxt T_open ->
              (forall T_i, In T_i Ts_open -> ok_t tcxt T_i) ->
              (forall xs,
                 distinct (this::L_body) (length Ts) xs ->
                 let X_typs   := List.map (fun X => t_fvar X) Xs in
                 let thisTyp  := t_ext nil (n_typ C X_typs) in
                 let ecxt     := (this, thisTyp) :: (combine xs Ts) in
                 typing tcxt ecxt e T nil)) ->
           method_typing clsCxt (m, (methBnds, T, Ts, e)) C.


Inductive class_typing : classdef -> Prop :=
| w_cls : forall C tvbnds N fds mds L Xs,
          distinct L (length tvbnds) Xs ->
          let N_open := open_n_with_names 0 N Xs in
          let Ts_open := (* field types *)
            List.map
              (fun (fd:fielddef) =>
                 let (f, T) := fd in open_t_with_names 0 T Xs)
              fds
          in
          let tcxt := openToCtxt_tvbounds 0 Xs tvbnds in
          let clsVars := tvbounds_vars tvbnds in
          mono_n clsVars Xs N_open ->
          (forall T_i, In T_i Ts_open -> mono_t clsVars Xs T_i) ->
          ok_cxt_t nil tcxt ->
          ok_n tcxt N_open ->
          (forall T_i, In T_i Ts_open -> ok_t tcxt T_i) ->
          (forall md, In md mds -> method_typing tcxt md C) ->
          class_typing (C, tvbnds, N, fds, mds).


Definition CT_isOK : Prop :=
  forall C Cdef, In (C, Cdef) CT -> class_typing Cdef.

(* All lemmas should assume the class table is well-formed *)
Parameter classTableOK : CT_isOK.

