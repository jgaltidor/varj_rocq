(* Typing Judgments *)

Require Import VarJ_Syntax.
Require Import VarJ_Substitution.
Require Import VarJ_Variance.
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


Definition tname_notInFV (x:tname) (ts:list typ) : Prop :=
  ~(In x (fv_ts ts)).

Inductive wide_tname_notInFV : list tname -> list typ -> Prop :=
| wide_tname_notInFV_nil : forall ts, wide_tname_notInFV nil ts
| wide_tname_notInFV_cons :
    forall x xs ts,
      tname_notInFV x ts ->
      wide_tname_notInFV xs ts ->
      wide_tname_notInFV (x::xs) ts.


Inductive sift (E:Type) : list E -> list typ -> list tname ->
                          list E -> list typ -> Prop :=
| sift_empty : forall ys,
               sift E nil nil ys nil nil

| sift_add : forall e es u us ys es' us',
               (exists y, In y ys /\ In y (fv_t u)) ->
               (forall y, In y ys -> In y (fv_t u) -> var_t y u invar) ->
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


Inductive matchInputsOK (typeFormals:list typ) :
  list typ_p -> list tname -> list typ -> Prop :=
| matchInputsOK_nil : matchInputsOK typeFormals nil nil nil

| matchInputsOK_cons_infer :
    forall ps y ys t ts,
      In y (body_fv_ts typeFormals) ->
      matchInputsOK typeFormals ps ys ts ->
      matchInputsOK typeFormals (p_inf::ps) (y::ys) (t::ts)

| matchInputsOK_cons_given :
    forall ps y ys t ts,
      matchInputsOK typeFormals ps ys ts ->
      matchInputsOK typeFormals ((p_typ t)::ps) (y::ys) (t::ts).


Inductive defsubtype_possible :
  typ_n -> typ -> list tname -> list typ -> Prop :=
| defsubtype_possible_ext :
    forall N tbnd N' ys ts,
      (exists ts',
        wide_tname_notInFV ys ts'
        /\
        let N'_open := (open_n 0 N' ts') in
        subtype_n nil N (subst_n ys ts N'_open)) ->
    (* -------------------------------------------- *)
      defsubtype_possible N (t_ext tbnd N') ys ts
| defsubtype_possible_fvar :
    forall N X ys ts,
      defsubtype_possible N (t_fvar X) ys ts.


Inductive wide_defsubtype_possible :
  list typ_n -> list typ -> list tname -> list typ -> Prop :=
| wide_defsubtype_possible_nil :
    forall ys ts,
      wide_defsubtype_possible nil nil ys ts
| wide_defsubtype_possible_cons :
    forall n ns u us ys ts,
      defsubtype_possible n u ys ts ->
      wide_defsubtype_possible ns us ys ts ->
      wide_defsubtype_possible (n::ns) (u::us) ys ts.


Definition matching (ns: list typ_n) (us: list typ) (ps: list typ_p)
  (ys: list tname) (ts: list typ) : Prop :=
    matchInputsOK us ps ys ts
    /\
    wide_defsubtype_possible ns us ys ts
    /\
    wide_tname_notInFV ys ts.


Fixpoint filterPossibleSiftPairs (typePairs: list (typ * typ)) :
  (list (typ_n * typ)) :=
match typePairs with
  | (t, u)::Pairs =>
      match t with
        | t_ext _ N => (N, u)::(filterPossibleSiftPairs Pairs)
        | _ => filterPossibleSiftPairs Pairs
      end
  | nil => nil
end.


Inductive typing : cxt_t -> cxt_e -> exp -> typ -> cxt_t -> Prop :=

| typing_var : forall tcxt ecxt x t,
               binds x t ecxt ->
               typing tcxt ecxt (e_fvar x) t nil

| typing_new : forall tcxt ecxt C ts es fds us,
               ok_n tcxt (n_typ C ts) ->
               fields C fds ->
               let fieldNames := (dom fds) in
               wide_ftype (n_typ C ts) fieldNames us ->
               wide_typing tcxt ecxt es us nil ->
               typing tcxt ecxt (e_new (n_typ C ts) es)
                                (t_ext nil (n_typ C ts))
                                nil

| typing_field : forall tcxt ecxt e f tbnds N T tcxt',
                 typing tcxt ecxt e (t_ext tbnds N) nil ->
                 tbounds_matches_cxt tbnds tcxt' ->
                 let N_open := (open_n_with_names 0 N (dom tcxt')) in
                 ftype f N_open T ->
                 typing tcxt ecxt (e_field e f) T tcxt'

| typing_subs : forall tcxt ecxt e T U tcxt',
                typing tcxt ecxt e U tcxt' ->
                subtype_t (tcxt ++ tcxt') U T ->
                ok_cxt_t tcxt tcxt' ->
                ok_t tcxt T ->
                typing tcxt ecxt e T nil

| typing_invk :
    forall tcxt ecxt e m Ps es tcxt' tcxts tbnds N
           methBnds Us U Ts Targs Ns' Us' L,
      (* Checking qualifier of method invocation *)
      typing tcxt ecxt e (t_ext tbnds N) nil ->
      tbounds_matches_cxt tbnds tcxt' ->

      (* Checking type actuals of method invocation *)
      wide_ok_p tcxt Ps ->

      (* Checking expression actuals of method invocation *)
      wide_typing tcxt ecxt es Targs nil ->
      wide_boundsOfTyp_matches_cxt Targs tcxts ->

      (* Method type look up *)
      (let N_open := (open_n_with_names 0 N (dom tcxt')) in
       mtype m N_open (methBnds, Us, U)) ->

      (* Open bodies of types of expression actuals *)
      let Targs_NoRng := stripRanges Targs in
      let Targs_NoRng_open :=
          List.map
            (fun arg : (typ * cxt_t) =>
               let (Targs_NoRng_i, tcxt_i) := arg in
               open_t_with_names 0 Targs_NoRng_i (dom tcxt_i))
            (combine Targs_NoRng tcxts)
      in

      (* Perform sifting and matching for wildcard capture *)
      (forall Ys,
         (* Choosing some arbitrary names for method type parameters *)
         distinct L (length methBnds) Ys ->
         (* Opening terms in method type signature *)
         let methBnds_open     := open_t_bounds_with_names 0 methBnds Ys in
         let Us_open           := open_ts_with_names 0 Us Ys in
         let Nargs_Us_for_sift :=
             filterPossibleSiftPairs (combine Targs_NoRng_open Us_open)
         in
         let Nargs_for_sift :=
             List.map
               (fun (arg: typ_n * typ) => let (n, u) := arg in n)
               Nargs_Us_for_sift
         in
         let Us_for_sift :=
             List.map
               (fun (arg: typ_n * typ) => let (n, u) := arg in u)
               Nargs_Us_for_sift
         in
         sift typ_n Nargs_for_sift Us_for_sift Ys Ns' Us' /\
         matching Ns' Us' Ps Ys Ts) ->

      (* Check inferred type actuals are within method bounds *)
      let tcxt'' := tcxt ++ tcxt' ++ (flatten tcxts) in
      let methBnds_open := open_t_bounds 0 tbnds Ts in
      let lower_bounds := t_bounds_get_lower_bounds methBnds_open in
      let upper_bounds := t_bounds_get_upper_bounds methBnds_open in
      let Ts_as_Bs := List.map b_typ Ts in
      wide_subtype_b tcxt'' lower_bounds Ts_as_Bs ->
      wide_subtype_t tcxt'' Ts upper_bounds ->
      
      (* Check that the actual types are applicable subtypes
       * of formal types *)
      let Us_open := (open_ts 0 Us Ts) in
      wide_subtype_t tcxt'' Targs_NoRng_open Us_open ->
  (* ------------------------------------------------------------------ *)
      typing tcxt ecxt (e_minvk e m Ps es) (open_t 0 U Ts)
             (tcxt' ++ (flatten tcxts))


with wide_typing :
       cxt_t -> cxt_e -> list exp -> list typ -> cxt_t -> Prop :=
| wide_typing_nil :
    forall tcxt ecxt tcxt',
      wide_typing tcxt ecxt nil nil tcxt'
| wide_typing_cons :
    forall tcxt ecxt e es t ts tcxt',
      typing tcxt ecxt e t tcxt' ->
      wide_typing tcxt ecxt es ts tcxt' ->
      wide_typing tcxt ecxt (e::es) (t::ts) tcxt'.


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
              wide_ok_t tcxt Ts_open ->
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
          wide_ok_t tcxt Ts_open ->
          (forall md, In md mds -> method_typing tcxt md C) ->
          class_typing (C, tvbnds, N, fds, mds).


Definition CT_isOK : Prop :=
  forall C Cdef, In (C, Cdef) CT -> class_typing Cdef.

(* All lemmas should assume the class table is well-formed *)
Parameter classTableOK : CT_isOK.

