(* Judgments for wellformed types and environments in VarJ *)

From VarJ Require Import VarJ_Syntax.
From VarJ Require Import VarJ_OpenClose.
From VarJ Require Import VarJ_Subtyping.

(* ubound in VarJ paper needs to be fix *)
Inductive ubound_t : cxt_t -> typ -> typ -> Prop :=
| ubound_t_fvar : forall tcxt X t b_low t_up,
                  binds X (b_low, t_up) tcxt ->
                  ubound_t tcxt t_up t ->
                  ubound_t tcxt (t_fvar X) t

| ubound_t_ext : forall tcxt tbnds N,
                 ubound_t tcxt (t_ext tbnds N) (t_ext tbnds N).

#[global] Hint Constructors ubound_t : core.
                   
Inductive ubound_b : cxt_t -> typ_b -> typ_b -> Prop :=
| ubound_b_bot : forall tcxt,
                 ubound_b tcxt b_bot b_bot

| ubound_b_t : forall tcxt t t',
               ubound_t tcxt t t' ->
               ubound_b tcxt (b_typ t) (b_typ t').

#[global] Hint Constructors ubound_b : core.

Inductive ok_t : cxt_t -> typ -> Prop :=
| ok_t_fvar : forall tcxt X, In X (dom tcxt) -> ok_t tcxt (t_fvar X)

| ok_t_ext : forall tcxt tbnds N L xs,
                distinct L (length tbnds) xs ->
                let tcxt' := (openToCtxt_tbounds 0 xs tbnds) in
                let N'    := (open_n_with_names 0 N xs) in
                ok_cxt_t tcxt tcxt' ->
                ok_n (tcxt ++ tcxt') N' ->
       (* ---------------------------------------------------------- *)
             ok_t tcxt (t_ext tbnds N)

with ok_n : cxt_t -> typ_n -> Prop :=
| ok_n_obj : forall tcxt, ok_n tcxt (n_typ Object nil)

| ok_n_c : forall C tvbnds N fds mds tcxt ts,
           binds C (C, tvbnds, N, fds, mds) CT ->
           let tvbnds_opened := open_tv_bounds 0 tvbnds ts in
           let lower_bounds  := tv_bounds_get_lower_bounds tvbnds_opened in
           let upper_bounds  := tv_bounds_get_upper_bounds tvbnds_opened in
           let ts_as_bs      := List.map b_typ ts in
           wide_subtype_b tcxt lower_bounds ts_as_bs ->
           wide_subtype_t tcxt ts upper_bounds ->
           wide_ok_t tcxt ts ->
           ok_n tcxt (n_typ C ts)

with ok_b : cxt_t -> typ_b -> Prop :=
| ok_b_bot : forall tcxt, ok_b tcxt b_bot

| ok_b_t : forall tcxt t,
           ok_t tcxt t -> ok_b tcxt (b_typ t)

with ok_cxt_t : cxt_t -> cxt_t -> Prop :=
| ok_cxt_t_nil : forall tcxt, ok_cxt_t tcxt nil

| ok_cxt_t_cons:
    forall tcxt x b_low t_up tcxt'
           b_low_ubound t_up_ubound,
      no_binds x tcxt ->
      let entireCxt := (tcxt ++ ((x, (b_low, t_up))::tcxt')) in
      ok_b entireCxt b_low ->
      ok_t entireCxt t_up ->
      ubound_b tcxt b_low b_low_ubound ->
      ubound_t tcxt t_up  t_up_ubound ->
      subtype_b tcxt b_low_ubound (b_typ t_up_ubound) ->
      subtype_b tcxt b_low (b_typ t_up) ->
      ok_cxt_t (tcxt ++ ((x, (b_low, t_up))::nil)) tcxt' ->
  (* ---------------------------------------------------- *)
      ok_cxt_t tcxt ((x, (b_low, t_up)) :: tcxt')

with wide_ok_t : cxt_t -> list typ -> Prop :=
| wide_ok_t_nil : forall tcxt, wide_ok_t tcxt nil
| wide_ok_t_cons :
    forall tcxt t ts,
      ok_t tcxt t ->
      wide_ok_t tcxt ts ->
      wide_ok_t tcxt (t::ts).

#[global] Hint Constructors ok_t
                  ok_n
                  ok_b
                  ok_cxt_t
                  wide_ok_t : core.

Inductive ok_p : cxt_t -> typ_p -> Prop :=
| ok_p_inf : forall tcxt, ok_p tcxt p_inf

| ok_p_t : forall tcxt t,
           ok_t tcxt t -> ok_p tcxt (p_typ t).

#[global] Hint Constructors ok_p : core.

Inductive wide_ok_p : cxt_t -> list typ_p -> Prop :=
| wide_ok_p_nil : forall tcxt, wide_ok_p tcxt nil
| wide_ok_p_cons :
    forall tcxt p ps,
      ok_p tcxt p ->
      wide_ok_p tcxt ps ->
      wide_ok_p tcxt (p::ps).

#[global] Hint Constructors wide_ok_p : core.

Inductive ok_cxt_e : cxt_t -> cxt_e -> Prop :=
| ok_cxt_e_nil : forall tcxt, ok_cxt_e tcxt nil

| ok_cxt_e_cons : forall tcxt x t ecxt,
                  no_binds x ecxt ->
                  ok_t tcxt t ->
                  ok_cxt_e tcxt ecxt ->
                  ok_cxt_e tcxt ((x, t)::ecxt).

#[global] Hint Constructors ok_cxt_e : core.

