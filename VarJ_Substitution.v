From VarJ Require Import VarJ_Syntax.

Fixpoint subst_t (xs: list tname) (ts: list typ) (t: typ) : typ :=
  let subst_t_bound :=
    fun (xs: list tname) (ts: list typ) (tbnd: t_bound) =>
      let (b, t) := tbnd in (subst_b xs ts b, subst_t xs ts t)
  in
  let subst_t_bounds :=
    fun (xs: list tname) (ts: list typ) (tbnds: t_bounds) =>
      List.map (fun tbnd => subst_t_bound xs ts tbnd) tbnds
  in
  match t with
    | t_ext tbnds N =>
        t_ext (subst_t_bounds xs ts tbnds) (subst_n xs ts N)
    | t_bvar _ _ => t
    | t_fvar x =>
        match get x (combine xs ts) with
          | Some t' => t'
          | None => t
        end
  end

with subst_b (xs: list tname) (ts: list typ) (b: typ_b) : typ_b :=
  match b with
    | b_typ t => b_typ (subst_t xs ts t)
    | b_bot   => b_bot
  end

with subst_n (xs: list tname) (ts: list typ) (n: typ_n) : typ_n :=
  match n with n_typ C ts' =>
    n_typ C (List.map (fun t => subst_t xs ts t) ts')
  end.


Definition subst_p (xs: list tname) (ts: list typ) (p: typ_p) : typ_p :=
  match p with
    | p_typ t => p_typ (subst_t xs ts t)
    | p_inf => p_inf
  end.

Definition subst_ts (xs: list tname) (ts: list typ) (ts': list typ) : list typ :=
  List.map (fun t => subst_t xs ts t) ts'.

Definition subst_ps (xs: list tname) (ts: list typ) (ps: list typ_p) : list typ_p :=
  List.map (fun p => subst_p xs ts p) ps.

Definition subst_bs (xs: list tname) (ts: list typ) (bs: list typ_b) : list typ_b :=
  List.map (fun b => subst_b xs ts b) bs.

Definition subst_ns (xs: list tname) (ts: list typ) (ns: list typ_n) : list typ_n :=
  List.map (fun n => subst_n xs ts n) ns.

Definition subst_t_bound (xs: list tname) (ts: list typ) (tbnd: t_bound) : t_bound :=
  let (b, t) := tbnd in (subst_b xs ts b, subst_t xs ts t).

Definition subst_t_bounds (xs: list tname) (ts: list typ) (tbnds: t_bounds) : t_bounds :=
 List.map (fun tbnd => subst_t_bound xs ts tbnd) tbnds.


Fixpoint subst_e (xs: list ename) (es: list exp) (expr: exp) : exp :=
  match expr with
    | e_field e f => e_field (subst_e xs es e) f
    | e_minvk e m ps es' =>
        e_minvk (subst_e xs es e) m ps
                (List.map (fun e' => subst_e xs es e') es')
    | e_new N es' =>
        e_new N (List.map (fun e' => subst_e xs es e') es')
    | e_bvar _ => expr
    | e_fvar x =>
        match get x (combine xs es) with
          | Some e' => e'
          | None => expr
        end
  end.

