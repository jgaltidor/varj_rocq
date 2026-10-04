
Require Import Coq.Bool.Bool.

Inductive variance : Set :=
| covar : variance
| contravar : variance
| invar : variance
| bivar : variance.


Definition var_lt (v1:variance) (v2:variance) : bool :=
  match v1 with
    | bivar => false
    | invar =>
        match v2 with
          | invar => false
          | _ => true
        end
    | covar =>
        match v2 with
          | bivar => true
          | _ => false
        end
    | contravar =>
        match v2 with
          | bivar => true
          | _ => false
        end
    end.

Definition lt (v1:variance) (v2:variance) : Prop := Is_true(var_lt v1 v2).

Notation "v1 < v2" := (lt v1 v2).

Definition var_eq (v1:variance) (v2:variance) : bool :=
  match (v1 = v2) with
    | True => true
    | False => false
  end.


Definition le (v1:variance) (v2:variance) : bool :=
  (v1 < v2) \/ (v1 = v2).

