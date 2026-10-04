(** Names and environments for the locally nameless encoding.

    Atoms are natural numbers. An environment is an association list
    [list (atom * A)]; its order matters (see [dom]), so it is not a
    finite map. *)

From Stdlib Require Export List.
From Stdlib Require Import Arith Lia.

(** * Atoms *)

Definition atom := nat.

Definition eq_atom_dec : forall x y : atom, {x = y} + {x <> y} := Nat.eq_dec.

Notation "x == y" := (eq_atom_dec x y) (at level 67).

Lemma atom_fresh_for_list : forall (xs : list atom), { x : atom | ~ In x xs }.
Proof.
  intros xs. exists (S (list_max xs)). intros H.
  assert (Hle : list_max xs <= list_max xs) by reflexivity.
  apply list_max_le, Forall_forall with (x := S (list_max xs)) in Hle;
    [lia | assumption].
Qed.

(** * Environments *)

Notation "x \in E" := (In x E) (at level 69).
Notation "x \notin E" := (~ In x E) (at level 69).

Section Environment.

  Context {A : Type}.

  (** [get x E] is the first binding of [x] in [E]. *)
  Fixpoint get (x : atom) (E : list (atom * A)) : option A :=
    match E with
    | nil => None
    | (y, v) :: E => if x == y then Some v else get x E
    end.

  Definition binds x v E : Prop := get x E = Some v.

  Definition no_binds x E : Prop := get x E = None.

  (** The bound atoms of [E], in order. *)
  Definition dom (E : list (atom * A)) : list atom := List.map fst E.

End Environment.
