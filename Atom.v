(** Support for atoms, i.e., objects with decidable equality.  We
    provide here the ability to generate an atom fresh for any finite
    collection, i.e., the lemma [atom_fresh_for_set].

    Original authors: Arthur Chargueraud and Brian Aydemir.
*)

From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Peano_dec.

(* ********************************************************************** *)
(** * Definition *)

(** Atoms are structureless objects such that we can always generate
    one fresh from a finite collection.  Equality on atoms is [eq] and
    decidable.  We use Coq's module system to make abstract the
    implementation of atoms.  The [Export AtomImpl] line below allows
    us to refer to the type [atom] and its properties without having
    to qualify everything with "[AtomImpl.]". *)

Module Type ATOM.

  Parameter atom : Set.

  Parameter atom_fresh_for_list :
    forall (xs : list atom), {x : atom | ~ List.In x xs}.

  Parameter eq_atom_dec : forall x y : atom, {x = y} + {x <> y}.

End ATOM.

(** The implementation of the above interface is hidden for
    documentation purposes. *)

Module AtomImpl : ATOM.

  (* begin hide *)

  Definition atom := nat.

  Lemma max_lt_r : forall x y z,
    x <= z -> x <= max y z.
  Proof.
    intros. lia.
  Qed.

  Lemma nat_list_max : forall (xs : list nat),
    { n : nat | forall x, In x xs -> x <= n }.
  Proof.
    induction xs as [ | x xs [y H] ].
    (* case: nil *)
    exists 0. inversion 1.
    (* case: cons x xs *)
    exists (max x y). intros z J. simpl in J. destruct J as [K | K].
      subst. apply Nat.le_max_l.
      apply max_lt_r. auto.
  Qed.

  Lemma atom_fresh_for_list :
    forall (xs : list nat), { n : nat | ~ List.In n xs }.
  Proof.
    intros xs. destruct (nat_list_max xs) as [x H].
    exists (S x). intros J. specialize (H (S x) J).
    lia.
  Qed.

  Definition eq_atom_dec := Peano_dec.eq_nat_dec.

  (* end hide *)

End AtomImpl.

Export AtomImpl.

