Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.UnicodeNotations.


Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.Epis.
Require Import UniMath.CategoryTheory.category_hset.

Definition List : UU.
  use total2.
  exact nat.
  intro n.
  induction n.
  - exact unit.
    - exact (nat × IHn).
Defined.

Definition nil : List := (0 ,, tt).

Definition cons (a:nat) (l:List): List.
  use tpair.
  exact (S (pr1 l)).
  cbn.
  use tpair.
  exact a.
  exact (pr2 l).
  Defined.

(** The induction principle for lists defined using foldr *)
Section list_induction.

Variables (P : List -> UU) (PhSet : Π l, isaset (P l)).
Variables (P0 : P nil)
          (Pc : Π a l, P l -> P (cons a l)).

Lemma final (l:List) : P l.
  destruct l as [n l].
  induction n.
  - destruct l.
  exact P0.
  - destruct l as [a l].
    assert (Pc':= Pc a (n,,l)).
    apply Pc'.
    apply IHn.
Defined.

End list_induction.

Definition length (l:List) := final (fun _ => nat) 0 (fun _ _ n => S n) l.

Eval compute in (length nil).