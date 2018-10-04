(**
BinCoproducts from Coproduct on bool.
 *)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.Categories.


Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.limits.bincoproducts.



Open Scope cat.

(** the inverse of
 CoproductsBool: ∏ C : precategory, has_homsets C → BinCoproducts C → Coproducts bool C
*)
Definition BinCoproducts_from_CoproductsBool {C : category} (bc : Coproducts bool C) : BinCoproducts C.
  intros a b.
  set (CC := bc (fun x => if x then b else a)).
  use mk_BinCoproduct.
  - exact (CoproductObject _ _ CC).
  - apply (CoproductIn _ _ CC false) .
  - apply (CoproductIn _ _ CC true) .
  - use mk_isBinCoproduct;[apply homset_property|].
    intros c f g.
    use unique_exists; simpl.
    + apply CoproductArrow.
      induction i; assumption.
    + split.
      * use (CoproductInCommutes _ _ _ CC _ _ false).
      * use (CoproductInCommutes _ _ _ CC _ _ true).
    + intros h; apply isapropdirprod; apply homset_property.
    + (intros h [H1 H2]; apply CoproductArrowUnique; intro x; induction x); assumption.
Defined.