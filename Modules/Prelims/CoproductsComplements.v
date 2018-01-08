
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.ProductCategory.
Require Import UniMath.CategoryTheory.limits.coproducts.

Open Scope cat.

Section WEQ.

  Context {C : category} {I : UU} (cpC : Coproducts I C).
  Variable (a : I -> C).

  Definition from_Coproducts_weq c : (∏ i, C ⟦ a i , c ⟧) ≃ C ⟦ CoproductObject _ _ (cpC a) , c ⟧.
    use weqpair.
    - intro f.
      apply CoproductArrow.
      exact f.
    - intro y.
      unfold hfiber.
      use unique_exists.
      + intro i.
        eapply compose.
        * apply CoproductIn.
        * exact y.
      + cbn.
        apply pathsinv0.
        apply CoproductArrowEta.
      + intros h.
        apply (homset_property C).
      + cbn.
        intro y'.
        intro h.
        apply funextsec.
        intro i.
        etrans;[|apply cancel_precomposition;exact h].
        apply pathsinv0.
        apply CoproductInCommutes.
  Defined.
End WEQ.
  