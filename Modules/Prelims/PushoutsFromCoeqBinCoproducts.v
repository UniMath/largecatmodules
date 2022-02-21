(** * Pushouts from coequalizers and bincoproducts

The pushout
<<
A ---> B
|
|
|
V
C
>>
is defined as the coequalizer of
<<
A --> B + C
>>


 *)
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.limits.pushouts.
Require Import UniMath.CategoryTheory.limits.initial.


Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.limits.graphs.equalizers.
Require Import UniMath.CategoryTheory.limits.graphs.coequalizers.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.pushouts.

Local Open Scope cat.
Section d.
  Context {C : category} {g : graph} 
          (bc : BinCoproducts C)
          (coeq : Coequalizers C).

  Definition pushouts_from_coeq_bincoprod : Pushouts C.
    intros a b c u v.
    use make_Pushout.
    - unshelve eapply CoequalizerObject; revgoals.
      + red in coeq.
        specialize (coeq a (bc b c)).
        apply coeq.
      + eapply compose; [exact v|apply BinCoproductIn2].
      + eapply compose; [exact u|apply BinCoproductIn1].
    - cbn.
      eapply compose;[apply BinCoproductIn1|apply CoequalizerArrow].
    - cbn.
      eapply compose;[apply BinCoproductIn2|apply CoequalizerArrow].
    - cbn.
      repeat rewrite assoc.
      apply CoequalizerArrowEq.
    - intros e h k eq.
      cbn.
      use unique_exists.
      + use CoequalizerOut.
        * apply BinCoproductArrow; assumption.
        * do 2 rewrite <- assoc.
          rewrite BinCoproductIn1Commutes,BinCoproductIn2Commutes.
          exact eq.
      + split.
        * etrans.
          { etrans;[apply pathsinv0,assoc|].
            apply cancel_precomposition.
            apply CoequalizerArrowComm.
          }
          apply BinCoproductIn1Commutes.
        * etrans.
          { etrans;[apply pathsinv0,assoc|].
            apply cancel_precomposition.
            apply CoequalizerArrowComm.
          }
          apply BinCoproductIn2Commutes.
      + cbn -[isaprop].
        intros.
        apply isapropdirprod; apply homset_property.
      + cbn.
        intros w eq'.
        apply CoequalizerOutUnique.
        apply BinCoproductArrowUnique.
        * etrans;[apply assoc|exact (pr1 eq')].
        * etrans;[apply assoc|exact (pr2 eq')].
  Defined.

End d.
