(** 
If pushouts are computed pointwise, then a transfo nat which is an epi is
 pointwise an epi

Example of use of eq_diag

However a definition eq_cocone would simplify the proof

*)


Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.whiskering.

Require Import UniMath.CategoryTheory.Epis.

Require Import UniMath.CategoryTheory.Monads.
Require Import UniMath.CategoryTheory.RModules. 


Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Auxiliary.UnicodeNotations.
Require Import TypeTheory.Displayed_Cats.Auxiliary.
Require Import TypeTheory.Displayed_Cats.Core.
Require Import TypeTheory.Displayed_Cats.Constructions.
Require Import TypeTheory.Displayed_Cats.Fibrations.

Require Import UniMath.CategoryTheory.HorizontalComposition.

Require Import UniMath.CategoryTheory.category_hset.
Require Import UniMath.CategoryTheory.category_hset_structures.
Require Import UniMath.CategoryTheory.limits.graphs.pullbacks.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.limits.graphs.pushouts.
Require Import UniMath.CategoryTheory.limits.graphs.coequalizers.
Require Import UniMath.CategoryTheory.limits.pushouts.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.kernels.
Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import UniMath.CategoryTheory.limits.coequalizers.
Require Import UniMath.CategoryTheory.limits.EffectiveEpis.

Require Import Modules.Prelims.eqdiag.


Set Automatic Introduction.

Section PointwiseEpi.

  Definition functor_Precategory (C:precategory) (D:Precategory) : Precategory :=
    (functor_precategory C D (homset_property D),,
                         functor_category_has_homsets _ _ _).

  Context { C :precategory} {D:Precategory} .

  Local Notation CD := (functor_precategory C D (homset_property D)).
  Local Notation CD_Pre := (functor_Precategory C D).
  
  Lemma eq_diag_pushout {X Y Z :CD} {a:CD  ⟦ X, Y ⟧} {b:CD ⟦ X, Z⟧} x  :
    eq_diag 
            (diagram_pointwise (homset_property D)
                               (pushout_diagram CD a b) x)
            (pushout_diagram D (pr1 a x) (pr1 b x)).
  Proof.
      use tpair.
      use StandardFiniteSets.three_rec_dep;  apply idpath.
      use StandardFiniteSets.three_rec_dep;  use StandardFiniteSets.three_rec_dep; 
         exact (Empty_set_rect _ )||exact (fun _ => idpath _).
  Defined.    
    
  Import graphs.pushouts.

  
  Lemma Pushouts_pw_epi (colimD : Pushouts D) (A B : CD) (a:CD⟦ A,B⟧)
        (epia:isEpi a) : Π (x:C), isEpi (pr1 a x).
  Proof.    
    intro  x; simpl.
    apply (epi_to_pushout (C:=CD_Pre)) in epia.
    apply pushout_to_epi.
    simpl.
    apply equiv_isPushout1 in epia; [| apply homset_property].
    apply equiv_isPushout2; [ apply homset_property|].

    red in epia.
    red.
    eapply (isColimFunctor_is_pointwise_Colim
              (homset_property _)) in epia; cycle 1.

    {
      intro c.
      eapply eq_diag_liftcolimcocone.
      - apply sym_eq_diag.
        apply eq_diag_pushout.
      - apply colimD.
    }
    
    match goal with  h:isColimCocone ?po1 _ _ |- isColimCocone ?po2 _ _ =>
                     set (pd := po1) in h; set(pdw := po2) end.

    (* I am forced to re-build the cocone, unless I define a specific 
equality on cocone similar to eqdiag for diagrams, and use it *)
    assert(h:= (eq_diag_iscolimcocone _ (eq_diag_pushout x) epia)).

    intros c cc.
    specialize (h c cc).
    apply (unique_exists (pr1 (iscontrpr1 h))).
    - assert (hepi := pr2 (iscontrpr1 h)); simpl in hepi.
      intro v.
      generalize v (hepi v).
      use StandardFiniteSets.three_rec_dep; intro h'; apply h'.
    - intros y.
      apply impred_isaprop.
      intros t.
      apply homset_property.
    - assert (hepi2 := eq_exists_unique _ _ h); simpl in hepi2.
      intros y hv; specialize (hepi2 y).
      apply hepi2.
      intros v; specialize (hv v).
      revert v hv.
      use StandardFiniteSets.three_rec_dep;intro h'; apply h'.
  Qed.

End PointwiseEpi.

