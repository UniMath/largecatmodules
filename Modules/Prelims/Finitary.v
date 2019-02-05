(** * Finitary functors

*)
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.FunctorCategory.

Require Import UniMath.CategoryTheory.Subcategory.Core.
Require Import UniMath.CategoryTheory.Subcategory.Full.

(* Require Import UniMath.CategoryTheory.CommaCategories. *)
Require Import UniMath.CategoryTheory.slicecat.
Require Import UniMath.CategoryTheory.Epis.
Require Import UniMath.CategoryTheory.EpiFacts.

Require Import UniMath.CategoryTheory.categories.HSET.All.
(* Require Import UniMath.CategoryTheory.categories.FinSet. *)
Require Import UniMath.Combinatorics.FiniteSets.



Open Scope cat.

Definition colim_on_nat {C D : precategory}{F G : C ⟶ D} (p : F ⟹ G){g : graph}{d : diagram g C}
                  (cF : ColimCocone (mapdiagram F d))
                  (cG : ColimCocone (mapdiagram G d))
  :
    D ⟦ colim cF , colim cG ⟧
      :=
        colimOfArrows cF cG
                      (λ u : vertex g, p (dob d u))
                      (λ (u v : vertex g) (e : edge u v), nat_trans_ax p (dob d u) (dob d v) (dmor d e)).

Definition colimcompare
   {C : precategory}{D : precategory}(F : C ⟶ D){g : graph}{d : diagram g C}
   (cd : ColimCocone d)
   (cFd : ColimCocone (mapdiagram F d))
  : D ⟦ colim cFd ,  F (colim cd) ⟧ :=
    colimArrow _ _  (mapcocone F _ (colimCocone cd)).


(**

colim (F ∘ J) --> F (colim J)
   |                |
   |                |
   |                |
   |                |
   V                V
 colim (G ∘ J) --> G (colim J)
*)
Lemma colim_on_nat_is_nat {C D : precategory}{F G : C ⟶ D} (p : F ⟹ G){g : graph}{d : diagram g C}
                  (cd : ColimCocone d)
                  (cF : ColimCocone (mapdiagram F d))
                  (cG : ColimCocone (mapdiagram G d)) :
        colim_on_nat p cF cG · colimcompare G  cd cG
    = (colimcompare F  cd cF) · p (colim cd).
Proof.
  etrans; [apply precompWithColimOfArrows|].
  apply pathsinv0.
  apply colimArrowUnique.
  intro u.
  cbn.
  etrans.
  {
    etrans;[apply assoc|].
    apply cancel_postcomposition.
    unfold colimcompare.
    apply ( colimArrowCommutes cF (F (colim cd))).
  }
  apply nat_trans_ax.
Qed.

Local Notation "'SET' / X" :=(slice_precat HSET X has_homsets_HSET) (at level 3).

Definition is_finite_subob (X : hSet) (fX : SET / X) : hProp :=
  ((isfinite (pr1hSet (slicecat_ob_object _  _ fX))) ∧
    (isInjectiveFunction (slicecat_ob_morphism _ _ fX))).

Definition FinSubsets_precategory (X : hSet) : precategory :=
  full_sub_precategory (C := SET / X) (is_finite_subob X).

Definition forget_FinSubsets (X : hSet) : FinSubsets_precategory X ⟶ HSET :=
  (sub_precategory_inclusion _ _ ∙ slicecat_to_cat _ _).

Local Notation coSET d := (ColimsHSET_of_shape _ d).

Definition diag_subobj (X : hSet) :=
  (diagram_from_functor (FinSubsets_precategory X) HSET (forget_FinSubsets X)).

Definition colimcompare_fin (F : HSET ⟶ HSET) (X : hSet) : _ :=
  (colimcompare (C := HSET)(D := HSET) F
                            (coSET (diag_subobj X))
                            (coSET _)
              ).

Definition colimcompare_fin_injempty (F : HSET ⟶ HSET)  : isweq (colimcompare_fin F emptyHSET).
Proof.
Admitted.

(** The hard part *)
(* non empty sets *)
Definition colimcompare_fin_inj (F : HSET ⟶ HSET) (X : hSet) : ∥ X ∥ -> isInjective (colimcompare_fin F X).
Proof.
  apply factor_through_squash; [ apply isaprop_isInjective|].
  intro x.
Admitted.

Definition is_finitary (F : HSET ⟶ HSET) : UU :=
  ∏ X , isweq (colimcompare_fin F X).



Definition fin_nat_alt_eq
           {F G : HSET ⟶ HSET} (p : F ⟹ G)
            (X : hSet)
           (* (w := weqpair _ (finF X)) *)
  :
        colim_on_nat p (coSET _) (coSET _) ·
      colimcompare_fin G X
  = (colimcompare_fin F X) · p _ := colim_on_nat_is_nat _ _ _ _.

(** This is true of any colimit shape *)
Lemma epi_preserves_finepi {F G : HSET ⟶ HSET}
      {p : F ⟹ G}(epip : ∏ Y, isEpi (p Y))
      (finF : is_finitary F) (X : hSet) : isEpi (colimcompare_fin G X).
Proof.
  eapply isEpi_precomp.
  apply (transportb (isEpi (C := HSET) (x := _) (y := _)) (fin_nat_alt_eq p  X)) .
  apply isEpi_comp.
  - apply EpisAreSurjective_HSET.
    apply issurjectiveweq.
    apply finF.
  - apply epip.
Qed.

(* isweqinclandsurj *)
Lemma epi_preserves_finitary {F G : HSET ⟶ HSET}
      (p : F ⟹ G)(finF : is_finitary F) : is_finitary G.
Proof.
  (* this is a consequence of epi_preserves_finepi and colimcompare_fin_inj* *)
  