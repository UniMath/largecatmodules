Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.UnicodeNotations.


Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.graphs.binproducts.
Require Import Modules.Prelims.eqdiag.

Set Automatic Introduction.

Section ContreExempleBenedikt.


    Variables (C D : Precategory) (A B: functor C D) (x:C).
    Let CD := (functor_Precategory C D).

    Definition diag1 := diagram_pointwise (homset_property _) (binproduct_diagram CD A B) x.
    Definition diag2 := binproduct_diagram _ (A x) (B x).

    
    Lemma eq1 : diag1 = diag2.
    Proof.
      use total2_paths.
      - apply funextfun.
        intro y.
        now destruct y.
      - apply funextsec.
        intros v.
        apply funextsec.
        intro v'.
        apply funextsec.
        
        induction v ,v'; exact (Empty_set_rect _ ).
    Defined.

    Lemma eq2 : eq_diag diag1 diag2.
    Proof.
      use tpair.
      - now induction v.
      - intros v v'.
        induction v ,v'; exact (Empty_set_rect _ ).
    Defined.
        

    Definition transport_eq {C':precategory} {g:graph} {J J':diagram g C'} (e:J=J') c:
      cone J c -> cone J' c.
    Proof.
      intro hcone.
      use tpair.
      -
        intro v.
        induction e.
        apply (pr1 hcone).
      - abstract (induction e;        apply (pr2 hcone)).
    Defined.

    
    Variables (c:D) (c1 : cone diag1 c).

    Definition c2_impossible : cone diag2 c := transport_eq eq1 _ c1.
    Definition c2_facile : cone diag2 c := eq_diag_mkcone _ eq2  c1.

    Lemma facile : coneOut c2_facile true = coneOut c1 true.
      reflexivity.
    Qed.

    Lemma impossible : coneOut c2_impossible true = coneOut c1 true.
      reflexivity.
    Qed.

  End ContreExempleBenedikt.
