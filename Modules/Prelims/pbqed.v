Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.UnicodeNotations.


Require Import UniMath.CategoryTheory.Epis.
Require Import UniMath.CategoryTheory.category_hset.
Require Import UniMath.CategoryTheory.Monads.


Local Notation "# F" := (functor_on_morphisms F)(at level 3).
Local Notation "F ⟶ G" := (nat_trans F G) (at level 39).
Local Notation "G □ F" := (functor_composite F G) (at level 35).
Local Notation "F ;;; G" := (nat_trans_comp _ _ _ F G) (at level 35).

Lemma myadmit (A:UU) : A.
Admitted.


(**   We show some properties about quotient functors .

Let C be a category
Let R be a functor from C to Set.

Let X be an object of C
Let ~_X a family of equivalence relations on RX satisfying
if x ~_X y and f : X -> Y, then f(x) ~_Y f(y).

(in other words, ~ is a functor RxR -> hProp )

Then we can define R' := R/~ as a functor which to any X associates R'X := RX / ~_X

 *)
Section QuotientFunctor.


  Variable (R:functor HSET HSET).
  (* This is ~_X *)
  Variable (hequiv : Π (d:hSet),eqrel (pr1hSet (R d))).

  
  Section Def.
    
    Hypothesis(custom_isasetsetquot :Π (X : UU) (R : hrel X), isaset (setquot R)).
    
    (* Definition of the quotient functor *)
    Definition quot_functor_ob (d:hSet) :hSet. 
    Proof.      
      mkpair.
      apply (setquot (hequiv d)).
      apply custom_isasetsetquot.
    Defined.
    Definition quot_functor_mor (d d' : hSet) (f : HSET ⟦d, d'⟧)
      : HSET ⟦quot_functor_ob d, quot_functor_ob d' ⟧ := myadmit _.

    Definition quot_functor_data : functor_data HSET HSET := tpair _ _ quot_functor_mor.


    Lemma is_functor_quot_functor_data : is_functor quot_functor_data.
    Proof.
      apply myadmit.
    Qed.

    Definition quot_functor  : functor HSET HSET :=
      tpair _ _
            is_functor_quot_functor_data.

 
  End Def.

  Section QedVsDefined.

    (* Transparent version *)
    Definition isasetsetquot_def := @isasetsetquot.

    (* opacified *)
    Opaque isasetsetquot_def.
    Opaque isasetsetquot.


    (* Opaque version *)
    Lemma isasetsetquot_qed :Π (X : UU) (R : hrel X), isaset (setquot R).
      exact @isasetsetquot.
    Qed.

    Definition R'_def : functor _ _ := quot_functor isasetsetquot_def.
    Definition R'_qed : functor _ _ := quot_functor isasetsetquot_qed.

    Definition R'_Monad_def : Monad_data HSET := ((R'_def ,, myadmit _) ,, myadmit _).
    Definition R'_Monad_qed : Monad_data HSET := ((R'_qed ,, myadmit _) ,, myadmit _).

    Lemma R'_Monad_laws_qed : Monad_laws R'_Monad_qed.
    Proof.
      repeat split; apply myadmit.
      (* immediate *)
    Qed.

    Lemma R'_Monad_laws_def : Monad_laws R'_Monad_def.
    Proof.
      repeat split; apply myadmit.
      (* too long *)
    Qed.
    
  End QedVsDefined.


End QuotientFunctor.






  