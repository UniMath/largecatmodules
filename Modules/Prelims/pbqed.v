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

  Context {D:precategory}.

  Variable (R:functor D HSET).

  (* This is ~_X *)
  Variable (hequiv : Π (d:D),eqrel (pr1hSet (R d))).

  (* The relations satisfied by hequiv *)
  Hypothesis (congru: Π (x y:D) (f:D⟦ x,  y⟧), iscomprelrelfun (hequiv x) (hequiv y) (#R f)).

  Section Def.
    Hypothesis(custom_isasetsetquot :Π (X : UU) (R : hrel X), isaset (setquot R)).
    (* Definition of the quotient functor *)
    Definition quot_functor_ob (d:D) :hSet. (* := setquotinset (hequiv d). *)
    Proof.      
      mkpair.
      apply (setquot (hequiv d)).
      apply custom_isasetsetquot.
    Defined.
    Definition quot_functor_mor (d d' : D) (f : D ⟦d, d'⟧)
      : HSET ⟦quot_functor_ob d, quot_functor_ob d' ⟧ :=
      fun (c:quot_functor_ob d) =>  setquotfun (hequiv d) (hequiv d') (#R f) (congru d d' f) c.

    Definition quot_functor_data : functor_data D HSET := tpair _ _ quot_functor_mor.


    Lemma is_functor_quot_functor_data : is_functor quot_functor_data.
    Proof.
      split.
      - intros a; simpl.
        apply funextfun.
        intro c.
        apply (surjectionisepitosets (setquotpr _));
          [now apply issurjsetquotpr | apply isasetsetquot|].
        intro x; cbn.
        now rewrite (functor_id R).
      - intros a b c f g; simpl.
        apply funextfun; intro x.
        apply (surjectionisepitosets (setquotpr _));
          [now apply issurjsetquotpr | apply isasetsetquot|].
        intro y; cbn.        
        now rewrite (functor_comp R).
    Qed.

    Definition quot_functor  : functor D HSET := tpair _ _ is_functor_quot_functor_data.

    Definition proj_nat_trans_data : (Π x , HSET ⟦ R x, quot_functor  x ⟧) :=
      fun x a => setquotpr _ a.

    Lemma is_nat_trans_proj_nat_trans : is_nat_trans _ _ proj_nat_trans_data.
    Proof.
      red; intros; apply idpath.
    Qed.

    Definition proj_quot : (nat_trans R  quot_functor) := (_ ,, is_nat_trans_proj_nat_trans).

  
  End Def.



End QuotientFunctor.


Section QedVsDefined.

  Variable (R:functor HSET HSET).
  Variable (hequiv : Π (d:HSET),eqrel (pr1hSet (R d))).
  Hypothesis (congru: Π (x y:HSET) (f:HSET⟦ x,  y⟧), iscomprelrelfun (hequiv x) (hequiv y) (#R f)).

  Definition isasetsetquot_def := @isasetsetquot.
  
  Lemma isasetsetquot_qed :Π (X : UU) (R : hrel X), isaset (setquot R).
    exact @isasetsetquot.
  Qed.

  Definition R'_def : functor _ _ := quot_functor R hequiv congru isasetsetquot_def.
  Definition R'_qed : functor _ _ := quot_functor R hequiv congru isasetsetquot_qed.

  Lemma myadmit (A:UU) : A.
  Admitted.

  Definition R'_Monad_def : Monad_data HSET := ((R'_def ,, myadmit _) ,, myadmit _).
  Definition R'_Monad_qed : Monad_data HSET := ((R'_qed ,, myadmit _) ,, myadmit _).

  Lemma R'_Monad_laws_qed : Monad_laws R'_Monad_qed.
  Proof.
    repeat split; apply myadmit.
  Qed.

  Opaque isasetsetquot_def.
  Opaque isasetsetquot.

  Lemma R'_Monad_laws_def : Monad_laws R'_Monad_def.
  Proof.
    repeat split; apply myadmit.
  Qed.
  
End QedVsDefined.




  