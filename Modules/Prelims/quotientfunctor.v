Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.UnicodeNotations.


Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.Epis.
Require Import UniMath.CategoryTheory.category_hset.

(* Needed only for the definition of HSET_PreCategory *)
Require Import Modules.Prelims.setscomplements.


Local Notation "# F" := (functor_on_morphisms F)(at level 3).
Local Notation "F ⟶ G" := (nat_trans F G) (at level 39).
Local Notation "G □ F" := (functor_composite F G) (at level 35).
Local Notation "F ;;; G" := (nat_trans_comp _ _ _ F G) (at level 35).

Require Import TypeTheory.Auxiliary.Auxiliary.

(* adds a new equation z = ?x *)
Ltac neweq z :=
  let t := type of z in
  let x := fresh in
  evar (x:t); cut (z=x); subst x; cycle 1.

(* adds a new equation z = ?x and replace z with ?x in the current goal *)
Ltac neweqsubst z :=
  let h := fresh in
  neweq z; [subst z| intro h; rewrite h; clear h z].


(* Require Import Largecat.mylibtactics. *)

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

  Local Notation C := hset_Precategory.
  Context { D:precategory}.
  Variable (R:functor D C).

  (* This is ~_X *)
  Variable (hequiv : Π (d:D),eqrel (pr1hSet (R d))).

  (* The relations satisfied by hequiv *)
  Hypothesis (congru: Π (x y:D) (f:D⟦ x,  y⟧), iscomprelrelfun (hequiv x) (hequiv y) (#R f)).

  (* Definition of the quotient functor *)
  Definition quot_functor_ob (d:D) := setquotinset (hequiv d).
  Definition quot_functor_mor (d d' : D) (f : D ⟦d, d'⟧)
    : C ⟦quot_functor_ob d, quot_functor_ob d' ⟧ :=
    fun (c:quot_functor_ob d) =>  setquotfun (hequiv d) (hequiv d') (#R f) (congru d d' f) c.

  Definition quot_functor_data : functor_data D C := tpair _ _ quot_functor_mor.


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

  Definition quot_functor  : functor D C := tpair _ _ is_functor_quot_functor_data.


  Definition proj_nat_trans_data : (Π x , C ⟦ R x, quot_functor  x ⟧) :=
    fun x a => setquotpr _ a.

  Lemma is_nat_trans_proj_nat_trans : is_nat_trans _ _ proj_nat_trans_data.
  Proof.
    red; intros; apply idpath.
  Qed.

  Definition proj_quot : (nat_trans R  quot_functor) := (_ ,, is_nat_trans_proj_nat_trans).

  Lemma is_epi_proj_quot : isEpi (C:=functor_precategory _ _ (homset_property _) ) proj_quot.
  Proof.
    apply is_nat_trans_epi_from_pointwise_epis.
    intro a.
    cbn.
    unfold proj_nat_trans_data.
    intros z f g eqfg.
    apply funextfun.
    intro x.
    eapply surjectionisepitosets.
    apply  issurjsetquotpr.
    apply setproperty.
    intro u.
    apply toforallpaths in eqfg.
    apply eqfg.
  Qed.
End QuotientFunctor.