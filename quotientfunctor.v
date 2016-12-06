Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.UnicodeNotations.


Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.Epis.
Require Import UniMath.CategoryTheory.category_hset.

Definition hset_Precategory : Precategory := (hset_precategory ,, has_homsets_HSET).

Local Notation "# F" := (functor_on_morphisms F)(at level 3).
Local Notation "F ⟶ G" := (nat_trans F G) (at level 39).
Local Notation "G □ F" := (functor_composite F G) (at level 35).
Local Notation "F ;;; G" := (nat_trans_comp _ _ _ F G) (at level 35).


(* adds a new equation z = ?x *)
Ltac neweq z :=
  let t := type of z in
  let x := fresh in
  evar (x:t); cut (z=x); subst x; cycle 1.

(* adds a new equation z = ?x and replace z with ?x in the current goal *)
Ltac neweqsubst z :=
  let h := fresh in
  neweq z; [subst z| intro h; rewrite h; clear h z].


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

      apply funextsec.
      intro c.
      simpl.
      unfold quot_functor_mor;simpl.
      unfold setquotfun; simpl.
      match goal with | |-  (setquotuniv _ _  ?x _ _) = _ => pose (z := x)  end.
      neweq z.
      unfold z.
      etrans.
      apply funextsec.
      ZUT...
      apply maponpaths.
       (functor_id R a).
      intro hz.
      clearbody z.

      unfold setquotfun ;simpl.
      simpl.

      simpl.
      unfold identity at 2.
      simpl.

      destruct hz.
      unfold z.

      pattern c.
      match goal with |- ?P c => set (P':=P) end.

      apply (setquotunivprop _ P').
      apply funextsec.
      apply setquotunivcomm.

      (* rewrite hz ne marche pas *)
      clear; admit.
      clear; admit.
    - intros d d' c f g; simpl.
      apply funextsec.
      intros c'; unfold quot_functor_mor; simpl.
      symmetry.
      etrans.
      unfold compose; simpl.
      reflexivity.
      unfold setquotfun ; simpl.
      TODO
  Admitted.

End QuotientFunctor.