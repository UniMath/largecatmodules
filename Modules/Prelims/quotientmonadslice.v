(* =================================================================================== *)
(** ** Quotient of a monad by some elements of its coslice category                    *)
(* =================================================================================== *)

(* ----------------------------------------------------------------------------------- *)
(** Description: This module construct the quotient of a monad with respect
    some elements of its coslice category (see pdf sent to Benedikt)
    More precisely: let (f_j : R --> d_j) for j in a set J be a collection of
    morphisms of monads. We quotient R(X) by the following relation: x ~ y
    if and only if for all j, f_j(x) = f_j(y) *)
(* ----------------------------------------------------------------------------------- *)

Require Import UniMath.Foundations.PartD.

Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.SetValuedFunctors.
Require Import UniMath.CategoryTheory.HorizontalComposition.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.categories.category_hset.
Require Import UniMath.CategoryTheory.categories.category_hset_structures.

Require Import UniMath.CategoryTheory.Categories.

Require Import UniMath.Foundations.Sets.
Require Import UniMath.CategoryTheory.Epis.
Require Import UniMath.CategoryTheory.EpiFacts.

Require Import Modules.Prelims.lib.
Require Import Modules.Prelims.quotientmonad.

Local Notation "α ∙∙ β" := (horcomp β α) (at level 20).
Local Notation "'SET'" := hset_category.
Local Notation "F ;;; G" := (nat_trans_comp _ _ _ F G) (at level 35).

Open Scope cat.
    

Section QuotientMonad.

(** the axiom of choice is needed to prove the the horizontal composition of the
    canonical projection with itself is epimorphic *)

Variable (choice : AxiomOfChoice.AxiomOfChoice_surj).


Context {R : Monad SET} {J : UU} (d : J -> Monad SET)
          (ff : ∏ (j : J), Monad_Mor R (d j)).

(** Define two elements in R to be related if they are mapped
    to the same element by any morphism f of our collection of the slice category
*)
Definition equivc {X : SET} (x y : ( R X : hSet)) : UU
  := ∏ (j : J) , (ff j) X x = (ff j) X y.

(** [equivc] is a proposition
*)

Lemma isaprop_equivc_xy (c : SET) x y : isaprop (equivc (X:=c) x y).
Proof.
  apply impred_isaprop; intro S.
  apply setproperty.
Qed.

Definition equivc_xy_prop (X : SET) x y : hProp :=
  equivc (X:=X) x y ,, isaprop_equivc_xy X x y.

Definition hrel_equivc (X : SET) : hrel (R X : hSet)
  := fun x y => equivc_xy_prop X x y.

(** [equivc] is an equivalence relation *)

Lemma iseqrel_equivc (X : SET) : iseqrel (hrel_equivc X).
Proof.
  unfold hrel_equivc, equivc_xy_prop, equivc; simpl;
  repeat split.
  - intros x y z. cbn.
    intros h1 h2 S .
    rewrite h1,h2.
    apply idpath.
  - intros x y; cbn.
    intros h S .
    symmetry.
    apply h.
Qed.



(** [equivc] is an equivalence relation *)
Definition eqrel_equivc (X : SET) : eqrel _ := _ ,, iseqrel_equivc X.

(** For any f : X -> Y, #R f is compatible with previous equivalence relation *)
Lemma congr_equivc (X Y : SET) (f : SET ⟦X , Y⟧)
  : iscomprelrelfun (eqrel_equivc X) (eqrel_equivc Y) (# ( R) f).
Proof.
  intros z z' eqz S .
  assert (hg := nat_trans_ax (ff S) X Y f).
  apply toforallpaths in hg.
  etrans; [apply hg|].
  apply pathsinv0.
  etrans;[apply hg|].
  cbn.
  apply maponpaths. (* remove #S f *)
  cbn in eqz.
  apply pathsinv0, eqz.
Qed.

Let R' := R'  congr_equivc.
Let projR := projR  congr_equivc.
(** Two elements that are equal in the quotient 
    get mapped to equal elements by any morphism 
    of actions
*)
Lemma compat_slice (j : J) ( m := ff j)
  : ∏ (X : SET) (x y : (pr1 R X : hSet)),
    projR X x = projR X y → m X x =  m X y.
Proof.
  intros X x y eqpr.
  apply eq_projR_rel in eqpr.
  use eqpr.
Qed.

(** The induced natural transformation out of the quotient *)
Definition u (j : J) (S := d j) : nat_trans (pr1 R') S.
Proof.
  apply (quotientmonad.u congr_equivc _ (ff j)).
  apply compat_slice.
Defined.

(** The induced natural transformation makes a triangle commute *)
Lemma u_def (j : J) (m := ff j) : ∏ x,  m x = projR x · u j x.
Proof.
  apply (quotientmonad.u_def).
Qed.

(** We show that the relation induced by a morphism of models
    satisfies the conditions necessary to induce a quotient monad 
*)
Corollary compat_μ_slice : compat_μ_projR_def congr_equivc.
Proof.
  intros X x y hxy.
  apply rel_eq_projR.
  intros j .
  rewrite comp_cat_comp.
  rewrite comp_cat_comp.
  apply pathsinv0.
  eapply changef_path.
  - symmetry.
    etrans; [ apply (Monad_Mor_μ (ff j)) |].
    etrans.
    { apply (cancel_postcomposition (C:=SET)).
      etrans.
      { apply cancel_postcomposition.
        apply u_def. }
      apply cancel_precomposition.
      apply maponpaths.
      apply u_def .
    }
    etrans.
    { apply (cancel_postcomposition (C:=SET)).
      etrans.
      { symmetry.
        use assoc.
      }
      apply cancel_precomposition.
      etrans.
      { symmetry. apply nat_trans_ax. }
      apply cancel_postcomposition.
      use functor_comp.
    }
    repeat rewrite assoc.
    reflexivity.
  - cbn.
    do 3 apply maponpaths.
    exact (!hxy).
Qed.
  
(** Short notations for the quotient monad and the projection as a monad morphism *)
Definition R'_monad : Monad SET := R'_monad choice congr_equivc compat_μ_slice.
Definition projR_monad
  : Monad_Mor R R'_monad
  := projR_monad choice congr_equivc compat_μ_slice.

(** Short name for the monad morphism out of the quotient *)
Definition u_monad (j : J)  (m := ff j)
  : Monad_Mor R'_monad (d j)
  := quotientmonad.u_monad choice compat_μ_slice (S:= d j) m (compat_slice j).

End QuotientMonad.
  
Arguments projR : simpl never.
Arguments R' : simpl never.