Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.


Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Auxiliary.UnicodeNotations.
Require Import TypeTheory.Displayed_Cats.Auxiliary.
Require Import TypeTheory.Displayed_Cats.Core.
Require Import TypeTheory.Displayed_Cats.Constructions.

Set Automatic Introduction.

(**
 G,G'---> D
    /     |
   /      |
  /       V
C' -----> C
     F


G x : D (F x)
G' x : D (F x)
*)

Notation "# F" := (section_disp_on_morphisms F)
  (at level 3) : disp_lifting_scope.
Delimit Scope disp_lifting_scope with lift.
Definition is_nat_trans_lifting{C C' : category} {D : disp_cat C} {F : C' ⟶ C}
           {G G' : functor_lifting D F} (α : ∏ x : C', G x -->[identity x] G' x ) :=
  ∏ x x' (f : C' ⟦x, x'⟧),
    transportf _ (id_right _) ((# G f)%lift ;; α x')%mor_disp = transportf _ (id_left _) (α x ;; (# G' f)%lift)%mor_disp.

Definition nat_trans_lifting {C C' : category} {D : disp_cat C} {F : C' ⟶ C}
           (G G' : functor_lifting D F) := ∑ α, is_nat_trans_lifting (G := G) (G' := G') α.

Definition nat_trans_lifting_data {C C' : category} {D : disp_cat C} {F : C' ⟶ C}
           (G G' : functor_lifting D F) (α : nat_trans_lifting G G')  :
   ∏ x : C', G x -->[identity x] G' x  := pr1 α.

Coercion nat_trans_lifting_data : nat_trans_lifting >-> Funclass.

Definition compose_nat_trans_lifting {C C' : category} {D : disp_cat C} {F : C' ⟶ C}
           (G G' G'' : functor_lifting D F) (α : nat_trans_lifting G G') (α' : nat_trans_lifting G' G'')  : nat_trans_lifting G G''.
  mkpair.
  (* je vais avoir besoin d'un transport pour dire que identity x ;; identity x = identity x *)


Section NatTrans.
  Context {C C' : category} (D : disp_cat C) (F : C' ⟶ C). 

