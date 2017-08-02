
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.

Open Scope cat.
Set Automatic Introduction.

(* Definition des fibrations *)

Section fib.
  Context {C : category}.
  Definition is_fib (F : C -> category) (Ff : ∏ {x y} (f : C ⟦x, y⟧), functor (F x) (F y)) :=
    ∑ l : (∏ x, iso (C:= [_, _]) (Ff (identity x)) (functor_identity _)),
          ∑ α : (∏ x y z (f : C⟦x,y⟧) (g : C⟦y,z⟧), iso (C:=[_,_]) (Ff (f · g)) ((Ff f) ∙ Ff g)), True.
  (* plus d'autres cohérences ?? *)
  Definition fibration := 
    ∑ (F : C -> category) (Ff : ∏ x y (f : C ⟦x, y⟧), functor (F x) (F y)).
