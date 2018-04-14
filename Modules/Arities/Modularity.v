(** * Modularity for arities


Suppose we have the following pushout diagram in the category of arities:
<<<
                f1
       a0 ------------>  a1 
       |                 |
       |                 |
   f2  |                 | g2
       |                 |
       |                 |
       |                 |
       V                 V
       a2 ------------>  a' 
                 g1 
>>>

such that a1, a2 and a' are representable and above this
pushout there is a commuting square in the large category of representations:
<<<
                ff1
       R0 ------------>  R1 
       |                 |
       |                 |
  ff2  |                 | gg2
       |                 |
       |                 |
       |                 |
       V                 V
       R2 ------------>  R' 
                 gg1 
>>>

such that R1, R2, R' are the initial representations of respectively a1, a2 and a'.

Then the previous diagram is a pushout in the large category of representations [pushout_in_big_rep].


 *)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.limits.pushouts.
Require Import UniMath.CategoryTheory.limits.initial.

Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.

Require Import Modules.Arities.aritiesalt.
Require Import Modules.Prelims.FibrationInitialPushout.

Section pr.
  Context {C : category} (dC : disp_cat C).

  Local Notation TT := (disp_mor_to_total_mor (rep_disp C)).
  Context
          {a0 a1 a2 a' : @arity_category C}
          {f1 : arity_category ⟦ a0, a1 ⟧}{f2 : arity_category ⟦ a0, a2 ⟧}
          {g1 : arity_category ⟦ a1, a' ⟧}{g2 : arity_category ⟦ a2, a' ⟧}

          {R0 : rep_disp _  a0} {R1 : rep_disp _  a1} {R2 : rep_disp _  a2} {R' : rep_disp _ a'}
          (ff1 : R0 -->[f1] R1)(ff2 : R0 -->[f2] R2)
          (gg1 : R1 -->[g1] R')(gg2 : R2 -->[g2] R')

          (repr_R1 : isInitial  (fiber_category _ _) R1)
          (repr_R2 : isInitial  (fiber_category _ _) R2)
          (repr_R' : isInitial  (fiber_category _ _) R') .

           (** Require commuting diagram in the big representation category *)
  Context {eq_ff : TT ff1 · TT gg1 = TT ff2 · TT gg2}.

  Let heq :  f1 · g1 = f2 · g2 := base_paths _ _ eq_ff.

  Context (poC : isPushout f1 f2 g1 g2 heq).

  Let PO := mk_Pushout _ _ _ _ _ _ poC.


  Definition pushout_in_big_rep : isPushout (TT ff1)(TT ff2)(TT gg1)(TT gg2) eq_ff :=
    pushout_total (rep_disp C) (rep_cleaving C) ff1 ff2 gg1 gg2 repr_R1 repr_R2 repr_R' poC.


End pr.