(** * Modulsignature for signatures


Suppose we have the following pushout diagram in the category of signatures:
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

such that a0, a1, a2 and a' are representable with initial representations
R0, R1, R2 and R'. Then, above this pushout there is a pushout square in the
large category of representations:
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

Require Import Modules.Signatures.Signature.
Require Import Modules.Prelims.FibrationInitialPushout.


Section init.
  Context {C : category} (dC : disp_cat C).

  Local Notation TT := (disp_mor_to_total_mor (rep_disp C)).
  Context
          {a0 a1 a2 a' : @signature_category C}
          {f1 : signature_category ⟦ a0, a1 ⟧}{f2 : signature_category ⟦ a0, a2 ⟧}
          {g1 : signature_category ⟦ a1, a' ⟧}{g2 : signature_category ⟦ a2, a' ⟧}

          {R0 : rep_disp _  a0} {R1 : rep_disp _  a1} {R2 : rep_disp _  a2} {R' : rep_disp _ a'}
          (repr_R0 : isInitial  (fiber_category _ _) R0)  
          (repr_R1 : isInitial  (fiber_category _ _) R1)
          (repr_R2 : isInitial  (fiber_category _ _) R2)
          (repr_R' : isInitial  (fiber_category _ _) R') .

  Context  (heq :  f1 · g1 = f2 · g2)
    (poC : isPushout f1 f2 g1 g2 heq).


  Let ff1 : R0 -->[f1] R1 :=  disp_InitialArrow (rep_disp C) (rep_cleaving C) repr_R0 f1.
  Let ff2 : R0 -->[f2] R2 :=  disp_InitialArrow (rep_disp C) (rep_cleaving C) repr_R0 f2.
  Let gg1 : R1 -->[g1] R' :=  disp_InitialArrow (rep_disp C) (rep_cleaving C) repr_R1 g1.
  Let gg2 : R2 -->[g2] R' :=  disp_InitialArrow (rep_disp C) (rep_cleaving C) repr_R2 g2.

  Let eq_ff : TT ff1 · TT gg1 = TT ff2 · TT gg2.
  Proof.
    use total2_paths2_b.
    - exact heq.
    - etrans; [ apply (disp_InitialArrowUnique _ (rep_cleaving C) repr_R0) | ].
      apply pathsinv0.
      apply (disp_InitialArrowUnique _ (rep_cleaving C) repr_R0).
  Qed.


  Definition pushout_in_big_rep : isPushout (TT ff1)(TT ff2)(TT gg1)(TT gg2) eq_ff :=
    pushout_total (rep_disp C) (rep_cleaving C) ff1 ff2 gg1 gg2 repr_R1 repr_R2 repr_R' poC.


End init.