(** * Modularity for 2-signatures


Suppose we have the following pushout diagram in the category of 2-signatures:
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

such that a0, a1, a2 and a' are effective with initial models
R0, R1, R2 and R'. Then, above this pushout there is a pushout square in the
large category of models:
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

Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.FunctorCategory.

Require Import UniMath.CategoryTheory.Limits.Pushouts.
Require Import UniMath.CategoryTheory.Limits.Initial.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.

Require Import Modules.SoftEquations.CatOfTwoSignatures.
Require Import Modules.Prelims.FibrationInitialPushout.

Local Open Scope cat.
Local Notation TT := (disp_mor_to_total_mor two_model_disp ).

Local Notation ι := (disp_InitialArrow two_model_disp  TwoMod_cleaving _ ).

Definition pushout_in_big_rep
           {C : category}
           {a0 a1 a2 a' : @TwoSig_category C}
           {f1 : TwoSig_category ⟦ a0, a1 ⟧}{f2 : TwoSig_category ⟦ a0, a2 ⟧}
           {g1 : TwoSig_category ⟦ a1, a' ⟧}{g2 : TwoSig_category ⟦ a2, a' ⟧}

           {heq :  f1 · g1 = f2 · g2}
           (** If we have a pushout of signatures *)
           (poC : isPushout f1 f2 g1 g2 heq)

           (** and syntaxes for each of the signatures *)
           {R0 : two_model_disp a0} {R1 : two_model_disp a1} {R2 : two_model_disp a2} {R' : two_model_disp a'}
           (repr_R0 : isInitial  (fiber_category _ _) R0)
           (repr_R1 : isInitial  (fiber_category _ _) R1)
           (repr_R2 : isInitial  (fiber_category _ _) R2)
           (repr_R' : isInitial  (fiber_category _ _) R')
           (** Then the initial morphisms induce a pushout in the total category *)
  :  isPushout (TT (ι f1))
               (TT (ι f2))
               (TT (ι g1))
               (TT (ι g2))
               _ :=
  pushout_total_initial _ TwoMod_cleaving  repr_R1 repr_R2 repr_R' repr_R0 poC.
