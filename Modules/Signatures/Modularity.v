(** * Modularity for signatures


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

Require Import UniMath.CategoryTheory.limits.pushouts.
Require Import UniMath.CategoryTheory.limits.initial.

Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.

Require Import Modules.Signatures.Signature.
Require Import Modules.Prelims.FibrationInitialPushout.

Local Open Scope cat.
Local Notation TT := (disp_mor_to_total_mor (rep_disp _)).

Local Notation ι := (disp_InitialArrow (rep_disp _) (rep_cleaving _) _ ).

Definition pushout_in_big_rep
           {C : category}
           {a0 a1 a2 a' : @signature_category C}
           {f1 : signature_category ⟦ a0, a1 ⟧}{f2 : signature_category ⟦ a0, a2 ⟧}
           {g1 : signature_category ⟦ a1, a' ⟧}{g2 : signature_category ⟦ a2, a' ⟧}

           {heq :  f1 · g1 = f2 · g2}
           (** If we have a pushout of signatures *)
           (poC : isPushout f1 f2 g1 g2 heq)

           (** and syntaxes for each of the signatures *)
           {R0 : rep_disp _ a0} {R1 : rep_disp _ a1} {R2 : rep_disp _ a2} {R' : rep_disp _ a'}
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
  pushout_total_initial (rep_disp C) (rep_cleaving _)  repr_R1 repr_R2 repr_R' repr_R0 poC.
