(**
A monad morphism induces a left module morphism [monad_mor_to_lmodule]
*)
(** TODO: move to UniMath *)
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Monads.LModules.

(** strangely enough, I didn't find the following lemma : 
 *) 
Lemma monad_mor_to_lmodule_law {C : precategory} {R S : Monad C} 
           (f : Monad_Mor R S) : 
  LModule_Mor_laws R (T := tautological_LModule R) 
                   (T' := pb_LModule f (tautological_LModule S)) f. 
Proof. 
  intro x. 
+
  cbn. 
  rewrite assoc. 
  apply pathsinv0. 
  apply Monad_Mor_μ. 
Qed. 
 
Definition monad_mor_to_lmodule {C : precategory} {R S : Monad C} 
  (f : Monad_Mor R S) : LModule_Mor R (tautological_LModule R) (pb_LModule f (tautological_LModule S)) 
  := (f : nat_trans _ _) ,, monad_mor_to_lmodule_law f. 