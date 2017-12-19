(* Derivation induces an endofcuntro on the category of LModules over a monad *)
(* TODO : intégrer ça dans UniMath *)
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Monads.LModules.
Require Import UniMath.CategoryTheory.Monads.Derivative.

Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.

Require Import UniMath.CategoryTheory.Adjunctions.
Require Import UniMath.CategoryTheory.whiskering.

Require Import Modules.Prelims.lib.
Require Import Modules.Prelims.modules.
Require Import UniMath.SubstitutionSystems.ModulesFromSignatures.

Section DerivFunctor.
  Context {C : precategory}
          (o : C) (* derivation X ↦ X + o *)
          (bcpC : limits.bincoproducts.BinCoproducts C )
          {D : precategory}
          (hsD : has_homsets D)
          (T : Monad C).

  Local Notation "M '" := (LModule_deriv o bcpC M) (at level 30).

  Definition LModule_deriv_Mor_nt {M N : LModule T D} (f : LModule_Mor _ M N) :
    ( M ') ⟹ (N ') := pre_whisker _ f.

  (**
The top right segment is the left hand side
<<<
             f
M(RX + o) --------> N(RX + o)
    |                   |
    |                   |
    |    naturality     |
    |    of f           |
    |                   |
    V        f          V
MR(X+o)) --------->  NR(X+o)
    |                   |
    |     law of f      |
    |                   |
    V                   V
 M(X+o)  --------->   N(X+o)
>>>
*)
  Lemma LModule_deriv_Mor_laws {M N : LModule T D} (f : LModule_Mor _ M N) :
    LModule_Mor_laws _ (LModule_deriv_Mor_nt f).
  Proof.
    intro a.
    etrans; revgoals.
    {
      (* law of f *)
      etrans; [|apply assoc].
      apply cancel_precomposition.
      apply (LModule_Mor_σ _ f).
    }
    rewrite assoc.
    etrans;[apply assoc|].
    apply cancel_postcomposition.
    apply pathsinv0.
    apply (nat_trans_ax f).
  Qed.

  Definition LModule_deriv_Mor {M N : LModule T D} (f : LModule_Mor _ M N) :
    LModule_Mor _ ( M ') (N ') := _ ,, LModule_deriv_Mor_laws f.

  Local Notation LMOD :=(precategory_LModule T (category_pair _ hsD)).

  Definition LModule_deriv_functor_data  : functor_data LMOD LMOD
    := mk_functor_data (C := LMOD)(C' := LMOD)(LModule_deriv o bcpC) (@LModule_deriv_Mor).

  Lemma LModule_deriv_is_functor : is_functor LModule_deriv_functor_data.
  Proof.
    split.
    - intro M.
      apply LModule_Mor_equiv;[exact hsD|].
      apply pre_whisker_identity.
      exact hsD.
    - intros M N O f g.
      apply LModule_Mor_equiv;[exact hsD|].
      apply pre_whisker_composition.
      exact hsD.
  Qed.

  Definition LModule_deriv_functor  : functor LMOD LMOD := mk_functor _ LModule_deriv_is_functor. 
End DerivFunctor.