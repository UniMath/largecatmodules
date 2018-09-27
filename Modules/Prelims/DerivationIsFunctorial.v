(**
- Derivation induces an endofunctor on the category of LModules over a monad [LModule_deriv_functor]
- natural transformation from the identity functor to the derivation functor [LModule_to_deriv_functor]

TODO: reuse general stuff in Unimath Derivative about distributive laws
 *)
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
Require Import UniMath.CategoryTheory.limits.bincoproducts.

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

  Local Notation "∂" := LModule_deriv_functor.

  Definition LModule_to_deriv_nt (M : LModule T D ) : M ⟹ (∂ M : LModule T D).
  Proof.
  (*
M ---> M Id ---> M ∂
*)
    eapply (compose (C := [C,D , hsD]) ); [apply EndofunctorsMonoidal.λ_functor_inv|].
    apply post_whisker.
    apply coproduct_nat_trans_in2.
  Defined.

  Lemma LModule_to_deriv_laws (M : LModule T D) : LModule_Mor_laws _ (LModule_to_deriv_nt M).
  Proof.
    intro x.
    cbn -[BinCoproductIn2 BinCoproductArrow].
    repeat rewrite id_left.
    (*
The left hand side is top right. The outer diagram must commute
f := η ∘ in₁
<<<
          Min₂
    MRX --------> M(T+RX)
      |             |
      |             |
  id  |             | M[f,Rin₂]
      |             |
      V   MRin₂     V
    MRX --------> MR(T+X)
      |             |
      |             |
   σ  |   nat of σ  | σ
      |             |
      V             V
      MX -------> M(X+T)
           Min₂
>>>
*)
    etrans;[|apply (nat_trans_ax (lm_mult T M))].
    repeat rewrite assoc.
    apply cancel_postcomposition.
    rewrite <- functor_comp.
    apply (maponpaths (fun x => # M x)).
    apply BinCoproductIn2Commutes.
  Qed.


  Definition LModule_to_deriv (M : LModule T D) : LModule_Mor _ M (∂ M) :=
    _ ,, (LModule_to_deriv_laws _).

  Lemma LModule_to_deriv_is_nt : is_nat_trans (functor_identity _) ∂ LModule_to_deriv.
  Proof.
    intros M N f.
    apply (LModule_Mor_equiv _ hsD).
    apply (nat_trans_eq hsD).
    intro c.
    cbn.
    unfold coproduct_nat_trans_in2_data; cbn.
    repeat rewrite id_left.
    apply pathsinv0.
    apply (nat_trans_ax (f : LModule_Mor _ _ _)).
  Qed.

  Definition LModule_to_deriv_functor : (functor_identity _) ⟹ ∂ :=
    mk_nat_trans _ _ _ LModule_to_deriv_is_nt.
End DerivFunctor.