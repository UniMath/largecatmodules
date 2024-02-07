(** We show that presentable signatures generate a syntax
 *)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.
(* Require Import UniMath.SubstitutionSystems.FromBindingSigsToMonads_Summary. *)
Require Import UniMath.SubstitutionSystems.BindingSigToMonad.
Require Import UniMath.SubstitutionSystems.Signatures.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.Categories.HSET.All.

Require Import UniMath.CategoryTheory.Epis.
Require Import UniMath.CategoryTheory.EpiFacts.
Require Import Modules.Prelims.EpiComplements.
Require Import UniMath.Combinatorics.Lists.
Require Import UniMath.CategoryTheory.whiskering.
Require Import Modules.Prelims.lib.
Require Import Modules.Signatures.Signature.
Require Import Modules.Signatures.SigWithStrengthToSignature.
Require Import Modules.Signatures.BindingSig.
Require Import Modules.Signatures.EpiSigRepresentability.
Require Import Modules.Signatures.PreservesEpi.
Require Import Modules.Signatures.EpiArePointwise.

Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Monads.LModules.
Require Import UniMath.CategoryTheory.Limits.Initial.
Require Import UniMath.CategoryTheory.Limits.BinCoproducts.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Coproducts.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Open Scope cat.






Section PresentableDefinition.

Context {C : category} (bp : BinProducts C) (bcp : BinCoproducts C) (T : Terminal C)
          (cp : ∏ (I : hSet), Coproducts I C).

Let toSig sig  :=
  (BindingSigToSignature bp bcp T  sig (cp (BindingSigIndexhSet sig))).


Definition isPresentable (a : signature C) :=
  ∑ (S : BindingSig) (F : signature_Mor (sigWithStrength_to_sig (C := C) (toSig S)) a),
                            ∏ (R : Monad C), (isEpi (C := [_, _]) (pr1 (F R))).

End PresentableDefinition.


Section PresentableProjections.
  Context {C : category} {bp : BinProducts C} {bcp : BinCoproducts C} {T : Terminal C}
          {cp : ∏ (I : hSet), Coproducts I C}.


  Context {a : signature C} (p : isPresentable bp bcp T cp a).
Definition p_sig   : BindingSig := pr1 p.
Let toSig sig  :=
  (BindingSigToSignature bp bcp T  sig (cp (BindingSigIndexhSet sig))).
Definition p_alg_ar   : signature C :=
  sigWithStrength_to_sig (C := C) (toSig p_sig).

Definition p_mor : signature_Mor (p_alg_ar ) a := pr1 (pr2 p).
Definition epi_p_mor   :
  ∏ (R : Monad C), (isEpi (C := [_, _]) (pr1 (p_mor  R)))
  := pr2 (pr2 p).


End PresentableProjections.

Local Notation hom_SET := has_homsets_HSET.
Local Notation Sig := (Signature SET has_homsets_HSET hset_precategory has_homsets_HSET).
Local Notation EndSet := [hset_category, hset_category].



Local Notation toSig sig :=
  (BindingSigToSignature has_homsets_HSET BinProductsHSET
                         BinCoproductsHSET TerminalHSET sig
                         (CoproductsHSET (BindingSigIndex sig) (BindingSigIsaset sig))).



Lemma PresentableisEffective
      {a : signature SET} (p : isPresentable (C := SET) BinProductsHSET BinCoproductsHSET TerminalHSET
                                             (fun i => CoproductsHSET _ (setproperty i)) a)
  :
   Initial (rep_disp SET) [{a}].
Proof.
  use (push_initiality (p_mor  p) _ _  ).
  - apply alg_initialR.
  - apply algebraic_model_Epi.
  - apply BindingSig_on_model_isEpi.
  - apply algSig_NatEpi.
  - apply pwEpiSig_isEpi.
    apply epi_p_mor.
  - apply algebraic_sig_effective.
Qed.

