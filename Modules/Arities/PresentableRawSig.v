(** Presentable raw sigs are representable *)
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.catiso.
Require Import UniMath.CategoryTheory.functor_categories.

Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Monads.LModules.

Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.

Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.limits.initial.

Require Import Modules.Prelims.lib.
Require Import Modules.Prelims.modules.
Require Import Modules.Prelims.CoproductsComplements.
Require Import Modules.Prelims.LModuleCoproducts.
Require Import Modules.Arities.HArityCoproduct.
Require Import Modules.Arities.Signatures.
Require Import Modules.Arities.aritiesalt.
Require Import Modules.Arities.HssToArity.
Require Import Modules.Arities.RawSigToHAr.
Require Import Modules.Arities.PresentableHArityCoproducts.
Require Import Modules.Arities.PresentableArity.
Require  Modules.Arities.FullArities.
Require Import UniMath.CategoryTheory.categories.category_hset.

Require Import UniMath.CategoryTheory.categories.category_hset_structures.
Module FAr := FullArities.

Section RawSigRep.
Local Notation hom_SET := has_homsets_HSET.
(* Local Notation Sig := (Signature SET has_homsets_HSET hset_precategory has_homsets_HSET). *)
Local Notation EndSet := [hset_category, hset_category].


  Local Notation cp := CoproductsHSET.
  Local Notation bp := BinProductsHSET.
  Local Notation bcp := BinCoproductsHSET.
  Local Notation T := TerminalHSET.
  Context (rawsig  : @rawSig SET).
  Let O : hSet := base_of_rawSig rawsig.
  Let a : O -> arity SET := ar_of_rawSig rawsig.
  (** (O, a) is a presentable raw signature *)
  Context (pres_a : ∏ o, isPresentable (C:=SET) bp bcp T (fun i => cp _ (setproperty i))
                                       (a o)).


    (** This uses univalence to transform an isomorphism of category into an equality
       Another proof could be used without univalence though
       
     *)
  Lemma initial_presentable_raw_sig (ax:  AxiomOfChoice.AxiomOfChoice_surj): Initial (precategory_rep_sig (rawSigToSig rawsig)).
  Proof.
    eapply (transportb (fun X => Initial X)).
    apply catiso_to_precategory_path.
    - intros ? ? .
      apply isaset_rep_a_sig_mor. 
    - unshelve apply iso_a_sig_har_rep.
      apply cp.
      apply setproperty.
    - apply PresentableisRepresentable.
      + exact ax.
      + unfold rawSigToHAr.
        use coprod_isPresentable.
        apply pres_a.
  Qed.
End RawSigRep.


