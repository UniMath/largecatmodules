(* We show that presentable (half-)arities are representable *)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.
(* Require Import UniMath.SubstitutionSystems.FromBindingSigsToMonads_Summary. *)
Require Import UniMath.SubstitutionSystems.BindingSigToMonad.
Require Import UniMath.SubstitutionSystems.Signatures.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.categories.category_hset.

Require Import UniMath.CategoryTheory.categories.category_hset_structures.
Require Import UniMath.CategoryTheory.functor_categories.

Require Import UniMath.CategoryTheory.Epis.
Require Import UniMath.CategoryTheory.EpiFacts.
Require Import UniMath.Combinatorics.Lists.
Require Import UniMath.CategoryTheory.whiskering.
Require Import Modules.Prelims.lib.
Require Import Modules.Arities.aritiesalt.
Require Import Modules.Arities.HssToArity.
Require Import Modules.Arities.BindingSig.
Require Import Modules.Arities.uniproofalt.

Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Monads.LModules. 
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Open Scope cat.

Local Notation hom_SET := has_homsets_HSET.
Local Notation Sig := (Signature SET has_homsets_HSET hset_precategory has_homsets_HSET).
Local Notation EndSet := [hset_category, hset_category].

Local Notation toSig sig :=
  (BindingSigToSignature has_homsets_HSET BinProductsHSET
                         BinCoproductsHSET TerminalHSET sig
                         (CoproductsHSET (BindingSigIndex sig) (BindingSigIsaset sig))).

Definition isPresentable (a : arity SET) :=
  ∑ (S : BindingSig) (F : arity_Mor (hss_to_ar (C := SET) (toSig S)) a),
                            ∏ (R : Monad SET), (isEpi (C := [_, _]) (pr1 (F R))).

Definition p_sig {a : arity SET} (p : isPresentable a) : BindingSig := pr1 p.
Definition p_alg_ar {a : arity SET} (p : isPresentable a) : arity SET :=
  hss_to_ar (C := SET) (toSig (p_sig p)).

Definition p_mor {a : arity SET} (p : isPresentable a) : arity_Mor (p_alg_ar p) a := pr1 (pr2 p).
Definition epi_p_mor {a : arity SET} (p : isPresentable a) : 
  ∏ (R : Monad SET), (isEpi (C := [_, _]) (pr1 (p_mor p R)))
  := pr2 (pr2 p).


Lemma PresentableisRepresentable (choice : AxiomOfChoice.AxiomOfChoice_surj)
      {a : arity SET} (p : isPresentable a) :
   Initial (rep_disp SET)[{a}].
Proof.
  use (push_initiality_weaker choice (p_mor p)).
  - apply alg_initialR.
  - apply epi_p_mor.
  - (* TODO : faire un lemme séparé *)
    intros M N f.
    intro epif.
    assert (epip := (BindingSigAreEpiSig (p_sig p) _ _ (pr1 f)  epif )).
    unfold p_alg_ar.
    (* je ne sais pas pourquoi apply epip ne marche pas directement *)
    apply is_nat_trans_epi_from_pointwise_epis.
    intro X.
    apply (epi_nt_SET_pw _ epip X).
  - apply algbraic_sig_representable.
Qed.
