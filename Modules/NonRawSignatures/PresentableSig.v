(** Presentable sigs are representable *)
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

Require Import UniMath.CategoryTheory.Limits.Coproducts.
Require Import UniMath.CategoryTheory.Limits.Initial.
Require Import UniMath.CategoryTheory.EpiFacts.
Require Import UniMath.CategoryTheory.Epis.

Require Import Modules.Prelims.lib.
Require Import Modules.Prelims.modules.
Require Import Modules.Prelims.deriveadj.
Require Import Modules.Prelims.CoproductsComplements.
Require Import Modules.Prelims.LModuleCoproducts.
Require Import Modules.Signatures.HArityCoproduct.
Require Import Modules.Signatures.Signatures.
Require Import Modules.Signatures.aritiesalt.
Require Import Modules.Signatures.HssToArity.
Require Import Modules.Signatures.RawSigToHAr.
Require Import Modules.Signatures.PresentableHArityBinProdR.
Require Import Modules.Signatures.PresentableHArityCoproducts.
Require Import Modules.Signatures.PresentableArity.
Require Import Modules.Signatures.PresentableRawSig.
Require Import Modules.Signatures.Signatures.
Require  Modules.Signatures.FullSignatures.
Require Import Modules.Signatures.FullArToRaw.
Require Import Modules.Signatures.SigEquivRep.
Require Import Modules.Prelims.SetCatComplements.
Require Import UniMath.CategoryTheory.Categories.category_hset.

Require Import UniMath.CategoryTheory.Categories.category_hset_structures.
Module FAr := FullSignatures.

Section RawSigRep.
Local Notation hom_SET := has_homsets_HSET.
(* Local Notation Sig := (Signature SET has_homsets_HSET hset_precategory has_homsets_HSET). *)
Local Notation EndSet := [hset_category, hset_category].


  Local Notation cp := CoproductsHSET.
  Local Notation bp := BinProductsHSET.
Local Notation bpSET := BinProductsHSET.
  Local Notation bcp := BinCoproductsHSET.
  Local Notation T := TerminalHSET.
  Definition PresentableSignature {C} bpC bcpC Tc cpC :=
    ∑ (O : hSet), O -> (∑ α : arity C, isPresentable bpC bcpC Tc cpC α) × nat.

  Definition base_of_pres_sig
             {C} {bpC} {bcpC} {Tc} {cpC}
             (S : PresentableSignature (C:=C)bpC bcpC Tc cpC)
    : hSet := pr1 S.
Local Notation O := base_of_pres_sig.

Definition ar_of_pres_sig
             {C} {bpC} {bcpC} {Tc} {cpC}
             (S : PresentableSignature (C:=C)bpC bcpC Tc cpC)
  : O S -> arity C := fun o => (pr1 (pr1 (pr2 S o))).
Definition ar_of_pres_sig_isPresentable
             {C} {bpC} {bcpC} {Tc} {cpC}
             (S : PresentableSignature (C:=C)bpC bcpC Tc cpC)
  : ∏ o,   isPresentable bpC bcpC Tc cpC (ar_of_pres_sig S o):= fun o => (pr2 (pr1 (pr2 S o))).

Local Notation α := ar_of_pres_sig.
Definition nat_of_pres_sig
             {C} {bpC} {bcpC} {Tc} {cpC}
             (S : PresentableSignature (C:=C)bpC bcpC Tc cpC)
  : O S -> nat := fun o => ( (pr2 (pr2 S o))).


Let isPresentableSET :=
  isPresentable (C := SET) bp bcp T (λ i : hSet, cp (pr1 i) (setproperty i)).

Definition PresentableSignature_to_signature {C} bpC bcpC TC cpC
           (S : PresentableSignature (C:=C) bpC bcpC TC cpC)
  : signature C :=
  tpair (T := hSet) (fun X => X -> FAr.FullArity C) (O S) (fun o => (α S o ,,
                                                                nat_deriv_HAr bcpC TC
                                                      (nat_of_pres_sig S o))).

(* TODO move to derivadj *)
Definition adj1n n' R :
  ∏ a : arity SET,
  LModule_Mor R (a R) ((nat_deriv_HAr (C := SET) bcp T n') R)
  ≃ LModule_Mor R ((DeBind_HArity (C := SET) bpSET a n') R) (tautological_harity_on_objects R).
Proof.
  intro a.
  eapply equiv_is_rep_ar_to_raw .
  apply deriveadj.adj1.
Defined.

Import FullSignatures.

    (** This uses univalence to transform an isomorphism of category into an equality
       Another proof could be used without univalence though
 (@DeBind_HArity SET bpSET a n',, @tautological_harity SET)
(@DeBind_HArity SET bpSET a n',, @tautological_harity SET)
     *)


Lemma isPresentable_debind ar (har : isPresentableSET ar) n :
  isPresentableSET (DeBind_HArity (C:=SET) bpSET ar n).
Proof.
  revert ar har.
  induction n.
  - exact (fun a h => h).
  - intros ar pres_a.
    simpl.
    apply IHn.
    apply har_binprodR_isPresentable.
    + apply hset_category_isDistributive.
    + intros  F F' G G' f g epif epig.
      apply is_nat_trans_epi_from_pointwise_epis.
      intro a.
      apply isEpiBinProdHSET; apply epi_nt_SET_pw; assumption.
    + exact pres_a.
Qed.

Definition PresentableSignature_to_signature_2 (sig : PresentableSignature (C:=hset_category) bpSET bcp T (λ I : hSet, cp (pr1 I) (setproperty I)))
 : signature hset_category.
Proof.
  exists (O sig).
  intro o.
  exact (DeBind_HArity (C:=hset_category) bpSET (α sig o) (nat_of_pres_sig sig o),, tautological_harity).
Defined.

Definition catiso_Presentable_Raw (sig : PresentableSignature (C:=hset_category) bpSET bcp T (λ I : hSet, cp (pr1 I) (setproperty I))):
  let sig' := PresentableSignature_to_signature _ _  _ _ sig
  in
  catiso (precategory_rep_sig sig')
         (precategory_rep_sig (PresentableSignature_to_signature_2 sig)).
Proof.
  unshelve eapply iso_sig_sig_rep.
  + intros o R.
    cbn.
    apply adj1n.
  + unfold adj1n.
    cbn -[equiv_is_rep_ar_to_raw].
    intro o.
    set (n' := nat_of_pres_sig _ o).
    intros R S f.
    eapply (@equiv_raw_ar_mor_law SET _ _ _ deriveadj.adj1).
    * apply deriveadj.adj_law1.
    * apply deriveadj.adj_law2.
Defined.

Lemma initial_presentable_raw_sig sig (ax:  AxiomOfChoice.AxiomOfChoice_surj) :
  Initial (precategory_rep_sig
             (PresentableSignature_to_signature (C:=SET) bp bcp T
                                                (fun I => cp _ (setproperty I))  sig)).
Proof.
  set (sig' := PresentableSignature_to_signature _ _  _ _ sig).
  eapply (transportb (fun X => Initial X)).
  apply catiso_to_precategory_path.
  - intros ? ? .
    apply isaset_rep_a_sig_mor.
  - exact (catiso_Presentable_Raw sig).
  - (* This is a presentable raw signature, so it is representable *)
    set (rawS :=
           tpair (T := hSet) (fun z => z -> arity _)
                 (O sig)
                 (λ o : O sig, DeBind_HArity (C := SET) bpSET (α _ o) (nat_of_pres_sig _ o)) : rawSig).
    apply (initial_presentable_raw_sig rawS);[|apply ax].
    intro o.
    apply isPresentable_debind.
    apply ar_of_pres_sig_isPresentable.
Qed.

End RawSigRep.


