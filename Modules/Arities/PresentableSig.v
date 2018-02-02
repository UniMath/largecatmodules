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

Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.EpiFacts.
Require Import UniMath.CategoryTheory.Epis.

Require Import Modules.Prelims.lib.
Require Import Modules.Prelims.modules.
Require Import Modules.Prelims.deriveadj.
Require Import Modules.Prelims.CoproductsComplements.
Require Import Modules.Prelims.LModuleCoproducts.
Require Import Modules.Arities.HArityCoproduct.
Require Import Modules.Arities.Signatures.
Require Import Modules.Arities.aritiesalt.
Require Import Modules.Arities.HssToArity.
Require Import Modules.Arities.RawSigToHAr.
Require Import Modules.Arities.PresentableHArityBinProdR.
Require Import Modules.Arities.PresentableHArityCoproducts.
Require Import Modules.Arities.PresentableArity.
Require Import Modules.Arities.PresentableRawSig.
Require Import Modules.Arities.Signatures.
Require  Modules.Arities.FullArities.
Require Import Modules.Arities.FullArToRaw.
Require Import Modules.Arities.SigEquivRep.
Require Import Modules.Prelims.SetCatComplements.
Require Import UniMath.CategoryTheory.categories.category_hset.

Require Import UniMath.CategoryTheory.categories.category_hset_structures.
Module FAr := FullArities.

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

Import FullArities.

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
      apply isEpiBinProdHSET; apply epi_nt_SET_pw;assumption.
    + exact pres_a.
Qed.


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
    - 
      (* rawification of arities *)
      {
        unshelve eapply iso_sig_sig_rep.
        + exact (fun o =>
                   DeBind_HArity (C:=SET) bpSET (α _ o) (nat_of_pres_sig _ o) ,, tautological_harity).
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
      }
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


