
(**
Commutation of  the functor from hss signature to arities:
- preservation of binproducts
- preservation of coproducts
- coproducts of binding signatures and preservation
- preservation of tautological arities
(* - preservation of derivation *)

*)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.
(* Require Import UniMath.SubstitutionSystems.FromBindingSigsToMonads_Summary. *)
Require Import UniMath.SubstitutionSystems.BindingSigToMonad.
Require Import UniMath.SubstitutionSystems.Signatures.
Require Import UniMath.SubstitutionSystems.SignatureCategory.
Require Import UniMath.SubstitutionSystems.SignatureExamples.
Require Import UniMath.SubstitutionSystems.BinProductOfSignatures.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.Categories.HSET.All.

Require Import UniMath.CategoryTheory.Epis.
Require Import UniMath.CategoryTheory.Limits.Coproducts.
Require Import UniMath.CategoryTheory.Limits.BinCoproducts.
Require Import UniMath.CategoryTheory.Limits.Coproducts.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.EpiFacts.
Require Import UniMath.Combinatorics.Lists.
Require Import UniMath.CategoryTheory.whiskering.
Require Import Modules.Prelims.lib.
Require Import Modules.Prelims.CoproductsComplements.
Require Import Modules.Prelims.LModulesComplements.
Require Import Modules.Signatures.Signature.
Require Import Modules.Signatures.SigWithStrengthToSignature.
Require Import Modules.Signatures.BindingSig.
Require Import Modules.Signatures.PresentableSignature.
Require Import Modules.Signatures.SignatureBinproducts.
Require Import Modules.Signatures.SignatureCoproduct.
Require Import Modules.Signatures.SignatureDerivation.


Require Import Modules.Prelims.BinProductComplements.

Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Monads.LModules.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Open Scope cat.

(** LModule_M1_M2_iso-like but for signatures.
This section provides utilitary lemmas to show that two signatures sending a monad R
to the same underlying functor are isomorphic.

Then, they are used to show the required commutations.
 *)
Section GenericStrat.
  Context {C : category}.

  Context (Ffunc :  ∏ (R : Monad C), functor C C).
  Context (m1 m2 : ∏ (R : Monad C),  R ∙ (Ffunc R) ⟹ (Ffunc R)).

  Context (m1_law: ∏ R, LModule_laws R (Ffunc R,, m1 R)).
  Context (m2_law: ∏ R, LModule_laws R (Ffunc R,, m2 R)).
  Context (m12_eq : ∏ R, (∏ c : C, m1 R c = m2 R c)).

  Let M1 R : LModule _ _ := _ ,, m1_law R.
  Let M2 R : LModule _ _ := _ ,, m2_law R.

  Context (Sf1 : ∏ (R S : Monad C) (f : Monad_Mor R S), LModule_Mor _ (M1 R) (pb_LModule f (M1 S))).
  Context (Sf2 : ∏ (R S : Monad C) (f : Monad_Mor R S), LModule_Mor _ (M2 R) (pb_LModule f (M2 S))).

  Let S1_data : signature_data  := _ ,, Sf1.
  Let S2_data : signature_data  := _ ,, Sf2.

  Context (isS1 : is_signature S1_data).
  Context (isS2 : is_signature S2_data).

  Let S1 : signature C := _ ,, isS1.
  Let S2 : signature C := _ ,, isS2.

  Let S1_S2_R_iso (R : Monad C) :
    iso (C := category_LModule R _)
        (S1 R)
        ( S2 R) :=
    LModule_same_func_iso _ _ (m12_eq _).


  Hypothesis (Sf12_eq : ∏ R S f c, (Sf2 R S f c)  = (Sf1 R S f c) ).
  Definition signature_S1_S2_laws : is_signature_Mor  S1 S2 (fun R => (S1_S2_R_iso R : _ ⟦_ , _⟧ )).
    intros R S f.
    apply nat_trans_eq;[apply homset_property|].
    intro c.
    cbn.
    etrans;[apply id_right|].
    apply pathsinv0.
    etrans;[apply ( (id_left _))|].
    apply Sf12_eq.
  Qed.
  Definition signature_S2_S1_laws : is_signature_Mor  S2 S1 (fun R => (inv_from_iso (S1_S2_R_iso R))).
    intros R S f.
    apply nat_trans_eq;[apply homset_property|].
    intro c.
    cbn.
    repeat rewrite id_right.
    apply pathsinv0.
    etrans;[apply ( (id_left _))|].
    apply pathsinv0.
    apply Sf12_eq.
  Qed.

  Definition signature_S1_S2 : signature_Mor S1 S2 := _ ,, signature_S1_S2_laws.
  Definition signature_S2_S1 : signature_Mor S2 S1 := _ ,, signature_S2_S1_laws.

  Lemma signature_S1_S2_is_inverse  :
    is_inverse_in_precat (C := signature_category)
                         signature_S1_S2 signature_S2_S1.
  Proof.
    use make_is_inverse_in_precat.
    - apply signature_Mor_eq.
      intro X.
      use (iso_inv_after_iso (S1_S2_R_iso X)).
    - apply signature_Mor_eq.
      intro X.
      apply (iso_after_iso_inv (S1_S2_R_iso X)).
  Qed.

  Definition signature_S1_S2_iso : iso (C := signature_category) S1 S2 :=
    make_iso _ (
              is_iso_from_is_z_iso
                _
                (make_is_z_isomorphism _ _ signature_S1_S2_is_inverse)).


End GenericStrat.

Section commuteBinProdSig.
  Context {C : category}  .
  Local Notation SIG := (Signature_category C C C).
  Context {I : UU}
          (bpC :  BinProducts C).
  Let hss_bpSig  : BinProducts  SIG
    := BinProducts_Signature_category C C bpC C.

  Let bpSig := signature_BinProducts (C := C) bpC.

  Variable (a b : Signature C C C).

  Let ar_a :=  sigWithStrength_to_sig a.
  Let ar_b :=  sigWithStrength_to_sig b.
  Local Notation BPO := (BinProductObject _ ).

  (**  to get this statment, I first tried to use LModule_M1_M2_iso
  Lemma  binprod_sigs_har_mod_iso R :
    iso (C := category_LModule R _)
        ( sigWithStrength_to_sig (BPO (hss_bpSig a b)) R)
        ( (BPO (bpSig ar_a ar_b) : signature _ ) R).
  Proof.
    apply LModule_M1_M2_iso.
*)
  Lemma binprod_sigs_har_mod_eq_mult R c  :

    (ModulesFromSignatures.lift_lm_mult (BPO (hss_bpSig a b)) R (tautological_LModule R) : nat_trans _ _) c =
    (LModulesBinProducts.LModule_binproduct_mult bpC (ar_a R) (ar_b R) c).
  Proof.
    cbn.
    unfold BinProductOfSignatures.θ_ob_fun.
    unfold binproduct_nat_trans_data.
    etrans;[apply postcompWithBinProductArrow|].
    unfold BinProductOfArrows.
    repeat rewrite assoc.
    apply idpath.
  Defined.

  Lemma binprod_sigs_har_eq (R S : Monad C) (f : Monad_Mor R S) (c : C) :
    (signature_BinProduct_on_morphisms ar_a ar_b R S f) c =
    (lift_lmodule_mor (BPO (hss_bpSig a b)) R (monad_mor_to_lmodule f) c) · (lift_pb_LModule
                                                                                 (BPO (hss_bpSig a b)) f) c.
  Proof.
    cbn.
    unfold binproduct_nat_trans_data, nat_trans_comp; cbn.
    unfold binproduct_nat_trans_pr1_data; cbn.
    unfold binproduct_nat_trans_pr2_data; cbn.
    unfold BinProduct_of_functors_ob.
    repeat rewrite id_right.
    reflexivity.
  Qed.




  Definition binprod_sigs_har_iso : iso (C := signature_category)
                                        ( sigWithStrength_to_sig (BPO (hss_bpSig a b)) )
                                        ( (BPO (bpSig ar_a ar_b) : signature _ ) ).
  Proof.
    use signature_S1_S2_iso.
    - intros R S.
      use binprod_sigs_har_mod_eq_mult.
    - intros R S f c.
      cbn beta.
      use binprod_sigs_har_eq.
  Defined.
End commuteBinProdSig.

Section CoprodAr.
  Context {C : category}  .
  Local Notation SIG := (Signature_category C C C).
  Context {I : UU}
          (cpC :  Coproducts I C).
  Let hss_cpSig  : Coproducts I SIG
    := Coproducts_Signature_category _ C _ _ cpC.
  Let cpSig := signature_Coproducts (C := C) cpC.

  Variable (sigs : I -> SIG).
  Let ars : I -> signature C := fun i => sigWithStrength_to_sig (sigs i).
  Local Notation CPO := (CoproductObject _ _).

  Lemma coprod_sigs_har_mod_eq_mult R c  :
    (ModulesFromSignatures.lift_lm_mult (CPO (hss_cpSig sigs)) R (tautological_LModule R) : nat_trans _ _) c =
    (LModulesCoproducts.LModule_coproduct_mult cpC (λ o : I, (ars o) R)) c.
  Proof.
    cbn.
    unfold SumOfSignatures.θ_ob_fun.
    unfold Coproducts.coproduct_nat_trans_data.
    etrans;[apply precompWithCoproductArrow|].
    unfold LModulesCoproducts.LModule_coproduct_mult_data.
    unfold CoproductOfArrows.
    apply maponpaths.
    apply funextsec.
    intro i.
    apply  assoc.
  Qed.

  Lemma  coprod_sigs_har_eq (R S : Monad C) (f : Monad_Mor R S) c :
  (signature_coprod_on_morphisms ars R S f) c =
  ((lift_lmodule_mor (CPO (hss_cpSig sigs)) R (monad_mor_to_lmodule f )c) · lift_pb_LModule
                                                                                  (CPO (hss_cpSig sigs)) f c) .
  Proof.
    cbn.
    unfold coproduct_nat_trans_data , coproduct_nat_trans_in , nat_trans_comp, coproduct_of_functors; cbn.
    repeat rewrite id_right.
    repeat rewrite id_left.
    apply maponpaths.
    apply funextsec.
    intro i.
    rewrite id_right.
    reflexivity.
  Qed.
  Definition coprod_sigs_har_iso : iso (C := signature_category) (sigWithStrength_to_sig (CPO (hss_cpSig sigs)))
                                       (CPO (cpSig ars)).
    use signature_S1_S2_iso.
    - cbn.  use coprod_sigs_har_mod_eq_mult.
    - use coprod_sigs_har_eq.
  Defined.


End CoprodAr.
Section TautologicalPreserve.
  Context {C : category}.
  Local Notation SIG := (Signature_category C C).
  Let a := (sigWithStrength_to_sig (IdSignature C C)).
  Let b := (tautological_signature (C:=C)).

  Definition tauto_sigs_har_iso : iso (C := signature_category) a
                                       b.
  Proof.
    use signature_S1_S2_iso.
    - cbn.
      intros; apply id_left.
    - intros R S f c.
      cbn.
      apply pathsinv0, id_right.
  Defined.

End TautologicalPreserve.




(*
Section DerivationPreserve.
  Context {C : category}.
  Context (bc : BinCoproducts C)(T : Terminal C).

  (** unfortunately, there isn't any notion of derivation of strengthened signature
      in UniMath: only n-th derivation of the tautological signature *)
  Context (n : nat).
  Let a := precomp_option_iter_Signature (homset_property C) bc T n.

  Lemma  deriv_sigs_har_mod_iso R :
    iso (C := category_LModule R _)
        ( sigWithStrength_to_sig (precomp_option_iter_Signature (homset_property C) bc T (S n))  R)
        ( (signature_deriv bc T
                           (sigWithStrength_to_sig
                               (precomp_option_iter_Signature (homset_property C) bc T n)  )
          )  R).
    (*
    iso (C := category_LModule R _)
        ( sigWithStrength_to_sig (precomp_option_iter_Signature (homset_property C) bc T (S n))  R)
        ( (signature_deriv bc T
                           (sigWithStrength_to_sig
                               (precomp_option_iter_Signature (homset_property C) bc T n)  )
          )  R).
*)
  Proof.
    cbn.
    use tpair.
    use tpair.
    use tpair.
    intro X.
    cbn.
    use tpair.
        apply LModule_M1_M2_iso.

    unfold a.
    induction n.

*)
