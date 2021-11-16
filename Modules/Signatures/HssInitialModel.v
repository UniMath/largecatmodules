(**
We show that initial hss coming from strengthened signatures yield initial models [hss_sig_initial].
We work in the category of sets, although the proof could certainly be carried out in a more general
case.
 *)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.SubstitutionSystems.Signatures.

Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.categories.HSET.All.
Require Import UniMath.CategoryTheory.FunctorCategory.

Require Import UniMath.Combinatorics.Lists.
Require Import UniMath.CategoryTheory.whiskering.
Require Import Modules.Prelims.lib.
Require Import Modules.Prelims.CoproductsComplements.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import Modules.Signatures.SigWithStrengthToSignature.
Require Import Modules.Signatures.Signature.
Require Import UniMath.SubstitutionSystems.ModulesFromSignatures.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.Chains.Chains.
Require Import UniMath.CategoryTheory.Chains.Adamek.
Require Import UniMath.CategoryTheory.Chains.OmegaCocontFunctors.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.SubstitutionSystems.LiftingInitial_alt.
Require Import UniMath.SubstitutionSystems.ModulesFromSignatures.
Require Import UniMath.SubstitutionSystems.SignatureCategory.
Require Import UniMath.SubstitutionSystems.MonadsFromSubstitutionSystems.
Open Scope cat.


(** specific definition for the hSet category *)

Section EpiSignatureSig.

  (* Local Notation H_SET := hset_category. *)
  Local Notation hom_SET := has_homsets_HSET.
  Local Notation Sig := (Signature SET SET HSET).
  Local Notation EndSet := [hset_category, hset_category].
  (* Local Notation toSig := SigToSignatureHSET . *)
  
  Local Notation iniHSS sig hsig  := (InitialHSS SET BinCoproductsHSET InitialHSET
                                        (ColimsHSET_of_shape nat_graph)
                                        sig
                                        (hsig : is_omega_cocont sig)).

  (** The initial model of the hss signature *)
  Lemma hss_initial_model {sig : Sig}(hsig : is_omega_cocont sig) : (rep_disp SET) [{ (sigWithStrength_to_sig sig)}].
  Proof.
    use tpair.
    - exact (Monad_from_hss _  BinCoproductsHSET sig(InitialObject (iniHSS sig hsig))).
    - apply τ_lmodule_mor.
  Defined.

  Definition hss_initial_arrow_mon {sig : Sig} (hsig : is_omega_cocont sig)
    (b : model (sigWithStrength_to_sig sig)) :
      Monad_Mor  (pr1 (hss_initial_model hsig)) b.
  Proof.
    apply j_mon.
    apply (model_τ b).
  Defined.

  (* j_mon is a morphism of model *)
  Definition hss_initial_arrow_law {sig : Sig} (hsig : is_omega_cocont sig)
    (b : model (sigWithStrength_to_sig sig)) :
    model_mor_law (hss_initial_model hsig) b (signature_Mor_id (sigWithStrength_to_sig sig))
      (hss_initial_arrow_mon hsig b).
  Proof.
    intro c.
    apply j_mor_rep.
  Qed.

  Definition hss_initial_arrow {sig : Sig}(hsig : is_omega_cocont sig) 
    (b : model (sigWithStrength_to_sig (C := SET)( sig))) :
    (rep_disp SET) [{(sigWithStrength_to_sig sig)}] ⟦ hss_initial_model hsig, b ⟧
    := hss_initial_arrow_mon hsig b,, hss_initial_arrow_law hsig b.

  Local Notation EndAlg sig :=
    (FunctorAlg (Id_H HSET BinCoproductsHSET ( sig))).

  Local Notation M_alg := (ModulesFromSignatures.M_alg HSET BinCoproductsHSET).


  Lemma rep_mor_to_alg_is_alg_mor {sig : Sig}
        (hsig : is_omega_cocont sig)
             (b : model (sigWithStrength_to_sig sig))
             (t : (rep_disp SET) [{(sigWithStrength_to_sig sig)}] ⟦ hss_initial_model hsig, b ⟧) :
    is_algebra_mor (Id_H HSET  BinCoproductsHSET ( sig))
                   (pr1 (pr1 (iniHSS sig hsig)))
                   (M_alg sig b (model_τ b))
                   (pr1 (pr1 t)).
  Proof.
    red.
    apply nat_trans_eq; [apply (homset_property SET)|].
    intro X.
    apply funextfun.
    intro x.
    (* x is in a coproduct. We check both cases *)
    destruct x as [x|x].
    - assert (ht := Monad_Mor_η (pr1 ( t)) X).
      apply toforallpaths in ht.
      specialize (ht x).
      apply ht.
    - assert (ht := model_mor_ax t X).
      apply toforallpaths in ht.
      specialize (ht x).
      apply ht.
  Qed.

    
    
  
  Definition rep_mor_to_alg_mor {sig : Sig}
             (hsig : is_omega_cocont sig)
             (b : model (sigWithStrength_to_sig sig))
             (t : (rep_disp SET) [{(sigWithStrength_to_sig sig)}] ⟦ hss_initial_model hsig, b ⟧) :
    EndAlg sig ⟦ (pr1 (pr1 (iniHSS sig hsig))) , M_alg sig b (model_τ b) ⟧.
  Proof.
    use tpair.
    - apply t.
    - apply (rep_mor_to_alg_is_alg_mor hsig b t).
  Defined.



  Lemma hss_initial_arrow_unique  {sig : Sig} 
        (hsig : is_omega_cocont sig)
    (b : model (sigWithStrength_to_sig sig)) :
    ∏ t : (rep_disp SET) [{(sigWithStrength_to_sig sig)}] ⟦ hss_initial_model hsig, b ⟧,
          t = hss_initial_arrow hsig b.
  Proof.
    intro t.

    (* TODO : mettre ce lemme d'unicité qui vient de la définition de j avec sa définition
 dans ModulesFromSignatures *)
    assert (h := (InitialArrowUnique
     (colimAlgInitial 
        (Initial_functor_precat HSET HSET InitialHSET)
        (is_omega_cocont_Id_H HSET BinCoproductsHSET ( sig)
           hsig)
        (colimits.ColimsFunctorCategory_of_shape nat_graph 
           HSET HSET (ColimsHSET_of_shape nat_graph)
           (initChain (Initial_functor_precat HSET HSET InitialHSET)
              (Id_H HSET BinCoproductsHSET ( sig)))))
     (ModulesFromSignatures.M_alg HSET BinCoproductsHSET ( sig) b (model_τ b)))).
   
    specialize (h (rep_mor_to_alg_mor hsig b t)).
    apply model_mor_mor_equiv.
    apply algebra_mor_eq in h;
    intro c.
    eapply nat_trans_eq_pointwise in h.
    apply h.
  Qed.
       
       

  Theorem hss_sig_effective {sig : Sig}(hsig : is_omega_cocont sig)
    : isInitial _ (hss_initial_model hsig).
  Proof.
    intro b.
    cbn in b.
    unshelve eapply make_iscontr.
    - apply hss_initial_arrow.
    - apply hss_initial_arrow_unique.
  Qed.




  Definition hss_sig_initial {sig : Sig} (hsig : is_omega_cocont sig)
    : Initial (rep_disp SET)[{sigWithStrength_to_sig sig}]  := make_Initial _ (hss_sig_effective hsig).


End EpiSignatureSig.
