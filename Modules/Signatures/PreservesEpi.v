(** Epi-signatures

- see [sig_preservesNatEpiMonad], and its pointwise variant [sig_preservesNatEpiMonad_pw]
- algebraic signatures are such ones [algSig_NatEpi]
- the tautological signature is such a signature [tautological_epiSig]
- derivation preserves this property [deriv_epiSig]
- binary products preserve this property [binProd_epiSig]

*)
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.categories.HSET.All.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.Epis.
Require Import UniMath.CategoryTheory.EpiFacts.

Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Monads.LModules.

Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.

Require Import Modules.Prelims.lib.
Require Import Modules.Prelims.EpiComplements.
Require Import Modules.Signatures.Signature.
Require Import UniMath.SubstitutionSystems.Signatures.
Require Import UniMath.SubstitutionSystems.BindingSigToMonad.
Require Import Modules.Signatures.HssToSignature.
Require Import Modules.Signatures.BindingSig.
Require Import Modules.Signatures.SignatureDerivation.
Require Import Modules.Signatures.SignatureBinproducts.

  (** An epi-signature preserves epimorphicity of natural
      transformations. Note that this is not implied by the axiom of choice
      because the retract may not be a monad morphism.
      (see [algSig_NatEpi] in PresentableSignature for the example of algebraic signatures 
   *)
Definition sig_preservesNatEpiMonad {C : category} (c : signature C)
  : UU
  := ∏ (M N : Monad C) (f : Monad_Mor M N),
     (** pointwise epis and epi as natural transformation are equivalent in Set *)
     (* (∏ o, isEpi  (f o)) -> (isEpi (C := functor_category _ _) ( (#c f)%ar  : nat_trans _ _)). *)
     isEpi (C := functor_category _ _) ( f : nat_trans _ _) -> isEpi (C:= functor_category _ _)
                                                       (pr1 (#c f)%ar).

(** these are equivalent in Set *)
Definition sig_preservesNatEpiMonad_pw {C : category} (c : signature C)
  : UU
  := ∏ (M N : Monad C) (f : Monad_Mor M N),
     (** pointwise epis and epi as natural transformation are equivalent in Set *)
     (∏ o, isEpi  (f o)) -> (∏ o, isEpi  ( (#c f o)%ar)).

(** Actually, this is a logical equivalence *)
Lemma sig_preservesNatEpiMonad_reduce_pw_SET (S : signature SET) :
  sig_preservesNatEpiMonad_pw S -> sig_preservesNatEpiMonad S.
Proof.
  intros h M N f epif.
  apply is_nat_trans_epi_from_pointwise_epis.
  intro X.
  apply h.
  apply epi_nt_SET_pw.
  exact epif.
Qed.

(** Proof that an epiSig preserves natural epimorphicity *)
Lemma epiSig_NatEpi {C : category} (S : Signature C (homset_property C) C (homset_property C))
      (epiS : preserves_Epi (S : functor _ _)) : sig_preservesNatEpiMonad (hss_to_ar S).
Proof.
    intros M N f.
    intro epif.
    (* unshelve eapply is_nat_trans_epi_from_pointwise_epis in epif;[apply homset_property|]. *)
    assert (epip := (epiS _ _ (pr1 f)  epif )).
    revert epip.
    apply transportf.
    cbn.
    apply pathsinv0.
    apply (id_right (C := [C,C]) (#S (pr1 f : nat_trans _ _))).
Qed.

(** An algebraic signature preserves natural epimorphicity *)
Corollary  algSig_NatEpi (S : BindingSig)
  : sig_preservesNatEpiMonad
      (hss_to_ar (C := SET)
                 (BindingSigToSignature (homset_property SET)
                                        BinProductsHSET
                                        BinCoproductsHSET TerminalHSET
                                        S
                                        (CoproductsHSET (BindingSigIndexhSet S) (setproperty _)))
      ).
Proof.
  apply epiSig_NatEpi.
  apply BindingSigAreEpiSig.
Qed.


(** The tautological arity preserves epi *)
Definition tautological_epiSig {C : category} : sig_preservesNatEpiMonad (tautological_signature (C := C)) :=
  (* fun R S f h => is_nat_trans_epi_from_pointwise_epis _ _ (homset_property _) _ _ _ h . *)
  fun R S f h => h.

(** Derivation preserves epi-sig *)
Lemma deriv_epiSig {C : category} bc T (Sig : signature C) (h : sig_preservesNatEpiMonad_pw Sig)
   : (sig_preservesNatEpiMonad_pw (signature_deriv bc T Sig )).
Proof.
  intros R S f epif.
  intro o.
  cbn.
  repeat rewrite id_right.
  apply h.
  exact epif.
Qed.

Lemma binProd_epiSig {C : category} bp
      (** products of epis are epis
          This is true of regular epis in a regular category such as Set.
            (e.g. in a topos, pullbacks of epis are epis)
       *)
      (productEpis : products_preserves_Epis (C := C) bp)
      (S1 S2 : signature C)
      (h1 : sig_preservesNatEpiMonad_pw S1)
      (h2 : sig_preservesNatEpiMonad_pw S2)
      : sig_preservesNatEpiMonad_pw (BinProductObject _ (signature_BinProducts bp S1 S2)).
Proof.
  intros R S f epif.
  intro o.
  cbn.
  rewrite id_right.
  apply productEpis;[apply h1|apply h2]; exact epif.
Defined.

Definition binProd_epiSigSET 
      (S1 S2 : signature SET)
      (h1 : sig_preservesNatEpiMonad_pw S1)
      (h2 : sig_preservesNatEpiMonad_pw S2)
  : sig_preservesNatEpiMonad_pw (BinProductObject _ (signature_BinProducts (C := SET) BinProductsHSET S1 S2))
  :=
    binProd_epiSig (C := SET) BinProductsHSET (@productEpisSET) S1 S2 h1 h2.