(** * Complements about binding/algebraic signatures


- Binding Signature operations (specified by arities) yield signature-over morphisms [bindingSig_op_to_sig_mor]
- Their category of models in the sense of ModelCat has an initial object [bindingSigHSET_Initial]
*)
Require Import UniMath.Foundations.PartD.

Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Monads.LModules.
Require Import UniMath.CategoryTheory.SetValuedFunctors.
Require Import UniMath.CategoryTheory.HorizontalComposition.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.Categories.HSET.All.
Require Import UniMath.CategoryTheory.Limits.BinCoproducts.
Require Import UniMath.CategoryTheory.catiso.

Require Import UniMath.Foundations.Sets.
Require Import UniMath.SubstitutionSystems.BindingSigToMonad.


Require Import Modules.Prelims.lib.
Require Import Modules.Signatures.Signature.
Require Import Modules.Signatures.PreservesEpi.
Require Import Modules.Signatures.ModelCat.

Require Import Modules.Prelims.LModulesBinProducts.
Require Import Modules.Signatures.BindingSig.
Require Import Modules.Signatures.SignatureBinproducts.
Require Import Modules.Signatures.SignatureCoproduct.
Require Import Modules.Signatures.SignatureDerivation.

Require Import Modules.Signatures.SigWithStrengthToSignature.
Require Import Modules.Signatures.HssSignatureCommutation.
Require Import Modules.Prelims.deriveadj.
Require Import Modules.SoftEquations.SignatureOver.
Require Import Modules.SoftEquations.Equation.
Require Import Modules.SoftEquations.quotientequation.
Require Import Modules.Prelims.BinProductComplements.
Require Import Modules.Prelims.CoproductsComplements.

Require Import UniMath.CategoryTheory.Limits.Initial.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Coproducts.
Require Import UniMath.CategoryTheory.Limits.Terminal.

Require Import Modules.SoftEquations.SignatureOverBinproducts.

Local Notation ι := (sig_over_from_sig _).
Local Notation θ := (tautological_signature).

(** Binding Signature operations (specified by arities) yield signature-over morphisms *)
Definition bindingSig_op_to_sig_mor {C : category}
           bpC bcpC  cpC TC
           (S : BindingSig) (o : BindingSigIndex S) :
  signature_over_Mor (C := C) (binding_to_one_sig bpC bcpC  cpC TC S)
                     (ι (arity_to_one_sig bpC bcpC TC (BindingSigMap _ o)))
                     (ι θ).
Proof.
  eapply (compose (C := signature_over_category _)  ); revgoals.
  - apply action_sig_over_mor.
  -  apply sig_sig_over_mor.
    eapply (compose (C := signature_category )  ); revgoals.
      + use inv_from_iso .
        apply coprod_sigs_har_iso.
      + use (CoproductIn _ _ _ o).
Defined.

(** Specific definition for SET *)
Definition bindingSig_op_to_sig_morHSET :=
  bindingSig_op_to_sig_mor (C := SET) BinProductsHSET BinCoproductsHSET
                            CoproductsHSET TerminalHSET .



Definition bindingSigHSET_Initial (S : BindingSig) :  Initial (rep_fiber_category (binding_to_one_sigHSET  S)).
Proof.
  eapply catiso_initial.
  - apply catiso_modelcat.
  - apply algebraic_sig_initial.
Defined.
