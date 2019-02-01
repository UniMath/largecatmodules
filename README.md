# largecatmodules
Large category of modules over monads on top of UniMath.
Signatures for higher order syntax.

Preliminaries are in the subfolder Modules/Prelims
1-Signature related proofs are in the subfolder Modules/Signatures
2-Signature related proofs are in the subfolder Modules/SoftEquations

Requirement: the UniMath library (installed with `$ make install`)

To compile (Coq 8.8): `$ make`



# List of some important formalized propositions and definitions

The file `SoftEquations/Summary` gives a summary of main formalized propositions and definitions
for 2-signatures and elementary equations.

For the rest:

- Definition of signatures and their actions : `Signatures/Signature`
- Representability of presentable signatures : `Signatures/PresentableSignature`
- Representability of the codomain epimorphic morphism of signature : `Signatures/EpiSigRepresentability`
- Adjunction in the category of modules over a specific monad R  on Set
          Hom(M x R', N) ~ Hom(M , N') : `Prelims/derivadj`
          

- A coproduct of presentable  signatures is presentable : `Signatures/PresentableSignatureCoproducts` 
- The binproduct of a presentable  signature with the tautological signature is
     presentable : `Signatures/PresentableSignatureBinProdR` 
- pointwise limits and colimits of modules : `Prelims/LModuleColims`
- pointwise limits and colimits of signatures : `Signatures/SignaturesColims`
- quotient monad : `Prelims/quotientmonad`
- Epimorphisms of signatures are pointwise epimorphisms : `Signatures/EpiArePointwise`
- Modularity in the context of a fibration : `Prelims/FibrationInitialPushout`
- Modularity in the specific context of signatures and their models : `Signatures/Modularity`
          
The fact that algebraic signatures are representable is already proved in
a different setting in the Heterogeneous Substitution System package of UniMath.
The adaptation to our setting is carried out in the files : `Signatures/SigWithStrengthToSignature`,
`Signatures/HssInitialModel` and `Signatures/BindingSig`.

# Summary of files
By folder

## Prelims

    
- `quotientmonad`, `quotientmonadslice` : the quotient monad construction
- `FibrationInitialPushout` : modularity in the context of a fibration

- `DerivationIsFunctorial` : Proof that derivation of modules is functorial
- `derivadj` : Adjunction in the category of modules over a specific monad R on Set
          Hom(M x R', N) ~ Hom(M , N') 

- `LModulesFibration` : fibration of left modules over monads
- `LModulesColims` : limits and colimits of modules
- `LModulesBinProducts`, `LModulesCoproducts` : direct definition of some particular
    colimits/limits of modules

- `PushoutsFromCoeqBinCoproducts` : Pushouts from coequalizers and binary coproducts
- `FaithfulFibrationEqualizer` : Faithful fibrations lift coequalizers
- `Opfibration` : definition of opfibrations (adapted from the definition of fibrations in UniMath)

- `BinCoproductComplements`, `BinProductComplements` , `CoproductsComplements`, `EpiComplements`
  `LModulesComplements`, `SetCatComplements`, `lib` : various complements

## Signatures
Everything here is about 1-signatures

- `Signature` : definition of signatures and the displayed category of models 
- `ModelCat` : direct definition of the category of models of a signature
- `EpiSigRepresentability` : proof of the technical lemma : epimorphisms of signatures preserves
       representability
- `PresentableSignatures` : presentable signatures are representable.
- `Modularity` : Modularity in the specific context of signatures and their models
- `quotientrep` : quotient model construction

- `HssInitialModel`, `BindingSig` : adaptation of the proof in UniMath of initiality for strengthened signatures
       (in particular, for binding or algebraic signatures)
- `PreservesEpi` : Epi-signatures 

- `EpiArePointwise` : epimorphisms of signatures are pointwise epimorphisms
- `PresentableSignatureCoproducts` : a coproduct of presentable  signatures is presentable.
- `PresentableSignatureBinProdR` : if `a` is presentable, then so is the product of `a` with
       the tautological signature 
- `SignaturesColims` : colimits of  signatures
- `SignatureBinproducts` : direct definition of bin products of  signatures
- `SignatureCoproduct` : direct definition of coproducts of  signatures
- `SignatureDerivation` : derivation of signatures

- `SigWithStrengthToSignature` : Functor between signatures with strength
       and our  signatures.
- `HssSignatureCommutation` : Somme commutation rules between colimits/limits and the 
       functor between signatures with strength and our
       signatures
       
## SoftEquations
This folder is about 2-signatures and elementary equations

- `Summary` : summary of main propositions and definitions

- `SignatureOver` : category of Σ-modules
- `CatOfTwoSignatures` : category of 2-signatures, fibration of 2-models over it
- `Equation` : equations, and category of models satisfying those equations
- `quotientequation` : quotient model satisfying the equations
- `quotientrepslice` : more general quotient model construction
- `AdjunctionEquationRep` : algebraic 2-signatures are representable and related proofs
- `Modularity` : modularity in the specific context of 2-signatures and their models

- `Examples/LCBetaEta` : example of the lambda calculus modulo beta eta
- `SignatureOverAsFiber` : (unused) alternative definition of Σ-modules as a displayed category
        over the category of 1-signatures
- `SignatureOverBinproducts` : binary products of Σ-modules
- `SignatureOverDerivation` : derivative of a Σ-module
- `BindingSig` : complements about algebraic 1-signatures
