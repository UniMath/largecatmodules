# largecatmodules
Large category of modules over monads on top of UniMaths and TypeTheory
Signatures and signatures for higher order syntax.

Preliminaries are in the subfolder Modules/Prelims
Signature and Signature related proofs are in the subfolder Modules/Signatures

To compile (coq 8.7): make.



# List of formalized propositions and definitions

- Definition of signatures and their actions : `Signatures/Signature`
- Definition of signatures and their actions  : `Signatures/FullSignatures`
- Definition of signatures and their actions  : `Signatures/Signature`
- Representability of presentable signatures : `Signatures/PresentableSignature`
- Representability of presentable signatures : `Signatures/PresentableSig`
- Representability of presentable raw signatures : `Signatures/PresentableRawSig`
- Representability of the codomain epimorphic morphism of signature : `Signatures/EpiSigRepresentability`
- Adjunction in the category of modules over a specific monad R  on Set
          Hom(M x R', N) ~ Hom(M , N') : `Prelims/derivadj.v`
          

- A coproduct of presentable  signatures is presentable : `Signatures/PresentableHSignatureCoproducts` 
- The binproduct of a presentable  signature with the tautological signature is
     presentable : `Signatures/PresentableHSignatureBinProdR` 
- Equivalence of actions between a raw signature and the coproduct
of its  signatures : `Signatures/RawSigToHAr` 
- pointwise limits and colimits of modules : `Prelims/LModuleColims`
- pointwise limits and colimits of signatures : `Signatures/HSignaturesColims`
- quotient monad : `Prelims/quotientmonad`
- Modularity in the context of a fibration : `Prelims/FibrationInitialPushout`
- Modularity in the specific context of signatures and their representations : `Signatures/Modularity`
          
The fact that algebraic signatures are representable is already proved in
a different setting in the Heterogeneous Substitution System package of UniMaths.
The adaptation to our setting is carried out in the files : `Signatures/HssToSignature` and
`Signatures/BindingSig`

# Summary of files
By folder

## Prelims

- `modules` : complements about modules
- `LModPbCommute` : commutation of the pullback functor (change of base)
        with limits/colimits
    
- `DerivationIsFunctorial` : Proof that derivation of modules is functorial
- `derivadj` : Adjunction in the category of modules over a specific monad R on Set
          Hom(M x R', N) ~ Hom(M , N') 

- `quotientmonad` : the quotient monad construction

- `LModuleColims` : limits and colimits of modules
- `LModuleBinProduct` : direct definition of binary product of modules
- `LModuleCoproducts` : direct definition of coproduct of modules
    There are also direct definitions for specific 

- `CoproductsComplements`, `BinProductComplements`,`lib`, `SetCatComplements` : self-explanatory
- `FibrationInitialPushout` : modularity in the context of a fibration

## Signatures
- `Signature` : definition of  signatures and their actions
- `EpiSigRepresentability` : proof of the technical lemma : epimorphisms of signatures preserves
        representability
- `FullSignatures` : definition of signatures and their actions
- `Signatures` : definition of signatures and their actions
- `PresentableSig` : definition and representability of presentable signatures
- `PresentableSignature` : presentable  signatures are representable.
- `PresentableRawSig` : representability of presentable raw signatures
- `quotientrep` : quotient action construction
- `PresentableHSignatureCoproducts` : a coproduct of presentable  signatures is presentable.
- `PresentableHSignatureBinProdR` : if `a` is presentable, then so is the product of `a` with
  the tautological signature 
- `FullArToRaw`: convert a signature to a raw signature using the adjunction Hom(M x R, N) ~ Hom(M, N')
- `SigEquivRep` : Equivalence of actions between two signatures whose signatures 
     have equivalent actions
- `RawSigToHAr` : equivalence of action between a raw signature and the coproduct of its 
      signatures
- `HssToSignature` : Functor between signatures in the sense of heterogeneous substitution systems
       and our  signatures.
- `BindingSig` : adaptation of the proof in UniMath that algebraic signatures are representable
- `HssSignatureCommutation` : Somme commutation rules between colimits/limits and the 
    functor between signature in the sense of heterogeneous substitution systems and our
    signatures
- `HSignaturesColims` : colimits of  signatures
- `HSignatureBinproducts` : direct definition of bin products of  signatures
- `HSignatureCoproduct` : direct definition of coproducts of  signatures
- `HSignatureDerivation` : derivation of signatures
- `Modularity` : Modularity in the specific context of signatures and their representations
          

