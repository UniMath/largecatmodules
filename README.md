# largecatmodules
Large category of modules over monads on top of UniMath
Signatures and signatures for higher order syntax.

Preliminaries are in the subfolder Modules/Prelims
Signature and Signature related proofs are in the subfolder Modules/Signatures

To compile (coq 8.8): `$ make`



# List of formalized propositions and definitions

- Definition of signatures and their actions : `Signatures/Signature`
- Representability of presentable signatures : `Signatures/PresentableSignature`
- Representability of the codomain epimorphic morphism of signature : `Signatures/EpiSigRepresentability`
- Adjunction in the category of modules over a specific monad R  on Set
          Hom(M x R', N) ~ Hom(M , N') : `Prelims/derivadj.v`
          

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
- `PresentableSignature` : presentable  signatures are representable.
- `quotientrep` : quotient action construction
- `PresentableSignatureCoproducts` : a coproduct of presentable  signatures is presentable.
- `PresentableSignatureBinProdR` : if `a` is presentable, then so is the product of `a` with
  the tautological signature 
- `HssToSignature` : Functor between signatures in the sense of heterogeneous substitution systems
       and our  signatures.
- `BindingSig` : adaptation of the proof in UniMath that algebraic signatures are representable
- `HssSignatureCommutation` : Somme commutation rules between colimits/limits and the 
    functor between signature in the sense of heterogeneous substitution systems and our
    signatures
- `SignaturesColims` : colimits of  signatures
- `SignatureBinproducts` : direct definition of bin products of  signatures
- `SignatureCoproduct` : direct definition of coproducts of  signatures
- `SignatureDerivation` : derivation of signatures
- `Signatures/EpiArePointwise` : epimorphisms of signatures are pointwise epimorphisms
- `Modularity` : Modularity in the specific context of signatures and their models
