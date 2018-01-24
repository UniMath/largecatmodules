# largecatmodules
Large category of modules over monads on top of UniMaths and TypeTheory
Arities and signatures for higher order syntax.

Preliminaries are in the subfolder Modules/Prelims
Arity and Signature related proofs are in the subfolder Modules/Arities

To compile (coq 8.7): make.



# List of formalized propositions and definitions

- Definition of half-arities and their representations : `Arities/aritiesalt`
- Definition of arities and their representations  : `Arities/FullArities`
- Definition of signatures and their representations  : `Arities/Signature`
- Representability of presentable half-arities : `Arities/PresentableArity`
- Representability of presentable raw signatures : `Arities/PresentableRawSig`
- Representability of the codomain epimorphic morphism of half-arity : `Arities/uniproofalt`
- Adjunction in the category of modules over a specific monad R  on Set
          Hom(M x R', N) ~ Hom(M , N') : `Prelims/derivadj.v`
          

- A coproduct of presentable half arities is presentable : `Arities/PresentableHArityCoproducts` 
- Equivalence of representations between a raw signature and the coproduct
of its half arities : `Arities/RawSigToHAr` 
- pointwise limits and colimits of modules : `Prelims/LModuleColims`
- pointwise limits and colimits of arities : `Arities/HAritiesColims`
- quotient monad : `Prelims/quotientmonad`
          
The fact that algebraic signatures are representable is already proved in
a different setting in the Heterogeneous Substitution System package of UniMaths.
The adaptation to our setting is carried out in the files : `Arities/HssToArity` and
`Arities/BindingSig`

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

- `CoproductsComplements`, `BinProductComplements`,`lib` : self-explanatory

## Arities
- `aritiesalt` : definition of half arities and their representations
- `uniproofalt` : proof of the technical lemma : epimorphisms of half-arities preserves
        representability
- `FullArities` : definition of arities and their representations
- `Signatures` : definition of signatures and their representations
- `PresentableArity` : presentable half arities are representable.
- `Arities/PresentableRawSig` : Representability of presentable raw signatures
- `quotientrep` : quotient representation construction
- `PresentableHArityCoproducts` : a coproduct of presentable half arities is presentable.
- `PresentableHArityBinProdR` : if `a` is presentable, then so is the product of `a` with
  the tautological half-arity 
- `FullArToRaw`: convert an arity to a raw arity using the adjunction Hom(M x R, N) ~ Hom(M, N')
- `SigEquivRep` : Equivalence of representations between two signatures whose arities 
     have equivalent representations
- `RawSigToHAr` : equivalence of representation between a raw signature and the coproduct of its half
      arities
- `HssToArity` : Functor between signatures in the sense of heterogeneous substitution systems
       and our half arities.
- `BindingSig` : adaptation of the proof in UniMath that algebraic signatures are 
    representable
- `HssArityCommutation` : Somme commutation rules between colimits/limits and the 
    functor between signature in the sense of heterogeneous substitution systems and our
    half-arities
- `HAritiesColims` : colimits of half arities
- `HArityBinproducts` : direct definition of bin products of half arities
- `HArityCoproduct` : direct definition of coproducts of half arities
- `HArityDerivation` : derivation of arities
          

