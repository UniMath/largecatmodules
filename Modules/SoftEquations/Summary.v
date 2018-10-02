(** Summary of the formalization (kernel)

Tip: The Coq command [About ident] prints where the ident was defined
 *)


Require Import UniMath.Foundations.PartD.

Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Monads.LModules. 
Require Import UniMath.CategoryTheory.Monads.Derivative.
Require Import UniMath.CategoryTheory.SetValuedFunctors.
Require Import UniMath.CategoryTheory.HorizontalComposition.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.categories.category_hset.
Require Import UniMath.CategoryTheory.categories.category_hset_structures.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.CategoryTheory.Epis.
Require Import UniMath.CategoryTheory.EpiFacts.
Require Import Modules.Prelims.EpiComplements.

Require Import Modules.Prelims.lib.
Require Import Modules.Prelims.quotientmonad.
Require Import Modules.Prelims.quotientmonadslice.
Require Import Modules.Signatures.Signature.
Require Import Modules.Signatures.PreservesEpi.
Require Import Modules.SoftEquations.ModelCat.
Require Import Modules.Prelims.modules.

Require Import Modules.SoftEquations.quotientrepslice.
Require Import Modules.SoftEquations.SignatureOver.
Require Import Modules.SoftEquations.SignatureOverDerivation.
Require Import Modules.SoftEquations.Equation.
Require Import Modules.SoftEquations.quotientrepslice.
Require Import Modules.SoftEquations.quotientequation.

Require Import UniMath.CategoryTheory.limits.initial.
Require Import Modules.SoftEquations.AdjunctionEquationRep.

Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.

Require Import UniMath.CategoryTheory.Subcategory.Core.
Require Import UniMath.CategoryTheory.Subcategory.Full.

Require Import UniMath.SubstitutionSystems.BindingSigToMonad.
Require Import Modules.Signatures.BindingSig.
Require Import Modules.SoftEquations.BindingSig.

Local Notation MONAD := (Monad SET).
Local Notation MODULE R := (LModule R SET).

(**
The command:

Check (x ::= y) 

succeeds if and only if [x] is convertible to [y]

*)
Notation  "x ::= y"  := ((idpath _ : x = y) = idpath _) (at level 70, no associativity).

Fail Check (true ::= false).
Check (true ::= true).

(** *******************

 Definition of a signature

The more detailed definition can be found in Signature/Signature.v

 ****** *)

Check (
    signature_data (C := SET) ::=
      (** a signature assigns to each monad a module over it *)
      ∑ F : (∏ R : MONAD, MODULE R),
            (** a signature sends monad morphisms on module morphisms *)
            ∏ (R S : MONAD) (f : Monad_Mor R S), LModule_Mor _ (F R) (pb_LModule f (F S))
  ).

(** Functoriality for signatures:
- [signature_idax] means that # F id = id
- [signature_compax] means that # F (f o g) = # F f o # F g
 *)
Check (∏ (F : signature_data (C:= SET)),
       is_signature  F ::=
         (signature_idax F × signature_compax F)).

Check (signature SET ::= ∑ F : signature_data, is_signature F).

  (** An epi-signature preserves epimorphicity of natural
      transformations. Note that this is not implied by the axiom of choice
      because the retract may not be a monad morphism.
   *)
Check (∏ (S : signature SET),
       sig_preservesNatEpiMonad S ::=
         ∏ M N (f : category_Monad _⟦M,N⟧),
         isEpi (C := functor_category SET SET) (pr1 f) ->
         isEpi (C:= functor_category SET SET)
               (pr1 (#S f)%ar)).


Local Notation SIGNATURE := (signature SET).

Local Notation BC := BinCoproductsHSET.
Local Notation T := TerminalHSET.

(** *******************

 Definition of a model of a signature

The more detailed definitions of models can be found in Signatures/Signature.v
The more detailed definitions of model morphisms can be found in SoftSignatures/ModelCat.v

 ****** *)

(** The tautological module R over the monad R  (defined in UniMath) *)
Local Notation Θ := tautological_LModule.
Check (∏ (R : MONAD), (Θ R : functor _ _) ::= R).

(** The derivative of a module M over the monad R (defined in UniMath) *)
Local Notation "M ′" := (LModule_deriv unitHSET BC  M) (at level 6).
(** M′ (X) = M′ (1 ⨿ X) where 1 = unit is the terminal object and ⨿ is the
    disjoint union *)
Check (∏ (R : MONAD) (M : LModule R SET) (X : SET),
         (M ′ X) ::= M (setcoprod unitHSET (X : hSet))) .


(**
A model of a signature S is a monad R with a module morphism from S R to R, called an action.
*)
Check (∏ (S : SIGNATURE), model S ::=
    ∑ R : MONAD, LModule_Mor R (S R) (Θ R)).

(** the action of a model *)
Check (∏ (S : SIGNATURE) (M : model S),
       model_τ M ::= pr2 M).

(**
Given a signature S, a model morphism is a monad morphism commuting with the action
*)
Check (∏ (S : SIGNATURE) (M N : model S),
       rep_fiber_mor M N  ::=
         ∑ g:Monad_Mor M N,
             ∏ c : SET, model_τ M c · g c = ((#S g)%ar:nat_trans _ _) c ·  model_τ N c ).


Local Notation  "R →→ S" := (rep_fiber_mor  R S) (at level 6).


(** The category of 1-models *)
Check (∏ (S : SIGNATURE),
       rep_fiber_precategory S ::=
         (precategory_data_pair
            (** the object and morphisms of the category *)
            (precategory_ob_mor_pair (model S) rep_fiber_mor)
            (** the identity morphism *)
            (λ R, rep_fiber_id R)
            (** Composition *)
            (λ M N O , rep_fiber_comp)
           ,,
             (** This second component is a proof that the axioms of categories are satisfied *)
             is_precategory_rep_fiber_precategory_data S)
         ).


(** *******************

 Definition of an S-signature, or that of a signature over a 1-signature S

The more detailed definitions can be found in SoftSignatures/SignatureOver.v

 ****** *)

(**
a signature over a 1-sig S assigns functorially to any model of S a module over the underlying monad.
*)
Check (∏ (S : SIGNATURE),
       signature_over S ::=
         ∑ F :
           (** model -> module over the monad *)
           (∑ F : (∏ R : model S, MODULE R),
                  (** model morphism -> module morphism *)
                  ∏ (R S : model S) (f : R →→ S),
                  LModule_Mor _ (F R) (pb_LModule f (F S))),

               (** functoriality conditions (see SignatureOver.v) *)
               is_signature_over S F).

(** Some examples of 1-signature *)

  (** The tautological signature maps a monad to itself *)
  Local Notation ΣΘ := (tautological_signature_over _).
  (** The n-th derivative of an over signature M *)
  Local Notation "M ^( n )" := (signature_over_deriv_n (C := SET) _ BC T M n) (at level 6).
  (** The n+1-th derivative is the derivative of the n-th derivative *)
  Check (∏ (S : SIGNATURE) (F : signature_over S)(n : nat) (R : model S) (X : hSet),
         F ^(1+n) R  ::= (F ^( n) R) ′).

  (** The 0th derivative does not do anything *)
  Check (∏ (S : SIGNATURE) (F : signature_over S)(n : nat) (R : model S) (X : hSet),
         F ^(0) R  ::= F R).



(**
a morphism of oversignature is a natural transformation
*)
Check (∏ (S : SIGNATURE)
         (F F' : signature_over S),
       signature_over_Mor S F F' ::=
         (** a family of module morphism from F R to F' R for any model R *)
         ∑ (f : (∏ R : model S, LModule_Mor R (F R) (F' R))),
         (** subject to naturality conditions (see SignatureOver.v for the full definition) *)
           is_signature_over_Mor S F F' f
      ).
Local Notation "F ⟹ G" := (signature_over_Mor _ F G) (at level 39).

(** Definition of an oversignature which preserve epimorphisms in the category of natural transformations
(Cf SoftEquations/quotientequation.v).
This definition is analogous to [sig_preservesNatEpiMonad], but for oversignature
rathen than 1-signatures.
 *)
Check (∏ (S : SIGNATURE)
         (F : signature_over S),
       isEpi_overSig F ::=
        ∏ R S (f : R →→ S),
                   isEpi (C := [SET, SET]) (f : nat_trans _ _) ->
                   isEpi (C := [SET, SET]) (# F f : nat_trans _ _)%sigo
       ).

(** Definition of a soft-over signature (SoftEquations/quotientequation.v) 

It is a signature Σ such that for any model R, and any family of model morphisms 
(f_j : R --> d_j), the following diagram can be completed in the category
of natural transformations:

<<<
           Σ(f_j)
    Σ(R) ----------->  Σ(d_j)
     |
     |
     |
 Σ(π)|
     |
     V
    Σ(S)

>>>

where π : R -> S is the canonical projection (S is R quotiented by the family (f_j)_j

 *)
Check (∏ (S : SIGNATURE)
         (** S is an epi-signature *)
         (isEpi_sig : sig_preservesNatEpiMonad S)
         (F : signature_over S)
         (** this is implied by the axiom of choice *)
         (SR_epi : ∏ R : Monad SET, preserves_Epi R -> preserves_Epi (S R)) ,
       isSoft  isEpi_sig SR_epi F
       ::=
         (∏ (R : model S)
            (** implied by the axiom of choice *)
            (R_epi : preserves_Epi R)
            (J : UU)(d : J -> (model S))(f : ∏ j, R →→ (d j))
            X (x y : (F R X : hSet))
            (pi := projR_rep S isEpi_sig R_epi (SR_epi _ R_epi) d f),
          (∏ j, (# F (f j))%sigo X x  = (# F (f j))%sigo X y )
          -> (# F pi X x)%sigo = 
            (# F pi X y)%sigo  )
       ).


(**
  Example of soft S-module: a finite derivative of the tautological signature
 *)
Check (@isSoft_finite_deriv_tauto:
         ∏ (Sig : SIGNATURE)
           (* Sig is an epi-1-signature *)
           (epiSig : sig_preservesNatEpiMonad Sig)
            (** implied by the axiom of choice *)
          (epiSigpw : ∏ R : Monad SET, preserves_Epi R -> preserves_Epi (Sig R))
           (n : nat),
         isSoft epiSig epiSigpw (ΣΘ ^(n))).


(* **********

Definition of Equations. See SoftEquations/Equation.v

************ **)

(** An equation over a signature S is a pair of two signatures over S, and a signature over morphism between them *)
Check (∏ (S : SIGNATURE),
       equation (Sig := S) ::=
    ∑ (S1 S2 : signature_over S), S1 ⟹ S2 × S1 ⟹ S2).

(** Soft equation: the domain must be an epi over-signature, and the target
    must be soft (SoftEquations/quotientequation)
 *)
Check (∏ (S : SIGNATURE)
         (** S is an epi-signature *)
         (isEpi_sig : sig_preservesNatEpiMonad S)
         (** this is implied by the axiom of choice *)
        (SR_epi : ∏ R : Monad SET, preserves_Epi R -> preserves_Epi (S R)),

       soft_equation isEpi_sig SR_epi ::=
        ∑ (e : equation), isSoft isEpi_sig SR_epi (pr1 (pr2 e)) × isEpi_overSig (pr1 e)).

(** Elementary equations: the domain is an epi over-signature, and the target
    is a finite derivative of the tautological signature mapping a model to itself
    (SoftEquations/quotientequation.v).
 *)
Check (∏ (S : SIGNATURE),
     elementary_equation (Sig := S) ::=
         ∑ (S1 : signature_over S)(n : nat),
         isEpi_overSig S1 × half_equation S1 (ΣΘ ^(n)) × half_equation S1 (ΣΘ ^(n))).

(** Elementary equations yield soft equations
 *)
Check (∏ (S : SIGNATURE)
         (** this is implied by the axiom of choice *)
         (SR_epi : ∏ R : Monad SET, preserves_Epi R ->  preserves_Epi (S R))
         (** but not that *)
         epiSig
         (e : elementary_equation),
       (soft_equation_from_elementary_equation epiSig SR_epi e  : soft_equation _ _
       ) ::=
         mk_soft_equation epiSig SR_epi
                          (half_elem_eqs e)  (source_elem_epiSig e)
                          (isSoft_finite_deriv_tauto epiSig SR_epi (target_elem_eq e))).


(** 
Definition of the category of 2-models of a 1-signature with a family of equation.

It is the full subcategory of 1-models satisfying all the equations

See SoftEquations/Equation.v for details

*)

(** a model R satifies the equations if the R-component of the two over-signature morphisms are equal for any
    equation of the family *)
Check (∏ (S : SIGNATURE)
         (** a family of equations indexed by O *)
         O (e : O -> equation (Sig := S))
         (R : model S)
       ,
    satisfies_all_equations_hp e R ::=
         (
           (∏ (o : O),
            (** the first half-equation of the equation [e o] *)
            pr1 (pr2 (pr2 (e o))) R =
            (** the second half-equation of the equation [e o] *)
            pr2 (pr2 (pr2 (e o))) R)
          ,,
            (** this second component is a proof that this predicate is hProp *)
            _)
           ).

(** The category of 2-models  is the full subcategory of the category [rep_fiber_category S]
  satisfying all the equations *)
Check (∏ (S : SIGNATURE)
         (** a family of equations indexed by O *)
         O (e : O -> equation (Sig := S)),

   precategory_model_equations e ::=
    full_sub_precategory (C := rep_fiber_precategory S)
                         (satisfies_all_equations_hp e)).


(** *********************** 

Our main result : if a 1-signature Σ generates a syntax, then the 2-signature over Σ
consisting of any family of soft equations over Σ also generates a syntax
(SoftEquations/InitialEquationRep.v)

*)
Check (@soft_equations_preserve_initiality :
         ∏ 
           (Sig : SIGNATURE)
           (** S is an epi-signature *)
           (epiSig : sig_preservesNatEpiMonad Sig)
           (** this is implied by the axiom of choice *)
           (SR_epi : ∏ R : Monad SET, preserves_Epi R ->  preserves_Epi (Sig R))
           (** A family of equations *)
           (O : UU) (eq : O → soft_equation epiSig SR_epi),
         (** If the category of 1-models has an initial object, .. *)
         ∏ (R : Initial (rep_fiber_category Sig)) , preserves_Epi (InitialObject R : model Sig)
        (** .. then the category of 2-models has an initial object *)
         → Initial (precategory_model_equations eq)).



(** As a corrolary, the case of a family of elementary equations *)
Check (@elementary_equations_preserve_initiality :
         ∏ 
           (Sig : SIGNATURE)
           (** (1) The 1-signature must be an epi-signature
            *)
           (epiSig : sig_preservesNatEpiMonad Sig)
           (** (2) this is implied by the axiom of choice
            *)
           (SR_epi : ∏ R : Monad SET, preserves_Epi R ->  preserves_Epi (Sig R))
           (** A family of equations *)
           (O : UU) (eq : O → elementary_equation (Sig := Sig)),
         (** If the category of 1-models has an initial object, .. *)
         ∏ (R : Initial (rep_fiber_category Sig)) ,
         (** (3) preserving epis (implied by the axiom of choice)
          *)
         preserves_Epi (InitialObject R : model Sig)
        (** .. then the category of 2-models has an initial object *)
         → Initial (precategory_model_equations
                      (fun o => soft_equation_from_elementary_equation epiSig SR_epi (eq o)))).

(** As a corrolary, the case of an algebraic signature with elementary equations
No preservation of epis is needed anymore
 *)
Check (@elementary_equations_on_alg_preserve_initiality
       : ∏
           (S : BindingSig) (Sig := binding_to_one_sigHSET S)
           (O : UU) (eq : O → elementary_equation (Sig := Sig)) ,
         (** .. then the category of 2-models has an initial object *)
         Initial (precategory_model_equations
                    ( fun o => soft_equation_from_elementary_equation
                           (algSig_NatEpi S)
                           (BindingSigAreEpiEpiSig S)
                           (eq o))
      )).

(** With the stronger assumption (implied by the axiom of choice) that
any model preserves epis, , we can prove that
the forgetful functor from 2-models to 1-models has a left adjoint *)
Check (@forget_2model_is_right_adjoint :
         ∏ 
           (Sig : SIGNATURE)
           (** S is an epi-signature *)
           (epiSig : sig_preservesNatEpiMonad Sig)
           (** this is implied by the axiom of choice *)
           (SR_epi : ∏ R : Monad SET, preserves_Epi R ->  preserves_Epi (Sig R))
           (** A family of equations *)
           (O : UU) (eq : O → soft_equation epiSig SR_epi)
         (** The stronger assumption is that any 1-model of Sig preserve epis *)
         (modEpis : (∏ R : model Sig, preserves_Epi R)),
         Adjunctions.is_right_adjoint (forget_2model eq)).

(**


Note that an epimorphic monad morphism may not be epimorphic as a natural transformation.

A natural transformation is epimorphic if and only if it is pointwise epimorphic.
Thus, Hypotheses (2) and (3) are implied by the axiom of choice (because 
any epimorphism has a section). Hypothesis (1) does not seem (at least trivially) implied
by the axiom of choice because one would need that the retract is a monad morphism (and even
I don't know how to use the axiom of choice to yield a natural transformation retration).

Where are the hypotheses (1), (2), (3) used in the proof of the theorem above:

(3) is used:

- to build the multiplication of the quotient monad. Indeed, it is defined as the
completion of the following diagram (so that the canonical projection π is a monad morphism):
<<
                  μ R
            R R  ----->   R
             |           |
         π π |           | π
             v           v
            R' R'        R'
                  
>>
where R' is the quotient monad. This definition requires that π π = R' π ∘ π R = π R' ∘ R π
is an epimorphism, and this is implied by R π being an epi. Hence the requirement that R preserves epis
(since π is indeed an epi, as a canonical projection)

- to show that Σ_R' preserves epi in when showing that 
    the Σ-action of the quotient monad is a module morphism (see diagram (Act) below)


(1) is used:

- to build the Σ-action for the quotient monad. Indeed, it is defined as the completion of the
 following diagram (so that the canonical projection π is a model morphism)

<<
            Σ_π
     Σ_R -----------> Σ_R'
     |                 
     |                 
  τ_R|                 
     |                 
     V                 
     R ------------->  R'
           π
>>
where R' is the quotient monad. This definition requires that Σ π 
is an epimorphism, hence the requirement that Σ sends epimorphic natural transformations
to epimorphisms (π is indeed an epimorphic natural transformation, as a canonical projection)


(2) is used:

- to show that the Σ-action is a module morphism. It is used for the specific
  case of the monad R .
  Indeed, I need to show that the following diagram commutes:
<<
                          
     Σ_R' R' -----------> Σ_R'
        |                 |
        |                 |
        |                 |       (Act)
        |                 |
        |                 |
        V                 V
     R'  R' ----------->  R'
>>
The strategy is to precompose this diagram with Σ_R'(π) in order to use the
fact that the Σ-action for R is a module morphism. This argument requires that
Σ_R'(π) is epi, and this is the case because Σ_R'(π) ∘ Σ_π R = Σ_π R' ∘ Σ_R (π) is epi,
as a composition of epis.


- as a consequence, it is used in the definition of soft equations for any model R
  (because the quotient model is always required  to exist).

*)


