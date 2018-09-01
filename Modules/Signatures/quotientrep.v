
Require Import UniMath.Foundations.PartD.

Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Monads.LModules. 
Require Import UniMath.CategoryTheory.SetValuedFunctors.
Require Import UniMath.CategoryTheory.HorizontalComposition.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.categories.category_hset.
Require Import UniMath.CategoryTheory.categories.category_hset_structures.

Require Import UniMath.CategoryTheory.Categories.

Require Import UniMath.Foundations.Sets.
Require Import UniMath.CategoryTheory.Epis.
Require Import UniMath.CategoryTheory.EpiFacts.

Require Import Modules.Prelims.lib.
Require Import Modules.Prelims.quotientmonad.
Require Import UniMath.CategoryTheory.whiskering.


Local Notation "α ∙∙ β" := (horcomp β α) (at level 20).
Local Notation "α 'ø' Z" := (pre_whisker Z α)  (at level 25).
Local Notation "Z ∘ α" := (post_whisker α Z) (at level 50, left associativity).


Open Scope cat.

    
Set Automatic Introduction.

Section QuotientMonad.

Variable (choice : AxiomOfChoice.AxiomOfChoice_surj).
Context {R : Monad SET}
        {eqrel_equivc : ∏ c, eqrel (R c : hSet)}
        (congr_equivc : ∏ (x y : SET) (f : SET⟦x, y⟧),
                        iscomprelrelfun (eqrel_equivc x) (eqrel_equivc y) (# R f))
        (compat_μ_projR : compat_μ_projR_def congr_equivc).

Let equivc {c:hSet} x y : hProp := eqrel_equivc c x y.
  
(* We define the quotient functor of R by these equivalence relations

The following comment may be outdated
----
I need to make it not convertible to quot_functor otherwise
Coq takes a long time to check or compute things.
For example :   R' ((R' □ R') c) = (R' □ R') (R' c) by reflexivity
is so slow when R' is definitely equal to quot_functor !
----

*)
  (* FIN DE LA SECONDE ETAPE *)

Let R' : SET ⟶ SET
  := R' congr_equivc.
Let projR : (R : SET ⟶ SET) ⟹ quotientmonad.R' congr_equivc
  := projR congr_equivc.
Let R'_monad : Monad SET
  := R'_monad choice congr_equivc compat_μ_projR.
Let projR_monad
  : Monad_Mor R (quotientmonad.R'_monad choice congr_equivc compat_μ_projR)
  := projR_monad choice congr_equivc compat_μ_projR.

Local Notation π := projR_monad.
Local Notation Θ := tautological_LModule.


(*

Let a be a R -module
    b      R'-module

Let τ  : a -> R a R-module morphism
    h  : a -> π^*(b) a R-module morphism (where π := projR)
(this could certainly be generalized to the case where the  codomain of τ is an
arbitrary R-module but we are interested in the category of models)

We want to define a R'-module morphism τ' : b -> R' defined by the following diagram :

<<<<<<<<<<<

        τ
   a ------> R
   |         |
   |         |
 h |         | π
   |         |
   V         V
   b ------> R'
       τ'

>>>>>>>>>>>>

so we need that h is epimorphic (uniqueness) and that
h is compatible with π ∘ τ
   *)

Context {a : LModule R SET}
        {b : LModule R'_monad SET}
        {τ : LModule_Mor _ a (Θ R)}
        {h : LModule_Mor _ a (pb_LModule projR_monad b)}
        (* TODO : define the general type of compatability that is used everywhere to define
            a morphism out of an epimorphism (Cf quotient monad : compat_μ_def ..) *)
        (compath : ∏ X (x y:(a X:hSet)), h X x = h X y -> 
                                         (τ X · projR_monad X) x = (τ X · projR_monad X) y)
        (* TODO : demander que ce soit pointwise epi plutôt *)
        (isEpih : isEpi (C:=[SET,SET]) (h:nat_trans _ _)).

Definition R'_model_τ  : nat_trans b R'.
Proof.
  (* TODO : adapter univ_surj_nt pour que ça demande epi pointwise pour h *)
  apply (univ_surj_nt _ (((τ :nat_trans _ _):[SET,SET]⟦_,_⟧) · (projR_monad:nat_trans _ _)) compath).
  apply isEpih.
Defined.

Local Notation τ' := R'_model_τ.
           
Definition R'_model_τ_def : ∏ X, h X · τ' X = τ X · projR_monad X.
Proof.
  apply (univ_surj_nt_ax_pw _
                            (((τ : nat_trans _ _ ) : [SET,SET]⟦_,_⟧) · (projR_monad : nat_trans _ _))
                            compath
                            isEpih).
Qed.


Local Notation σ := (lm_mult _).

(**

 τ' is a module morphism

This is the following diagram :

<<<<<<<<<<<

          τ' R'
   b R' --------> R' R'
   |               |
   |               |
σ b|               | μ'
   |               |
   V               V
   b ------------> R'
           τ'

>>>>>>>>>>>>

To show this, we post-compose with h·π (horizontal composition)
(see t'_law_eq1 & 2)


  *)


(**
h·π ;; τ' R' ;; μ' = (h ;; τ')·π ;; μ'   ( property of horizontal comp)
                   = (τ ;; π )·π ;; μ'   (definition of τ')
                   = (τ·id) ;; π ·π ;; μ' (propoerty of horizontal comp)
                   = τ R    ;; μ ;; π     (π is a monad morphism)
                   = σ a    ;; τ  ;; π     (τ is a module morphism)
*)
Lemma τ'_law_eq1 X : ((h∙∙projR_monad :[SET,SET]⟦_,_⟧)
                     · (τ' ø R'(* ∘ τ' *):nat_trans _ (functor_composite R' R'))
                     · (μ R'_monad):nat_trans _ _) X =
                     ((σ a:[SET,SET]⟦_,_⟧) · (τ:nat_trans _ _) · projR : nat_trans _ _) X.
Proof.
  etrans.
  { apply cancel_postcomposition.
    etrans.
    { etrans;[eapply pathsinv0; apply assoc|].
      apply cancel_precomposition.
      apply (nat_trans_ax τ').
    }
    etrans; [apply assoc|].
    apply cancel_postcomposition.
    (* definition of τ' *)
    apply R'_model_τ_def.
  }
  repeat rewrite <- assoc.
  etrans.
  { apply cancel_precomposition.
    (* π est un morphisme de moande (par définition) *)
    apply R'_μ_def.
  }
  do 2 rewrite assoc. apply cancel_postcomposition.
  apply (LModule_Mor_σ R τ).
Qed.


(*
And on the other side


h·π ;; σ b ;; τ' = h R ;; R' π ;; σ b ;; τ' (property of horizontal comp)
                 = h R ;; σ (π^* b) ;; τ'   (definition of a pull back module)
                 = σ a ;; h ;; τ'   (h is a module morphism)
                 = σ a ;; τ ;; π    (definition of τ')
*)
Lemma τ'_law_eq2 X : ((h∙∙projR_monad :[SET,SET]⟦_,_⟧)
                     · (σ b)
                     · τ':nat_trans _ _) X =
                     ((σ a : [SET,SET]⟦_,_⟧) · (τ : nat_trans _ _) · projR : nat_trans _ _) X.
Proof.
  etrans.
  { apply cancel_postcomposition.
    apply (LModule_Mor_σ R h). 
  }
  repeat rewrite <- assoc.
  apply cancel_precomposition.
  apply R'_model_τ_def.
Qed.

Lemma R'_model_τ_module_laws 
  : LModule_Mor_laws _ 
                     (T:=b)
                     (T':= tautological_LModule R'_monad)
                     R'_model_τ.
Proof.
  intro X.
  
  (* En vrai, je n'ai pas besoin ici que ce soit un epi pointwise (me semble-t-il)*)
  assert (epi : isEpi (* (C:=functor_Precategory SET SET) *)
                  ((h ∙∙ projR) X)
         ).
  {
    apply isEpi_comp.
    - intro Y.
      apply epi_nt_SET_pw.
      apply isEpih.
    - apply preserves_to_HSET_isEpi.
      + exact choice.
      + apply isEpi_projR_pw.
  }
  apply epi.
  etrans; [ apply τ'_law_eq1 |].
  apply pathsinv0.
  apply τ'_law_eq2.
Qed.    

Definition R'_model_τ_module : LModule_Mor _ b (tautological_LModule R'_monad) 
  := _ ,, R'_model_τ_module_laws.

(** Let S a monad, m : R -> S a monad morphism compatible with the equivalence relation
This induces a monad morphism u : R' -> S that makes the following diagram commute
(Cf quotientmonad)

<<<<<<<<<<<<<
     m
  R --> S
  |     ^
  |    /
π |   / u
  |  /
  V /
  R'

>>>>>>>>>>>>


*)
Context {S : Monad SET}  
        {m : Monad_Mor R S}
        (compatm : ∏ (X : SET) 
                     (x y : (R X : hSet)), projR X x = projR X y → m X x = m X y).

Let u_monad := quotientmonad.u_monad choice compat_μ_projR _ compatm.

(**
Let c be a S-Module
    F : b -> u^*(c) a module morphism.
    s: c -> S a S-module morphism

We also suppose that the following diagram commute (m should be a model
morphism)

<<<<<<<<<<<

               τ
        a  ----------> R
        |              |
        |              |
h ;; F  |              | m
        |              |
        V              V
        c -----------> S
                s

>>>>>>>>>>>>

Then the following diagram commute :

<<<<<<<<<<<

               τ'
        b    --------> R'
        |              |
        |              |
     F  |              | u
        |              |
        V              V
        c -----------> S
                s

>>>>>>>>>>>>

Let us prove this by post-composition by the h : a -> b

h ;; τ' ;; u =  τ ;; π ;; u (definition of τ')
             =  τ ;; m      (definition of u)
             =  h ;; F ;; s      (previous commuting diagram for m)

*)

Context {c : LModule S SET} 
        {s : LModule_Mor _ c (Θ S)}
        {F : LModule_Mor _ b (pb_LModule u_monad c)}.

Variable (compat_m_rep : ∏ X, τ X · m X = h X · F X · s X).


(* j'ai besoin que h est pointwise un epi pour pouvoir montrer cette version pw*)
Lemma u_rep_laws X : F X · s X = τ' X · u_monad X.
Proof.
  assert (epih_pw : forall X, isEpi (h X)).
  {
    apply epi_nt_SET_pw.
    apply isEpih.
  }
  apply epih_pw.
  apply pathsinv0.
  etrans.
  { rewrite assoc.
    apply cancel_postcomposition.
    apply R'_model_τ_def.
  } 
  etrans.
  { rewrite <- assoc.
    apply cancel_precomposition.
    eapply pathsinv0.
    apply quotientmonad.u_def.
  }
  apply compat_m_rep.
Qed.

End QuotientMonad.
