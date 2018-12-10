
(** * Quotient a model by a given set of its slice arrows

Let Σ be an epi 1-signature.
Let R be a 1-model of Σ and (α_i : R → S_i)_i be a (possibly large) family of
1-model morphisms. Then we can construct the quotient monad R' (see
Prelims.quotientmonadslice) which is defined as R'(X) = R(X) / ~
and x ~ y iff for all i, α_i(x) = α_i(y)

This file show that this quotient monad can be given an action so that it induces
a 1-model.

Note:
It is probably possible to generalize in order to factorize this file with the quotient model
built in Signatures/quotienrep.v (note, besides, that they do not use the same category of models: here we
have defined the category of 1-models of a signature, where as there it is retrieved as a fiber category
of the displayed category of 1-models  over 1-signatures). However, I fear that such generalization would
complicate its use.

 *)

Require Import UniMath.Foundations.PartD.

Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Monads.LModules. 
Require Import UniMath.CategoryTheory.SetValuedFunctors.
Require Import UniMath.CategoryTheory.HorizontalComposition.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.categories.HSET.All.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.CategoryTheory.Epis.
Require Import UniMath.CategoryTheory.EpiFacts.

Require Import Modules.Prelims.lib.
Require Import Modules.Prelims.LModulesComplements.
Require Import Modules.Prelims.quotientmonad.
Require Import Modules.Prelims.quotientmonadslice.
Require Import Modules.Signatures.Signature.
Require Import Modules.Signatures.PreservesEpi.
Require Import Modules.Prelims.EpiComplements.
Require Import Modules.Signatures.ModelCat.


Open Scope cat.


(** TODO : move this section in Prelims/..
and use thees results to shorten quotienrep (or don't do that because we don't care about
this old presentable stuff 
 *)
Section univ_mod.
  Context {C  : category}{R : Monad C}.
  Local Notation MOD := (category_LModule R SET).
  Context {M N O : LModule R SET} (p : LModule_Mor _ M N) (f : LModule_Mor _ M O).
  (**
completion of the diagram with an arrow from N to O
<<
         p
   M -------->> N
   |
   |
 f |
   |
   V
   O
>>
*)
  Context (compat : (∏ (X : C) (x y : (M X : hSet)), p X x = p X y → f X x = f X y)).

  Lemma univ_surj_lmod_laws
        (epip : isEpi (C := [C, SET]) (p : nat_trans M N))
    :
    LModule_Mor_laws R (univ_surj_nt p f compat epip).
  Proof.
    intro c.
    assert (epip' := epip).
    eapply epi_nt_SET_pw in epip'.
    eapply epip'.
    rewrite assoc.
    rewrite univ_surj_nt_ax_pw.
    rewrite LModule_Mor_σ.
    rewrite assoc.
    rewrite (LModule_Mor_σ R p).
    rewrite <- assoc.
    apply cancel_precomposition.
    apply pathsinv0.
    apply univ_surj_nt_ax_pw.
  Qed.

  (** Note that a module morphism is epimorphic iff it is as a natural transformation
     (and thus pointwise)
   *)
  Definition univ_surj_lmod_nt_epi epip : LModule_Mor R N O := _ ,, univ_surj_lmod_laws epip.

      
End univ_mod.

(** Now we do the same when N and O are modules over another monad S
and there is a morphism of monads m : R -> S such that # M (m X) is epimorphic
for any set X.
 *)
Section univ_pb_mod.
  Context {C  : category}{R S : Monad C}.
  Local Notation MOD Mon := (category_LModule Mon SET).
  Context {M : LModule R SET}.
  Context {N O : LModule S SET}.
  Context (m : Monad_Mor R S)
          (epim_pw : ∏ c, isEpi (# N (m c))).
  Context (p : LModule_Mor R M (pb_LModule m N)) (f : LModule_Mor _ M (pb_LModule m O)).
  Context (compat : (∏ (X : C) (x y : (M X : hSet)), p X x = p X y → f X x = f X y)).


  (**
By the previous section, we get a R-module morphism from N to O.
But here, we want a S-module morphism. Hence, we need an additional hypothesis, namely that #N m is epi
         p
   M -------->> m*N
   |
   |
 f |
   |
   V
   m*O
*)

  Lemma univ_surj_pb_lmod_laws 
        (epip : isEpi (C := [C, SET]) (p : nat_trans M N)) :
          LModule_Mor_laws S (univ_surj_nt p f compat epip).
  Proof.
    intro c.

    apply epim_pw.
    etrans; [ | apply (univ_surj_lmod_laws p f compat epip)].
    etrans.
    {
      etrans;[apply assoc|].
      apply cancel_postcomposition.
      apply nat_trans_ax.
    }
    reflexivity.
  Qed.

  (** Note that a module morphism is epimorphic iff it is as a natural transformation
     (and thus pointwise)
   *)
  Definition univ_surj_pb_lmod_nt_epi epip : LModule_Mor S N O := _ ,, univ_surj_pb_lmod_laws epip.

      
End univ_pb_mod.

    
Local Notation  "R →→ S" := (rep_fiber_mor R S) (at level 6).

Section QuotientRep.

  Local Notation MOD Mon := (category_LModule Mon SET).
Local Notation MONAD := (Monad SET).
Local Notation SIG := (signature SET).

Context (Sig : SIG).
(** The 1-signature must preserves epimorphicity of natural transformations *)
Context (epiSig : sig_preservesNatEpiMonad Sig).

(** implied by the axiom of choice *)
(* Context (epiSigpw : ∏ (R : Monad _), preserves_Epi R -> preserves_Epi (Sig R)). *)

Local Notation REP := (model Sig).
Local Notation REP_CAT := (rep_fiber_category Sig).

Context {R : REP}.
Context (R_epi : preserves_Epi R).
Context (epiSigR : preserves_Epi (Sig R)).
Context {J : UU} (d : J -> REP)
          (ff : ∏ (j : J),  R →→ (d j)).

Let R' : Monad SET := R'_monad R_epi d ff.
Let projR : Monad_Mor R R' := projR_monad R_epi d ff.

Lemma epiSigR' : preserves_Epi (Sig R').
Proof.
  intros a b f epif.
  use (isEpi_precomp SET (# Sig projR _)%ar).
  rewrite <- (nat_trans_ax (#Sig projR)%ar).
  apply isEpi_comp.
  - apply epiSigR; exact epif.
  - apply epi_nt_SET_pw.
    apply epiSig.
    apply isEpi_projR.
Qed.

  

Local Notation π := projR.
Local Notation Θ := tautological_LModule.

Lemma R'_action_compat :
  ∏ (X : SET) (x y : (Sig R) X : hSet),
  (# Sig)%ar projR X x = (# Sig)%ar projR X y
  → ((model_τ R : MOD R ⟦ Sig (pr1 R), Θ (pr1 R) ⟧) · monad_mor_to_lmodule projR : LModule_Mor _ _ _) X x =
    ((model_τ R : MOD R ⟦ Sig (pr1 R), Θ (pr1 R) ⟧) · monad_mor_to_lmodule projR : LModule_Mor _ _ _) X y.
Proof.
  - intros X x y eq.
    apply rel_eq_projR.
    intro j.
    rewrite comp_cat_comp.
    rewrite comp_cat_comp.
    eapply changef_path.
    + etrans;[|apply (!(rep_fiber_mor_ax (ff j) _))].
      rewrite (quotientmonadslice.u_monad_def R_epi d ff j ).
      rewrite signature_comp.
      reflexivity.
    + cbn.
      apply maponpaths.
      apply maponpaths.
      exact eq.
Qed.

(** R' can be given an action such that the following diagram commutes

<<
            Sig_π
   Sig_R ---------> Sig_R'
     |                 |
     |                 |
  τ_R|                 |
     |                 |
     V                 V
     R ----------->    R'
           π
          
>>
 *)
Definition R'_action : LModule_Mor R' (Sig R') (Θ R').
Proof.
  use (univ_surj_pb_lmod_nt_epi
         projR
         _ (# Sig projR)%ar
         ((model_τ R : MOD R ⟦_,_⟧ ) · (monad_mor_to_lmodule projR ))
      ); revgoals.
  - apply epiSig.
    apply isEpi_projR.
  - apply R'_action_compat.
  - intro c.
    apply epiSigR'.
    apply isEpi_projR_pw.
Defined.

Definition R'_model : model Sig := R' ,, R'_action.

(** π is a morphism of model *)
Lemma π_rep_laws : rep_fiber_mor_law R R'_model projR.
Proof.
  intro x.
  cbn -[compose].
  apply pathsinv0.
  use univ_surj_nt_ax_pw.
Qed.

Definition projR_rep : R →→ R'_model := projR ,, π_rep_laws.

Lemma isEpi_projR_rep : isEpi (C := REP_CAT) projR_rep.
Proof.
  intros f g h e.
  apply rep_fiber_mor_eq_nt.
  apply isEpi_projR.
  exact (maponpaths (fun (x : _ →→ _) => (x : nat_trans _ _)) e).
Qed.


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

Let u := u_monad R_epi d ff.


(** u is a morphism of 1-model *)
Lemma u_rep_laws j : rep_fiber_mor_law R'_model (d j) (u j).
Proof.
  intro c.
  do 2 rewrite nat_trans_comp_pointwise'.
  apply nat_trans_eq_pointwise.
  apply (epiSig _ _ projR ).
  { apply isEpi_projR. }
  (* TODO: ne pas repasser en pointwise *)
  apply nat_trans_eq; [apply homset_property|].
  intro X.
  etrans.
  {
    etrans;[ apply assoc|].
    etrans.
    {
      apply cancel_postcomposition.
      (* TODO : faire une version non pointwise de ce lemme *)
      apply (! (rep_fiber_mor_ax projR_rep _)).
    }
    rewrite <- assoc.
    apply cancel_precomposition.
    apply pathsinv0.
    apply (u_def d ff j).
  }
  etrans; [apply rep_fiber_mor_ax|].
  rewrite assoc.
  apply cancel_postcomposition.
  
  rewrite (u_monad_def R_epi  d ff).
  rewrite signature_comp.
  reflexivity.
  (* simpl. *)
  (* apply (cancel_precomposition SET). *)
  (* apply id_right. *)
Qed.


(** Any morphism from [R] to d_j factors through the canonical projection R -> R' *)
Definition u_rep j :  R'_model →→ (d j) := u j ,, u_rep_laws j.

Lemma u_rep_def (j : J)  : ff j = (projR_rep : REP_CAT ⟦_,_⟧) · (u_rep j).
Proof.
  apply rep_fiber_mor_eq_nt.
  apply (quotientmonad.u_def_nt).
Qed.


End QuotientRep.
