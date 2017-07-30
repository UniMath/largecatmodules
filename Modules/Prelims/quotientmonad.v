
Require Import UniMath.Foundations.PartD.

Require Import UniMath.CategoryTheory.Monads.Monads.
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

Local Notation "α ∙∙ β" := (horcomp β α) (at level 20).
Local Notation "'SET'" := hset_category.
Local Notation "F ;;; G" := (nat_trans_comp _ _ _ F G) (at level 35).

Open Scope cat.

    
Set Automatic Introduction.

Section QuotientMonad.

Context {R : Monad SET} {eqrel_equivc : ∏ c, eqrel (R c : hSet)}
        (congr_equivc : ∏ (x y : SET) (f : SET⟦x,y⟧),
                        iscomprelrelfun (eqrel_equivc x) (eqrel_equivc y) (# R f)).

Let equivc {c:hSet} x y := eqrel_equivc c x y.
  
(** We define the quotient functor of R by these equivalence relations

The following comment may be outdated
----
I need to make it not convertible to quot_functor otherwise
Coq takes a long time to check or compute things.
For example :   R' ((R' □ R') c) = (R' □ R') (R' c) by reflexivity
is so slow when R' is definitely equal to quot_functor !
----

*)

Definition R': functor SET SET := quot_functor (pr1 (pr1 R)) _ congr_equivc.

Definition projR : (R:functor _ _) ⟹ R':= pr_quot_functor _ _ congr_equivc.

Arguments projR : simpl never.
Arguments R' : simpl never.

Lemma isEpi_projR_pw : ∏ x, isEpi (projR x).
Proof.
  apply isEpi_pw_pr_quot_functor.
Qed.
  (* TODO: utiliser partout ce lemme où c'est nécessaire *)
Lemma isEpi_projR : isEpi (C:=functor_category _ _) projR.
Proof.
  apply isEpi_pr_quot_functor.
Qed.

Lemma isEpi_projR_projR : isEpi (C:=functor_category _ _) (projR ∙∙ projR).
Proof.
  apply isEpi_horcomp. 
  - apply isEpi_projR.
  - apply isEpi_projR_pw.
Qed.


Lemma eq_projR_rel X x y : projR X x = projR X y -> equivc x y.
Proof.
  use invmap.
  apply (weqpathsinpr_quot_functor (D:=SET) _ _ congr_equivc).
Qed.
Lemma rel_eq_projR X x y : equivc x y -> projR X x = projR X y.
Proof.
  apply (weqpathsinpr_quot_functor (D:=SET) _ _ congr_equivc).
Qed.

Definition R'_η : (functor_identity SET) ⟹ R' := η R ;;; projR .

Lemma R'_η_def : ∏ x, R'_η x =  η R x · projR x.
Proof.
  intro x.
  apply idpath.
Qed.

  (* R'_μ is defined by the following diagram :
<<
                  μ R
            R R  ----->   R
             |           |
 projR projR |     H     | projR
             v           v
            R' R' ---->  R'
                  R'_μ
>>
   *)
(* The following condition is required about the equivalence relation
to make a monad out of R' *)
Definition compat_μ_projR_def 
  := ∏ (X : SET) (x y : pr1 ((pr1 (R □ R)) X)),
     (projR ∙∙ projR) X x = (projR ∙∙ projR) X y →
     (μ R;;; projR) X x = (μ R;;; projR) X y.


Variable compat_μ_projR : compat_μ_projR_def.
  
Definition R'_μ  : R'□  R' ⟹ R'.
Proof.
  apply (univ_surj_nt (A:= R □ R) (B:=functor_composite R' R')                    
                      ( projR ∙∙ projR)
                      (μ  ( R) ;;; projR)).
  (* asbtract these *)
  -  apply compat_μ_projR.
  - apply isEpi_projR_projR.
Defined.

Lemma R'_μ_def : ∏ (x:SET),
                 (projR ∙∙ projR) x · R'_μ x = μ ( R) x · projR x .
Proof.
  intro x.
  unfold R'_μ.
  apply univ_surj_nt_ax_pw.
Qed.

Definition R'_Monad_data : Monad_data SET := ((R' ,, R'_μ) ,, R'_η).

 

Lemma R'_Monad_law_η1 : ∏ c : SET, R'_η (R' c) · R'_μ c = identity (R' c).
Proof.
  intro c.
  use (is_pointwise_epi_from_set_nat_trans_epi _ _ _ (projR)).
  apply isEpi_projR.
  repeat rewrite assoc.
  etrans.
  { apply cancel_postcomposition. 
    unfold R'_η.
    etrans;[apply assoc|].
    apply cancel_postcomposition.
    apply (nat_trans_ax (η  R)).
  }  
  rewrite <- assoc.
  rewrite <- assoc.
  etrans.
  { apply (cancel_precomposition _ _ _ (R' c)).
    cbn.
    apply R'_μ_def.
  }
  rewrite assoc, id_right.
  etrans.
  { apply cancel_postcomposition.
    apply (Monad_law1 (T:=R)). }
  apply id_left.
Qed.

Lemma R'_Monad_law_η2 : ∏ c : SET, # R' (R'_η c) · R'_μ c = identity (R' c).
Proof.
  intro c.
  etrans.
    apply cancel_postcomposition.
    etrans.
    { apply maponpaths.
      apply R'_η_def. }
    apply functor_comp.
    use (is_pointwise_epi_from_set_nat_trans_epi _ _ _ projR).
    apply isEpi_projR.
  repeat rewrite assoc.
  etrans.
    apply cancel_postcomposition.
    apply cancel_postcomposition.
    symmetry.
    apply (nat_trans_ax (projR)).
  rewrite <- assoc.
  rewrite <- assoc.
  etrans.
    apply cancel_precomposition.
    apply R'_μ_def.
  rewrite assoc, id_right.
  rewrite (Monad_law2 (T:=R)).
  now rewrite id_left.
Qed.

Lemma assoc_ppprojR c 
  : (projR ∙∙ projR) ( R c) · # (R' □ R') (projR c)
    = 
    (projR ∙∙ (projR ∙∙ projR)) c.
Proof.
  apply (horcomp_assoc projR projR projR c).
Qed.

Lemma R'_Monad_law_μ : ∏ c : SET,
                             # R' (R'_μ  c) · R'_μ c = R'_μ (R' c) · R'_μ c.
Proof.
  intro c.
 
      (* Note : 

If I write instead :
  assert (epi :isEpi (horcomp projR (horcomp projR projR)  c)).
(convertibly the same by associativity)

then 'apply epi' takes a huge amount of time for Coq !!
This is due to the fact that Coq takes a long time to show that
   ((R' □ R') □ R') c = R' ((R' □ R') c)
because it has a very bad computing strategy. He tries to evaluates R'
which is bad idea. Probably because somewhere there is a Defined instead of 
Qed for some proof, and I suspect somewhere in the section about
quotients in basics/Sets.v

       *)
  assert (epi : isEpi (horcomp (horcomp projR projR) projR c)).
  {
    apply Pushouts_pw_epi.
    apply PushoutsHSET_from_Colims.
    apply isEpi_horcomp.
    apply isEpi_projR_projR.
    apply isEpi_projR_pw.
  }
  apply epi.

      (* To understand the proof, see the string diagram muproof sent to
Benedikt.

Legend of the diagram :
- μ = μ R
- ν = R'_μ
- i = projR
*)      
  etrans.
  (* First equality *)
  etrans.
  apply (assoc (C:=SET)).
  rewrite horcomp_pre_post.
    
  etrans.
  apply cancel_postcomposition. 
  
  etrans.
  apply cancel_postcomposition.
  unfold compose.
  cbn -[R' compose horcomp].
  reflexivity.

  
  rewrite <- assoc.
  
  apply (cancel_precomposition SET).
  rewrite <- (functor_comp (C:=SET) (C':=SET)).
  apply maponpaths.      
  apply R'_μ_def.
  
  rewrite functor_comp,assoc.
  apply (cancel_postcomposition).
  symmetry.
  apply cancel_postcomposition.
  apply (nat_trans_ax (projR)).
  
  (* second equality *)
  etrans.
  rewrite <- assoc.
  rewrite <- assoc.
  apply (cancel_precomposition (SET)).     
  apply (R'_μ_def c).
  
  (* third equality *)
  etrans.
  rewrite assoc.
  
  etrans.
  apply cancel_postcomposition.
  apply (Monad_law3 (T:=R) c).
  
  (* Fourth equality *)
  rewrite <- assoc.
  
  etrans.
  apply cancel_precomposition.
  symmetry.
  apply R'_μ_def.
  
  rewrite assoc.      
  apply cancel_postcomposition.
  
  (* Fifth equality *)
  etrans.
  cbn -[projR compose].
  rewrite (assoc (C:=SET)).
  apply (cancel_postcomposition SET).
  symmetry.
  apply R'_μ_def.
  
  
  (* Close to the end *)
  etrans.
  rewrite <- assoc.
  apply (cancel_precomposition SET).
  symmetry.
  apply (nat_trans_ax (R'_μ) ( R c)).
  
  rewrite assoc.
  reflexivity.
  
  etrans.
  rewrite <- assoc.
  reflexivity.
  
  
  apply cancel_postcomposition.
  
  (* association of horcomposition *)
  apply assoc_ppprojR.
Qed.

Lemma R'_Monad_laws : Monad_laws R'_Monad_data.
Proof.
  repeat split.
  -  apply R'_Monad_law_η1.
  -  apply R'_Monad_law_η2.
  - apply R'_Monad_law_μ.
Qed.

(* Le QED précédent prend énormément de temps.. pourquoi ? *)

Definition R'_monad : Monad _ := _ ,, R'_Monad_laws.

(*

FIN DE LA PREMIERE ETAPE

 *)

Lemma projR_monad_laws: Monad_Mor_laws (T':= R'_monad) projR.
Proof.
  split.
  - intro X.
    symmetry.
    apply R'_μ_def.
  - intro X.
    symmetry.
    apply R'_η_def.
Qed.

Definition projR_monad : Monad_Mor (R) (R'_monad) :=
  (_ ,, projR_monad_laws).

Lemma isEpi_projR_monad : isEpi (C:=category_Monad _) projR_monad.
Proof.    
  apply (faithful_reflects_epis (forgetfunctor_Monad _));
  [ apply forgetMonad_faithful|apply isEpi_projR].
Qed.

  (* FIN DE LA SECONDE ETAPE *)

Variables (S : Monad SET) 
          (m : Monad_Mor R S)
          (compatm : ∏ (X:SET) (x y : (R X : hSet)), 
                     projR X x = projR X y → m X x = m X y).

Local Definition u : nat_trans R' S.
Proof.
  apply (univ_surj_nt projR (m)) ; [| apply isEpi_projR].
  apply compatm.
Defined.

Local Lemma u_def : ∏ x, m x = projR x · u x.
Proof.
  symmetry.
  apply univ_surj_nt_ax_pw.
Qed.

Local Lemma u_monad_laws : Monad_Mor_laws (T:= R'_monad) (T':= S) u.
Proof.
  red.
  split.
  - intro X.
    assert (epi :isEpi ( (horcomp projR projR) X)).
    {
      apply Pushouts_pw_epi.
      apply PushoutsHSET_from_Colims.
      apply isEpi_projR_projR.
    }
    apply epi.
    

    (* Now the real work begins *)
    etrans.
    
    (* use the monadicity of μ *)
    apply cancel_postcomposition.
    apply (nat_trans_ax (projR)).
    etrans.
    
    
        
    rewrite assoc.        
    apply cancel_postcomposition.
    symmetry.
    apply (Monad_Mor_μ (projR_monad)).
    
    (* definition of u *)
    etrans.
    rewrite <- assoc.
    cpre _.
    symmetry.
    apply u_def.
    
    (* m is a morphism of monad *)
    etrans.
    apply (Monad_Mor_μ (m)).
    
    (* Definition of u *)
    etrans.
    
    cpost _.
    etrans.
    etrans.
    cpost _.
    apply u_def.        
    cpre _.
    etrans.
    apply maponpaths.
    apply u_def.
    apply functor_comp.
    
    (* il s'agit de rememmtre les termes dans l'ordre *)
    
    rewrite assoc.
    cpost _.
    rewrite <- assoc.
    cpre _.
    symmetry.
    apply (nat_trans_ax (u )).
    rewrite assoc.
    cbn.
    reflexivity.
  - intro X.
    etrans.
    cpost _.
    apply R'_η_def.
    rewrite <- assoc.
    rewrite <- u_def.
    apply (Monad_Mor_η (m)).
Qed.
Local Definition u_monad : Monad_Mor ( R'_monad) S :=
      (_ ,, u_monad_laws).
End QuotientMonad.
  
Arguments projR : simpl never.
Arguments R' : simpl never.
Arguments u_monad [R _ _] _ [_] _ .