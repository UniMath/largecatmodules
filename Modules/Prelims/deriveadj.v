(* We show that there is an adjunction
Hom(M x R, N) -> Hom(M, N')
[deriv_adj]

The unit of the adjunction is the subtitution operation ([substitution]) M' x R -> M

 *)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Monads.LModules.
Require Import UniMath.CategoryTheory.Monads.Derivative.

Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.

Require Import UniMath.CategoryTheory.Adjunctions.Core.

Require Import Modules.Prelims.lib.
Require Import Modules.Prelims.LModulesComplements.
Require Import Modules.Prelims.LModulesBinProducts.
Require Import Modules.Prelims.DerivationIsFunctorial.
Require Import UniMath.SubstitutionSystems.ModulesFromSignatures.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.UnitorsAndAssociatorsForEndofunctors.
Require Import UniMath.CategoryTheory.categories.HSET.All.


(* Question pour Benedikt : est ce bien utile ce abstract (exact HH) *)
  (** Note that this makes the second component opaque for efficiency reasons *)
(*
  Definition mk_are_adjoints {A B : precategory}
             (F : functor A B) (G : functor B A)
             (eta : nat_trans (functor_identity A) (functor_composite F G))
             (eps : nat_trans (functor_composite G F) (functor_identity B))
             (HH : form_adjunction F G eta eps) : are_adjoints F G.
  Proof.
    exists (eta,,eps).
    abstract (exact HH).
  Defined.
*)

Open Scope cat.

(**
Definition of the substitution operation M' × R -> M as a module morphism.
(this will be the unit of the adjunction).
This is defined as M' x R -> MR -> M
 *)
  Local Notation bpS := BinProductsHSET.
  Local Notation bcpS := BinCoproductsHSET.
  Local Notation T := TerminalHSET.
  Local Notation hsS := has_homsets_HSET. 
Section substitution.
  Context {R : Monad SET}.
  Local Infix "+" := setcoprod : set_scope.
  Local Infix "×" := setdirprod : set_scope.
  Delimit Scope set_scope with set.

  Local Notation bpFunc := (BinProducts_functor_precat _ _ bpS).
  (* Local Notation bcpFunc := (BinCoproducts_functor_precat _ _ bpS hsS). *)
  Local Notation TFunc := (option_functor bcpS T).

  Definition pre_subst_nt_data (M : functor SET SET) (X : hSet)
             (* already known (isasetcoprod) but needed 
  otherwise pre_subst_is_nat_trans does not typecheck*)
             {h : isaset (coprod unit X)}
                                                          :
    (M (coprod unit X ,, h)  × R X  )%set -> (M (R X) : hSet).
  Proof.
    induction 1 as [m t].
    revert m.
    apply (functor_on_morphisms M).
    intros x.
    induction x as [|x].
    - exact t.
    - use (η R X x).
  Defined.


  (**
We must show that the following diagram commutes:
<<<
    x    , t
  M(1+X) × RX --------------> M (1+Y) × RY
         |                            |
         |                            |
pre_sub_X|                            | pre_subst_Y
         |                            |
         |                            |
         V                            V
       MRX    -------------->       MRY
                MRf
>>>
but this is the same as the following diagram, when seeing t as a morphism 1 -> RX
<<<
                M(1+f)
       M(1+X)  -------------->    M (1+Y) 
         |                            |
         |                            |
 M[η,t]  |                            | M[η,Rf∘t]
         |                            |
         |                            |
         V                            V
       MRX    -------------->       MRY
                MRf
>>>
and now we show the same diagram without the application of M
*)
  Lemma pre_subst_is_nat_trans  (M : functor SET SET)  :
    is_nat_trans (BinProductObject _
                    ( bpFunc (TFunc ∙ M ) (R : functor _ _)   ) : functor _ _)
                 ( R ∙ M) (fun X => pre_subst_nt_data M X (h := _)).
  Proof.
    intros a b f .
    apply funextfun.
    intros x.
    induction x as [x t].
    cbn -[isasetcoprod]; unfold pre_subst_nt_data ; cbn -[isasetcoprod].
    etrans;rewrite comp_cat_comp.
    apply idpath.
    
    revert x.
    use toforallpaths.
    do 2 rewrite <- (functor_comp M).
    (* remove the M applicaiton *)
    apply maponpaths.
    apply funextfun.
    intro x1.
    induction x1 as [|x].
    - apply idpath.
    - cbn.
      assert (h := nat_trans_ax (η R) _ _ f).
      apply toforallpaths in h.
      apply h.
  Qed.


  Definition pre_subst_nt (M : functor SET SET) :
    nat_trans (BinProductObject _
                                ( bpFunc (TFunc ∙ M ) (R : functor _ _)   ) : functor _ _)
              ( R ∙ M) :=
    _ ,, (pre_subst_is_nat_trans M).

  Local Notation LMOD_bp := (LModule_BinProducts R bpS).
  Local Notation "∂" := (LModule_deriv_functor (TerminalObject T) bcpS R).
  Local Notation Θ := tautological_LModule.
  Local Notation "×ℜ" := (functor_fix_snd_arg _ _ _  (binproduct_functor  LMOD_bp)
                                              (Θ R)).
  Local Notation σ := (lm_mult _).

  Definition substitution_nt (M : LModule R SET)
    : nat_trans (×ℜ (∂ M) : LModule _ _) M
    := (pre_subst_nt M : [SET, SET]⟦ _ , _⟧) · (σ M).

  Lemma substitution_laws (M : LModule R SET) :
    LModule_Mor_laws R (T := ×ℜ (∂ M) : LModule _ _)
                     (T' :=  M)  (substitution_nt M).
  Proof.
    intro X.
    apply funextfun.
    intros x.
    induction x as [x t].
    cbn in x,t.
    cbn -[isasetcoprod]; unfold pre_subst_nt_data; cbn-[isasetcoprod].
     (*
t : 1 --> RRX
top right is right hand side
<<<
       x         M[t,η]    
    M(1+RX) -----------------------------> MRR X
        |                                     |
        |                                     |
        |                                     | σ_RX
        |                                     |
M[ηi1,Ri2]|                                   M RX 
        |                                     |
        |                                     | σ
        V                                     V
      MR(1+X) --------> M(1+X) ----> MRX ---> MX
                σ_1+X        M[μ∘t,η]     σ
>>>

by naturality of σ_R, we can rewrite the bottom arrow:
<<<
MR(1+X) --------> M(1+X) ----> MRX
          σ_1+X        M[μ∘t,η]  
>>>

as

<<<
MR(1+X) --------> MRRX ----> MRX
         MR[μ∘t,η]      σ_RX
>>>

then we replace σ ∘ σ with M μ ∘ σ
and then we eliminate the application of M

*)
    etrans;revgoals.
    {
    eapply (maponpaths (σ M X)).
    use (fun x x' f => toforallpaths _ _ _ (nat_trans_ax (σ M) x x' f)).
    }
    use (fun c t1 t2  => changef_path _ _ t1 t2 (LModule_law2 _ (T :=M) c) ).
    apply (maponpaths (σ M X)).
    cbn -[isasetcoprod].
    etrans; rewrite comp_cat_comp; [|rewrite comp_cat_comp].
    apply idpath.
    revert x.
    use toforallpaths.
    do 3 rewrite <- (functor_comp M).
    (* On élimine M *)
    apply maponpaths.
    apply funextfun.
    intros x.
    induction x as [p|x]; cbn -[isasetcoprod].
    -  pose (t' := (fun _ => t) : SET ⟦unitset , R (R X)⟧).
      (* 
       i1       
    1 ---> 1 + X
    |         |
 η  |         | η
    V         V           R [μ ∘ t, η]         μ
    R 1 ---> R (1 + X) --------------> R R X --> R X
        Ri1

donc ça donne
1 ---> R 1 ---------> R R R X ------->  R R X --> R X
  η         R t                 R μ          μ
et encoer par naturalité de η,                 
1 ---> R R X ---------> R R R X ------->  R R X --> R X
  t          η t                 R μ             μ
et on utilise les 2 lois de monades
         
*)
      etrans; revgoals.
      {
        rewrite comp_cat_comp.
        rewrite comp_cat_comp.
        rewrite (comp_cat_comp (A := unitset) _ _  p).
        revert p.
        apply toforallpaths.
        rewrite assoc.
        eapply pathsinv0.
      etrans.
      {
         (* eapply (cancel_postcomposition (C := SET)) *)
        match goal with
          |-  ?a · ?c = _ => eapply (cancel_postcomposition (C := SET) a _ c)
        end.
        apply (nat_trans_ax (η R)).
      }
      rewrite  assoc.
      etrans.
      {
        match goal with
          |-  ?a · ?c = _ => eapply (cancel_postcomposition (C := SET) a _ c)
        end.
        etrans.
        {
          rewrite <- assoc.
          eapply (cancel_precomposition (SET) ).
          etrans;[eapply pathsinv0; apply functor_comp|].
          unfold coprod_rect.
          unfold compose at 1.
          simpl.
          apply (functor_comp R t' (μ R X)).
        }
        rewrite assoc.
        match goal with
          |-  ?a · ?c = _ =>
          eapply (cancel_postcomposition (C := SET) a _ c)
        end.
        eapply pathsinv0.
        apply (nat_trans_ax (η R)).
      }
      etrans.
      {
        do 2 rewrite <- assoc.
        match goal with
          |-  ?a · ?c = _ => eapply (cancel_precomposition (SET) _ _ _ c _ a)
        end.
        etrans.
        + match goal with
          |-  ?a · ?c = _ => eapply (cancel_precomposition (SET) _ _ _ c _ a)
          end.
          apply Monad_law3.
        + rewrite  assoc.
          eapply (cancel_postcomposition (C := SET)).
          apply Monad_law1.
      }
      apply idpath.
      }
      apply idpath.
    - etrans;rewrite comp_cat_comp;[|rewrite comp_cat_comp].
      apply idpath.
      revert x.
      use toforallpaths.
      etrans;[apply (Monad_law1 (T:=R))|].
      apply pathsinv0.
      etrans;[|apply (Monad_law2 (T:=R))].
      rewrite assoc.
      apply (cancel_postcomposition (C:=SET)).
      apply pathsinv0.
      etrans;[| apply functor_comp].
      apply idpath.
  Qed.

  Definition substitution (M : LModule R SET)  : LModule_Mor R (×ℜ (∂ M)) M :=
    substitution_nt M ,, substitution_laws M.

  Lemma subst_is_nat_trans : is_nat_trans (∂ ∙ ×ℜ)  (functor_identity _) substitution.
  Proof.
    intros M M' m.
    simpl in M,M',m.
    apply LModule_Mor_equiv;[exact hsS|].
    apply nat_trans_eq;[exact hsS|].
    intro X.
    apply funextfun.
    intro x.
    cbn in x.
    induction x as [x t].
    cbn -[isasetcoprod]; unfold pre_subst_nt_data ; cbn -[isasetcoprod].
    etrans;revgoals.
    {
      assert (h := LModule_Mor_σ _ m X).
      apply toforallpaths in h.
      use h.
    }
    cbn -[isasetcoprod].
    apply maponpaths.
    etrans; rewrite comp_cat_comp.
    apply idpath.
    revert x.
    apply toforallpaths.
    apply pathsinv0.
    apply (nat_trans_ax m). 
  Qed.

  Definition substitution_nat_trans : nat_trans (∂ ∙ ×ℜ) (functor_identity _)
             := substitution ,, subst_is_nat_trans.


End substitution.


(* for the counit, we generalize to any category *)
Section DerivCounit.

  Context {C : category} (R : Monad C)
          (bpC : BinProducts C)
          (T : Terminal C)
          (bcpC : BinCoproducts C).

  Local Notation hsC := (homset_property C).

    
  (* functors that are in stake *)
  Local Notation LMOD_bp := (LModule_BinProducts R bpC).
  Local Notation "∂" := (LModule_deriv_functor (TerminalObject T) bcpC R).
  Local Notation Θ := tautological_LModule.
  Local Infix "××" := (LModule_binproduct bpC) (at level 3).
  Local Notation "×ℜ" := (functor_fix_snd_arg _ _ _  (binproduct_functor  LMOD_bp)
                                              (Θ R)).
  Local Notation LMOD := (category_LModule R C).

  Local Notation bpCC := (BinProducts_functor_precat C C bpC).

  (**
M X ----> M (X + T) x R(X + T)

Mais il ne sait pas que (MxR)' = M' x R' en temps que module, bien que
ça marche en temps que foncteurs
*)
  Local Lemma commutes_binproduct_derivation_laws (M N : LModule  R C) :
    LModule_Mor_laws R (T :=  (∂ M) ×× (∂ N) )(T' := ∂ ( M ×× N) : LModule _ _)
                 (* M N *)
                     (nat_trans_id ((∂ M) ×× (∂ N) )).
  Proof.
    intro x.
    etrans;[apply id_left|].
    apply pathsinv0.
    etrans;[apply id_right|].
    apply pathsinv0.
    apply BinProductOfArrows_comp.
  Qed.


  Local Definition commutes_binproduct_derivation (M N : LModule R C) :
    LModule_Mor R ( (∂ M) ×× (∂ N) )( ∂ ( M ×× N)) :=
    _ ,, commutes_binproduct_derivation_laws M N.


  (* Maybe we can do it in a smarter way but I don't want to bother (using the eta rule)*)

  (* These functors are actually equals, but this is life..*)
  Definition Terminal_EndC_constant_terminal :
    (TerminalObject (Terminal_functor_precat C C T) : functor _ _)
      ⟹ constant_functor C C T  .
  Proof.
    use make_nat_trans.
    exact (fun x => identity T).
    abstract(
        intros x y f;
        rewrite id_left, id_right;
        apply pathsinv0, TerminalArrowUnique).
  Defined.

  (* I have a transfo nat 1 -> 1 + X -> R (1 + X) *)
  (* This morphism is independant from M *)
  Local Definition toR' (M : functor _ _)  : nat_trans M (∂ (Θ R) : LModule _ _).
  Proof.
    set (F := (BinCoproduct_of_functors C C bcpC (constant_functor C C T) (functor_identity C))).
    eapply (compose (C := [C,C]) (b := functor_composite F (functor_identity C))); revgoals.
    - apply pre_whisker.
      exact (η R).
    - eapply compose; [|apply ρ_functors_inv].
      eapply compose; [|apply coproduct_nat_trans_in1].
      eapply compose;[apply (TerminalArrow  (Terminal_functor_precat C _ T)) |].
      apply Terminal_EndC_constant_terminal.
  Defined.

  (* Probably there is a smarter way to prove this by reusing
stuff proved in Derivative of a Module, or by considering coproducts of Modules *)
  Local Lemma toR'_laws  (M : LModule _ _)  : LModule_Mor_laws _ (toR' M).
  Proof.
    intro x.
    simpl.
    repeat rewrite id_right.
    etrans; revgoals.
    {
      repeat rewrite assoc.
      apply cancel_postcomposition.
      apply cancel_postcomposition.
      eapply pathsinv0.
      apply TerminalArrowUnique.
    }
    repeat rewrite <- assoc.
    apply cancel_precomposition.
    (*
Maybe there is a smarter way to prove that the following (outer) diagram commutes.
f := η ∘ in₁_X
Top right is right hand side.
<<<
        f
  T --------------> R(T+X)
  |                  |
in|     composition  |  id
  |                  |   
  V                  V
  T+RX ----------> R(T+X)
  |    [f,Rin₂]      ^
  |                  |   
η |     nat of η     |   μ
  |   & monad law    |   
  V                  |
R(T+RX) -------> RR(T+X)
        R[f,Rin₂]

>>>
*)
    etrans.
    {
      apply cancel_precomposition.
      etrans;[apply assoc|].
      (* η natural & monad law *) 
      etrans.
      - (* η natural *)
        apply cancel_postcomposition.
        eapply pathsinv0.
        apply (nat_trans_ax (η R)).
      - (* Monad law *)
        rewrite <- assoc.
        apply cancel_precomposition.
        apply Monad_law1.
      }
    rewrite id_right.
    apply BinCoproductIn1Commutes.
  Qed.

  Local Definition toR'_MOD  (M : LModule _ _)  : LModule_Mor _ M (∂ (Θ R)) :=
    _ ,, toR'_laws M.
  (* ((∂ (Θ R): LModule _ _) : functor _ _))). *)




  Definition deriv_counit_data (M : LModule R C) : LModule_Mor _ M  ((×ℜ ∙ ∂) M).
  Proof.
    eapply (compose (C := LMOD)); [ | apply commutes_binproduct_derivation].
    apply (( @BinProductArrow LMOD _ _ (LMOD_bp ((∂ M: LModule _ _) )
                                             ((∂ (Θ R): LModule _ _)))) M).
    - apply LModule_to_deriv.
    - apply toR'_MOD.
  Defined.



  Lemma deriv_counit_is_nat_trans : is_nat_trans (functor_identity LMOD) (×ℜ ∙ ∂)
                                                 deriv_counit_data.
  Proof.
    intros M N m.
    apply LModule_Mor_equiv;[exact hsC|].
    apply nat_trans_eq;[exact hsC|].
    intro x.
    unfold compose.
    cbn -[compose BinProductArrow].
    etrans;[apply assoc|].
    etrans;[apply id_right|].
    etrans;[|apply assoc].
    apply pathsinv0.
    etrans;[apply cancel_precomposition;apply id_left|].
    (*
<<<
        toR',toM'
   M  -------------> R' x M'
   |                  |
   |                  |
   |                  |  id x m
m  |                  |
   |                  |
   V                  V
   N --------------> R' x N'
          toR',toM'


>>>


*)
    etrans;[apply postcompWithBinProductArrow|].
    apply pathsinv0.
    etrans;[apply precompWithBinProductArrow|].
    apply map_on_two_paths.
    - cbn.
      repeat rewrite id_left.
      apply pathsinv0.
      apply (nat_trans_ax (m : LModule_Mor _ _ _)).
    - cbn.
      repeat rewrite id_right.
      repeat rewrite assoc.
      apply cancel_postcomposition.
      apply cancel_postcomposition.
      apply TerminalArrowUnique.
  Qed.
  Definition deriv_counit : nat_trans (functor_identity LMOD) (×ℜ ∙ ∂) :=
    deriv_counit_data ,, deriv_counit_is_nat_trans.

End DerivCounit.

Section derivadj.
  Context {R : Monad SET}.
  Local Notation T := TerminalHSET.
  Local Notation bpS := BinProductsHSET.
  Local Notation bcpS := BinCoproductsHSET.
  Local Notation hsS := has_homsets_HSET.
  Local Infix "+" := setcoprod : set_scope.
  Local Infix "×" := setdirprod : set_scope.
  Delimit Scope set_scope with set.
  Local Notation LMOD_bp := (LModule_BinProducts R bpS).
  Local Notation "∂" := (LModule_deriv_functor (TerminalObject T) bcpS R).
  Local Notation Θ := tautological_LModule.
  Local Notation "×ℜ" := (functor_fix_snd_arg _ _ _  (binproduct_functor  LMOD_bp)
                                              (Θ R)).
  Local Notation σ := (lm_mult _).
  Local Notation counit := (deriv_counit R bpS T bcpS).

  Local Lemma counit_subst_adjunction :
    form_adjunction ×ℜ ∂ counit substitution_nat_trans.
  Proof.
    split.
    - intro M.
      cbn in M.
      apply LModule_Mor_equiv;[exact hsS|].
      apply nat_trans_eq;[exact hsS|].
      intro X.
      cbn -[isasetcoprod].
      apply funextfun.
      intro x.
      cbn in x.
      induction x as [x t].
      cbn -[isasetcoprod].
      unfold prodtofuntoprod; cbn -[isasetcoprod].
      unfold make_dirprod; cbn -[isasetcoprod].
      apply dirprod_paths; cbn -[isasetcoprod].
      + do 2 rewrite comp_cat_comp.
        revert x.
        apply toforallpaths.
        rewrite assoc.
        etrans.
        {
          apply (cancel_postcomposition (C := SET)).
          eapply pathsinv0.
          apply (functor_comp M).
        }
        cbn.
        apply (LModule_law1 _ (T := M)).
      + etrans.
        {
          apply maponpaths.
          assert (h := fun x x' f => toforallpaths _  _ _ (nat_trans_ax (η R) x x' f)).
          eapply pathsinv0.
          use h.
        }
        cbn.
        revert t.
        use toforallpaths.
        apply (Monad_law1  (T := R)).
    - intro M.
      cbn in M.
      apply LModule_Mor_equiv;[exact hsS|].
      apply nat_trans_eq;[exact hsS|].
      intro X.
      cbn -[isasetcoprod].
      (* maybe funext is not needed but who cares *)
      apply funextfun.
      intro x.
      cbn -[isasetcoprod]; unfold pre_subst_nt_data; cbn -[isasetcoprod].
      do 2 rewrite comp_cat_comp.
      etrans.
      {
        use (maponpaths (σ M _)); revgoals.
        rewrite comp_cat_comp.
        rewrite <- (functor_comp M).
        apply idpath.
      }
      cbn.
      (*
                M η                      σ
  M (1 + X)  -------------> M R (1 + X) -----> M (1 + X)
       *)
      etrans; revgoals.
      {
        revert x.
        apply toforallpaths.
        apply (LModule_law1 _ (T := M)).
      }
      cbn.
      use maponpaths.
      revert x.
      apply toforallpaths.
      apply maponpaths.
      apply funextfun.
      intro x.
      induction x as [p|x]; cbn.
      + induction p.
        apply idpath.
      + apply idpath.
  Qed.

  Lemma deriv_adj : are_adjoints  ×ℜ ∂.
  Proof.
    use make_are_adjoints.
  - use deriv_counit.
  - apply substitution_nat_trans.
  - exact counit_subst_adjunction.
  Defined.


  
End derivadj.
Section Functoriality.
  Local Notation LMOD_bp := (LModule_BinProducts _ bpS hsS).
  (** A × B → C × D from a map A → C and B → D *)
  Local Infix "×a" :=  (BinProductOfArrows _ (bpS _ _)(bpS _ _) ) (at level 9).
  Local Notation "∂" := (LModule_deriv_functor (TerminalObject T) bcpS hsS _).
  Local Notation Θ := tautological_LModule.


(**
Let f : R -> S be a monad morphism. Then,
<<<
            s_R
 R' x R -----------> R
    |                |
    |                |
f' x|f               | f
    |                |
    V                V
 S' x S -----------> S
           s_S
>>>
 *)
  Lemma functorial_counit_derivadj {R S : Monad SET} (f : Monad_Mor (C := SET) R S) :
      ∏ (X : hSet), (substitution (Θ R) X) · f X = ((f _) ×a (f _)) · (substitution (Θ S) X)  .
  Proof.
    intro X.
    cbn -[compose].
    apply funextfun.
    intros [x' x].
    cbn -[isasetcoprod].
    unfold prodtofuntoprod.
    cbn -[isasetcoprod].
    unfold pre_subst_nt_data.
    cbn -[isasetcoprod].
    assert (h := Monad_Mor_μ f X).
    eapply toforallpaths  in h.
    etrans;[ eapply h|].
    cbn -[isasetcoprod].
    apply maponpaths.
    set (ff := fun x => _).
    set (bp := BinCoproductsHSET).
    assert (h' := nat_trans_ax f (bp unitHSET X) _ ff).
    apply toforallpaths in h'.
    specialize (h' x').
    cbn in h'.
    etrans.
    {
    apply maponpaths.
    apply h'.
    }

    etrans; [ do 2 rewrite comp_cat_comp | rewrite comp_cat_comp; reflexivity ].
    etrans.
    eapply (maponpaths (fun f => f x')).
    apply (cancel_precomposition (SET)).
    eapply pathsinv0.
    apply  (functor_comp S (a := bp unitHSET X) ff (f X)).
    cbn -[isasetcoprod].
    apply (maponpaths (fun f => # S f _)).
    apply funextfun.
    intros [|y]; cbn.
    + reflexivity.
    + assert (hf := (Monad_Mor_η f X)).
      apply toforallpaths in hf.
      use hf.
  Qed.

  End Functoriality.

(* Require Import Modules.Arities.FullArToRaw. *)
(** Hom (M, N') ~ Hom (M x R, N)
so adj1 (id_R') : R' x R → R
 *)
Local Definition adj1 := (fun R M N  => invweq (adjunction_hom_weq
                                                                    (@deriv_adj R) M N
                                                      )).
(* Local Definition test := iso_FAr_full_HAr_rep _ _  _ test1. *)

(* Let us check that conditions to redu full arity to a raw arity are met *)
Local Lemma adj_law1 : (∏ (R S : Monad SET) (f : Monad_Mor R S) (M N : LModule R SET) (A : LModule S SET)
 (u : LModule_Mor R M (Derivative.LModule_deriv TerminalHSET BinCoproductsHSET N))
 (v : LModule_Mor R N (pb_LModule f A)),
 (adj1 R M (pb_LModule f A))
   ((u
     :
     (λ R0 : Monad SET, precategory_LModule R0 SET) R ⟦ M,
     Derivative.LModule_deriv TerminalHSET BinCoproductsHSET N ⟧) · # (LModule_deriv_functor
                                                                         TerminalHSET BinCoproductsHSET
                                                                          R) v) =
 ((adj1 R M N) u
  :
  (λ R0 : Monad SET, precategory_LModule R0 SET) R
  ⟦ (λ R0 : Monad SET, LModule_binproduct BinProductsHSET ) R M
      (tautological_LModule R), N ⟧) · v).
Proof.
  intros R S f M N A u v.
  apply LModule_Mor_equiv;[apply (homset_property SET)|].
  apply nat_trans_eq;[apply (homset_property SET)|].
  intros X.
  apply funextfun.
  intros [x y].
  cbn -[isasetcoprod].
  unfold prodtofuntoprod.
  cbn -[isasetcoprod].
  unfold pre_subst_nt_data.
  cbn -[isasetcoprod].
  assert (h := LModule_Mor_σ R v X).
  eapply toforallpaths  in h.
  etrans;[| apply h].
  cbn -[isasetcoprod].
  apply maponpaths.
  apply maponpaths.
  set (ff := fun x => _).
  set (bp := BinCoproductsHSET).
  apply pathsinv0.
  assert (h' := nat_trans_ax v (bp unitHSET X) _ ff).
  apply toforallpaths in h'.
  set (ux := u X x).
  cbn in ux.
  red in h'.
  cbn in h'.
  eapply h'.
Qed.
Local Lemma adj_law2 :
(∏ (R S : Monad SET) (f : Monad_Mor R S) (M : LModule R SET) (A B : LModule S SET)
   (u : LModule_Mor R M (pb_LModule f A))
   (v : LModule_Mor S A (Derivative.LModule_deriv TerminalHSET BinCoproductsHSET B)),
   (adj1 R M (pb_LModule f B))
     ((u : (λ R0 : Monad SET, precategory_LModule R0 SET) R ⟦ M, pb_LModule f A ⟧) · 
      pb_LModule_Mor f v · (λ (R0 S0 : Monad SET) (f0 : Monad_Mor R0 S0),
                            (* LModPbCommute.pb_deriv_to_deriv_pb_iso *)
                            pb_LModule_deriv_iso
                              TerminalHSET BinCoproductsHSET f0) R
                             S f B) =
   BinProductOfArrows (category_LModule R (make_category SET (homset_property SET)))
     ((λ R0 : Monad SET, LModule_BinProducts R0 BinProductsHSET ) R
        (pb_LModule f A) (pb_LModule f (tautological_LModule S)))
     ((λ R0 : Monad SET, LModule_BinProducts R0 BinProductsHSET ) R M
        (tautological_LModule R))
     (u : (λ R0 : Monad SET, precategory_LModule R0 SET) R ⟦ M, pb_LModule f A ⟧)
     (monad_mor_to_lmodule f
      :
      (λ R0 : Monad SET, precategory_LModule R0 SET) R ⟦ tautological_LModule R,
      pb_LModule f (tautological_LModule S) ⟧) · (λ (R0 S0 : Monad SET) (f0 : Monad_Mor R0 S0),
                                                  binprod_pbm_to_pbm_iso f0) R S f A
                                                   (tautological_LModule S) · 
   pb_LModule_Mor f ((adj1 S A B) v)).
Proof.
  intros.
  apply LModule_Mor_equiv;[apply (homset_property SET)|].
  apply nat_trans_eq;[apply (homset_property SET)|].
  intro X.
  cbn -[isasetcoprod].
  apply funextfun.
  intros[x y].
  apply maponpaths.
  unfold pre_subst_nt_data,prodtofuntoprod; cbn -[isasetcoprod].
  set (ff :=  (fun z => _)).
  set (bp := BinCoproductsHSET).
  assert (h :=  functor_comp B  (a := bp unitHSET _) ff (f X)).
  set (vv := (v X (u X x))).
  cbn in vv.
  apply toforallpaths in h.
  (* match goal with *)
  (*   |- context [# B _ ?zz] => set (uu := zz) end. *)
  specialize (h vv).
  cbn in h.
  unfold vv in h.
  apply pathsinv0.
  etrans;[|apply h].
  apply map_on_two_paths.
  - apply funextfun.
    intros[|z]; cbn.
    +apply idpath.
    + clear h.
      assert (h := Monad_Mor_η f X).
      apply toforallpaths in h.
      apply pathsinv0.
      apply h.
  - apply idpath.
Qed.
