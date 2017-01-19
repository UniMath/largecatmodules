Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.bincoproducts.

Require Import UniMath.CategoryTheory.Monads.
(* Require Import Modules.Prelims.modules. *)
Require Import UniMath.CategoryTheory.RModules.


Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Auxiliary.UnicodeNotations.
Require Import TypeTheory.Displayed_Cats.Auxiliary.
Require Import TypeTheory.Displayed_Cats.Core.
Require Import TypeTheory.Displayed_Cats.Constructions.
Require Import TypeTheory.Displayed_Cats.Fibrations.

Require Import Modules.Prelims.lib.

Local Notation "# F" := (functor_on_morphisms F)(at level 3).
Local Notation "F ⟶ G" := (nat_trans F G) (at level 39).
Local Notation "G □ F" := (functor_composite F G) (at level 35).
Local Notation "F ;;; G" := (nat_trans_comp _ _ _ F G) (at level 35).

(* Trouvé dans SubstitutionsSystem/Notation *)
Notation "α 'ø' Z" := (pre_whisker Z α)  (at level 25).
Notation "Z ∘ α" := (post_whisker α Z) (at level 50, left associativity).

(*
Ltac pr1_norm  :=
  match goal with
    |- context f [pr1 ?T] =>
    let x:=type of (pr1 T) in
    change (pr1 T) with (T:x) (* (RModule_data_from_RModule _ _ T) *)
  end.
 *)
(*
Ltac receq t t' :=
  let u := constr:( ( t , t') )  in
  match u with
    (?f ?x, ?f' ?x') =>
    let h := fresh in
    cut (x=x');[intro h; try rewrite h; clear h;
                receq f f'|]
  | (?x,?x')=>
    let h := fresh in
    cut (x=x');[intro h; try rewrite h; clear h|]
  end.


Ltac my_f_equal :=
  match goal with
  | |- paths ?x ?y => receq x y; try reflexivity
 end.
*)

Ltac pathvia b := (apply (@pathscomp0 _ _ b _ )).

(**
TODO : To be moved in the files Monads and modules

Monads and Modules are more than precategories : they are Precategories (homset property)

*)
Section PrecatModulesMonads.

  Section MonadPrecategory.
    Variable  (C:Precategory).

    (* total_precat_has_homsets *)
    Lemma monad_category_has_homsets : has_homsets (precategory_Monad C (homset_property C)).
      intros F G.
      simpl.

      unfold Monad_Mor.
      apply isaset_total2 .
      apply isaset_nat_trans.
      apply homset_property.
      intros m.

      apply isasetaprop.
      apply isaprop_Monad_Mor_laws.
      apply homset_property.
    Qed.

    Definition monadPrecategory  : Precategory :=
      (precategory_Monad C (homset_property C) ,, monad_category_has_homsets ).

  End MonadPrecategory.

  Section ModulePrecategory.

    (* We don't need the hypothesis that C has homsets *)
    Context {C:precategory} (R:Monad C) (D:Precategory).

    Lemma rmodule_category_has_homsets : has_homsets
                                           (precategory_RModule R D (homset_property D)).
      intros F G.
      simpl.

      apply isaset_total2 .
      apply isaset_nat_trans.
      apply homset_property.
      intros m.

      apply isasetaprop.
      apply isaprop_RModule_Mor_laws.
      apply homset_property.
    Qed.

    Definition rmodulePrecategory  : Precategory :=
      (precategory_RModule R D (homset_property D) ,, rmodule_category_has_homsets ).

  End ModulePrecategory.

End PrecatModulesMonads.


(* The name is self-explainatory : any monad R is a module over R *)
Section TautologicalModule.

  Context {C:precategory} (R:Monad C).



  Definition taut_rmod_data  : RModule_data R C.
    intros.
    exists (pr1 R).
    apply μ.
  Defined.

  Lemma taut_rmod_law  : RModule_laws R (taut_rmod_data ).
  Proof.
    split; intro c.
    - apply Monad_law2.
    - apply Monad_law3.
  Qed.

  Definition taut_rmod : RModule R C := (taut_rmod_data ,, taut_rmod_law ).


End TautologicalModule.


(* Let m : M -> M' a monad morphism.

m induces a functor m* between the category of modules over M' and the category of modules over M

If T is a module over M', we call m* T the pullback module of T along m
*)
Section Pullback_module.
  Context {B:precategory} {M M':Monad B} (m: Monad_Mor M M').

  Context {C:precategory}.

  Variable (T:RModule M' C).

  Definition pbm_σ : T □ M ⟶ T :=  (T ∘ m) ;;; σ _ T.

  Definition pbm_data : Σ F : functor B C, F □ M ⟶ F := tpair _ (T:functor B C) pbm_σ.

  Definition pbm_laws : RModule_laws M pbm_data.
    split.
    - simpl.
      assert (hT1:= RModule_law2 _ (T:=T)).
      assert (hT2:= RModule_law1 _ (T:=T)).
      intro c.
      rewrite <- hT2; clear hT2.
      simpl.
      assert (hm := Monad_Mor_η m).
      rewrite <- hm; clear hm.
      rewrite functor_comp.
      now rewrite assoc.
    - simpl.
      intro c.
      assert (hT1:= RModule_law2 _ (T:=T)).

      assert (hm := Monad_Mor_μ m).
      rewrite assoc.
      rewrite <- (functor_comp T).
      specialize (hm c).
      simpl in hm.
      etrans.
      apply cancel_postcomposition.
      apply cancel_functor_on_morph.
      apply hm.

      rewrite functor_comp.
      rewrite <- assoc.
      etrans.
      apply cancel_precomposition.
      apply hT1.
      repeat rewrite functor_comp.
      assert (hs := nat_trans_ax (σ M' T)).
      
      etrans.
      rewrite <- assoc.
      apply cancel_precomposition.
      rewrite assoc.
      apply cancel_postcomposition.
      apply (nat_trans_ax (σ M' T)).
      now repeat rewrite assoc.
  Qed.

  Definition pullback_module : RModule M C := tpair _ _ pbm_laws.

End Pullback_module.

Tactic Notation "cpre" uconstr(x) := apply (cancel_precomposition x).
Tactic Notation "cpost" uconstr(x) := apply (cancel_postcomposition (C:=x)).
(* Ltac cpre x :=  apply (cancel_precomposition x). *)
(* Ltac cpost x :=  apply (cancel_postcomposition (C:=x)). *)

(*

Let m:M -> M' be a monad morphism et n : T -> T' a morphism in the category of modules over M'.
In this section we construct the morphism m* n : m*T -> m*T' in the category of modules over M
between the pullback modules along m.

*)
Section Pullback_Module_Morphism.

  Context {B} {M M':Monad B} (m:Monad_Mor M M') {C:precategory} {T T' :RModule M' C}
          (n : RModule_Mor _ T T').

  Local Notation pbmT := (pullback_module m T).
  Local Notation pbmT' := (pullback_module m T').

  Lemma pbm_mor_law : RModule_Mor_laws M (T:=pbmT) (T':=pbmT') n.
    intros b.
    set (pbmT := pullback_module m T).
    set (pbmT' := pullback_module m T').
    cbn.
    eapply pathscomp0;revgoals.
    rewrite <-assoc.
    cpre _.
    apply RModule_Mor_σ.    
    repeat rewrite assoc.
    cpost _.
    apply pathsinv0.
    apply nat_trans_ax.
  Qed.

  Definition pbm_mor  : RModule_Mor _  pbmT pbmT'  := ( _ ,, pbm_mor_law).


End Pullback_Module_Morphism.
(*
  (* adds a new equation z = ?x *)
Ltac neweq z :=
  let t := type of z in
  let x := fresh in
  evar (x:t); cut (z=x); subst x; cycle 1.

(* adds a new equation z = ?x and replace z with ?x in the current goal *)
Ltac neweqsubst z :=
  let h := fresh in
  neweq z; [subst z| intro h; rewrite h; clear h z].
*)




(*
Let T be a module on M'.

In this section, we construct the module morphism T -> id* T (which is
actully an iso) where id* T is the pullback module of T along
the identity morphism in M'.

*)
Section Pullback_Identity_Module.

    Context {B} {M':Monad B}  {C:precategory} {T  :RModule M' C}.

    Local Notation pbmid := (pullback_module (Monad_identity M') T).

    Lemma  pbm_id_is_nat_trans  :  is_nat_trans T  pbmid (fun x => identity _).
      red; intros; simpl.
      now rewrite id_right, id_left.
    Qed.

    Definition pbm_id_nat_trans : nat_trans T pbmid  := (_ ,, pbm_id_is_nat_trans).

    Lemma pbm_id_law : RModule_Mor_laws _ (T:=T) (T':=pbmid) pbm_id_nat_trans.
      red.
      intros b; simpl.
      rewrite id_left,id_right.
      etrans.
      cpost _.
      apply Precategories.Functor_identity.
      apply id_left.
    Qed.

    Definition pbm_id  : RModule_Mor _ T pbmid := (_ ,, pbm_id_law) .

End Pullback_Identity_Module.

(*

In this section, we construct the module morphism (which is actually an iso)
between m*(m'*(T'')) and (m o m')*(T'')

*)
Section Pullback_Composition.

   Context {B} {M M':Monad B} (m:Monad_Mor M M') {C:precategory}
     {M'': Monad B} (m' : Monad_Mor M' M'') (T'' : RModule M'' C).

    Local Notation comp_pbm := (pullback_module m (pullback_module m' T'')).
    Local Notation pbm_comp := (pullback_module (Monad_composition m  m') T'').

    Lemma pbm_mor_comp_is_nat_trans
      : is_nat_trans comp_pbm pbm_comp (fun x => identity _).
      red; intros; simpl.
      rewrite id_right.
      rewrite id_left.
      reflexivity.
    Qed.

    Definition pbm_mor_comp_nat_trans := (_ ,, pbm_mor_comp_is_nat_trans ).

    Lemma pbm_mor_comp_law : RModule_Mor_laws (T:=comp_pbm) (T':=pbm_comp) _ pbm_mor_comp_nat_trans.
      intros b; simpl.
      now rewrite id_left,id_right, (functor_comp T''), assoc.
    Qed.

    Definition pbm_mor_comp : RModule_Mor _ comp_pbm pbm_comp := (_ ,, pbm_mor_comp_law).
End Pullback_Composition.


(**
The pullback module/morphism construction allow to construct a large category of modules over monads
where objects are pairs (Monad, Module over this monad).
*)
Section LargeCatMod.

  Context (C:Precategory).


  (* range of modules *)
  Context (D:Precategory).




  Local Notation MONAD := (monadPrecategory C).
  Local Notation MODULE R := (precategory_RModule R _ (homset_property D)).

  Definition bmod_disp_ob_mor : disp_precat_ob_mor MONAD.
  Proof.
    exists (fun R : MONAD => ob (MODULE R)).
    intros xx' yy' g h ff'.
    exact (precategory_morphisms  g ( pullback_module  ff'  h )).
  Defined.

  Definition bmod_id_comp : disp_precat_id_comp _ bmod_disp_ob_mor.
  Proof.
    split.
    - intros x xx.
      simpl.
      apply pbm_id.
    - intros x y z f g xx yy zz ff gg.
      set (pbm_g := pbm_mor f gg).
      set (pbm_gf := (RModule_composition _ pbm_g (pbm_mor_comp f g _))).
      exact (compose ff pbm_gf).
  Defined.


  Definition bmod_data : disp_precat_data _
    := (bmod_disp_ob_mor ,, bmod_id_comp).

  (* Peut etre que c'est le genre de pb qui intéresse André.. Cf utilisation de foo *)
  Lemma bmod_transport (x y : MONAD) (f g : MONAD ⟦ x, y ⟧)
        (e : f = g)
        (xx : bmod_data x)
        (yy : pr1 bmod_data y)
        (ff : xx -->[ f] yy)
        (c : C) : (pr1 (transportf (mor_disp xx yy) e ff) c = pr1 ff c).
  Proof.
    induction e.
    intros.
    apply idpath.
  Qed.


  Lemma bmod_axioms : disp_precat_axioms MONAD bmod_data.
  Proof.
    repeat apply tpair; intros; try apply homset_property.
    - simpl.
      unfold id_disp; simpl.
      apply (invmap ((@RModule_Mor_equiv _ x _ (homset_property D) _ _ _ _  ))).
      apply nat_trans_eq; try apply homset_property.
      intros c; simpl.
      simpl.
      rewrite assoc; simpl.
      apply pathsinv0.
      etrans.
      apply bmod_transport.
      now rewrite id_right,id_left.
    - set (heqf := id_right f).
      apply (invmap ((@RModule_Mor_equiv _ x _ (homset_property D) _ _ _ _  ))).
      apply nat_trans_eq; try apply homset_property.
      simpl.
      intros c.
      rewrite id_right,id_right.
      revert ff.
      induction (heqf).
      intros; simpl.
      reflexivity.
    - set (heqf:= assoc f g h).
      apply (invmap ((@RModule_Mor_equiv _ x _ (homset_property D) _ _ _ _  ))).
      apply nat_trans_eq; try apply homset_property.
      intros c; simpl.
      apply pathsinv0.
      etrans.
      (* set (z:= (ff:nat c ;; gg c ;; hh c). *)
      clearbody heqf.
      apply bmod_transport.
      cbn.
      repeat rewrite id_right.
      rewrite assoc.
      reflexivity.
    - simpl.
      apply rmodule_category_has_homsets.
  Qed.

  Definition bmod_disp : disp_precat MONAD:=
    (bmod_data ,, bmod_axioms).


End LargeCatMod.

Inductive phantom {A:UU} (x:A) :UU := ttp.

Arguments ttp {_} _.

Notation TTP := (ttp _) (only parsing).

(* a category can be viewed as a display category with singletons.
*)
Section LiftCatDispCat.

  Context (C:Precategory).

  Definition liftcat_disp_ob_mor : disp_precat_ob_mor C:=
    ((fun x => phantom x) ,, fun  _ _ _ _ f => phantom f).

  Definition liftcat_id_comp : disp_precat_id_comp _ liftcat_disp_ob_mor.
  Proof.
    split.
    - intros x xx.
      simpl.
      apply  ttp.
    - intros x y z f g xx yy zz ff gg.
      apply ttp.
  Defined.


  Definition liftcat_data : disp_precat_data _
    := (liftcat_disp_ob_mor ,, liftcat_id_comp).

  Lemma uniq_tt (A:UU) (x:A) (y:phantom x): y=ttp x.
    now destruct y.
  Qed.

  Lemma iscontr_ttp (A:UU) (x:A) :iscontr (phantom x).
  Proof.
    intros A x.
    exists (ttp x).
    apply uniq_tt.
  Qed.

  Lemma isasetphantom (A:UU) (x:A) : isaset (phantom x).
  Proof.
    intros A x.
    apply isasetifcontr.
    apply iscontr_ttp.
  Qed.    

  Lemma liftcat_axioms : disp_precat_axioms _ liftcat_data.
  Proof.
    repeat apply tpair; intros; try apply homset_property; try  now rewrite uniq_tt;
      symmetry;    rewrite uniq_tt.
    apply isasetphantom.
  Qed.

  Definition liftcat_disp : disp_precat _ :=
    (liftcat_data ,, liftcat_axioms).


End LiftCatDispCat.

(* Une première définition possible des arités, en tant que functor_lifting

Inconvénient : ce n'est pas démontré dans la bibliothèque DisplayCat que les functor_lifting
forment une catégorie. Il faudra donc démontrer que les arités forment une catégorie.

.*)
Module Arites1.
  Section Arities.

    Variables (C D:Precategory).

    Local Notation MONAD := (monadPrecategory C).
    Local Notation BMOD := (bmod_disp C D).

    (* Définitions des arités *)
    Definition arity := functor_lifting BMOD (functor_identity MONAD).


    (* Preuve que les arités sont right-inverse du foncteur d'oubli bmod -> mon *)
    Lemma right_inverse_arity  (ar:arity ) :
      ((pr1_precat BMOD)□ (lifted_functor ar) )    =  (functor_identity MONAD).
    Proof.
      intros.
      apply subtypeEquality; [| reflexivity].
      red.
      intros;  apply isaprop_is_functor.
      apply homset_property.
    Qed.

    (* Réciproque : si on a un foncteur qui vérifié ça, alors on a un functor lifting qui vaut
lui-même *)

    Section Reciproque.

      Variable (F:functor MONAD (total_precat BMOD)).
      Hypothesis (hF :  ((pr1_precat (bmod_disp C D))□ F) = (functor_identity (monadPrecategory C))).

      Definition ar_inv_ob (x:MONAD): BMOD x.
        intro x.

        unfold BMOD; simpl.
        change x with (functor_identity MONAD x).
        rewrite <- hF.
        exact (pr2 (F x)).
      Defined.

      Definition ar_inv_data : section_disp_data BMOD.
        exists ar_inv_ob.
        intros.
        unfold mor_disp.
        (* Trop dur, il faut faire des transport c'est trop la galère *)
        change f with (#(functor_identity MONAD) f).
        (* rewrite <- hF. *)
      Abort.


    End Reciproque.

  End Arities.
End Arites1.

(* Second way to define an arity
As a display functor over identity between the category of monads seen as a display category
and the large category of representations.

Same inconvenient as before : it is not shown directly in the display_cat lib that functor_over is
a category.

The solution is the following : define an arity as an object in the fiber category over the identity
(which is actually equivalent)

*)
Module Arites2.

  Section Arities.

    Variables (C D:Precategory).

    Local Notation MONAD := (monadPrecategory C).
    Local Notation BMOD := (bmod_disp C D).
    Local Notation LMONAD := (liftcat_disp MONAD).

    (* Définitions des arités *)
    Definition arity2 := functor_over (functor_identity _) LMONAD (bmod_disp C D).

    (* Preuve que les arités sont right-inverse du foncteur d'oubli bmod -> mon *)
    Lemma right_inverse_arity2  (ar:arity2 ) :
      ((pr1_precat BMOD)□ (total_functor ar) )    =  (pr1_precat LMONAD).
    Proof.
      intros.
      apply subtypeEquality; [| reflexivity].
      red.
      intros;  apply isaprop_is_functor.
      apply homset_property.
    Qed.
  End Arities.
End Arites2.





(* large category of representation defined as a display category

Not that contrary to the large category of modules, we do not construct the category of
representations of a specific arity

This is an attempt to use directly the display category construction.
The category of represenations of a specific arity can be retrieved as a fiber category.


Let us recall what it the category of representations of an arity B.
It is a pair (R,m) where R is monad and m a module morphism (on R) m : B(R) -> R.

Now, any morphism of arity F : A -> B induces a functor F* : Rep(B) -> Rep(A) defined by
F*(R,m) = (R, m o (F R))

That's how the large category of representations is built.



*)
Section LargeCatRep.

  Variable (C :Precategory).

  Local Notation MONAD := (monadPrecategory C).
  Local Notation LMONAD := (liftcat_disp MONAD).
  Local Notation BMOD := (bmod_disp C C).
  Local Notation GEN_ARITY := (disp_functor_precat _ _ LMONAD BMOD).
  
  (* Arities are display functors over the identity *)
  Local Notation ARITY :=  (fiber_precategory GEN_ARITY (functor_identity _)).

  Definition arity_Precategory : Precategory :=
    (ARITY,, has_homsets_fiber GEN_ARITY (functor_identity _)).

  (* Preuve que les arités sont right-inverse du foncteur d'oubli bmod -> mon *)
  Lemma right_inverse_arity3  (ar:ARITY )
    :  ((pr1_precat BMOD)□ (total_functor ar) )    =  (pr1_precat LMONAD).
  Proof.
    intros.
    apply subtypeEquality; [| reflexivity].
    red.
    intros;  apply isaprop_is_functor.
    apply homset_property.
  Qed.

  Local Notation Θ := taut_rmod.


  (* a representation is a monad with a module morphisme from arity to itself *)
  Definition rep_ar (ar: ARITY) :=
    Σ (R:MONAD),
    RModule_Mor R (((ar:functor_over _ _ _):functor_over_data _ _ _) R (ttp R) )
                (Θ R).

  Coercion Monad_from_rep_ar (ar:ARITY) (X:rep_ar ar) : MONAD := pr1 X.

  Definition μr {ar:ARITY} (X:rep_ar ar) := pr2 X.

  Definition functor_from_monad (R:MONAD) : functor C C := pr1 (pr1 R).

  Definition functor_from_module {D:precategory} {R:MONAD} (S:RModule R D) : functor C D :=
    pr1 (pr1 S).

  Definition ar_obj (a:ARITY) (M:MONAD)  := pr1 a M (ttp M).

  Delimit Scope arity_scope with ar.
  (* ne marche pas.. *)
  (* Coercion ar_obj : ARITY >-> Funclass. *)
  Notation AO := ar_obj.

  Definition ar_mor (a:ARITY) {M N:MONAD} (f:MONAD  ⟦ M,N ⟧) :
    ((ar_obj a M )  -->[f] (ar_obj a N))%mor_disp.
  Proof.
    simpl.
    intros.
    apply (functor_over_on_morphisms a).
    apply ttp.
  Defined.

  Lemma ar_mor_eq (a:ARITY) {M N:MONAD} (f:MONAD  ⟦ M,N ⟧) :
    @functor_over_on_morphisms
      (monadPrecategory C) (monadPrecategory C)
      (functor_identity (precategory_Monad_data C)) (liftcat_disp (monadPrecategory C))
      (bmod_disp C C) (functor_over_data_from_functor_over a) M N (ttp _) (ttp _) f (ttp _) =
    ar_mor a f .
  Proof.
    reflexivity.
  Qed.

  Notation "# F" := (ar_mor F)
                      (at level 3) : arity_scope.

  Delimit Scope arity_scope with ar.

  Definition armor_ob {a b : ARITY} (f:ARITY⟦a,b⟧) (R:MONAD) :=
    (pr1 (pr1 f R (ttp R))).

  Definition rep_ar_mor_law {a b : ARITY} (M:rep_ar a) (N: rep_ar b) (f: ARITY ⟦ a, b ⟧)
             (g:MONAD ⟦ M, N ⟧) :=
        Π c,  ((μr M) c);; (pr1 g c) =   pr1 (#a g )%ar c ;; armor_ob f N  c ;; μr N c .
        (* or the other way around a g ;;; f N : it is the same thanks to the naturality of f *)
    (* Π c,  ((μr M) c);; (pr1 g c) = armor_ob f M  c ;;  pr1 (#b g )%ar c ;; μr N c . *)

  Lemma isaprop_rep_ar_mor_law {a b : ARITY} (M:rep_ar a) (N: rep_ar b) (f: ARITY ⟦ a, b ⟧)
        (g:MONAD ⟦ M, N ⟧) :
    isaprop (rep_ar_mor_law (M:rep_ar a) (N: rep_ar b) (f: ARITY ⟦ a, b ⟧)
                            (g:MONAD ⟦ M, N ⟧)).
  Proof.
    intros.
    apply impred; intro c.
    apply homset_property.
  Qed.

  Definition rep_ar_mor_mor (a b : ARITY) (M:rep_ar a) (N: rep_ar b) (f: ARITY ⟦ a, b ⟧) :=
    Σ g:MONAD ⟦ M, N ⟧, rep_ar_mor_law  M N f g.

  Lemma isaset_rep_ar_mor_mor (a b : ARITY) (M:rep_ar a) (N: rep_ar b) (f: ARITY ⟦ a, b ⟧) :
    isaset (rep_ar_mor_mor a b M N f).
  Proof.
    intros.
    apply isaset_total2 .
    apply monad_category_has_homsets.
    intros.
    apply isasetaprop.
    apply isaprop_rep_ar_mor_law.
  Qed.

  Coercion monad_morphism_from_rep_ar_mor_mor {a b : ARITY} {M:rep_ar a} {N: rep_ar b}
           {f: ARITY ⟦ a, b ⟧} (h:rep_ar_mor_mor a b M N f) : MONAD ⟦ M, N ⟧
    := pr1 h.

  Definition rep_ar_mor_law1 {a b : ARITY} {M:rep_ar a} {N: rep_ar b}
             {f: ARITY ⟦ a, b ⟧} (h:rep_ar_mor_mor a b M N f) :
    Π c,  ((μr M) c);; (pr1 (pr1 h) c) =   pr1 (#a h )%ar c ;; armor_ob f N  c ;; μr N c 
    (* Π c,  ((μr M) c);; pr1 (monad_morphism_from_rep_ar_mor_mor h) c = *)
    (*       armor_ob f M  c ;;  pr1 (#b (monad_morphism_from_rep_ar_mor_mor h ))%ar c ;; μr N c  *)
    := pr2 h.



  Definition brep_disp_ob_mor : disp_precat_ob_mor ARITY:= (rep_ar,, rep_ar_mor_mor).


  Lemma brep_id_law (a : ARITY) (RM : brep_disp_ob_mor a) :
    (rep_ar_mor_law RM RM (identity _) (Monad_identity _)).
    intros.
    intro c.
    apply pathsinv0.
    etrans.
    apply cancel_postcomposition.
    (* apply id_left *)
    apply id_right.
    etrans.
    apply cancel_postcomposition.
    eapply nat_trans_eq_pointwise.
    apply maponpaths.
    apply (functor_over_id a).
    etrans.
    apply id_left.
    apply pathsinv0.
    apply id_right.
  Qed.

  Definition brep_id  (a : ARITY) (RM : brep_disp_ob_mor a) : RM -->[ identity a] RM.
    intros.
    exists (Monad_identity _).
    apply brep_id_law.
  Defined.

  Lemma transport_disp_mor {C} {d:disp_precat C} {x y : C} {f g : C ⟦ x, y ⟧}
        (e : f = g)
        {xx : d x}     {yy : d y}
        (ff : xx -->[ f] yy)
        (Q : UU)
        (P : Π (z:C ⟦ x, y ⟧) ,xx -->[ z] yy -> Q  )
        :
    (P _ (transportf (mor_disp xx yy) e ff))  = P _ ff.
  Proof.
    destruct e.
    intros.
    apply idpath.
  Qed.



  Lemma eq_ar_pointwise  (a b c : ARITY) ( f : ARITY ⟦ a, b ⟧) ( g : ARITY ⟦ b, c ⟧) (R:MONAD) x :
    armor_ob (f ;; g) R  x = armor_ob f R x ;; armor_ob g R x .
    intros.
    simpl.
    match goal with
    | |- ?x = _ => let t:=type of ( x) in set (typet := t)
    end.
    - unfold compose.
      simpl.
      match goal with
        | |- context g [transportf _ ?eg ?funf'] => set (funf := funf'); set (e:= eg)
      end.

      assert (h:= transport_disp_mor (d:=GEN_ARITY) e (xx:=a) (yy:=c) funf typet).
      etrans.
      assert (h2 := h (fun a b => pr1 (pr1 b R (ttp _)) x)).
      apply h2.
      simpl.
      rewrite id_right.
      reflexivity.
Qed.

  Lemma transport_arity_mor (x y : ARITY) (f g : ARITY ⟦ x, y ⟧)
        (e : f = g)
        (xx : brep_disp_ob_mor x)
        (yy : brep_disp_ob_mor y)
        (ff : xx -->[ f] yy)
        (c : C) :
    pr1 (pr1 (transportf (mor_disp xx yy) e ff)) c = pr1 (pr1 ff) c.
  Proof.
    destruct e.
    intros.
    apply idpath.
  Qed.

  Lemma brep_transport    (x y : ARITY)
        (R S:MONAD)
        (f g : MONAD ⟦ R, S ⟧)
        (e : f = g)
        (* (xx : _ x) *)
        (* (yy : pr1 _ y) *)

        (ff : pr1 x R (ttp _) -->[ f] pr1 y S (ttp _))
        (c : C) :
      pr1 (transportf _ e ff) c  = pr1 ff c .
  Proof.
    intros.
    simpl.
    now induction e.
  Qed.
  (* type de ff ; b (pr1 R) tt -->[ identity (pr1 R) ;; pr1 α] c (pr1 S) tt *)

  (** Defining the composition in brep *)

  Lemma brep_comp_law  (a b c : ARITY) (f : ARITY ⟦ a, b ⟧) (g : ARITY ⟦ b, c ⟧)
             (R : brep_disp_ob_mor a) (S : brep_disp_ob_mor b)    (T : brep_disp_ob_mor c)
             (α:R -->[ f ] S) (β:S -->[g]  T) :
    (rep_ar_mor_law R T (f;;g)
                    ( monad_morphism_from_rep_ar_mor_mor α ;; monad_morphism_from_rep_ar_mor_mor β)).
  Proof.
    intros.
    intros x.
    simpl.

    rewrite assoc.
    etrans.
    apply cancel_postcomposition.
    use rep_ar_mor_law1.
    simpl.

    etrans.
    rewrite <- assoc.
    apply cancel_precomposition.
    use rep_ar_mor_law1.

    simpl.
    (* Cf diagramme à ce point *)

    symmetry.
    etrans.
    apply cancel_postcomposition.

    etrans.
    apply cancel_precomposition.
    (* apply cancel_postcomposition. *)
    apply eq_ar_pointwise.

    apply cancel_postcomposition.
    (* apply (functor_over_comp a). *)
    (* apply cancel_precomposition. *)
    (* set (z := (# ( c))%ar _). *)
    set (z := (# ( a))%ar _).
    neweqsubst z.
    apply(  (@functor_over_comp _ _ _ _ _ (a (* c *))) (pr1 R) (pr1 S) (pr1 T) (ttp _) (ttp _)
                                                     (ttp _)
                                                    (pr1 α) (pr1  β) (ttp _) (ttp _)).

    simpl.
    rewrite ar_mor_eq,ar_mor_eq,id_right.
    reflexivity.

    simpl.

    repeat rewrite assoc.
    apply cancel_postcomposition.
    apply cancel_postcomposition.
    repeat rewrite <- assoc.
    apply cancel_precomposition.
    (* naturality of f (* g *) *)
    simpl in f.
    simpl.
    unfold ar_mor,armor_ob.
    
    (* pr1_norm. *)
    simpl.
    set (z:= pr1 f (* g *)).
    simpl in z.
    unfold nat_trans_over_data in z.
    simpl in z.
    assert (hg := pr2 f (* g *)).
    simpl in hg.
    unfold nat_trans_over_axioms in hg.
    simpl in hg.
    assert (hg':= fun a b c=> hg a b c (ttp _) (ttp _) (ttp _)).    

    evar (A:Monad C).
    evar (B:Monad C).
    evar (m:Monad_Mor A B).
    (* assert (hg'' := hg' (pr1 R) (pr1 S) (pr1 α)). *)
    assert (hg'' := hg' A B m).
    simpl in hg''.
    simpl.
    match type of hg'' with
    | ?a = ?b => set (xa := a) in *; set (xb := b) in *
    end.
    assert (heqx: pr1 xa x = pr1 xb x).
    now rewrite hg''.
    simpl in heqx.
    rewrite id_right in heqx.
    cbn in heqx.
    (* symmetry. *)
    etrans.
    subst A B m.
    apply heqx.
    unfold xb.
    etrans.
    apply brep_transport.
    simpl.
    now rewrite id_right.
  Qed.




  Definition brep_comp (a b c : ARITY) (f : ARITY ⟦ a, b ⟧) (g : ARITY ⟦ b, c ⟧)
             (RMa : brep_disp_ob_mor a) (RMb : brep_disp_ob_mor b)    (RMc : brep_disp_ob_mor c)
             (mab:RMa -->[ f ] RMb) (mbc:RMb -->[g]  RMc) : RMa -->[f;;g] RMc.
    intros.
    exists (pr1 mab;; pr1 mbc).
    apply brep_comp_law.
  Defined.


  Definition brep_id_comp : disp_precat_id_comp _ brep_disp_ob_mor.
  Proof.
    split.
    - apply brep_id.
    - apply brep_comp.
  Defined.


  Definition brep_data : disp_precat_data _
    := (brep_disp_ob_mor ,, brep_id_comp).

  Lemma rep_ar_mor_mor_equiv (a b : ARITY) (R:brep_data a) (S:brep_data b) (f:ARITY  ⟦ a, b ⟧)
        (a b: R -->[ f] S) :
    (Π c, pr1 (pr1 a) c = pr1 (pr1 b) c) -> a = b.
    intros.
    use (invmap (subtypeInjectivity _ _ _ _  )) ; cycle 1.
    use (invmap (Monad_Mor_equiv _ _  _  )) ; cycle 1.
    apply nat_trans_eq.
    apply homset_property.
    assumption.
    apply homset_property.
    intro g.
    apply isaprop_rep_ar_mor_law.
  Qed.



  Lemma brep_axioms : disp_precat_axioms arity_Precategory brep_data.
  Proof.

    repeat apply tpair; intros; try apply homset_property.
    -  apply rep_ar_mor_mor_equiv.
       intros c.
       etrans. apply id_left.
      symmetry.
      apply transport_arity_mor.
    - apply rep_ar_mor_mor_equiv.
      intro c.
      etrans. apply id_right.
      symmetry.
      apply transport_arity_mor.
    - set (heqf:= assoc f g h).
      apply rep_ar_mor_mor_equiv.
      intros c.
      etrans; cycle 1.
      symmetry.
      apply transport_arity_mor.
      cbn.
      now rewrite assoc.
    -  apply isaset_rep_ar_mor_mor.
  Qed.

  Definition brep_disp : disp_precat arity_Precategory :=
    (brep_data ,, brep_axioms).

End LargeCatRep.
