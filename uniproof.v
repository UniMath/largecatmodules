
Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.bincoproducts.

Require Import UniMath.CategoryTheory.Monads.
Require Import Largecat.modules.
(* Require Import UniMath.CategoryTheory.Modules. *)


Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Auxiliary.UnicodeNotations.
Require Import TypeTheory.Displayed_Cats.Auxiliary.
Require Import TypeTheory.Displayed_Cats.Core.
Require Import TypeTheory.Displayed_Cats.Constructions.
Require Import TypeTheory.Displayed_Cats.Fibrations.

Local Notation "# F" := (functor_on_morphisms F)(at level 3).
Local Notation "F ⟶ G" := (nat_trans F G) (at level 39).
Local Notation "G □ F" := (functor_composite F G) (at level 35).
Local Notation "F ;;; G" := (nat_trans_comp _ _ _ F G) (at level 35).

(* Trouvé dans SubstitutionsSystem/Notation *)
Notation "α 'ø' Z" := (pre_whisker Z α)  (at level 25).
Notation "Z ∘ α" := (post_whisker α Z) (at level 50, left associativity).


        Ltac pr1_norm  := match goal with
                       |- context f [pr1 ?T] =>
                       let x:=type of (pr1 T) in
                       change (pr1 T) with (T:x) (* (RModule_data_from_RModule _ _ T) *)
                     end.

        Ltac receq t t' :=
          let u := constr:(t,t') in
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


Ltac pathvia b := (apply (@pathscomp0 _ _ b _ )).

Section Pullback_module.
  Context {B:precategory} {M M':Monad B} (m: Monad_Mor M M').

  Context {C:precategory}.

  Variable (T:RModule M' C).

  Definition pbm_σ : T □ M ⟶ T :=  (T ∘ m) ;;; σ _ T.

  Definition pbm_data : Σ F : functor B C, F □ M ⟶ F := tpair _ (T:functor B C) pbm_σ.



  Definition pbm_laws : RModule_laws M pbm_data.
    split.
    - simpl.
      (* repeat autorewrite with coercions. *)
      (* rewrite functor_data_from_functorE. *)
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
      repeat pr1_norm.
      rewrite hm; clear hm.
      rewrite functor_comp.
      rewrite <- assoc.
      specialize (hT1 c).
      simpl in hT1.
      simpl.
      rewrite hT1; clear hT1.
      repeat rewrite functor_comp.

      assert (hs := nat_trans_ax (σ M' T)).
      simpl.
      simpl in hs.
      repeat rewrite assoc.
      my_f_equal.
      repeat rewrite <- assoc.
      rewrite <- hs.
      reflexivity.
Qed.


  Definition pullback_module : RModule M C := tpair _ _ pbm_laws.





End Pullback_module.


Definition pbm_mor {B} {M M':Monad B} (m:Monad_Mor M M') {C:precategory} {T T' :RModule M' C} (n : RModule_Mor _ T T') : RModule_Mor _ (pullback_module m T) (pullback_module m T').

  intros.
  exists n.
  intros b.

  set (pbmT := pullback_module m T).
  set (pbmT' := pullback_module m T').

  assert (hn:= RModule_Mor_σ _ n b).
  simpl in hn.
  revert hn.
  pr1_norm ;  simpl.
  intros hn.
  rewrite <- assoc.
  rewrite <- hn.
  clear hn.
  repeat rewrite assoc.
  my_f_equal.
  rewrite (nat_trans_ax n).
  reflexivity.
Defined.

Lemma is_nat_trans_id_pw {B C} {F G:functor B C} (f:Π x : B, C ⟦ F x, G x ⟧) (heq: Π x,  F x = G x) (heqf:Π x, f x = transportf (fun A =>  C ⟦ F x, A ⟧) (heq x) (identity (F x) )) : is_nat_trans F G f.
  intros.
  red.
  intros b b' g.
  rewrite heqf.
  rewrite heqf.
  clear heqf.
  simpl.
  assert  (tr:= fun P Q f=> transport_map(P:=P) (Q:=Q)f (heq b)).
  simpl.
Abort.
(*
  rewrite transportf_fun.
  unfold heq.
  rewrite transportf_id2.
  set (Q:=(λ A : C, C ⟦ F b, A ⟧)).
  assert (tr2 :=  tr (fun _ => unit) Q).
  set (f' := fun (z:C) _  => identity z : Q z).
  simpl in tr2.
  (fun z _ => identity z) tt).
  rewrite tr2.
*)

  Definition pbm_mor_comp_nat_trans {B} {M M' M'':Monad B} (m:Monad_Mor M M') (m':Monad_Mor M' M'') {C:precategory} {T :RModule M'' C} : (pullback_module m (pullback_module m' T)) ⟶ pullback_module (Monad_composition m  m') T.
    intros.
  exists (fun x => identity _).
  red; intros; simpl.
  rewrite id_right.
  rewrite id_left.
  reflexivity.
Defined.

  Definition pbm_mor_comp {B} {M M' M'':Monad B} (m:Monad_Mor M M') (m':Monad_Mor M' M'') {C:precategory} {T :RModule M'' C} : RModule_Mor _ (pullback_module m (pullback_module m' T))  (pullback_module (Monad_composition m  m') T).
    intros.
    exists (pbm_mor_comp_nat_trans m m').
     intros b; simpl.
     rewrite id_left,id_right.
     rewrite (functor_comp T).
     rewrite assoc.
     reflexivity.
  Defined. (* would be a HUGE mistake to put Qed here *)

(*
  unfold pullback_module.
  use subtypeEquality_prop.
  use total2_paths.

  Search
  -
 *)

(* Maybe reuse pbm_mor_comp_nat_trans *)
Definition pbm_id_nat_trans {B} {M :Monad B}  {C:precategory} {T :RModule  M C} : T ⟶ pullback_module (Monad_identity M) T.
  intros.
  exists (fun x => identity _).
  red; intros; simpl.
  rewrite id_right.
  rewrite id_left.
  reflexivity.
Defined.

Definition pbm_id {B} {M :Monad B}  {C:precategory} {T :RModule  M C}  : RModule_Mor _ T (pullback_module  (Monad_identity M)  T) .
  intros.
  exists pbm_id_nat_trans.
  red.
  intros b; simpl.
  rewrite id_left,id_right.
  pr1_norm.
  rewrite Precategories.Functor_identity.
  rewrite id_left.
  reflexivity.
Defined.

Section LargeCatMod.

  Context (C:Precategory).


  (* range of modules *)
  Context (D:Precategory).




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

    Lemma rmodule_category_has_homsets (R:Monad C): has_homsets (precategory_RModule R D (homset_property D)).
    intros R F G.
    simpl.


    apply isaset_total2 .
    apply isaset_nat_trans.
    apply homset_property.
    intros m.

    apply isasetaprop.
    apply isaprop_RModule_Mor_laws.
    apply homset_property.
  Qed.


    Definition monadPrecategory : Precategory := (precategory_Monad C (homset_property C) ,, monad_category_has_homsets).


  Local Notation MONAD := monadPrecategory.
  Local Notation MODULE R := (precategory_RModule R _ (homset_property D)).
          (* Search (_ -> isaset _). *)
        (* apply impred_isaset. *)
    (* apply isaset_total2_subset. *)
    (* apply isaset_total2_hSet. *)

Definition bmod_disp_ob_mor : disp_precat_ob_mor MONAD.
Proof.
  exists (fun R : MONAD => ob (MODULE R)).
  intros xx' yy' g h ff'.
    exact (precategory_morphisms (* (C:= MODULE xx') *) g ( pullback_module  ff'  h )).
Defined.

Definition bmod_id_comp : disp_precat_id_comp _ bmod_disp_ob_mor.
Proof.
  split.
  -
    intros x xx.
    simpl.
    apply pbm_id.

  - intros x y z f g xx yy zz ff gg.
    set (pbm_g := pbm_mor f gg).
    set (pbm_gf := (RModule_composition _ pbm_g (pbm_mor_comp f g ))).
    exact (compose ff pbm_gf).
Defined.


Definition bmod_data : disp_precat_data _
:= (bmod_disp_ob_mor ,, bmod_id_comp).

(* Peut etre que c'est le genre de pb qui intéresse André.. Cf utilisation de foo *)
Lemma foo (x y : MONAD) (f g : MONAD ⟦ x, y ⟧)
  (e : f = g)
  (xx : bmod_data x)
  (yy : pr1 bmod_data y)
  (ff : xx -->[ f] yy)
  (c : C) :
  (pr1 (transportf (mor_disp xx yy) e ff)) c = pr1 ff c.
Proof.
  destruct e.
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
    etrans. Focus 2. eapply pathsinv0.
      apply  foo.
   cbn. simpl. unfold pbm_mor_comp.
      unfold transportb.
      rewrite id_left.
      rewrite id_right.
      apply idpath.
  - (* this is for Ambroise *)

    set (heqf := id_right f).
     apply (invmap ((@RModule_Mor_equiv _ x _ (homset_property D) _ _ _ _  ))).
     apply nat_trans_eq; try apply homset_property.
     simpl.
     intros c.
     rewrite id_right,id_right.
    revert ff.

    destruct (heqf).
    intros; simpl.
    reflexivity.
  - set (heqf:= assoc f g h).
     apply (invmap ((@RModule_Mor_equiv _ x _ (homset_property D) _ _ _ _  ))).
     apply nat_trans_eq; try apply homset_property.
     intros c; simpl.
     (* rewrite id_right,id_right. *)
     (* rewrite assoc. *)
     etrans; cycle 1.
     (* set (z:= (ff:nat c ;; gg c ;; hh c). *)
     symmetry.

     clearbody heqf.

(* impossible de faire un destruct ici... *)

     apply foo.
     simpl.
     repeat rewrite id_right.
     rewrite assoc.
     reflexivity.
  - simpl.
    apply rmodule_category_has_homsets.
Qed.

Definition bmod_disp : disp_precat MONAD:=
   (bmod_data ,, bmod_axioms).


End LargeCatMod.


(* a category can be viewed as a display category with singletons. But useless since there
are already lifting functors in the Display Category library *)
Section LiftCatDispCat.

  Context (C:Precategory).


Definition liftcat_disp_ob_mor : disp_precat_ob_mor C.
Proof.
  exists (fun R : C => unit).
  intros xx' yy' g h ff'.
  exact unit.
    (* exact (precategory_morphisms (* (C:= MODULE xx') *) g ( pullback_module  ff'  h )). *)
Defined.

Definition liftcat_id_comp : disp_precat_id_comp _ liftcat_disp_ob_mor.
Proof.
  split.
  -
    intros x xx.
    simpl.
    exact tt.


  - intros x y z f g xx yy zz ff gg.
    exact tt.
Defined.


Definition liftcat_data : disp_precat_data _
:= (liftcat_disp_ob_mor ,, liftcat_id_comp).

Lemma uniq_tt (x:unit) : x=tt.
  now destruct x.
Qed.
Lemma liftcat_axioms : disp_precat_axioms _ liftcat_data.
Proof.

  repeat apply tpair; intros; try apply homset_property; try  now rewrite uniq_tt;   symmetry;    rewrite uniq_tt.
  exact isasetunit.
Qed.

Definition liftcat_disp : disp_precat _ :=
   (liftcat_data ,, liftcat_axioms).

(* Lemma iso_liftcast_disp : *)

End LiftCatDispCat.


Section Arities.

  Variables (C D:Precategory).

  Local Notation MONAD := (monadPrecategory C).
  Local Notation BMOD := (bmod_disp C D).

(* Définitions des arités *)
Definition arity := functor_lifting BMOD (functor_identity MONAD).

  (* functor_over (functor_identity _) (liftcat_disp (monadPrecategory C)) (bmod_disp C D). *)

(* Preuve que les arités sont right-inverse du foncteur d'oubli bmod -> mon *)
Lemma right_inverse_arity  (ar:arity ) :  ((pr1_precat BMOD)□ (lifted_functor ar) )    =  (functor_identity MONAD).
  intros.
  apply subtypeEquality; [| reflexivity].
  red.
  intros;  apply isaprop_is_functor.
  apply homset_property.
Qed.

(* Réciproque : si on a un foncteur qui vérifié ça, alors on a un functor lifting qui vaut lui-même *)

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
(*
    simpl.
    assert (hf : forall g,  f = g -> pullback_module f (ar_inv_ob y) = pullback_module ( g) (ar_inv_ob y)).
    { intros g heq.
      destruct heq.
      reflexivity.
    }
    erewrite hf; cycle 1.
    clear.
    assert (hf2 : forall A B (g:Monad_Mor A B), #(pr1_precat BMOD □ F) g = #(functor_identity MONAD) g).

    rewrite <- hF.
    change f with
etrans.
    erewrite hf.
    assert (Ff := (#F f)).

    assert (Ffm := pr2 Ff).
    simpl in Ffm.

    rewrite <- hF.
    simpl.
    intro f.

    intros f.
    exact (pr2 (#F f)).
    set (Ff := pr2 (#F f)).
    simpl in Ff.

  Lemma right_inverse_arity_rep   ->
                                                                    exists (ar:arity), (lifted_functor ar) = F.
    intros.
    apply subtypeEquality; [| reflexivity].
    red.
    intros;  apply isaprop_is_functor.
    apply homset_property.
  Qed.*)


    End Reciproque.
End Arities.


(* deuxième manière de définir les arités *)
Section Arities2.

  Variables (C D:Precategory).

  Local Notation MONAD := (monadPrecategory C).
  Local Notation BMOD := (bmod_disp C D).
  Local Notation LMONAD := (liftcat_disp MONAD).

(* Définitions des arités *)
Definition arity2 := functor_over (functor_identity _) LMONAD (bmod_disp C D).

(* Preuve que les arités sont right-inverse du foncteur d'oubli bmod -> mon *)
Lemma right_inverse_arity2  (ar:arity2 ) :  ((pr1_precat BMOD)□ (total_functor ar) )    =  (pr1_precat LMONAD).
  intros.
  apply subtypeEquality; [| reflexivity].
  red.
  intros;  apply isaprop_is_functor.
  apply homset_property.
Qed.

End Arities2.
(* large category of representation defined as a display category

Not that contrary to the large category of modules, we do not construct the category of
representations of a specific arity

This is an attempt to use directly the display category construction.
The category of represenations of a specific arity can be retrieved as a fiber category.

*)
Section LargeCatRep.

  Variable (C :Precategory).

  Local Notation MONAD := (monadPrecategory C).
  Local Notation LMONAD := (liftcat_disp MONAD).
  Local Notation BMOD := (bmod_disp C C).
  Local Notation GEN_ARITY := (disp_functor_precat _ _ LMONAD BMOD).
  (* Arities are display functors over the identity *)
  Local Notation ARITY :=  (fiber_precategory GEN_ARITY (functor_identity _)).



  (*
************

 ??? Question pour Benedikt :


************
*)
  (* pourquoi ce check  ne marche pas : *)
  (* Check (forall a:ob ARITY, Some (a:functor_over_data _ _ _) = None). *)
  (* et ceux-là marchent ? *)
  Check (forall a:ob ARITY, Some (a:functor_over  _ _  _) = None).
  Check (forall a:ob ARITY, Some ((a:functor_over  _ _  _):functor_over_data _ _ _) = None).


  Definition taut_rmod_data (R:MONAD) : RModule_data R C.
    intros.
    exists (pr1 R).
    apply μ.
  Defined.
  Definition taut_rmod (R:Monad C) : BMOD R.
    intros R.
    exists (taut_rmod_data R).



    split; intro c.
    (* Soooo enervinggggggg  et ce n'est pas le seul truc que j'ai testé bien sûr *)

    rewrite functor_id_id.
    repeat pr1_norm.
        unfold pr1.
    apply   functor_id_id.

        assert (h:=Monad_law1 (T:=R) c).
        rewrite h.
        refl
    rewrite Monad_law1.
    intro h.
    rewrite h.
    rewrite Monad_law1.
    etrans.
    apply maponpaths.
    pr1_norm.
    rewrite Monad_law1.
TODO


  Definition brep_disp_ob_mor : disp_precat_ob_mor ARITY.
Proof.
  exists (fun ar:ob ARITY => Σ (R:MONAD), RModule_Mor (((ar:functor_over _ _ _):functor_over_data _ _ _) R tt) R).
  intros xx' yy' g h ff'.
    exact (precategory_morphisms (* (C:= MODULE xx') *) g ( pullback_module  ff'  h )).
Defined.

Definition brep_id_comp : disp_precat_id_comp _ brep_disp_ob_mor.
Proof.
  split.
  -
    intros x xx.
    simpl.
    apply pbm_id.

  - intros x y z f g xx yy zz ff gg.
    set (pbm_g := pbm_mor f gg).
    set (pbm_gf := (RModule_composition _ pbm_g (pbm_mor_comp f g ))).
    exact (compose ff pbm_gf).
Defined.


Definition brep_data : disp_precat_data _
:= (brep_disp_ob_mor ,, brep_id_comp).


Lemma foo (x y : MONAD) (f g : MONAD ⟦ x, y ⟧)
  (e : f = g)
  (xx : brep_data x)
  (yy : pr1 brep_data y)
  (ff : xx -->[ f] yy)
  (c : C) :
  (pr1 (transportf (mor_disp xx yy) e ff)) c = pr1 ff c.
Proof.
  destruct e.
  intros.
  apply idpath.
Qed.


Lemma brep_axioms : disp_precat_axioms MONAD brep_data.
Proof.

  repeat apply tpair; intros; try apply homset_property.
  - simpl.
    unfold id_disp; simpl.

    apply (invmap ((@RModule_Mor_equiv _ x _ (homset_property D) _ _ _ _  ))).
    apply nat_trans_eq; try apply homset_property.
    intros c; simpl.
    simpl.
    rewrite assoc; simpl.
    etrans. Focus 2. eapply pathsinv0.
      apply  foo.
   cbn. simpl. unfold pbm_mor_comp.
      unfold transportb.
      rewrite id_left.
      rewrite id_right.
      apply idpath.
  - (* this is for Ambroise *)

    set (heqf := id_right f).
     apply (invmap ((@RModule_Mor_equiv _ x _ (homset_property D) _ _ _ _  ))).
     apply nat_trans_eq; try apply homset_property.
     simpl.
     intros c.
     rewrite id_right,id_right.
    revert ff.

    destruct (heqf).
    intros; simpl.
    reflexivity.
  - set (heqf:= assoc f g h).
     apply (invmap ((@RModule_Mor_equiv _ x _ (homset_property D) _ _ _ _  ))).
     apply nat_trans_eq; try apply homset_property.
     intros c; simpl.
     (* rewrite id_right,id_right. *)
     (* rewrite assoc. *)
     etrans; cycle 1.
     (* set (z:= (ff:nat c ;; gg c ;; hh c). *)
     symmetry.

     clearbody heqf.

(* impossible de faire un destruct ici... *)

     apply foo.
     simpl.
     repeat rewrite id_right.
     rewrite assoc.
     reflexivity.
  - simpl.
    apply rmodule_category_has_homsets.
Qed.

Definition brep_disp : disp_precat MONAD:=
   (brep_data ,, brep_axioms).

End LargeCatRep.

  (*
 Definition nat_trans_dataE {C C' : precategory_data}
  {F F' : functor_data C C'}(a : nat_trans F F') : pr1 a = (nat_trans_data a  :
   Π x : ob C, F x --> F' x)  := idpath _.

 Definition precategory_data_from_precategoryE (C : precategory) : pr1 C = precategory_data_from_precategory C := idpath _.
*)
 (* Definition functor_data_from_functorE (C C': precategory_data) *)
 (*     (F : functor C C') : pr1 F = functor_data_from_functor _ _ F  := idpath _. *)


(* Hint Rewrite @nat_trans_dataE functor_data_from_functorE : coercions. *)



Require Import lemmacoercions.
