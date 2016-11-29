
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
  Qed.

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
TODO
    reflexivity.
    rewrite <- nat_trans_over_id_left.
    unfold mor_disp; simpl.
  apply isasetaprop, homset_property.
Qed.

Definition bmod_disp : disp_precat MONAD.
  := (bmod_data ,, bmod_axioms).


  TODO





Definition arrow_data : disp_precat_data _
  := (arrow_disp_ob_mor ,, arrow_id_comp).

Lemma arrow_axioms : disp_precat_axioms (C × C) arrow_data.
Proof.
  repeat apply tpair; intros; try apply homset_property.
  apply isasetaprop, homset_property.
Qed.


End Arrow_Disp.
*)

(** Pull back module **)





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
