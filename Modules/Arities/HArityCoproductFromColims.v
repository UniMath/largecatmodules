(*
pullback of coproducts
 Coproducts of half-arities
using LModulesColims
 *)
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.

Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Monads.LModules.

Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.

Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.

Require Import Modules.Prelims.lib.
Require Import Modules.Prelims.modules.
Require Import Modules.Arities.LModuleColims.
Require Import Modules.Arities.aritiesalt.

Section pullback_coprod.
  Context {C : category} {B : precategory}.
  Context {R : Monad B}{S : Monad B} (f : Monad_Mor R S).

  Context {O : UU}.
  Context {Co : Colims_of_shape (I_graph O) C}.
          (* (cpLM: ∏ (X : Monad B), Coproducts O (precategory_LModule X C)). *)

  Let Func_coproducts_as_Colims  :=
                           (ColimsFunctorCategory_of_shape _ B C
                                                           (homset_property _) Co).
  (* Maybe usseless ? *)
  Let Func_coproducts_from_Colims : Coproducts O [B, C] :=
    Coproducts_from_Colims O [B , C] (homset_property _)
                           Func_coproducts_as_Colims.

  Definition LModule_coproducts_from_Colims (R : Monad B) :
    Coproducts O (precategory_LModule R C) :=
    Coproducts_from_Colims _ _ (has_homsets_LModule R C)
                           (LModule_Colims_of_shape C R _ Co).

  Local Notation cpcolFunc := Func_coproducts_as_Colims.
  Local Notation cpFunc := Func_coproducts_from_Colims.
  Local Notation cpLM := LModule_coproducts_from_Colims.

  Context (α : O -> LModule S C ).
  Let αF : O -> functor B C := fun o => α o.
  Let pbm_α : O -> LModule R C := fun o => pb_LModule f (α o).

  Definition pbm_coprod := pb_LModule f (CoproductObject _ _ (cpLM _ α)).
  Definition coprod_pbm : LModule _ _ := CoproductObject _ _ (cpLM _ pbm_α).

  Definition coprod_pbm_to_pbm_coprod_nat_trans : nat_trans coprod_pbm pbm_coprod.
    use (colimOfArrows (Func_coproducts_as_Colims _) (Func_coproducts_as_Colims _)).
    - intro u.
      cbn.
      apply nat_trans_id.
    - intros u v.
      use empty_rect.
  (*
      cbn in e.
    (* cbn -[Coproducts]. *)
    (* apply nat_trans_id. *)
    (* simpl. *)
    assert (h := fun a b =>
              (CoproductOfArrows _ _ (Func_coproducts_from_Colims a) (Func_coproducts_from_Colims b)))
    .
    cbn in h.
    cbn.
    use h.
    cbn.
    unfold coprod_pbm.
    apply Cop
  use tpair.
   *)
  Defined.
  Lemma coprod_pbm_to_pbm_coprod_laws : LModule_Mor_laws _ (T := coprod_pbm) (T' := pbm_coprod)
                                                         coprod_pbm_to_pbm_coprod_nat_trans.
  Proof.
    intro c.
    apply pathsinv0.
    etrans;[apply precompWithColimOfArrows|].
    apply pathsinv0.
    apply colimArrowUnique.
    cbn.
    intro u.
    cbn.
    etrans.
    {
      etrans;[apply assoc|].
      apply maponpaths_2.
      set (CC := Co _).
      use (colimArrowCommutes CC).
    }
    cbn.
    etrans.
    {
      etrans;[apply maponpaths_2; apply id_left|].
  Abort.
      }
    cbn.
    rewrite id_left
    etrans;[apply assoc|].

    etrans;[apply id_left|apply id_right].
  
  Definition coprod_pbm_to_pbm_coprod : LModule_Mor  _ coprod_pbm pbm_coprod.
    use tpair.
    - use tpair

End pullback_coprod.

Section Coprod.
  Context {C : category} {O : UU}.
  Local Notation hsC := (homset_property C).

  (* C has coproducts *)
  Context {Co : Colims_of_shape (I_graph O) C}.
  Check (Coproducts_from_Colims _ _ hsC Co : Coproducts O C).

  Local Notation HalfArity := (arity C).

  Definition LModule_coproducts_from_Colims (R : Monad C) :
    Coproducts O (precategory_LModule R C) :=
    Coproducts_from_Colims _ _ (has_homsets_LModule R C)
                           (LModule_Colims_of_shape C R _ Co).

  Local Notation MOD_cop := LModule_coproducts_from_Colims.

  (* Local Notation HARITY := (arity C). *)

  Context (α : O -> HalfArity).
  Local Notation α' R := (fun o => α o R).

  Definition harity_coprod_on_objects (R : Monad C) : LModule R C :=
    CoproductObject _ _ (LModule_coproducts_from_Colims R (α' R)).

  Definition harity_coprod_on_morphisms (R S : Monad C)
             (f : Monad_Mor R S) : LModule_Mor _ (harity_coprod_on_objects R)
                                               (pb_LModule f (harity_coprod_on_objects S)).
    use tpair.
    - assert (h := fun c=> (CoproductOfArrows _ _ (MOD_cop R (α' R)) (c:= c))).
    : arity_on_morphisms  (R : Monad C) : LModule R C :=
    CoproductObject _ _ (LModule_coproducts_from_Colims R (fun o => α o R)).

  Definition harity_coprod : HalfArity.