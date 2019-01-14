(**
Complements about hset_category (true of any topos: Cf. Sheaves and Geometry)
(actually could be generalized to non hset types)
 - bin products of epi is epi
 - distributive

 *)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.FunctorCategory.

Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Monads.LModules.

Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.

Require Import UniMath.CategoryTheory.Adjunctions.Core.

Require Import Modules.Prelims.lib.
Require Import Modules.Prelims.BinProductComplements.
Require Import Modules.Prelims.CoproductsComplements.
Require Import UniMath.SubstitutionSystems.ModulesFromSignatures.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Epis.
Require Import UniMath.CategoryTheory.EpiFacts.

Require Import UniMath.CategoryTheory.categories.HSET.All.

Lemma hset_category_isDistributive (I : hSet)  :
   bp_coprod_isDistributive BinProductsHSET (CoproductsHSET  I (setproperty I)).
Proof.
  intros f X.
  eapply is_iso_from_is_z_iso.
  use mk_is_z_isomorphism.
  - intros [[i a] b].
    exact (i ,, (a ,, b)).
  - use mk_is_inverse_in_precat; apply idpath.
Defined.

Lemma isEpiBinProdHSET {X X' Y Y' : hSet} (f : X -> Y)(g : X' -> Y') :
  isEpi (C := SET) f -> isEpi (C:=SET) g -> isEpi (C:=SET)
                                                (BinProductOfArrows _ 
                                                                    (BinProductsHSET Y Y')
                                                                    (BinProductsHSET X X')
                                                            f g).
Proof.
  intros epif epig.
  apply EpisAreSurjective_HSET in epif.
  apply EpisAreSurjective_HSET in epig.
  intros Z u v h.
  apply funextfun.
  apply toforallpaths in h.
  red.
  eapply surjectionisepitosets; [| apply setproperty | apply h].
  intros [y y'].
  generalize (epif y).
  generalize (epig y').
  apply hinhfun2.
  intros  [x' hx'][x hx].
  use hfiberpair.
  - exact (x,,x').
  - cbn.
    apply dirprodeq; apply hx' || apply hx.
Qed.
