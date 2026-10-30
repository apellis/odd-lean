/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVContentPairTensor

/-! # Associativity of the content induction comparisons

`contentETripleComparison_assoc` identifies the named triple comparison with
suffix-first composition, including all endpoint equality transports. This is
whole natural-isomorphism coherence for the content triple action; it supplies
the comparison needed to identify independently defined triple operators.

The proof uses uniqueness of left adjoints, not transport of generator formulas.
There are no finiteness, field, or flatness assumptions.
-/
noncomputable section
open CategoryTheory
universe u
namespace OddMath.QuiverHecke.ELVOld.ContentComparisonCoherence
variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
variable {F : A ⥤ B} {G : B ⥤ A} {H : B ⥤ C} {I : C ⥤ B} {J : C ⥤ D} {K : D ⥤ C}
variable {P : A ⥤ C} {Q : B ⥤ D} {R : A ⥤ D}
variable (a : F ⊣ G) (b : H ⊣ I) (c : J ⊣ K) (p : P ⊣ I ⋙ G) (q : Q ⊣ K ⋙ I) (r : R ⊣ (K ⋙ I) ⋙ G)

private theorem uniq_whisker_right (x : A) :
    J.map (((a.comp b).leftAdjointUniq p).hom.app x) =
    (((a.comp b).comp c).leftAdjointUniq (p.comp c)).hom.app x := by
  apply (((a.comp b).comp c).homEquiv _ _).injective
  erw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
  simp only [Adjunction.homEquiv_unit, Adjunction.comp_unit_app, Functor.comp_map,
    Category.assoc]
  rw [← G.map_comp, ← I.map_comp, c.unit_naturality]
  rw [I.map_comp, G.map_comp]
  rw [← Category.assoc, ← Category.assoc]
  have he := Adjunction.unit_leftAdjointUniq_hom_app (a.comp b) p x
  rw [Adjunction.comp_unit_app] at he
  exact congrArg (fun f => f ≫ G.map (I.map (c.unit.app (P.obj x)))) he


private theorem uniq_whisker_left (x : A) :
    ((b.comp c).leftAdjointUniq q).hom.app (F.obj x) =
    (((a.comp b).comp c).leftAdjointUniq (a.comp q)).hom.app x := by
  apply (((a.comp b).comp c).homEquiv _ _).injective
  erw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
  simp only [Adjunction.homEquiv_unit, Adjunction.comp_unit_app, Functor.comp_map,
    Category.assoc]
  have he := Adjunction.unit_leftAdjointUniq_hom_app (b.comp c) q (F.obj x)
  rw [Adjunction.comp_unit_app] at he
  have hh := congrArg (fun f => a.unit.app x ≫ G.map f) he
  simpa only [Functor.map_comp, Functor.comp_map, Functor.comp_obj, Category.assoc] using hh

private theorem uniq_associativity (x : A) :
    J.map (((a.comp b).leftAdjointUniq p).hom.app x) ≫
      ((p.comp c).leftAdjointUniq r).hom.app x =
    ((b.comp c).leftAdjointUniq q).hom.app (F.obj x) ≫
      ((a.comp q).leftAdjointUniq r).hom.app x := by
  rw [uniq_whisker_right a b c p x, uniq_whisker_left a b c q x]
  rw [Adjunction.leftAdjointUniq_trans_app, Adjunction.leftAdjointUniq_trans_app]

end OddMath.QuiverHecke.ELVOld.ContentComparisonCoherence

open StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
variable {k : Type u} [CommRing k]
variable {C D E F : Type u} [Category.{u} C] [Category.{u} D]
  [Category.{u} E] [Category.{u} F]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive D] [Linear k D] [Supercategory k D]
  [Preadditive E] [Linear k E] [Supercategory k E]
  [Preadditive F] [Linear k F] [Supercategory k F]
variable (J : C ⥤ D) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
variable (K : D ⥤ E) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
variable (L : E ⥤ F) [L.Additive] [L.Linear k] [IsSuperfunctor k L]


variable (P : C ⥤ E) [P.Additive] [P.Linear k] [IsSuperfunctor k P]
variable (Q : D ⥤ F) [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q]
variable (R : C ⥤ F) [R.Additive] [R.Linear k] [IsSuperfunctor k R]

/-- Equality-transported composition comparisons commute on every module. -/
theorem inductionCompOfEq_assoc_hom
    (eP : J ⋙ K = P) (eQ : K ⋙ L = Q) (eR : P ⋙ L = R) (eS : J ⋙ Q = R)
    (M : Superfunctor k C (SVec k)) :
    (BalancedInduction.induction L).map ((inductionCompOfEq J K P eP).hom.app M) ≫
      (inductionCompOfEq P L R eR).hom.app M =
    (inductionCompOfEq K L Q eQ).hom.app (BalancedInduction.induced J M) ≫
      (inductionCompOfEq J Q R eS).hom.app M := by
  subst P
  subst Q
  subst R
  simp only [inductionCompOfEq, eqToIso_refl, Iso.trans_refl]
  exact OddMath.QuiverHecke.ELVOld.ContentComparisonCoherence.uniq_associativity
      (BalancedInduction.adjunction J) (BalancedInduction.adjunction K)
      (BalancedInduction.adjunction L) (BalancedInduction.adjunction (J ⋙ K))
      (BalancedInduction.adjunction (K ⋙ L)) (BalancedInduction.adjunction ((J ⋙ K) ⋙ L)) M

/-- Associativity includes the four independently supplied functor equalities. -/
theorem inductionCompOfEq_assoc
    (eP : J ⋙ K = P) (eQ : K ⋙ L = Q) (eR : P ⋙ L = R) (eS : J ⋙ Q = R) :
    Functor.isoWhiskerRight (inductionCompOfEq (k := k) J K P eP) (BalancedInduction.induction (k := k) L) ≪≫
      inductionCompOfEq (k := k) P L R eR =
    Functor.associator (BalancedInduction.induction (k := k) J) (BalancedInduction.induction (k := k) K)
      (BalancedInduction.induction (k := k) L) ≪≫
      Functor.isoWhiskerLeft (BalancedInduction.induction (k := k) J) (inductionCompOfEq (k := k) K L Q eQ) ≪≫
      inductionCompOfEq (k := k) J Q R eS := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp]
  exact inductionCompOfEq_assoc_hom J K L P Q R eP eQ eR eS M
end OddMath.QuiverHecke.ELVOld

namespace OddMath.QuiverHecke.ELVOld
section Content
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
variable (β : Multiset I) (i j : I)
local notation "δ₁" => (β + ([i] : Multiset I))
local notation "δ₂" => ((β + ([i] : Multiset I)) + ([j] : Multiset I))
local notation "J" => contentAppend D Sc cutoff N β [i]
local notation "K" => contentAppend D Sc cutoff N δ₁ [j]
variable (τ : List I) (γ : Multiset I)
  (hγ : ((β + ([i] : Multiset I)) + ([j] : Multiset I)) + (τ : Multiset I) = γ)
  (hs : (β + ([i] : Multiset I)) + (([j] ++ τ : List I) : Multiset I) = γ)
  (h : β + (([i,j] ++ τ : List I) : Multiset I) = γ)
local notation "L" => contentAppendTo D Sc cutoff N δ₂ τ γ hγ

/-- Pair-first and suffix-first content comparisons agree as natural isomorphisms. -/
theorem contentInductionComp_assoc :
    Functor.isoWhiskerRight (contentEPairComparison D Sc cutoff N β i j)
        (BalancedInduction.induction L) ≪≫
      contentInductionCompTo D Sc cutoff N β [i,j] δ₂ (contentPair_sum β i j) τ γ hγ h =
    Functor.associator (BalancedInduction.induction J) (BalancedInduction.induction K)
      (BalancedInduction.induction L) ≪≫
      Functor.isoWhiskerLeft (BalancedInduction.induction J)
        (contentInductionComp D Sc cutoff N δ₁ [j] τ γ hγ hs) ≪≫
      contentInductionComp D Sc cutoff N β [i] ([j] ++ τ) γ hs h := by
  rw [contentInductionCompTo_eq]
  exact inductionCompOfEq_assoc J K L
    (contentAppendTo D Sc cutoff N β [i,j] δ₂ (contentPair_sum β i j))
    (contentAppendTo D Sc cutoff N δ₁ ([j] ++ τ) γ hs)
    (contentAppendTo D Sc cutoff N β ([i,j] ++ τ) γ h)
    (contentAppend_comp_eq D Sc cutoff N β [i] [j] δ₂ rfl (contentPair_sum β i j))
    (contentAppend_comp_eq D Sc cutoff N δ₁ [j] τ γ hγ hs)
    (contentAppend_compTo_eq D Sc cutoff N β [i,j] δ₂ (contentPair_sum β i j) τ γ hγ h)
    (contentAppend_comp_eq D Sc cutoff N β [i] ([j] ++ τ) γ hs h)

/-- The named triple comparison agrees with the suffix-first composition tree. -/
theorem contentETripleComparison_assoc (l : I) (γ : Multiset I)
    (h : β + ([i,j,l] : Multiset I) = γ)
    (hs : δ₁ + ([j,l] : Multiset I) = γ) :
    contentETripleComparison D Sc cutoff N β i j l γ h =
    Functor.associator (contentE D Sc cutoff N β i) (contentE D Sc cutoff N δ₁ j)
      (contentInductionTo D Sc cutoff N δ₂ [l] γ
        (by rw [add_assoc, add_assoc]; exact h)) ≪≫
      Functor.isoWhiskerLeft (contentE D Sc cutoff N β i)
        (contentInductionComp D Sc cutoff N δ₁ [j] [l] γ
          (by rw [add_assoc, add_assoc]; exact h) hs) ≪≫
      contentInductionComp D Sc cutoff N β [i] [j,l] γ hs h :=
  contentInductionComp_assoc D Sc cutoff N β i j [l] γ _ hs h
/-- Equality of the whole linear maps of the two named triple comparison trees. -/
theorem contentETripleComparison_assoc_total (l : I) (γ : Multiset I)
    (h : β + ([i,j,l] : Multiset I) = γ)
    (hs : δ₁ + ([j,l] : Multiset I) = γ)
    (M : ContentModules D Sc cutoff N β) (t : ContentCategory D Sc cutoff N γ) :
    ((contentETripleComparison D Sc cutoff N β i j l γ h).hom.app M).total t =
    ((Functor.associator (contentE D Sc cutoff N β i) (contentE D Sc cutoff N δ₁ j)
      (contentInductionTo D Sc cutoff N δ₂ [l] γ
        (by rw [add_assoc, add_assoc]; exact h)) ≪≫
      Functor.isoWhiskerLeft (contentE D Sc cutoff N β i)
        (contentInductionComp D Sc cutoff N δ₁ [j] [l] γ
          (by rw [add_assoc, add_assoc]; exact h) hs) ≪≫
      contentInductionComp D Sc cutoff N β [i] [j,l] γ hs h).hom.app M).total t := by
  exact congrArg (fun e => (e.hom.app M).total t)
    (contentETripleComparison_assoc D Sc cutoff N β i j l γ h hs)

end Content
end OddMath.QuiverHecke.ELVOld
