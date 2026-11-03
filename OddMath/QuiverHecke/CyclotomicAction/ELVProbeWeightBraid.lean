/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeBlockBraid

/-! # The equal-colour braid on the entire OLD probe weight category

Brundan–Ellis (1.9): compare the two actual crossing whiskerings through
one selected triple-coordinate equality. The direct stored-target OLD
block braid supplies the relation. No braid, comparison, inversion or
finite-weight-fibre premise is introduced; absent coordinates are zero.
-/
noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open ELVOld ELVOld.BalancedInduction CyclotomicAction
universe u v w z

private theorem braid_prefix_conjugate
    {C A : Type v} [Category.{w} C] [Category.{z} A]
    (G : C ⥤ A) {M₀ M₁ : C} (hM : M₀ = M₁) {V : A}
    (hV : V = G.obj M₀) (hW : V = G.obj M₁) (d : End M₁) :
    eqToHom hV ≫ G.map (eqToHom hM ≫ d ≫ eqToHom hM.symm) ≫ eqToHom hV.symm =
      eqToHom hW ≫ G.map d ≫ eqToHom hW.symm := by
  cases hM
  cases hV
  cases hW
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

private theorem braid_suffix_conjugate
    {k : Type u} [CommRing k] {C A : Type v}
    [Category.{w} C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category.{z} A] [Preadditive A] [Linear k A] [Supercategory k A]
    (G : C ⥤ A) {M₀ M₁ : C} (hM : M₀ = M₁) {V : A}
    (hV : V = G.obj M₀) (hW : V = G.obj M₁) (d : SuperNatTrans k G G) :
    eqToHom hV ≫ d.total M₀ ≫ eqToHom hV.symm =
      eqToHom hW ≫ d.total M₁ ≫ eqToHom hW.symm := by
  cases hM
  cases hV
  cases hW
  rfl

private theorem conjugate_braid {C : Type v} [Category.{w} C]
    {A B : C} (e : A = B) (a b : End B)
    (hb : b ≫ a ≫ b = a ≫ b ≫ a) :
    (eqToHom e ≫ b ≫ eqToHom e.symm) ≫ (eqToHom e ≫ a ≫ eqToHom e.symm) ≫
        (eqToHom e ≫ b ≫ eqToHom e.symm) =
      (eqToHom e ≫ a ≫ eqToHom e.symm) ≫ (eqToHom e ≫ b ≫ eqToHom e.symm) ≫
        (eqToHom e ≫ a ≫ eqToHom e.symm) := by
  cases e
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using hb

private theorem reassociated_probePrefix_total
    {k : Type u} [CommRing k] {A B C E : PiSCat.{u, u, u + 1} k}
    (F : A ⟶ B) (G : B ⟶ C) (H : C ⟶ E) (x : F ≫ G ⟶ F ≫ G) (M : A) :
    ((associator F G H).inv ≫ x ▷ H ≫ (associator F G H).hom).total M = H.map (x.total M) := by
  erw [PiSCat.associator_inv, PiSCat.associator_hom, Category.id_comp, Category.comp_id]
  change H.map (x.app 0 M) + H.map (x.app 1 M) = H.map (x.app 0 M + x.app 1 M)
  exact H.toFunctor.map_add.symm

private theorem braid_total_three
    {k : Type u} [CommRing k] {C A : Type v}
    [Category.{w} C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category.{z} A] [Preadditive A] [Linear k A] [Supercategory k A]
    (F : Superfunctor k C A) (f g h : End F) (M : C) :
    (f ≫ g ≫ h).total M = f.total M ≫ g.total M ≫ h.total M := by
  rw [Superfunctor.comp_total, Superfunctor.comp_total]

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (i : I) (Λ : X) {x₀ x₁ x₂ x₃ : X}
  (h₁ : x₀ + D.α i = x₁) (h₂ : x₁ + D.α i = x₂) (h₃ : x₂ + D.α i = x₃)
local notation "E₁" => probeOldE D Sc m i Λ h₁
local notation "E₂" => probeOldE D Sc m i Λ h₂
local notation "E₃" => probeOldE D Sc m i Λ h₃

/-- The actual first pair crossing in the prescribed right-associated triple. -/
abbrev probeOldWeightBraidPrefix : End (E₁ ≫ E₂ ≫ E₃) :=
  (associator E₁ E₂ E₃).inv ≫
    probeOldActionEqualCross D Sc m i Λ h₁ h₂ ▷ E₃ ≫ (associator E₁ E₂ E₃).hom

/-- The independently chosen second pair crossing, after the actual first induction. -/
abbrev probeOldWeightBraidSuffix : End (E₁ ≫ E₂ ≫ E₃) :=
  E₁ ◁ probeOldActionEqualCross D Sc m i Λ h₂ h₃

theorem probeOldWeightBraidPrefix_total (M : ProbeOldWeightProduct D Sc m Λ x₀)
    (ε : WeightBlocks D Λ x₃) :
    (probeOldWeightBraidPrefix D Sc m i Λ h₁ h₂ h₃).total M ε =
      (probeOldInductionComponent D Sc m i Λ h₃ ε).map
        ((probeOldActionEqualCross D Sc m i Λ h₁ h₂).total M) :=
  congrFun (reassociated_probePrefix_total E₁ E₂ E₃
    (probeOldActionEqualCross D Sc m i Λ h₁ h₂) M) ε

theorem probeOldWeightBraidSuffix_total (M : ProbeOldWeightProduct D Sc m Λ x₀)
    (ε : WeightBlocks D Λ x₃) :
    (probeOldWeightBraidSuffix D Sc m i Λ h₁ h₂ h₃).total M ε =
      (probeOldActionEqualCross D Sc m i Λ h₂ h₃).total ((E₁).obj M) ε := rfl

/-- The actual first crossing uses the selected triple coordinate and prescribed block map. -/
theorem probeOldWeightBraidPrefix_component (β : WeightBlocks D Λ x₀)
    (M : ProbeOldWeightProduct D Sc m Λ x₀) :
    (probeOldWeightBraidPrefix D Sc m i Λ h₁ h₂ h₃).total M
        (probeOldBlockSucc₃ D i i i Λ h₁ h₂ h₃ β) =
      eqToHom (probeOldWeightTriple_obj_eq D Sc m i i i Λ h₁ h₂ h₃ β M) ≫
        (probeOldBlockBraidPrefix D Sc m i Λ h₁ h₂ h₃ β).total (M β) ≫
        eqToHom (probeOldWeightTriple_obj_eq D Sc m i i i Λ h₁ h₂ h₃ β M).symm := by
  rw [probeOldWeightBraidPrefix_total, probeOldInductionComponent_map_blockSucc]
  simp only [probeOldActionEqualCross]
  rw [probeOldWeightEqualCross_total_of D Sc m i Λ h₁ h₂ M β _ rfl,
    probeOldWeightEqualCrossVia_total, probeOldBlockBraidPrefix_total]
  have ht := braid_prefix_conjugate
    (probeOldBlockInd D Sc m i Λ h₃ (blockSucc₂ D i i Λ h₁ h₂ β)).toFunctor
    (probeOldWeightPair_obj_eq D Sc m i Λ h₁ h₂ β M)
    (probeOldInductionComponent_obj_blockSucc D Sc m i Λ h₃ (blockSucc₂ D i i Λ h₁ h₂ β)
      ((E₁ ≫ E₂).obj M))
    (probeOldWeightTriple_obj_eq D Sc m i i i Λ h₁ h₂ h₃ β M)
    ((probeOldBlockEqualCross D Sc m i Λ h₁ h₂ β).total (M β))
  convert! ht using 1

/-- The independently chosen second crossing uses that identical triple coordinate. -/
theorem probeOldWeightBraidSuffix_component (β : WeightBlocks D Λ x₀)
    (M : ProbeOldWeightProduct D Sc m Λ x₀) :
    (probeOldWeightBraidSuffix D Sc m i Λ h₁ h₂ h₃).total M
        (probeOldBlockSucc₃ D i i i Λ h₁ h₂ h₃ β) =
      eqToHom (probeOldWeightTriple_obj_eq D Sc m i i i Λ h₁ h₂ h₃ β M) ≫
        (probeOldBlockBraidSuffix D Sc m i Λ h₁ h₂ h₃ β).total (M β) ≫
        eqToHom (probeOldWeightTriple_obj_eq D Sc m i i i Λ h₁ h₂ h₃ β M).symm := by
  rw [probeOldWeightBraidSuffix_total]
  simp only [probeOldActionEqualCross]
  rw [probeOldWeightEqualCross_total_of D Sc m i Λ h₂ h₃ ((E₁).obj M)
      (blockSucc D Λ i h₁ β) _ rfl,
    probeOldWeightEqualCrossVia_total, probeOldBlockBraidSuffix_total]
  have ht := braid_suffix_conjugate
    (probeOldBlockPairInd D Sc m i i Λ h₂ h₃ (blockSucc D Λ i h₁ β)).toFunctor
    (probeOldInductionComponent_obj_blockSucc D Sc m i Λ h₁ β M)
    (probeOldWeightPair_obj_eq D Sc m i Λ h₂ h₃ (blockSucc D Λ i h₁ β) ((E₁).obj M))
    (probeOldWeightTriple_obj_eq D Sc m i i i Λ h₁ h₂ h₃ β M)
    (probeOldBlockEqualCross D Sc m i Λ h₂ h₃ (blockSucc D Λ i h₁ β))
  exact ht

/-- The prescribed equal crossings satisfy the whole-weight OLD probe braid. -/
theorem probeOldActionEqualCross_braid :
    probeOldWeightBraidSuffix D Sc m i Λ h₁ h₂ h₃ ≫
      probeOldWeightBraidPrefix D Sc m i Λ h₁ h₂ h₃ ≫
        probeOldWeightBraidSuffix D Sc m i Λ h₁ h₂ h₃ =
    probeOldWeightBraidPrefix D Sc m i Λ h₁ h₂ h₃ ≫
      probeOldWeightBraidSuffix D Sc m i Λ h₁ h₂ h₃ ≫
        probeOldWeightBraidPrefix D Sc m i Λ h₁ h₂ h₃ := by
  apply OddMath.HomogeneousSuperfunctorIso.total_ext
  intro M
  funext ε
  have hL := congrFun (braid_total_three (E₁ ≫ E₂ ≫ E₃)
    (probeOldWeightBraidSuffix D Sc m i Λ h₁ h₂ h₃)
    (probeOldWeightBraidPrefix D Sc m i Λ h₁ h₂ h₃)
    (probeOldWeightBraidSuffix D Sc m i Λ h₁ h₂ h₃) M) ε
  have hR := congrFun (braid_total_three (E₁ ≫ E₂ ≫ E₃)
    (probeOldWeightBraidPrefix D Sc m i Λ h₁ h₂ h₃)
    (probeOldWeightBraidSuffix D Sc m i Λ h₁ h₂ h₃)
    (probeOldWeightBraidPrefix D Sc m i Λ h₁ h₂ h₃) M) ε
  apply hL.trans
  apply Eq.trans _ hR.symm
  by_cases hε : ∃ β, probeOldBlockSucc₃ D i i i Λ h₁ h₂ h₃ β = ε
  · obtain ⟨β, rfl⟩ := hε
    change (probeOldWeightBraidSuffix D Sc m i Λ h₁ h₂ h₃).total M _ ≫
        (probeOldWeightBraidPrefix D Sc m i Λ h₁ h₂ h₃).total M _ ≫
          (probeOldWeightBraidSuffix D Sc m i Λ h₁ h₂ h₃).total M _ =
      (probeOldWeightBraidPrefix D Sc m i Λ h₁ h₂ h₃).total M _ ≫
        (probeOldWeightBraidSuffix D Sc m i Λ h₁ h₂ h₃).total M _ ≫
          (probeOldWeightBraidPrefix D Sc m i Λ h₁ h₂ h₃).total M _
    rw [probeOldWeightBraidPrefix_component, probeOldWeightBraidSuffix_component]
    have hb := congrArg
      (fun f : End (probeOldBlockTripleInd D Sc m i i i Λ h₁ h₂ h₃ β) => f.total (M β))
      (probeOldBlockEqualCross_braid D Sc m i Λ h₁ h₂ h₃ β)
    rw [Superfunctor.comp_total, Superfunctor.comp_total,
      Superfunctor.comp_total, Superfunctor.comp_total] at hb
    have ht := conjugate_braid (probeOldWeightTriple_obj_eq D Sc m i i i Λ h₁ h₂ h₃ β M)
      ((probeOldBlockBraidPrefix D Sc m i Λ h₁ h₂ h₃ β).total (M β))
      ((probeOldBlockBraidSuffix D Sc m i Λ h₁ h₂ h₃ β).total (M β)) hb
    convert! ht using 1
  · exact (probeOldEFunctor_comp₃_isZero D Sc m i i i Λ h₁ h₂ h₃ ε hε M).eq_of_src _ _

end OddMath.QuiverHecke
