import OddMath.QuiverHecke.CyclotomicAction.ELVProbeBlockDistinctSlides
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightDotWhiskering

/-! # Distinct-colour slides on every OLD probe weight

Brundan–Ellis (1.8): both independently chosen dots and the positive
crossing are compared through their exact source and target coordinates.
Absent predecessor blocks use their constructed zero object.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open CyclotomicAction
universe u
private theorem distinct_total_smul {k C A : Type*} [CommRing k]
    [Category C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category A] [Preadditive A] [Linear k A] [Supercategory k A]
    {F G : Superfunctor k C A} (a : k) (f : F ⟶ G) (N : C) :
    (a • f).total N = a • f.total N := by
  change a • f.app 0 N + a • f.app 1 N = a • (f.app 0 N + f.app 1 N)
  exact (smul_add _ _ _).symm

private theorem distinct_conjugate_slide {k C : Type*} [CommRing k]
    [Category C] [Preadditive C] [Linear k C]
    {A A' B B' : C} (e : A = A') (f : B = B') (c : A' ⟶ B')
    (b : End B') (d : End A') (a : k) (h : c ≫ b = a • (d ≫ c)) :
    (eqToHom e ≫ c ≫ eqToHom f.symm) ≫ (eqToHom f ≫ b ≫ eqToHom f.symm) =
      a • ((eqToHom e ≫ d ≫ eqToHom e.symm) ≫ (eqToHom e ≫ c ≫ eqToHom f.symm)) := by
  cases e
  cases f
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using h

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
section Pair
variable (i j : I) (Λ : X) {x₀ x₁ xu : X}
  (h₁ : x₀ + D.α j = x₁) (h₂ : x₁ + D.α i = xu)

theorem probeOldPairOuterDotTo_total (β : WeightBlocks D Λ x₀) (ε : WeightBlocks D Λ xu)
    (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε) (M : ProbeOldWeightProduct D Sc m Λ x₀) :
    (probeOldE D Sc m j Λ h₁ ◁ probeOldActionDot D Sc m i Λ h₂).total M ε =
      eqToHom (Functor.congr_obj (probeOldEFunctor_comp₂_to D Sc m i j Λ h₁ h₂ β ε hε) M) ≫
        (probeOldBlockPairOuterDotTo D Sc m i j Λ h₁ h₂ β ε hε).total (M β) ≫
      eqToHom (Functor.congr_obj (probeOldEFunctor_comp₂_to D Sc m i j Λ h₁ h₂ β ε hε) M).symm := by
  subst ε
  change (probeOldE D Sc m j Λ h₁ ◁ probeOldActionDot D Sc m i Λ h₂).app 0 M _ + (probeOldE D Sc m j Λ h₁ ◁ probeOldActionDot D Sc m i Λ h₂).app 1 M _ = _
  rw [probeOldPairOuterDot_component, probeOldPairOuterDot_component]
  change _ = eqToHom _ ≫
    ((probeOldBlockPairOuterDotTo D Sc m i j Λ h₁ h₂ β _ rfl).app 0 (M β) +
     (probeOldBlockPairOuterDotTo D Sc m i j Λ h₁ h₂ β _ rfl).app 1 (M β)) ≫ eqToHom _
  rw [Preadditive.add_comp, Preadditive.comp_add]
  rfl

theorem probeOldPairInnerDotTo_total (β : WeightBlocks D Λ x₀) (ε : WeightBlocks D Λ xu)
    (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε) (M : ProbeOldWeightProduct D Sc m Λ x₀) :
    (probeOldActionDot D Sc m j Λ h₁ ▷ probeOldE D Sc m i Λ h₂).total M ε =
      eqToHom (Functor.congr_obj (probeOldEFunctor_comp₂_to D Sc m i j Λ h₁ h₂ β ε hε) M) ≫
        (probeOldBlockPairInnerDotTo D Sc m i j Λ h₁ h₂ β ε hε).total (M β) ≫
      eqToHom (Functor.congr_obj (probeOldEFunctor_comp₂_to D Sc m i j Λ h₁ h₂ β ε hε) M).symm := by
  subst ε
  change (probeOldActionDot D Sc m j Λ h₁ ▷ probeOldE D Sc m i Λ h₂).app 0 M _ + (probeOldActionDot D Sc m j Λ h₁ ▷ probeOldE D Sc m i Λ h₂).app 1 M _ = _
  rw [probeOldPairInnerDot_component, probeOldPairInnerDot_component]
  change _ = eqToHom _ ≫
    ((probeOldBlockPairInnerDotTo D Sc m i j Λ h₁ h₂ β _ rfl).app 0 (M β) +
     (probeOldBlockPairInnerDotTo D Sc m i j Λ h₁ h₂ β _ rfl).app 1 (M β)) ≫ eqToHom _
  rw [Preadditive.add_comp, Preadditive.comp_add]
  simp only [probeOldBlockPairInnerDotTo, Superfunctor.whiskerRight_app]
end Pair
section Crossing
variable (i j : I) (Λ : X) {x₀ xj xi xu : X}
  (h₁ : x₀ + D.α j = xj) (h₂ : xj + D.α i = xu)
  (h₃ : x₀ + D.α i = xi) (h₄ : xi + D.α j = xu)
local notation "sw" => blockSucc₂_swap D i j Λ h₁ h₂ h₃ h₄

theorem probeOldActionDistinctCross_total_of (β : WeightBlocks D Λ x₀)
    (ε : WeightBlocks D Λ xu) (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε)
    (M : ProbeOldWeightProduct D Sc m Λ x₀) :
    (probeOldActionDistinctCross D Sc m i j Λ h₁ h₂ h₃ h₄).total M ε =
      eqToHom (Functor.congr_obj (probeOldEFunctor_comp₂_to D Sc m i j Λ h₁ h₂ β ε hε) M) ≫
        (probeOldBlockDistinctCross D Sc m i j Λ h₁ h₂ h₃ h₄ β ε hε).total (M β) ≫
      eqToHom (Functor.congr_obj (probeOldEFunctor_comp₂_to D Sc m j i Λ h₃ h₄ β ε (sw hε)) M).symm := by
  change probeOldWeightDistinctCrossComponent D Sc m i j Λ h₁ h₂ h₃ h₄ 0 M ε +
    probeOldWeightDistinctCrossComponent D Sc m i j Λ h₁ h₂ h₃ h₄ 1 M ε = _
  rw [probeOldWeightDistinctCrossComponent_of D Sc m i j Λ h₁ h₂ h₃ h₄ 0 M β ε hε,
      probeOldWeightDistinctCrossComponent_of D Sc m i j Λ h₁ h₂ h₃ h₄ 1 M β ε hε,
      probeOldWeightDistinctCrossVia_component, probeOldWeightDistinctCrossVia_component]
  change _ = eqToHom _ ≫
    ((probeOldBlockDistinctCross D Sc m i j Λ h₁ h₂ h₃ h₄ β ε hε).app 0 (M β) +
     (probeOldBlockDistinctCross D Sc m i j Λ h₁ h₂ h₃ h₄ β ε hε).app 1 (M β)) ≫ eqToHom _
  rw [Preadditive.add_comp, Preadditive.comp_add]

theorem probeOldActionDistinctCross_slide_inner (hij : i ≠ j) :
    probeOldActionDistinctCross D Sc m i j Λ h₁ h₂ h₃ h₄ ≫ (probeOldActionDot D Sc m i Λ h₃ ▷ probeOldE D Sc m j Λ h₄) =
      sign k (D.parity i * D.parity j) •
        ((probeOldE D Sc m j Λ h₁ ◁ probeOldActionDot D Sc m i Λ h₂) ≫ probeOldActionDistinctCross D Sc m i j Λ h₁ h₂ h₃ h₄) := by
  apply OddMath.HomogeneousSuperfunctorIso.total_ext
  intro M
  rw [Superfunctor.comp_total, distinct_total_smul, Superfunctor.comp_total]
  funext ε
  change (probeOldActionDistinctCross D Sc m i j Λ h₁ h₂ h₃ h₄).total M ε ≫
      (probeOldActionDot D Sc m i Λ h₃ ▷ probeOldE D Sc m j Λ h₄).total M ε =
    sign k (D.parity i * D.parity j) •
      ((probeOldE D Sc m j Λ h₁ ◁ probeOldActionDot D Sc m i Λ h₂).total M ε ≫
        (probeOldActionDistinctCross D Sc m i j Λ h₁ h₂ h₃ h₄).total M ε)
  by_cases hε : ∃ β, blockSucc₂ D i j Λ h₁ h₂ β = ε
  · obtain ⟨β, hβ⟩ := hε
    rw [probeOldActionDistinctCross_total_of D Sc m i j Λ h₁ h₂ h₃ h₄ β ε hβ,
      probeOldPairInnerDotTo_total D Sc m j i Λ h₃ h₄ β ε (sw hβ),
      probeOldPairOuterDotTo_total D Sc m i j Λ h₁ h₂ β ε hβ]
    have hb := congrArg (fun f => f.total (M β))
      (probeOldBlockDistinctCross_slide_inner D Sc m i j Λ h₁ h₂ h₃ h₄ hij β ε hβ)
    rw [Superfunctor.comp_total, distinct_total_smul, Superfunctor.comp_total] at hb
    exact distinct_conjugate_slide _ _ _ _ _ _ hb
  · exact (probeOldEFunctor_comp₂_isZero D Sc m i j Λ h₁ h₂ ε hε M).eq_of_src _ _

theorem probeOldActionDistinctCross_slide_outer (hij : i ≠ j) :
    probeOldActionDistinctCross D Sc m i j Λ h₁ h₂ h₃ h₄ ≫ (probeOldE D Sc m i Λ h₃ ◁ probeOldActionDot D Sc m j Λ h₄) =
      sign k (D.parity i * D.parity j) •
        ((probeOldActionDot D Sc m j Λ h₁ ▷ probeOldE D Sc m i Λ h₂) ≫ probeOldActionDistinctCross D Sc m i j Λ h₁ h₂ h₃ h₄) := by
  apply OddMath.HomogeneousSuperfunctorIso.total_ext
  intro M
  rw [Superfunctor.comp_total, distinct_total_smul, Superfunctor.comp_total]
  funext ε
  change (probeOldActionDistinctCross D Sc m i j Λ h₁ h₂ h₃ h₄).total M ε ≫
      (probeOldE D Sc m i Λ h₃ ◁ probeOldActionDot D Sc m j Λ h₄).total M ε =
    sign k (D.parity i * D.parity j) •
      ((probeOldActionDot D Sc m j Λ h₁ ▷ probeOldE D Sc m i Λ h₂).total M ε ≫
        (probeOldActionDistinctCross D Sc m i j Λ h₁ h₂ h₃ h₄).total M ε)
  by_cases hε : ∃ β, blockSucc₂ D i j Λ h₁ h₂ β = ε
  · obtain ⟨β, hβ⟩ := hε
    rw [probeOldActionDistinctCross_total_of D Sc m i j Λ h₁ h₂ h₃ h₄ β ε hβ,
      probeOldPairOuterDotTo_total D Sc m j i Λ h₃ h₄ β ε (sw hβ),
      probeOldPairInnerDotTo_total D Sc m i j Λ h₁ h₂ β ε hβ]
    have hb := congrArg (fun f => f.total (M β))
      (probeOldBlockDistinctCross_slide_outer D Sc m i j Λ h₁ h₂ h₃ h₄ hij β ε hβ)
    rw [Superfunctor.comp_total, distinct_total_smul, Superfunctor.comp_total] at hb
    exact distinct_conjugate_slide _ _ _ _ _ _ hb
  · exact (probeOldEFunctor_comp₂_isZero D Sc m i j Λ h₁ h₂ ε hε M).eq_of_src _ _

end Crossing
end OddMath.QuiverHecke
