import OddMath.SKM.SameColourSourceCoordinates
import OddMath.SKM.PairedSourceNormalization

/-! Paired source columns are supported on the actual swapped paired sector,
including the downward-dot normalization and the full input coefficient twist. -/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Presentation
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k}

private def sourceCapSpan (i : I) (μ : X) :
    Submodule k ((pres D Sc).obj (ob D μ [up i, dn i]) ⟶ (pres D Sc).obj (ob D μ [])) :=
  Submodule.span k (Set.range fun mz : ℕ × End ((pres D Sc).obj (ob D μ [])) =>
    eLM D Sc i μ mz.1 ≫ mz.2)

private theorem sourceCapSpan_generator (i : I) (μ : X) (m : ℕ)
    (z : End ((pres D Sc).obj (ob D μ []))) :
    eLM D Sc i μ m ≫ z ∈ sourceCapSpan (Sc := Sc) i μ :=
  Submodule.subset_span ⟨(m, z), rfl⟩

private theorem sourceCapSpan_comp (i : I) (μ : X)
    {f : (pres D Sc).obj (ob D μ [up i, dn i]) ⟶ (pres D Sc).obj (ob D μ [])}
    (hf : f ∈ sourceCapSpan (Sc := Sc) i μ) (z : End ((pres D Sc).obj (ob D μ []))) :
    f ≫ z ∈ sourceCapSpan (Sc := Sc) i μ := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨⟨m, w⟩, rfl⟩ := hf
    simpa only [Category.assoc] using sourceCapSpan_generator i μ m (w ≫ z)
  | zero => simp
  | add f g _ _ hf hg => simpa only [Preadditive.add_comp] using Submodule.add_mem _ hf hg
  | smul a f _ hf => simpa only [Linear.smul_comp] using Submodule.smul_mem _ a hf

private theorem sourceCapSpan_precomp (i : I) (μ : X) (b : ℕ)
    {f : (pres D Sc).obj (ob D μ [up i, dn i]) ⟶ (pres D Sc).obj (ob D μ [])}
    (hf : f ∈ sourceCapSpan (Sc := Sc) i μ) :
    cpow (uLM D Sc i μ) b ≫ f ∈ sourceCapSpan (Sc := Sc) i μ := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨⟨m, z⟩, rfl⟩ := hf
    rw [← Category.assoc, cpow_uL_eL]
    exact sourceCapSpan_generator i μ (b + m) z
  | zero => simp
  | add f g _ _ hf hg => simpa only [Preadditive.comp_add] using Submodule.add_mem _ hf hg
  | smul a f _ hf => simpa only [Linear.comp_smul] using Submodule.smul_mem _ a hf

private theorem sourceCapSpan_initial (cs : CScalars Sc) (i : I) (μ : X) :
    sgM D Sc i μ ≫ epsP cs i μ ∈ sourceCapSpan (Sc := Sc) i μ := by
  by_cases hh : 0 ≤ D.h i μ
  · rw [paired_source_initial cs i μ hh]
    apply Submodule.smul_mem
    apply Submodule.sub_mem
    · apply Submodule.sum_mem
      intro j _
      exact sourceCapSpan_generator i μ j _
    · simpa only [Category.comp_id] using sourceCapSpan_generator (Sc := Sc) i μ
        (D.h i μ).toNat (𝟙 _)
  · rw [eq_2_14_a cs i μ (by omega)]
    exact Submodule.zero_mem _

private theorem sourceCapSpan_upward (cs : CScalars Sc) (i : I) (μ : X) (b : ℕ) :
    sgM D Sc i μ ≫ cpow (uRM D Sc i μ) b ≫ epsP cs i μ ∈
      sourceCapSpan (Sc := Sc) i μ := by
  rw [paired_source_expansion cs i μ b]
  apply Submodule.add_mem
  · apply Submodule.smul_mem
    exact sourceCapSpan_precomp i μ b (sourceCapSpan_initial cs i μ)
  · apply Submodule.sum_mem
    intro s _
    apply Submodule.smul_mem
    exact sourceCapSpan_generator i μ s _

private theorem sourceCapSpan_downward (cs : CScalars Sc) (i : I) (μ : X) (b : ℕ) :
    sgM D Sc i μ ≫ cpow (dLM D Sc i μ) b ≫ epsP cs i μ ∈
      sourceCapSpan (Sc := Sc) i μ := by
  obtain ⟨a, z, _, _, H⟩ := source_cap_downward_triangular cs i μ b
  rw [H, Preadditive.comp_add, Linear.comp_smul]
  apply Submodule.add_mem
  · exact Submodule.smul_mem _ a (sourceCapSpan_upward cs i μ b)
  · simpa only [Category.assoc] using
      sourceCapSpan_comp i μ (sourceCapSpan_upward cs i μ (b - 1)) z

namespace SameColourSourceFrame
variable {P Q Z : List (Letter I)} {i : I} (F : SameColourSourceFrame P Q Z i)
  {cs : CScalars Sc} {μ : X}

private theorem swappedCoordinates_local_capSpan_off
    (hG : Function.Injective (F.swapped.expansion cs μ))
    (f : (pres D Sc).obj (ob D μ (P ++ Q)) ⟶ (pres D Sc).obj (ob D μ Z))
    {g : (pres D Sc).obj (ob D (wt D μ Q) [up i, dn i]) ⟶
      (pres D Sc).obj (ob D (wt D μ Q) [])}
    (hg : g ∈ sourceCapSpan (Sc := Sc) i (wt D μ Q))
    (d : SYM D k) (t : F.original.Labels) (ht : t ∉ Set.range F.paired) :
    F.swappedCoordinates hG (MatchingBasisChoice.rightAction cs μ
      (plcW μ (P ++ up i :: dn i :: Q) (P ++ Q) P Q [up i, dn i] [] g ≫ f) d)
        (F.exchange t) = 0 := by
  induction hg using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨⟨m, z⟩, rfl⟩ := hg
    rw [← sourcePlcW_comp_at μ _ _ (P ++ Q) P Q [up i, dn i] [] [] (by simp), Category.assoc]
    exact F.swappedCoordinates_cap_rightAction_off hG _ m d t ht
  | zero => simp [MatchingBasisChoice.rightAction]
  | add g h _ _ hg hh =>
    simp only [map_add, Preadditive.add_comp, MatchingBasisChoice.rightAction,
      Preadditive.comp_add, Finsupp.add_apply] at *
    rw [hg, hh, add_zero]
  | smul a g _ hg =>
    simp only [map_smul, Linear.smul_comp, MatchingBasisChoice.rightAction,
      Linear.comp_smul, Finsupp.smul_apply] at *
    rw [hg, smul_zero]

/-- Every actual paired original column has zero unpaired principal coordinates. -/
theorem swappedCoordinates_paired_cross_off
    (hG : Function.Injective (F.swapped.expansion cs μ)) (b : ℕ)
    (r : F.residual.Labels) (d : SYM D k) (t : F.original.Labels)
    (ht : t ∉ Set.range F.paired) :
    F.swappedCoordinates hG
      (sameColourSourceCross (Sc := Sc) μ P Q i ≫
        F.original.expansion cs μ (Finsupp.single (F.paired (b, r)) d)) (F.exchange t) = 0 := by
  rw [F.original.source_expansion_single, F.original_row, sameColourSourceCross_rightAction]
  unfold sameColourSourceCross
  rw [← Category.assoc, sourcePlcW_comp_at μ _ _ (P ++ dn i :: up i :: Q)
    P Q [up i, dn i] [dn i, up i] [] (by simp)]
  exact F.swappedCoordinates_local_capSpan_off hG _
    (sourceCapSpan_downward cs i (wt D μ Q) b) _ t ht

end SameColourSourceFrame
end OddMath.SKM
