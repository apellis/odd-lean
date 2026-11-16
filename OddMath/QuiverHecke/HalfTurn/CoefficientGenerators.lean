/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.HalfTurn.IdealIdentification

/-!
# The half-turn and extra coefficient generators

`docs/Nondegeneracy/SwappedVacuumCoordinates.md` §§5–6: the transformed ideal `K_(N,T)` may
contain the coefficient-power ideal `T` of a nilpotent reservoir, a set of coefficients imposed as
the extra generators `a ⊗ 1`, `a ∈ T`. The half-turn fixes these generators (`U(a ⊗ 1) = a ⊗ 1`),
so for homogeneous `T` the half-turn identifies `K_(N,T)` with `I_N + (T)`, where `(T)` is the
two-sided span of the same generators for the twisted parameters.

## Main declarations

* `CoefficientGeneratorSpan`: the two-sided span `(T)` of the generators `a ⊗ 1`, `a ∈ T`.
* `transformedIdeal_eq_sup`: `K_(N,T) = K_N + (T)`.
* `map_htCoef_coefficientGeneratorSpan`: `U((T)) = (T)` for homogeneous `T`.
* `map_htCoef_transformedIdeal_sup`: **`U(K_(N,T)) = I_N + (T)`** for homogeneous `T`.
* `comap_htCoef_elvRelationSpan_sup`: **`U⁻¹(I_N + (T)) = K_(N,T)`**.
-/

noncomputable section
open scoped Classical TensorProduct
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams Supercategory
open SKM (zsign)
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k)

/-- The two-sided span of the coefficient generators `a ⊗ 1`, `a ∈ T`, with arbitrary
coefficient-extended affine multipliers, at fixed strand number. -/
def CoefficientGeneratorSpan (T : Set (SKM.SYM D k)) (s t : List I) :
    Submodule k (coefficientObj D Sc s ⟶ coefficientObj D Sc t) :=
  Submodule.span k {f | ∃ v : List I, v.length = s.length ∧ ∃ a ∈ T,
    ∃ x : coefficientObj D Sc s ⟶ coefficientObj D Sc v,
    ∃ y : coefficientObj D Sc v ⟶ coefficientObj D Sc t,
      x ≫ sourceCoefficientHom D Sc a (𝟙 ((pres D Sc).obj (ob D v))) ≫ y = f}

/-- **`K_(N,T) = K_N + (T)`**: the extra coefficients of the transformed ideal contribute
exactly their two-sided span. -/
theorem transformedIdeal_eq_sup (cutoff : I → ℕ) (T : Set (SKM.SYM D k)) (s t : List I) :
    TransformedIdeal D Sc cutoff T s t =
      TransformedIdeal D Sc cutoff ∅ s t ⊔ CoefficientGeneratorSpan D Sc T s t := by
  refine le_antisymm (Submodule.span_le.mpr ?_) (sup_le (Submodule.span_mono ?_)
    (Submodule.span_le.mpr ?_))
  · rintro _ ⟨v, hv, r, hr, a, b, rfl⟩
    rcases hr with h | ⟨c, hc, rfl⟩ | h
    · exact Submodule.mem_sup_left (Submodule.subset_span ⟨v, hv, r, Or.inl h, a, b, rfl⟩)
    · exact Submodule.mem_sup_right (Submodule.subset_span ⟨v, hv, c, hc, a, b, rfl⟩)
    · exact Submodule.mem_sup_left
        (Submodule.subset_span ⟨v, hv, r, Or.inr (Or.inr h), a, b, rfl⟩)
  · rintro _ ⟨v, hv, r, hr, a, b, rfl⟩
    refine ⟨v, hv, r, ?_, a, b, rfl⟩
    rcases hr with h | ⟨c, hc, _⟩ | h
    · exact Or.inl h
    · exact absurd hc (Set.notMem_empty c)
    · exact Or.inr (Or.inr h)
  · rintro _ ⟨v, hv, c, hc, a, b, rfl⟩
    exact Submodule.subset_span ⟨v, hv, _, Or.inr (Or.inl ⟨c, hc, rfl⟩), a, b, rfl⟩

/-- The half-turn maps the span of homogeneous coefficient generators into the span of the same
generators for the twisted parameters: `U(x ≫ a ⊗ 1 ≫ y) = ± U(y) ≫ a ⊗ 1 ≫ U(x)`. -/
theorem htCoef_coefficientGeneratorSpan_le (T : Set (SKM.SYM D k))
    (hT : ∀ a ∈ T, ∃ q, CoefParity D q a) (s t : List I) :
    (CoefficientGeneratorSpan D Sc T s t).map (htCoef D Sc s t) ≤
      CoefficientGeneratorSpan D (parameterTwist D Sc) T t.reverse s.reverse := by
  rw [Submodule.map_le_iff_le_comap]
  apply Submodule.span_le.mpr
  rintro _ ⟨v, -, γ, hγ, a, b, rfl⟩
  obtain ⟨q, hq⟩ := hT γ hγ
  simp only [SetLike.mem_coe, Submodule.mem_comap]
  refine coef_induction D Sc (P := fun a => htCoef D Sc s t
    (a ≫ sourceCoefficientHom D Sc γ (𝟙 ((pres D Sc).obj (ob D v))) ≫ b) ∈
      CoefficientGeneratorSpan D (parameterTwist D Sc) T t.reverse s.reverse) ?_ ?_ ?_ a
  · simp
  · intro x y hx hy
    rw [Preadditive.add_comp, map_add]; exact Submodule.add_mem _ hx hy
  intro p α hα A hA
  refine coef_induction D Sc (P := fun b => htCoef D Sc s t
    (sourceCoefficientHom D Sc α ((pres D Sc).diag (mkD D A hA)) ≫
      sourceCoefficientHom D Sc γ (𝟙 ((pres D Sc).obj (ob D v))) ≫ b) ∈
      CoefficientGeneratorSpan D (parameterTwist D Sc) T t.reverse s.reverse) ?_ ?_ ?_ b
  · simp
  · intro x y hx hy
    rw [Preadditive.comp_add, Preadditive.comp_add, map_add]; exact Submodule.add_mem _ hx hy
  intro _ β _ C hC
  have e1 : (𝟙 ((pres D Sc).obj (ob D v))) =
      (pres D Sc).diag (mkD D [] (t := v) (t' := v) rfl) := by
    rw [← Presentation.diag_id]; rfl
  have e2 : htPres D Sc v v ((pres D Sc).diag (mkD D [] (t := v) (t' := v) rfl)) = 𝟙 _ := by
    rw [← e1]; exact htPres_id D Sc v
  rw [e1, htCoef_sandwich D Sc hα hq β A [] C hA rfl hC, e2]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨v.reverse, ?_, γ, hγ, _, _, rfl⟩)
  simp [sChain_length hC]

theorem scalarsCast_mem_coefficientGeneratorSpan {Sc₁ Sc₂ : SKM.Scalars D k} (e : Sc₁ = Sc₂)
    {s s' t t' : List I} (hs : s = s') (ht : t = t') (T : Set (SKM.SYM D k))
    {x : coefficientObj D Sc₁ s ⟶ coefficientObj D Sc₁ t}
    (hx : x ∈ CoefficientGeneratorSpan D Sc₁ T s t) :
    scalarsCast D e hs ht x ∈ CoefficientGeneratorSpan D Sc₂ T s' t' := by
  subst e hs ht; exact hx

/-- **`U((T)) = (T)`** for a set `T` of homogeneous coefficients. -/
theorem map_htCoef_coefficientGeneratorSpan (T : Set (SKM.SYM D k))
    (hT : ∀ a ∈ T, ∃ q, CoefParity D q a) (s t : List I) :
    (CoefficientGeneratorSpan D Sc T s t).map (htCoef D Sc s t) =
      CoefficientGeneratorSpan D (parameterTwist D Sc) T t.reverse s.reverse := by
  refine le_antisymm (htCoef_coefficientGeneratorSpan_le D Sc T hT s t) fun y hy => ?_
  refine ⟨htCoefInv D Sc s t y, ?_, htCoef_htCoefInv D Sc y⟩
  exact scalarsCast_mem_coefficientGeneratorSpan D _ _ _ T
    (htCoef_coefficientGeneratorSpan_le D (parameterTwist D Sc) T hT t.reverse s.reverse
      (Submodule.mem_map_of_mem hy))

/-- **`U(K_(N,T)) = I_N + (T)`** (`SwappedVacuumCoordinates.md` §§5–6) for a set `T` of
homogeneous coefficients: the half-turn fixes the extra coefficient generators. -/
theorem map_htCoef_transformedIdeal_sup (cutoff : I → ℕ) (T : Set (SKM.SYM D k))
    (hT : ∀ a ∈ T, ∃ q, CoefParity D q a) (s t : List I) :
    (TransformedIdeal D Sc cutoff T s t).map (htCoef D Sc s t) =
      ELVRelationSpan D (parameterTwist D Sc) cutoff t.reverse s.reverse ⊔
        CoefficientGeneratorSpan D (parameterTwist D Sc) T t.reverse s.reverse := by
  rw [transformedIdeal_eq_sup, Submodule.map_sup, map_htCoef_transformedIdeal,
    map_htCoef_coefficientGeneratorSpan D Sc T hT]

/-- **`U⁻¹(I_N + (T)) = K_(N,T)`** for a set `T` of homogeneous coefficients. -/
theorem comap_htCoef_elvRelationSpan_sup (cutoff : I → ℕ) (T : Set (SKM.SYM D k))
    (hT : ∀ a ∈ T, ∃ q, CoefParity D q a) (s t : List I) :
    (ELVRelationSpan D (parameterTwist D Sc) cutoff t.reverse s.reverse ⊔
        CoefficientGeneratorSpan D (parameterTwist D Sc) T t.reverse s.reverse).comap
          (htCoef D Sc s t) = TransformedIdeal D Sc cutoff T s t := by
  rw [← map_htCoef_transformedIdeal_sup D Sc cutoff T hT,
    Submodule.comap_map_eq_of_injective (htCoef_injective D Sc s t)]

end OddMath.QuiverHecke
