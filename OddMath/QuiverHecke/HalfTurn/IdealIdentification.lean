/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.HalfTurn.Involution

/-!
# The half-turn identifies the transformed ideal with the ELV relation span

`docs/Nondegeneracy/SwappedVacuumCoordinates.md` §5: the inverse image under the half-turn `U` of
the first-boundary ideal `I_N` (`ELVRelationSpan` for the parameters `parameterTwist D Sc`) is the
transformed ideal `K_N` (`TransformedIdeal` with no extra coefficients).

`htCoef_transformedIdeal_le` (`CornerIdeal.lean`) gives `U(K_N) ⊆ I_N`. This file runs the same
computation from the first-strand side: the half-turn maps `I_N` for `Sc` into `K_N` for
`parameterTwist D Sc` (`htCoef_elvRelationSpan_le`); the first-strand cyclotomic polynomial of
colour `i` goes to `±` the transformed last-strand polynomial (4). With the involution
`htCoef_htCoef` this gives the reverse inclusion.

## Main declarations

* `htPres_firstDotPower`: `U(y_first^j) = (-1)^{p(i) C(j,2)} y_last^j`.
* `htCoef_elvRelationSpan_le`: `U(I_N) ⊆ K_N` for the twisted parameters.
* `map_htCoef_transformedIdeal`: **`U(K_N) = I_N`**.
* `comap_htCoef_elvRelationSpan`: **`U⁻¹(I_N) = K_N`**.
-/

noncomputable section
open scoped Classical TensorProduct
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams Supercategory
open SKM (zsign)
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k)

theorem reverse_cons_eq (u : List I) (i : I) : u.reverse ++ [i] = (i :: u).reverse := by simp

set_option backward.isDefEq.respectTransparency false in
/-- **The half-turn of a first-strand dot power**: `U(y_first^j) = (-1)^{p(i) C(j,2)} y_last^j`. -/
theorem htPres_firstDotPower (u : List I) (i : I) (j : ℕ) :
    htPres D Sc (i :: u) (i :: u) (firstDotPower D Sc (i :: u) j) =
      zsign k (D.parity i * (j.choose 2 : ℕ)) •
        (pres D (parameterTwist D Sc)).castHom (congrArg (ob D) (reverse_cons_eq u i))
          (congrArg (ob D) (reverse_cons_eq u i))
          (lastDotPower D (parameterTwist D Sc) (u.reverse ++ [i]) j) := by
  have hc : halfTurnC (k := k) D (pl (i :: u) ((List.replicate j 0).map PG.dot)) =
      zsign k (D.parity i * (j.choose 2 : ℕ)) := by
    rw [firstDot_layers]; exact halfTurnC_replicate_dot D _ i rfl j
  unfold lastDotPower firstDotPower cl
  rw [htPres_diag_mkD, hc, Presentation.castHom_diag]
  congr 1
  apply Presentation.diag_eq_of_layers_eq
  simp only [Diagram.layers_cast, layers_mkD]
  rw [lastDot_layers, firstDot_layers]
  simp [halfTurnL, halfTurnLD]

/-- The sign identity behind the first-strand cyclotomic case. -/
theorem firstCyclotomic_sign_identity (N j P c p A C : ZMod 2) :
    ((N + j) * P * C + p * (j * P + C) + A * (j * P + C) + j * P * C + (N + j) * P * A +
        p * (j * P + A)) + P * c =
      N * P * (A + C) + p * (A + C) + A * C + P * c := by
  revert N j P c p A C; decide

set_option backward.isDefEq.respectTransparency false in
/-- **The half-turn of one term of a first-strand cyclotomic sandwich**: the factor coefficient
`c_j` of `y_first^j` becomes the transformed coefficient `(-1)^{p(i) C(j,2)} c_j` of `y_last^j`,
with a sign independent of `j`. -/
theorem htCoef_firstCyclotomic_term {s w t : List I} {i : I} {p : ZMod 2} {α : SKM.SYM D k}
    (hα : CoefParity D p α) (β : SKM.SYM D k) (A C : List (LayerData I))
    (hA : SChain s A (i :: w)) (hC : SChain (i :: w) C t) (N : ℕ) (j : Fin (N + 1)) :
    htCoef D Sc s t (sourceCoefficientHom D Sc α ((pres D Sc).diag (mkD D A hA)) ≫
        sourceCoefficientHom D Sc (factorCoefficient D i N j)
          (firstDotPower D Sc (i :: w) j.val) ≫
        sourceCoefficientHom D Sc β ((pres D Sc).diag (mkD D C hC))) =
      zsign k ((N : ZMod 2) * D.parity i * (psum D A + psum D C) + p * (psum D A + psum D C) +
          psum D A * psum D C) •
        ((sourceCoefficientHom D (parameterTwist D Sc) α
            (htPres D Sc (i :: w) t ((pres D Sc).diag (mkD D C hC))) ≫
            eqToHom (congrArg (coefficientObj D (parameterTwist D Sc))
              (reverse_cons_eq w i).symm)) ≫
          sourceCoefficientHom D (parameterTwist D Sc) (transformedCoefficient D i N j)
            (lastDotPower D (parameterTwist D Sc) (w.reverse ++ [i]) j.val) ≫
          (eqToHom (congrArg (coefficientObj D (parameterTwist D Sc)) (reverse_cons_eq w i)) ≫
            sourceCoefficientHom D (parameterTwist D Sc) β
              (htPres D Sc s (i :: w) ((pres D Sc).diag (mkD D A hA))))) := by
  have hB := sChain_pl (i :: w) ((List.replicate j.val 0).map PG.dot)
  simp only [tgt_map_dot] at hB
  have e : firstDotPower D Sc (i :: w) j.val = (pres D Sc).diag (mkD D _ hB) := rfl
  rw [e, htCoef_sandwich D Sc hα (coefParity_factorCoefficient D i N j) β A _ C hA hB hC,
    ← e, htPres_firstDotPower, sourceCoefficientHom_smul_right,
    sourceCoefficientHom_castHom D (parameterTwist D Sc) (reverse_cons_eq w i)
      (reverse_cons_eq w i),
    transformedCoefficient, sourceCoefficientHom_smul]
  simp only [Linear.smul_comp, Linear.comp_smul, smul_smul, Category.assoc]
  congr 1
  rw [transformedSign_eq, ← SKM.zsign_add, ← SKM.zsign_add, firstDot_layers, psum_replicate]
  congr 1
  simp only [Shape.parity]
  linear_combination firstCyclotomic_sign_identity (N : ZMod 2) (j.val : ZMod 2) (D.parity i)
    ((j.val.choose 2 : ℕ) : ZMod 2) p (psum D A) (psum D C)

theorem deformedCyclotomic_factorCoefficient_odd (i : {i : I // D.parity i = 1})
    (tail : List I) (N : ℕ) :
    elvCyclotomic D Sc i tail N = ∑ j : Fin (N + 1),
      sourceCoefficientHom D Sc (factorCoefficient D i.1 N j)
        (firstDotPower D Sc (i.1 :: tail) j.val) := by
  simp only [elvCyclotomic, deformedCyclotomic, factorCoefficient, i.2, ↓reduceDIte]

theorem deformedCyclotomic_factorCoefficient_even (i : I) (hi : D.parity i = 0)
    (tail : List I) (N : ℕ) :
    evenCyclotomic D Sc i tail N = ∑ j : Fin (N + 1),
      sourceCoefficientHom D Sc (factorCoefficient D i N j)
        (firstDotPower D Sc (i :: tail) j.val) := by
  have hP : D.parity i ≠ 1 := by rw [hi]; decide
  simp only [evenCyclotomic, deformedCyclotomic, factorCoefficient, hP, ↓reduceDIte]

/-- The half-turn of a first-strand cyclotomic sandwich lies in the transformed ideal. -/
theorem htCoef_firstCyclotomic_mem (cutoff : I → ℕ) {s w t : List I} {i : I} {p : ZMod 2}
    {α : SKM.SYM D k} (hα : CoefParity D p α) (β : SKM.SYM D k) (A C : List (LayerData I))
    (hA : SChain s A (i :: w)) (hC : SChain (i :: w) C t) :
    htCoef D Sc s t (sourceCoefficientHom D Sc α ((pres D Sc).diag (mkD D A hA)) ≫
        (∑ j : Fin (cutoff i + 1), sourceCoefficientHom D Sc (factorCoefficient D i (cutoff i) j)
          (firstDotPower D Sc (i :: w) j.val)) ≫
        sourceCoefficientHom D Sc β ((pres D Sc).diag (mkD D C hC))) ∈
      TransformedIdeal D (parameterTwist D Sc) cutoff ∅ t.reverse s.reverse := by
  simp only [Preadditive.sum_comp, Preadditive.comp_sum, map_sum]
  rw [Finset.sum_congr rfl fun j _ => htCoef_firstCyclotomic_term D Sc hα β A C hA hC (cutoff i) j,
    ← Finset.smul_sum, ← Preadditive.comp_sum, ← Preadditive.sum_comp]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨w.reverse ++ [i], ?_, _, ?_, _, _, rfl⟩)
  · simp [sChain_length hC]
  · refine Or.inr (Or.inr ⟨w.reverse, i, rfl, ?_⟩)
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id, transformedCyclotomic,
      lastBoundaryPolynomial]

/-- **The half-turn maps the ELV relation span into the transformed ideal**: `U(I_N) ⊆ K_N`
for the twisted parameters (`SwappedVacuumCoordinates.md` §5). The coefficient generators `J_N`
go to themselves, and the first-strand cyclotomic polynomial of colour `i` goes, up to a sign, to
the transformed last-strand polynomial (4) of colour `i`. -/
theorem htCoef_elvRelationSpan_le (cutoff : I → ℕ) (s t : List I) :
    (ELVRelationSpan D Sc cutoff s t).map (htCoef D Sc s t) ≤
      TransformedIdeal D (parameterTwist D Sc) cutoff ∅ t.reverse s.reverse := by
  rw [Submodule.map_le_iff_le_comap]
  apply Submodule.span_le.mpr
  rintro _ ⟨v, -, r, hr, a, b, rfl⟩
  simp only [SetLike.mem_coe, Submodule.mem_comap]
  refine coef_induction D Sc (P := fun a => htCoef D Sc s t (a ≫ r ≫ b) ∈
    TransformedIdeal D (parameterTwist D Sc) cutoff ∅ t.reverse s.reverse) ?_ ?_ ?_ a
  · simp
  · intro x y hx hy
    rw [Preadditive.add_comp, map_add]; exact Submodule.add_mem _ hx hy
  intro p α hα A hA
  refine coef_induction D Sc (P := fun b => htCoef D Sc s t
    (sourceCoefficientHom D Sc α ((pres D Sc).diag (mkD D A hA)) ≫ r ≫ b) ∈
      TransformedIdeal D (parameterTwist D Sc) cutoff ∅ t.reverse s.reverse) ?_ ?_ ?_ b
  · simp
  · intro x y hx hy
    rw [Preadditive.comp_add, Preadditive.comp_add, map_add]; exact Submodule.add_mem _ hx hy
  intro _ β _ C hC
  rcases hr with ⟨γ, hγ, rfl⟩ | ⟨i, tail, h, rfl⟩ | ⟨i, hi, tail, h, rfl⟩
  · have e1 : (𝟙 ((pres D Sc).obj (ob D v))) =
        (pres D Sc).diag (mkD D [] (t := v) (t' := v) rfl) := by
      rw [← Presentation.diag_id]; rfl
    have e2 : htPres D Sc v v ((pres D Sc).diag (mkD D [] (t := v) (t' := v) rfl)) = 𝟙 _ := by
      rw [← e1]; exact htPres_id D Sc v
    have hH := elvCoefficientIdeal_le_homogeneousSpan D cutoff hγ
    clear hγ
    induction hH using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨hyJ, q, hq⟩ := hy
      rw [e1, htCoef_sandwich D Sc hα hq β A [] C hA rfl hC, e2]
      refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨v.reverse, ?_, _,
        Or.inl ⟨y, hyJ, rfl⟩, _, _, rfl⟩)
      simp [sChain_length hC]
    | zero => simp
    | add x y _ _ hx hy =>
      rw [sourceCoefficientHom_add_left, Preadditive.add_comp, Preadditive.comp_add, map_add]
      exact Submodule.add_mem _ hx hy
    | smul c x _ hx =>
      rw [sourceCoefficientHom_smul, Linear.smul_comp, Linear.comp_smul, map_smul]
      exact Submodule.smul_mem _ c hx
  · subst h
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rw [deformedCyclotomic_factorCoefficient_odd]
    exact htCoef_firstCyclotomic_mem D Sc cutoff hα β A C hA hC
  · subst h
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rw [deformedCyclotomic_factorCoefficient_even D Sc i hi]
    exact htCoef_firstCyclotomic_mem D Sc cutoff hα β A C hA hC

/-! ## The identification -/

theorem scalarsCast_mem_transformedIdeal {Sc₁ Sc₂ : SKM.Scalars D k} (e : Sc₁ = Sc₂)
    {s s' t t' : List I} (hs : s = s') (ht : t = t') (cutoff : I → ℕ) (T : Set (SKM.SYM D k))
    {x : coefficientObj D Sc₁ s ⟶ coefficientObj D Sc₁ t}
    (hx : x ∈ TransformedIdeal D Sc₁ cutoff T s t) :
    scalarsCast D e hs ht x ∈ TransformedIdeal D Sc₂ cutoff T s' t' := by
  subst e hs ht; exact hx

/-- `I_N ⊆ U(K_N)`: every element of the ELV relation span for the twisted parameters is the
half-turn of an element of the transformed ideal, namely of its preimage `htCoefInv`. -/
theorem htCoefInv_mem_transformedIdeal (cutoff : I → ℕ) {s t : List I}
    {y : coefficientObj D (parameterTwist D Sc) t.reverse ⟶
      coefficientObj D (parameterTwist D Sc) s.reverse}
    (hy : y ∈ ELVRelationSpan D (parameterTwist D Sc) cutoff t.reverse s.reverse) :
    htCoefInv D Sc s t y ∈ TransformedIdeal D Sc cutoff ∅ s t := by
  have h := htCoef_elvRelationSpan_le D (parameterTwist D Sc) cutoff t.reverse s.reverse
    (Submodule.mem_map_of_mem hy)
  exact scalarsCast_mem_transformedIdeal D _ _ _ cutoff ∅ h

/-- **The half-turn identifies the transformed ideal with the ELV relation span**:
`U(K_N) = I_N` (`SwappedVacuumCoordinates.md` §5), for the transformed ideal with no extra
coefficients. -/
theorem map_htCoef_transformedIdeal (cutoff : I → ℕ) (s t : List I) :
    (TransformedIdeal D Sc cutoff ∅ s t).map (htCoef D Sc s t) =
      ELVRelationSpan D (parameterTwist D Sc) cutoff t.reverse s.reverse := by
  refine le_antisymm (htCoef_transformedIdeal_le D Sc cutoff s t) fun y hy => ?_
  exact ⟨htCoefInv D Sc s t y, htCoefInv_mem_transformedIdeal D Sc cutoff hy,
    htCoef_htCoefInv D Sc y⟩

/-- **`U⁻¹(I_N) = K_N`**: the transformed ideal is the inverse image of the ELV relation span
under the half-turn. -/
theorem comap_htCoef_elvRelationSpan (cutoff : I → ℕ) (s t : List I) :
    (ELVRelationSpan D (parameterTwist D Sc) cutoff t.reverse s.reverse).comap (htCoef D Sc s t) =
      TransformedIdeal D Sc cutoff ∅ s t := by
  rw [← map_htCoef_transformedIdeal,
    Submodule.comap_map_eq_of_injective (htCoef_injective D Sc s t)]

end OddMath.QuiverHecke
