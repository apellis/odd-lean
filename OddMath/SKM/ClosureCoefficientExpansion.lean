import OddMath.SKM.RightClosure
import OddMath.SKM.UpwardWordTransport

/-! Actual full-SYM coefficients under sorted right closure. -/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Presentation
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k}

private theorem rightClosure_bubAt_cl (μ : X) (l r : List I) (u v : List (Letter I))
    {A B : List (LayerData I)} (hA : SChain (u ++ dns r) A (dns l ++ v))
    (hB : SChain [] B []) :
    rightClosure D Sc μ l r u v
      (cl D Sc (wt D μ (ups r)) (u ++ dns r) (dns l ++ v) A ≫
        bubAt D Sc (wt D μ (ups r)) (dns l ++ v) (cl D Sc (wt D μ (ups r)) [] [] B)) =
    rightClosure D Sc μ l r u v (cl D Sc (wt D μ (ups r)) (u ++ dns r) (dns l ++ v) A) ≫
      wordCast μ (by simp) (by simp)
        (plcL D Sc μ v (ups r) [] [] (cl D Sc (wt D μ (ups r)) [] [] B)) := by
  rw [bubAt_cl, cl_comp hA (hB.wh (dns l ++ v) [] (by simp) (by simp)),
    rightClosure_cl, rightClosure_cl, plcL_cl, wordCast_cl,
    cl_comp (sChain_rightClosureL l r u v hA) (hB.wh v (ups r) (by simp) (by simp))]
  have E := cl_ixc_even (D := D) (Sc := Sc) (μ := μ) (S := ups l ++ u) (T := v ++ ups r)
    ((cupN r).map (whL (ups l ++ u) []) ++ A.map (whL (ups l) (ups r)))
    [] [] v (ups r) (sChain_capN l) hB (Or.inl (parsum_capN l))
  simpa [rightClosureL, List.append_assoc] using E.symm

/-- A rightmost coefficient on the original oriented diagram closes into
the region immediately to the left of the added upward suffix. -/
theorem rightClosure_bubAt (μ : X) (l r : List I) (u v : List (Letter I))
    (f : (pres D Sc).obj (ob D (wt D μ (ups r)) (u ++ dns r)) ⟶
      (pres D Sc).obj (ob D (wt D μ (ups r)) (dns l ++ v)))
    (β : (pres D Sc).obj (ob D (wt D μ (ups r)) []) ⟶
      (pres D Sc).obj (ob D (wt D μ (ups r)) [])) :
    rightClosure D Sc μ l r u v (f ≫ bubAt D Sc (wt D μ (ups r)) (dns l ++ v) β) =
      rightClosure D Sc μ l r u v f ≫
        wordCast μ (by simp) (by simp) (plcL D Sc μ v (ups r) [] [] β) := by
  induction mem_span_cl (wt D μ (ups r)) β using Submodule.span_induction with
  | mem β hβ =>
    obtain ⟨B, hB, rfl⟩ := hβ
    induction mem_span_cl (wt D μ (ups r)) f using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨A, hA, rfl⟩ := hf
      exact rightClosure_bubAt_cl μ l r u v hA hB
    | zero => simp only [Limits.zero_comp, map_zero]
    | add f g _ _ hf hg => simp only [Preadditive.add_comp, map_add, hf, hg]
    | smul a f _ hf => simp only [Linear.smul_comp, map_smul, hf]
  | zero => simp only [map_zero, Limits.comp_zero]
  | add β γ _ _ hβ hγ => simp only [map_add, Preadditive.comp_add, hβ, hγ]
  | smul a β _ hβ => simp only [map_smul, Linear.comp_smul, hβ]

/-- Full coefficients under the actual right closure: the principal term is
unchanged, and the error appends a nonempty upward dot diagram. -/
theorem rightClosure_betaSYM_expansion (cs : CScalars Sc) (μ : X)
    (l r : List I) (u v : List (Letter I))
    (f : (pres D Sc).obj (ob D (wt D μ (ups r)) (u ++ dns r)) ⟶
      (pres D Sc).obj (ob D (wt D μ (ups r)) (dns l ++ v))) (p : SYM D k) :
    ∃ z : PositiveWordDots (v ++ [] ++ ups r) →₀ SYM D k,
      rightClosure D Sc μ l r u v
        (f ≫ bubAt D Sc (wt D μ (ups r)) (dns l ++ v) (betaSYM cs (wt D μ (ups r)) p)) =
      rightClosure D Sc μ l r u v f ≫ bubAt D Sc μ (v ++ ups r) (betaSYM cs μ p) +
        rightClosure D Sc μ l r u v f ≫ wordCast μ (by simp) (by simp)
          (positiveWordExpansion cs μ (v ++ [] ++ ups r) z) := by
  obtain ⟨z, hz⟩ := betaSYM_exists_positiveWordExpansion cs μ r v p
  refine ⟨z, ?_⟩
  rw [rightClosure_bubAt, hz, map_add, Preadditive.comp_add, ← bubAt_congr]

/-- The native weak-mate closure coefficient identity. For any actual upward
layer diagram `A`, bending and closing its coefficient-decorated mate gives
`A` with the same coefficient, plus `A` followed by strictly positive dots.
No reducedness or independence is assumed by this identity. -/
theorem rightClosure_partialMate_betaSYM_expansion (cs : CScalars Sc) (μ : X)
    (l r : List I) (u v : List (Letter I)) {A : List (LayerData I)}
    (hA : SChain (ups l ++ u) A (v ++ ups r)) (p : SYM D k) :
    ∃ z : PositiveWordDots (v ++ [] ++ ups r) →₀ SYM D k,
      rightClosure D Sc μ l r u v
        (cl D Sc (wt D μ (ups r)) (u ++ dns r) (dns l ++ v) (partialRightMateL l r u v A) ≫
          bubAt D Sc (wt D μ (ups r)) (dns l ++ v) (betaSYM cs (wt D μ (ups r)) p)) =
      cl D Sc μ (ups l ++ u) (v ++ ups r) A ≫ bubAt D Sc μ (v ++ ups r) (betaSYM cs μ p) +
        cl D Sc μ (ups l ++ u) (v ++ ups r) A ≫ wordCast μ (by simp) (by simp)
          (positiveWordExpansion cs μ (v ++ [] ++ ups r) z) := by
  obtain ⟨z, hz⟩ := rightClosure_betaSYM_expansion cs μ l r u v
    (cl D Sc (wt D μ (ups r)) (u ++ dns r) (dns l ++ v) (partialRightMateL l r u v A)) p
  exact ⟨z, by simpa only [rightClosure_cl, cl_rightClosure_partialMate Sc μ l r u v hA] using hz⟩

end OddMath.SKM
