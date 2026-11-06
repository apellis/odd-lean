import OddMath.SKM.MateN

/-!
# Right closure for the oriented nondegeneracy reduction

Literal right-adjunction closure of a sorted boundary, using the cups and
caps of Brundan–Ellis, *Super Kac–Moody 2-categories*, Definition 2.1.
The mixed-crossing calculation is the elementary sweep step needed in the
proposed reduction of the §8 nondegeneracy conjecture to upward independence.
It does not use independence or an unrestricted pivotal isotopy principle.
-/

noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Presentation
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k}

/-- Close the downward source suffix and target prefix using right cups/caps.
The middle diagram has boundary `u ++ dns r → dns l ++ v`. -/
def rightClosureL (l r : List I) (u v : List (Letter I))
    (A : List (LayerData I)) : List (LayerData I) :=
  (cupN r).map (whL (ups l ++ u) []) ++ A.map (whL (ups l) (ups r)) ++
    (capN l).map (whL [] (v ++ ups r))

theorem sChain_rightClosureL (l r : List I) (u v : List (Letter I))
    {A : List (LayerData I)} (hA : SChain (u ++ dns r) A (dns l ++ v)) :
    SChain (ups l ++ u) (rightClosureL l r u v A) (v ++ ups r) := by
  unfold rightClosureL
  refine SChain.append (t' := ups l ++ (dns l ++ v) ++ ups r)
    (SChain.append (t' := ups l ++ (u ++ dns r) ++ ups r) ?_ ?_) ?_
  · exact (sChain_cupN r).wh (ups l ++ u) [] (by simp) (by simp [List.append_assoc])
  · exact hA.whisk (ups l) (ups r)
  · exact (sChain_capN l).wh [] (v ++ ups r) (by simp [List.append_assoc]) (by simp)

/-- The evaluated closure is a linear map. The external region of its input
is `wt D μ (ups r)`, not `μ`. -/
def rightClosure (D : Datum I X) (Sc : Scalars D k) (μ : X)
    (l r : List I) (u v : List (Letter I)) :
    ((pres D Sc).obj (ob D (wt D μ (ups r)) (u ++ dns r)) ⟶
      (pres D Sc).obj (ob D (wt D μ (ups r)) (dns l ++ v))) →ₗ[k]
    ((pres D Sc).obj (ob D μ (ups l ++ u)) ⟶
      (pres D Sc).obj (ob D μ (v ++ ups r))) :=
  ctxL D Sc μ (ups l ++ u) (v ++ ups r)
    ((cupN r).map (whL (ups l ++ u) [])) (ups l) (ups r)
    ((capN l).map (whL [] (v ++ ups r))) (u ++ dns r) (dns l ++ v)

theorem rightClosure_cl (μ : X) (l r : List I) (u v : List (Letter I))
    (A : List (LayerData I)) :
    rightClosure D Sc μ l r u v
      (cl D Sc (wt D μ (ups r)) (u ++ dns r) (dns l ++ v) A) =
    cl D Sc μ (ups l ++ u) (v ++ ups r) (rightClosureL l r u v A) := by
  apply ctxL_cl
  · exact (sChain_cupN r).wh (ups l ++ u) [] (by simp) (by simp [List.append_assoc])
  · exact (sChain_capN l).wh [] (v ++ ups r) (by simp [List.append_assoc]) (by simp)

/-- Bend the left source prefix and right target suffix of a layer block
using right adjunctions. This definition does not assert strict reducedness. -/
def partialRightMateL (l r : List I) (u v : List (Letter I))
    (A : List (LayerData I)) : List (LayerData I) :=
  (cupN l).map (whL [] (u ++ dns r)) ++ A.map (whL (dns l) (dns r)) ++
    (capN r).map (whL (dns l ++ v) [])

variable (Sc) in
/-- A literal partial right mate is undone by the sorted right closure.
The proof uses two word zigzags and interchanges only even cup/cap blocks.
No strictness of the mate or independence of either diagram family is assumed. -/
theorem cl_rightClosure_partialMate (μ : X) (l r : List I) (u v : List (Letter I))
    {A : List (LayerData I)} (hA : SChain (ups l ++ u) A (v ++ ups r)) :
    cl D Sc μ (ups l ++ u) (v ++ ups r)
      (rightClosureL l r u v (partialRightMateL l r u v A)) =
    cl D Sc μ (ups l ++ u) (v ++ ups r) A := by
  let B := A.map (whL [] (dns r)) ++ (capN r).map (whL v [])
  have hB : SChain (ups l ++ u ++ dns r) B v := by
    refine SChain.append (t' := v ++ ups r ++ dns r) ?_ ?_
    · exact hA.wh [] (dns r) (by simp) (by simp)
    · exact (sChain_capN r).wh v [] (by simp [List.append_assoc]) (by simp)
  have h1 : cl D Sc μ (ups l ++ u) (v ++ ups r)
      (rightClosureL l r u v (partialRightMateL l r u v A)) =
      cl D Sc μ (ups l ++ u) (v ++ ups r)
        ((cupN r).map (whL (ups l ++ u) []) ++
          (cupN l).map (whL (ups l) (u ++ dns r ++ ups r)) ++
          (capN l).map (whL [] (ups l ++ (u ++ dns r ++ ups r))) ++
          B.map (whL [] (ups r))) := by
    have E := cl_ixc_even (D := D) (Sc := Sc) (μ := μ)
      (S := ups l ++ u) (T := v ++ ups r)
      ((cupN r).map (whL (ups l ++ u) []) ++
        (cupN l).map (whL (ups l) (u ++ dns r ++ ups r))) [] [] [] (ups r)
      (sChain_capN l) hB (Or.inl (parsum_capN l))
    simpa [rightClosureL, partialRightMateL, B, List.append_assoc] using E.symm
  have h2 : cl D Sc μ (ups l ++ u) (v ++ ups r)
      ((cupN r).map (whL (ups l ++ u) []) ++
        (cupN l).map (whL (ups l) (u ++ dns r ++ ups r)) ++
        (capN l).map (whL [] (ups l ++ (u ++ dns r ++ ups r))) ++
        B.map (whL [] (ups r))) =
      cl D Sc μ (ups l ++ u) (v ++ ups r)
        ((cupN r).map (whL (ups l ++ u) []) ++ B.map (whL [] (ups r))) := by
    simpa using cl_zigE_ctx (zigE_N Sc l) μ ((cupN r).map (whL (ups l ++ u) []))
      (B.map (whL [] (ups r))) [] (u ++ dns r ++ ups r)
      ((sChain_cupN r).wh (ups l ++ u) [] (by simp) (by simp [List.append_assoc]))
      (hB.wh [] (ups r) (by simp [List.append_assoc]) (by simp))
  have h3 : cl D Sc μ (ups l ++ u) (v ++ ups r)
      ((cupN r).map (whL (ups l ++ u) []) ++ B.map (whL [] (ups r))) =
      cl D Sc μ (ups l ++ u) (v ++ ups r)
        (A ++ (cupN r).map (whL (v ++ ups r) []) ++
          (capN r).map (whL v (ups r))) := by
    have E := cl_ixc_even (D := D) (Sc := Sc) (μ := μ)
      (S := ups l ++ u) (T := v ++ ups r) [] ((capN r).map (whL v (ups r))) [] [] []
      hA (sChain_cupN r) (Or.inr (parsum_cupN r))
    simpa [B, List.append_assoc] using E.symm
  have h4 : cl D Sc μ (ups l ++ u) (v ++ ups r)
      (A ++ (cupN r).map (whL (v ++ ups r) []) ++
        (capN r).map (whL v (ups r))) =
      cl D Sc μ (ups l ++ u) (v ++ ups r) A := by
    simpa using cl_zigE_ctx (zigE_N Sc r) μ A [] v []
      (by simpa using hA) (by simp [SChain])
  exact h1.trans (h2.trans (h3.trans h4))

end OddMath.SKM
