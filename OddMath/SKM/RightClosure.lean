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

theorem sChain_partialRightMateL (l r : List I) (u v : List (Letter I))
    {A : List (LayerData I)} (hA : SChain (ups l ++ u) A (v ++ ups r)) :
    SChain (u ++ dns r) (partialRightMateL l r u v A) (dns l ++ v) := by
  unfold partialRightMateL
  refine SChain.append (t' := dns l ++ (v ++ ups r) ++ dns r)
    (SChain.append (t' := dns l ++ (ups l ++ u) ++ dns r) ?_ ?_) ?_
  · exact (sChain_cupN l).wh [] (u ++ dns r) (by simp) (by simp [List.append_assoc])
  · exact hA.whisk (dns l) (dns r)
  · exact (sChain_capN r).wh (dns l ++ v) [] (by simp [List.append_assoc]) (by simp)

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

variable (Sc) in
/-- Closing the mixed crossing gives the upward crossing, with coefficient
one for every pair of colors (including equal odd colors). -/
theorem cl_rightClosure_sigma (μ : X) (i j : I) :
    cl D Sc μ [up i, up j] [up j, up i]
      (rightClosureL [i] [i] [up j] [up j] (sigmaL i j)) =
    cl D Sc μ [up i, up j] [up j, up i] (crossL [] i j []) := by
  let A := [([up i, up j], Shape.cup i, [])] ++
    (crossL [] i j []).map (whL [] [dn i, up i]) ++
    [([up j], Shape.cap i, [up i])]
  let B := crossL [] i j [] ++
    [([up j, up i], Shape.cup i, []), ([up j], Shape.cap i, [up i])]
  have h1 : cl D Sc μ [up i, up j] [up j, up i]
      (rightClosureL [i] [i] [up j] [up j] (sigmaL i j)) =
      cl D Sc μ [up i, up j] [up j, up i] A := by
    apply cl_step (Sc := Sc) μ [([up i, up j], Shape.cup i, [])] [] [] [up i]
      (eq_2_4_a Sc i j (wt D μ [up i]))
      (show SChain [up i, up j] [([up i, up j], Shape.cup i, [])]
        ([] ++ [up i, up j, dn i] ++ [up i]) from ⟨rfl, rfl⟩)
      (show SChain ([] ++ [up j] ++ [up i]) [] [up j, up i] from rfl)
    · simp [rightClosureL, cupN, capN, ups, dns, whL]
    · simp [A, crossL, whL]
  have h2 := cl_interchange (D := D) (Sc := Sc) (μ := μ)
    (S := [up i, up j]) (T := [up j, up i]) []
    [([up j], Shape.cap i, [up i])] (s := [up i, up j]) (s' := [up j, up i])
    (t := []) (t' := [dn i, up i]) (A := crossL [] i j [])
    (B := [([], Shape.cup i, [])])
    (show SChain [up i, up j] (crossL [] i j []) [up j, up i] from ⟨rfl, rfl⟩)
    (show SChain [] [([], Shape.cup i, [])] [dn i, up i] from ⟨rfl, rfl⟩)
  simp only [parsum_cons, parsum_nil, Shape.parity, add_zero, mul_zero,
    zsign_zero, one_smul, List.nil_append] at h2
  have h3 : cl D Sc μ [up i, up j] [up j, up i] B =
      cl D Sc μ [up i, up j] [up j, up i] (crossL [] i j []) := by
    apply cl_step (Sc := Sc) μ (crossL [] i j []) [] [up j] []
      (cl_zigE Sc i (wt D μ []))
      (show SChain [up i, up j] (crossL [] i j []) ([up j] ++ [up i] ++ []) from ⟨rfl, rfl⟩)
      (show SChain ([up j] ++ [up i] ++ []) [] [up j, up i] from rfl)
    · simp [B, whL]
    · simp
  simp only [List.map_cons, List.map_nil, whL, List.nil_append,
    List.append_nil, List.cons_append, List.append_assoc] at h2
  exact h1.trans (h2.symm.trans h3)

/-- A block of right caps followed by a block of right cups, with endpoint
decorations on the corresponding upward words. -/
def pairedRightBlocksL (l r : List I) (A B : List (LayerData I)) : List (LayerData I) :=
  A.map (whL [] (dns r)) ++ capN r ++ cupN l ++ B.map (whL (dns l) [])

variable (Sc) in
/-- Closing decorated cap-cup blocks separates their decorations without
interchanging them. This is the nested-strand version of the elementary
paired sweep, with no restrictions on the colors in either word. -/
theorem cl_rightClosure_pairBlocks (μ : X) (l r : List I)
    {A B : List (LayerData I)} (hA : SChain (ups r) A (ups r))
    (hB : SChain (ups l) B (ups l)) :
    cl D Sc μ (ups l ++ ups r) (ups l ++ ups r)
      (rightClosureL l r (ups r) (ups l) (pairedRightBlocksL l r A B)) =
    cl D Sc μ (ups l ++ ups r) (ups l ++ ups r)
      (A.map (whL (ups l) []) ++ B.map (whL [] (ups r))) := by
  let tail := (cupN l).map (whL (ups l) (ups r)) ++
    B.map (whL (ups l ++ dns l) (ups r)) ++
    (capN l).map (whL [] (ups l ++ ups r))
  have htail : SChain (ups l ++ ups r) tail (ups l ++ ups r) := by
    refine SChain.append (t' := ups l ++ dns l ++ ups l ++ ups r)
      (SChain.append (t' := ups l ++ dns l ++ ups l ++ ups r) ?_ ?_) ?_
    · exact (sChain_cupN l).wh (ups l) (ups r)
        (by simp) (by simp [List.append_assoc])
    · exact hB.wh (ups l ++ dns l) (ups r) rfl rfl
    · exact (sChain_capN l).wh [] (ups l ++ ups r)
        (by simp [List.append_assoc]) (by simp)
  have h1 : cl D Sc μ (ups l ++ ups r) (ups l ++ ups r)
      (rightClosureL l r (ups r) (ups l) (pairedRightBlocksL l r A B)) =
      cl D Sc μ (ups l ++ ups r) (ups l ++ ups r)
        (A.map (whL (ups l) []) ++ (cupN r).map (whL (ups l ++ ups r) []) ++
          (capN r).map (whL (ups l) (ups r)) ++ tail) := by
    have E := cl_ixc_even (D := D) (Sc := Sc) (μ := μ)
      (S := ups l ++ ups r) (T := ups l ++ ups r) []
      ((capN r).map (whL (ups l) (ups r)) ++ tail) (ups l) [] []
      hA (sChain_cupN r) (Or.inr (parsum_cupN r))
    simpa [rightClosureL, pairedRightBlocksL, tail, List.append_assoc] using E.symm
  have h2 : cl D Sc μ (ups l ++ ups r) (ups l ++ ups r)
      (A.map (whL (ups l) []) ++ (cupN r).map (whL (ups l ++ ups r) []) ++
        (capN r).map (whL (ups l) (ups r)) ++ tail) =
      cl D Sc μ (ups l ++ ups r) (ups l ++ ups r)
        (A.map (whL (ups l) []) ++ tail) := by
    simpa using cl_zigE_ctx (zigE_N Sc r) μ (A.map (whL (ups l) [])) tail (ups l) []
      (hA.wh (ups l) [] (by simp) (by simp)) (by simpa using htail)
  have h3 : cl D Sc μ (ups l ++ ups r) (ups l ++ ups r)
      (A.map (whL (ups l) []) ++ tail) =
      cl D Sc μ (ups l ++ ups r) (ups l ++ ups r)
        (A.map (whL (ups l) []) ++ (cupN l).map (whL (ups l) (ups r)) ++
          (capN l).map (whL [] (ups l ++ ups r)) ++ B.map (whL [] (ups r))) := by
    have E := cl_ixc_even (D := D) (Sc := Sc) (μ := μ)
      (S := ups l ++ ups r) (T := ups l ++ ups r)
      (A.map (whL (ups l) []) ++ (cupN l).map (whL (ups l) (ups r))) [] [] [] (ups r)
      (sChain_capN l) hB (Or.inl (parsum_capN l))
    simpa [tail, List.append_assoc] using E.symm
  have h4 : cl D Sc μ (ups l ++ ups r) (ups l ++ ups r)
      (A.map (whL (ups l) []) ++ (cupN l).map (whL (ups l) (ups r)) ++
        (capN l).map (whL [] (ups l ++ ups r)) ++ B.map (whL [] (ups r))) =
      cl D Sc μ (ups l ++ ups r) (ups l ++ ups r)
        (A.map (whL (ups l) []) ++ B.map (whL [] (ups r))) := by
    simpa using cl_zigE_ctx (zigE_N Sc l) μ (A.map (whL (ups l) []))
      (B.map (whL [] (ups r))) [] (ups r)
      (hA.wh (ups l) [] (by simp) (by simp))
      (hB.wh [] (ups r) (by simp) (by simp))
  exact h1.trans (h2.trans (h3.trans h4))

/-- A right cap followed by a right cup, with upward endpoint decorations.
The decorations need not be individual dots. -/
def pairedRightL (i : I) (A B : List (LayerData I)) : List (LayerData I) :=
  A.map (whL [] [dn i]) ++ [([], Shape.cap i, []), ([], Shape.cup i, [])] ++
    B.map (whL [dn i] [])

variable (Sc) in
/-- Literal closure of a decorated cap-cup pair separates the decorations
onto the two upward strands. Their displayed chronological order is retained;
no unsigned interchange of the two possibly odd decorations is made. -/
theorem cl_rightClosure_pair (μ : X) (i : I) {A B : List (LayerData I)}
    (hA : SChain [up i] A [up i]) (hB : SChain [up i] B [up i]) :
    cl D Sc μ [up i, up i] [up i, up i]
      (rightClosureL [i] [i] [up i] [up i] (pairedRightL i A B)) =
    cl D Sc μ [up i, up i] [up i, up i]
      (A.map (whL [up i] []) ++ B.map (whL [] [up i])) := by
  simpa [rightClosureL, pairedRightL, pairedRightBlocksL, cupN, capN,
    ups, dns, List.append_assoc] using
    cl_rightClosure_pairBlocks Sc μ [i] [i] hA hB

variable (Sc) in
/-- Closing a decorated right cap retains its upward decoration. -/
theorem cl_rightClosure_cap (μ : X) (i : I) {A : List (LayerData I)}
    (hA : SChain [up i] A [up i]) :
    cl D Sc μ [up i] [up i]
      (rightClosureL [] [i] [up i] []
        (A.map (whL [] [dn i]) ++ [([], Shape.cap i, [])])) =
    cl D Sc μ [up i] [up i] A := by
  have hcup : SChain [] [([], Shape.cup i, [])] [dn i, up i] := ⟨rfl, rfl⟩
  have E := cl_ixc_even (D := D) (Sc := Sc) (μ := μ) (S := [up i]) (T := [up i])
    [] [([], Shape.cap i, [up i])] [] [] [] hA hcup
    (Or.inr (by simp [Shape.parity]))
  have h1 : cl D Sc μ [up i] [up i]
      (rightClosureL [] [i] [up i] []
        (A.map (whL [] [dn i]) ++ [([], Shape.cap i, [])])) =
      cl D Sc μ [up i] [up i]
        (A ++ [([up i], Shape.cup i, []), ([], Shape.cap i, [up i])]) := by
    simpa [rightClosureL, cupN, capN, ups, dns, whL, List.append_assoc] using E.symm
  have h2 : cl D Sc μ [up i] [up i]
      (A ++ [([up i], Shape.cup i, []), ([], Shape.cap i, [up i])]) =
      cl D Sc μ [up i] [up i] A := by
    apply cl_step (Sc := Sc) μ A [] [] [] (cl_zigE Sc i (wt D μ [])) hA rfl
    · simp
    · simp
  exact h1.trans h2

variable (Sc) in
/-- A downward-dot power survives right closure with the mate reversal
factor. In particular, two odd downward dots give minus the upward square,
not a square-zero relation. -/
theorem cl_rightClosure_downward_cap (μ : X) (i : I) (n : ℕ) :
    cl D Sc μ [up i] [up i]
      (rightClosureL [] [i] [up i] []
        ((ddotsL i n).map (whL [up i] []) ++ [([], Shape.cap i, [])])) =
    zsign k (D.parity i * ((n / 2 : ℕ) : ZMod 2)) •
      cl D Sc μ [up i] [up i] (dotsL [] i [] n) := by
  have E := congrArg (rightClosure D Sc μ [] [i] [up i] [])
    (eq_2_3_b Sc i (wt D μ [up i]) n)
  have hc (L : List (LayerData I)) :
      rightClosure D Sc μ [] [i] [up i] []
        (cl D Sc (wt D μ [up i]) [up i, dn i] [] L) =
      cl D Sc μ [up i] [up i] (rightClosureL [] [i] [up i] [] L) :=
    rightClosure_cl μ [] [i] [up i] [] L
  rw [map_smul, hc, hc] at E
  rw [cl_rightClosure_cap Sc μ i (sChain_dotsL [] i [] n)] at E
  rw [E, smul_smul, zsign_mul_self, one_smul]

end OddMath.SKM
