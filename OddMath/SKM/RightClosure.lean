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
  let tail := [([up i], Shape.cup i, [up i])] ++ B.map (whL [up i, dn i] [up i]) ++
    [([], Shape.cap i, [up i, up i])]
  have htail : SChain [up i, up i] tail [up i, up i] := by
    refine SChain.append (t' := [up i, dn i, up i, up i])
      (SChain.append (t' := [up i, dn i, up i, up i]) ⟨rfl, rfl⟩ ?_) ⟨rfl, rfl⟩
    simpa using hB.whisk [up i, dn i] [up i]
  have hcup : SChain [] [([], Shape.cup i, [])] [dn i, up i] := ⟨rfl, rfl⟩
  have hcap : SChain [up i, dn i] [([], Shape.cap i, [])] [] := ⟨rfl, rfl⟩
  have h1 : cl D Sc μ [up i, up i] [up i, up i]
      (rightClosureL [i] [i] [up i] [up i] (pairedRightL i A B)) =
      cl D Sc μ [up i, up i] [up i, up i]
        (A.map (whL [up i] []) ++
          [([up i, up i], Shape.cup i, []), ([up i], Shape.cap i, [up i])] ++ tail) := by
    have E := cl_ixc_even (D := D) (Sc := Sc) (μ := μ)
      (S := [up i, up i]) (T := [up i, up i]) []
      ([([up i], Shape.cap i, [up i])] ++ tail) [up i] [] [] hA hcup
      (Or.inr (by simp [Shape.parity]))
    simpa [rightClosureL, pairedRightL, cupN, capN, ups, dns, whL,
      tail, List.append_assoc] using E.symm
  have h2 : cl D Sc μ [up i, up i] [up i, up i]
      (A.map (whL [up i] []) ++
        [([up i, up i], Shape.cup i, []), ([up i], Shape.cap i, [up i])] ++ tail) =
      cl D Sc μ [up i, up i] [up i, up i] (A.map (whL [up i] []) ++ tail) := by
    apply cl_step (Sc := Sc) μ (A.map (whL [up i] [])) tail [up i] []
      (cl_zigE Sc i (wt D μ []))
      (hA.wh [up i] [] rfl rfl) htail
    · simp [whL, List.append_assoc]
    · simp
  have h3 : cl D Sc μ [up i, up i] [up i, up i] (A.map (whL [up i] []) ++ tail) =
      cl D Sc μ [up i, up i] [up i, up i]
        (A.map (whL [up i] []) ++
          [([up i], Shape.cup i, [up i]), ([], Shape.cap i, [up i, up i])] ++
          B.map (whL [] [up i])) := by
    have E := cl_ixc_even (D := D) (Sc := Sc) (μ := μ)
      (S := [up i, up i]) (T := [up i, up i])
      (A.map (whL [up i] []) ++ [([up i], Shape.cup i, [up i])]) [] [] [] [up i]
      hcap hB (Or.inl (by simp [Shape.parity]))
    simpa [tail, whL, List.append_assoc] using E.symm
  have h4 : cl D Sc μ [up i, up i] [up i, up i]
      (A.map (whL [up i] []) ++
        [([up i], Shape.cup i, [up i]), ([], Shape.cap i, [up i, up i])] ++
        B.map (whL [] [up i])) =
      cl D Sc μ [up i, up i] [up i, up i]
        (A.map (whL [up i] []) ++ B.map (whL [] [up i])) := by
    apply cl_step (Sc := Sc) μ (A.map (whL [up i] [])) (B.map (whL [] [up i])) [] [up i]
      (cl_zigE Sc i (wt D μ [up i]))
      (hA.wh [up i] [] rfl rfl) (hB.wh [] [up i] rfl rfl)
    · simp [whL, List.append_assoc]
    · simp
  exact h1.trans (h2.trans (h3.trans h4))

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
