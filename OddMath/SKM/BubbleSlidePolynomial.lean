/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.BubbleSlideRaw
import OddMath.SKM.BubbleSeriesStep
/-!
# Connected bubble slides with the full quadratic polynomial

The natural-dot instances of Brundan–Ellis, *Super Kac–Moody 2-categories*,
arXiv:1701.04133v2, Proposition 7.3(iii), (7.11)–(7.12). Both Cartan entries,
both colour parities, and all permitted scalar coefficients remain arbitrary.
The proof uses the pitchfork identities and the defining quadratic relation;
nonzero scalar coefficients supply exactly the parity needed for interchange.

These formulas do not assert the remaining negative-dot (fake-bubble) cases.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Presentation Finset
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X} {k : Type w} [CommRing k]
  {Sc : Scalars D k} (cs : CScalars Sc)

theorem bubbleR_polynomial_term (i j : I) (μ : X) (n p q : ℕ)
    (hq : (q : ZMod 2) * D.parity j = 0) :
    cl D Sc μ [up j] [dn i, up i, up j] ((etaL i n).map (whL [] [up j])) ≫
      cl D Sc μ [dn i, up i, up j] [dn i, up i, up j]
        (dotsL [dn i, up i] j [] q ++ dotsL [dn i] i [up j] p) ≫ capAt cs i μ [] [up j] =
    bubbleR_left cs i j μ (n + p) ≫ cl D Sc μ [up j] [up j] (dotsL [] j [] q) := by
  have het : SChain [up j] ((etaL i n).map (whL [] [up j])) [dn i, up i, up j] := by
    simpa using (sChain_etaL i n).whisk [] [up j]
  have hi := sChain_dotsL [dn i] i [] p
  have hj := sChain_dotsL [] j [] q
  have H := cl_interchange (D := D) (Sc := Sc) (μ := μ)
    (S := [dn i, up i, up j]) (T := [dn i, up i, up j]) [] [] hi hj
  simp only [parsum_dotsL, hq, mul_zero, zsign_zero, one_smul, List.nil_append,
    List.append_nil] at H
  have ei : (dotsL [dn i] i [] p).map (whL [] [up j]) = dotsL [dn i] i [up j] p := by
    simp [dotsL, whL, List.map_replicate]
  have ej : (dotsL [] j [] q).map (whL [dn i, up i] []) = dotsL [dn i, up i] j [] q := by
    simp [dotsL, whL, List.map_replicate]
  simp only [List.cons_append, List.nil_append] at H
  rw [ei, ej] at H
  rw [← H]
  have hi' : SChain [dn i, up i, up j] (dotsL [dn i] i [up j] p) [dn i, up i, up j] :=
    sChain_dotsL [dn i] i [up j] p
  have hj' : SChain [dn i, up i, up j] (dotsL [dn i, up i] j [] q) [dn i, up i, up j] :=
    sChain_dotsL [dn i, up i] j [] q
  rw [← cl_comp hi' hj', ← Category.assoc, ← Category.assoc, cl_comp het hi', etaL_dots]
  have het' : SChain [up j] ((etaL i (n + p)).map (whL [] [up j])) [dn i, up i, up j] := by
    simpa using (sChain_etaL i (n + p)).whisk [] [up j]
  rw [← ej, cl_comp het' (by simpa using hj.whisk [dn i, up i] [])]
  change _ ≫ plcL D Sc μ [] [up j] [dn i, up i] [] (epsP cs i (wt D μ [up j])) = _
  rw [bub_factor cs i j μ (n + p) hj, parsum_dotsL, hq, mul_zero, zsign_zero, one_smul]
  rfl

theorem bubbleR_slide_polynomial_raw (i j : I) (μ : X) (hij : i ≠ j)
    (hd : D.d i j ≠ 0) (n : ℕ) :
    bubbleR_right cs i j μ n =
      (Sc.t i j : k) • bubbleR_left cs i j μ (n + D.dn i j) +
      (Sc.t j i : k) • (bubbleR_left cs i j μ n ≫
        cl D Sc μ [up j] [up j] (dotsL [] j [] (D.dn j i))) +
      ∑ p ∈ Ioo 0 (D.dn i j), ∑ q ∈ Ioo 0 (D.dn j i),
        Sc.s i j p q • (bubbleR_left cs i j μ (n + p) ≫
          cl D Sc μ [up j] [up j] (dotsL [] j [] q)) := by
  rw [bubbleR_slide_quad cs i j μ hij n]
  have het : SChain [up j] ((etaL i n).map (whL [] [up j])) [dn i, up i, up j] := by
    simpa using (sChain_etaL i n).whisk [] [up j]
  have hcc : SChain [dn i, up i, up j] (crossL [dn i] i j [] ++ crossL [dn i] j i [])
      [dn i, up i, up j] := by simp [crossL, Shape.dom, Shape.cod]
  have e0 : cl D Sc μ [up j] [dn i, up i, up j]
      ((etaL i n).map (whL [] [up j]) ++ crossL [dn i] i j [] ++ crossL [dn i] j i []) =
      cl D Sc μ [up j] [dn i, up i, up j] ((etaL i n).map (whL [] [up j])) ≫
        cl D Sc μ [dn i, up i, up j] [dn i, up i, up j]
          (crossL [dn i] i j [] ++ crossL [dn i] j i []) := by
    rw [cl_comp het hcc, List.append_assoc]
  rw [e0, Category.assoc]
  have hq := congrArg (plcL D Sc μ [dn i] [] [up i, up j] [up i, up j])
    (cl_quadNe (Sc := Sc) i j (wt D μ []) hij hd)
  simp only [map_add, map_smul, map_sum, plcL_cl] at hq
  erw [hq]
  simp only [Preadditive.add_comp, Preadditive.comp_add, Linear.smul_comp, Linear.comp_smul,
    Preadditive.sum_comp, Preadditive.comp_sum]
  have ei (p : ℕ) : (dotsL [] i [up j] p).map (whL [dn i] []) = dotsL [dn i] i [up j] p := by
    simp [dotsL, whL, List.map_replicate]
  have ej (q : ℕ) : (dotsL [up i] j [] q).map (whL [dn i] []) = dotsL [dn i, up i] j [] q := by
    simp [dotsL, whL, List.map_replicate]
  simp only [List.map_append, ei, ej]
  have hi := bubbleR_polynomial_term cs i j μ n (D.dn i j) 0 (by simp)
  simp only [dotsL, List.replicate_zero, List.nil_append, cl_nil, Category.comp_id] at hi
  have hj := bubbleR_polynomial_term cs i j μ n 0 (D.dn j i) (by
    rw [mul_comm]; exact parity_mul_dn D j i)
  simp only [dotsL, List.replicate_zero, List.append_nil, Nat.cast_zero, add_zero] at hj
  erw [hi, hj]
  congr 1
  apply sum_congr rfl
  intro p _
  apply sum_congr rfl
  intro q _
  by_cases hs : Sc.s i j p q = 0
  · simp only [hs, zero_smul]
  · erw [bubbleR_polynomial_term cs i j μ n p q (Sc.parity_of_ne_zero hs).2]

theorem bubbleL_polynomial_term (i j : I) (μ : X) (n p q : ℕ)
    (hq : (q : ZMod 2) * D.parity j = 0) :
    plcL D Sc μ [up j] [] [] [up i, dn i] (etaP cs i (wt D μ [])) ≫
      cl D Sc μ [up j, up i, dn i] [up j, up i, dn i]
        (dotsL [up j] i [dn i] p ++ dotsL [] j [up i, dn i] q) ≫
      cl D Sc μ [up j, up i, dn i] [up j] ((epsL i n).map (whL [up j] [])) =
    cl D Sc μ [up j] [up j] (dotsL [] j [] q) ≫ bubbleL_right cs i j μ (n + p) := by
  have hi : SChain [up i, dn i] (dotsL [] i [dn i] p) [up i, dn i] := sChain_dotsL [] i [dn i] p
  have hj : SChain [up j] (dotsL [] j [] q) [up j] := sChain_dotsL [] j [] q
  have H := cl_interchange (D := D) (Sc := Sc) (μ := μ)
    (S := [up j, up i, dn i]) (T := [up j, up i, dn i]) [] [] hj hi
  simp only [parsum_dotsL, hq, zero_mul, zsign_zero, one_smul, List.nil_append,
    List.append_nil] at H
  have ei : (dotsL [] i [dn i] p).map (whL [up j] []) = dotsL [up j] i [dn i] p := by
    simp [dotsL, whL, List.map_replicate]
  have ej : (dotsL [] j [] q).map (whL [] [up i, dn i]) = dotsL [] j [up i, dn i] q := by
    simp [dotsL, whL, List.map_replicate]
  rw [ei, ej] at H
  rw [← H]
  have hi' : SChain [up j, up i, dn i] (dotsL [up j] i [dn i] p) [up j, up i, dn i] :=
    sChain_dotsL [up j] i [dn i] p
  have hj' : SChain [up j, up i, dn i] (dotsL [] j [up i, dn i] q) [up j, up i, dn i] :=
    sChain_dotsL [] j [up i, dn i] q
  rw [← cl_comp hj' hi', ← Category.assoc, ← Category.assoc]
  have hc := plcL_right_interchange (Sc := Sc) μ [up j] (etaP_mem cs i (wt D μ [])) hj
  simp only [map_whL_nil_nil, parsum_dotsL, hq, mul_zero, zsign_zero, one_smul, ej] at hc
  erw [hc]
  rw [Category.assoc, Category.assoc, pcu_bubble]
  rw [Nat.add_comm p n]
  rfl

/-- Natural-dot counterclockwise slide with the full quadratic correction. -/
theorem bubbleL_slide_polynomial_raw (i j : I) (μ : X) (hij : i ≠ j)
    (hd : D.d i j ≠ 0) (n : ℕ) :
    bubbleL_left cs i j μ n =
      (Sc.t i j : k) • bubbleL_right cs i j μ (n + D.dn i j) +
      (Sc.t j i : k) • (cl D Sc μ [up j] [up j] (dotsL [] j [] (D.dn j i)) ≫
        bubbleL_right cs i j μ n) +
      ∑ p ∈ Ioo 0 (D.dn i j), ∑ q ∈ Ioo 0 (D.dn j i),
        Sc.s i j p q • (cl D Sc μ [up j] [up j] (dotsL [] j [] q) ≫
          bubbleL_right cs i j μ (n + p)) := by
  change plcL D Sc μ [] [up j] [] [] (bubL cs i (wt D μ [up j]) n) = _
  rw [bubL_nat, ← pcuR_b cs i j μ hij n, ← eq_7_5_b, pcuL_b_reduce cs i j μ hij n]
  have hc : SChain [up j, up i, dn i] (crossL [] j i [dn i] ++ crossL [] i j [dn i])
      [up j, up i, dn i] := by simp [crossL, Shape.dom, Shape.cod]
  have he : SChain [up j, up i, dn i] ((epsL i n).map (whL [up j] [])) [up j] := by
    simpa using (sChain_epsL i n).whisk [up j] []
  rw [← cl_comp hc he]
  have hq := congrArg (plcL D Sc μ [] [dn i] [up j, up i] [up j, up i])
    (cl_quadNe (Sc := Sc) j i (wt D μ [dn i]) hij.symm
      (fun h => hd ((D.d_eq_zero_iff j i).mp h)))
  simp only [map_add, map_smul, map_sum, plcL_cl] at hq
  erw [hq]
  simp only [Preadditive.add_comp, Preadditive.comp_add, Linear.smul_comp, Linear.comp_smul,
    Preadditive.sum_comp, Preadditive.comp_sum]
  have ei (p : ℕ) : (dotsL [up j] i [] p).map (whL [] [dn i]) = dotsL [up j] i [dn i] p := by
    simp [dotsL, whL, List.map_replicate]
  have ej (q : ℕ) : (dotsL [] j [up i] q).map (whL [] [dn i]) = dotsL [] j [up i, dn i] q := by
    simp [dotsL, whL, List.map_replicate]
  simp only [List.map_append, ei, ej]
  have hi := bubbleL_polynomial_term cs i j μ n (D.dn i j) 0 (by simp)
  simp only [dotsL, List.replicate_zero, List.append_nil, cl_nil, Category.id_comp] at hi
  have hj := bubbleL_polynomial_term cs i j μ n 0 (D.dn j i) (by
    rw [mul_comm]; exact parity_mul_dn D j i)
  simp only [dotsL, List.replicate_zero, List.nil_append, Nat.cast_zero, add_zero] at hj
  erw [hi, hj]
  rw [add_comm ((Sc.t j i : k) • _), sum_comm]
  congr 1
  apply sum_congr rfl
  intro p _
  apply sum_congr rfl
  intro q _
  rw [← Sc.s_symm i j p q]
  by_cases hs : Sc.s i j p q = 0
  · simp only [hs, zero_smul]
  · erw [bubbleL_polynomial_term cs i j μ n p q (Sc.parity_of_ne_zero hs).2]
/-- Normalized coefficient of the connected quadratic correction.
At positive degree the support is `dᵢⱼ` and `dᵢⱼ - p`, retaining every `sᵢⱼ^{pq}`.
The constant coefficient is the identity, including for the formal series transport. -/
def bubbleSlidePolynomialCoeff (i j : I) (μ : X) (n : ℕ) :=
  if n = 0 then 𝟙 ((pres D Sc).obj (ob D μ [up j])) else
    (if n = D.dn i j then
      ((↑(Sc.t i j)⁻¹ : k) * (Sc.t j i : k)) •
        cl D Sc μ [up j] [up j] (dotsL [] j [] (D.dn j i)) else 0) +
    ∑ p ∈ Ioo 0 (D.dn i j), ∑ q ∈ Ioo 0 (D.dn j i),
      if n = D.dn i j - p then
        ((↑(Sc.t i j)⁻¹ : k) * Sc.s i j p q) •
          cl D Sc μ [up j] [up j] (dotsL [] j [] q) else 0

/-- For the actual normalized bubbles, the two polynomial series relations are equivalent.
This transports a proof between orientations; it does not assume or assert either slide. -/
theorem bubbleCoeff_polynomial_iff (i j : I) (μ : X) :
    ((fun n => rbub j μ (bubbleCoeffR cs i (wt D μ []) n)) =
      bubbleConvolution (fun n => lbub j μ (bubbleCoeffR cs i (wt D μ [up j]) n))
        (bubbleSlidePolynomialCoeff (Sc := Sc) i j μ)) ↔
    ((fun n => lbub j μ (bubbleCoeffL cs i (wt D μ [up j]) n)) =
      bubbleConvolution (bubbleSlidePolynomialCoeff (Sc := Sc) i j μ)
        (fun n => rbub j μ (bubbleCoeffL cs i (wt D μ []) n))) := by
  exact bubbleConvolution_inverse
    (fun n => rbub j μ (bubbleCoeffR cs i (wt D μ []) n))
    (fun n => lbub j μ (bubbleCoeffR cs i (wt D μ [up j]) n))
    (fun n => rbub j μ (bubbleCoeffL cs i (wt D μ []) n))
    (fun n => lbub j μ (bubbleCoeffL cs i (wt D μ [up j]) n))
    (bubbleSlidePolynomialCoeff (Sc := Sc) i j μ)
    (by simp only [rbub, bubbleCoeffR_zero, plcL_id]; rfl)
    (by simp only [lbub, bubbleCoeffR_zero, plcL_id]; rfl)
    (by simp only [rbub, bubbleCoeffL_zero, plcL_id]; rfl)
    (by simp only [lbub, bubbleCoeffL_zero, plcL_id]; rfl)
    (by simp [bubbleSlidePolynomialCoeff])
    (bubbleCoeff_key_place cs i μ [up j] []) (bubbleCoeff_key_place cs i μ [] [up j])

end OddMath.SKM
