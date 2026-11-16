import OddMath.QuiverHecke.SwappedAssembly.CentralInverse.ResidualComparison

/-! # Residual comparisons when the probe has a unit window

SwappedHomInversion equations (11)–(12), using the negative-height
subcases (b), (c) of ProbeWindowInverse §3. These complete the two mixed
residual shapes already handled for nonnegative probe height in
`ResidualComparison`. The reservoir principal and all closed errors
remain the specified inputs; no residual invertibility is assumed.
-/
namespace OddMath.QuiverHecke.SwappedAssembly.ProbeWindow
open CategoryTheory
variable {C : Type*} [Category C] [Preadditive C]
variable (J : CoefficientIdeal C) {XR YR XP YP O : C} {sR : XR ⟶ YR} {sP : XP ⟶ YP}
  {Cx : XR ⟶ YP} {Dx : XP ⟶ YR} {vR : ℕ → (XR ⟶ O)} {uR : ℕ → (O ⟶ YR)} {jR : YR ⟶ XR}
  (x : Aut XP) (y : Aut YP) (v : XP ⟶ O) (u : O ⟶ YP) (q : ℤ)

/-- Case (c) with a probe unit window of length `b` and `H` fused caps. -/
abbrev caseCNegMap (s : XP ⟶ YP) (H b : ℕ) :
    gObj XP O (Fin (H + b)) ⟶ gObj YP O (Fin H) :=
  gMap s (fun t : Fin (H + b) => q ^ ((t : ℕ) + 2) • (u ≫ (y ^ (-(t : ℤ) - 1)).hom))
    (fun r : Fin H => (x ^ (r : ℤ)).hom ≫ v)
    (fun t r => if (t : ℕ) = r then 𝟙 O else 0)

/-- Positive fused window, reservoir cap window, negative probe height. -/
theorem isIso_posMap_of_cap_of_cup_window (hq : q * q = 1)
    (hslide : sP ≫ y.hom - q • (x.hom ≫ sP) = v ≫ u) {H b N : ℕ}
    (rowP : Fin H → (XP ⟶ O)) (hrow : ∀ a, rowP a = (x ^ ((a : ℕ) : ℤ)).hom ≫ v)
    {AR : Fin (H + b) → (O ⟶ XR)} (hR : IsCapInverse sR (fun n => vR n) jR AR)
    (h0 : ∃ j A, IsCupInverse sP (fun n : Fin b => u ≫ (y ^ (n : ℤ)).hom) j A)
    (hN : H + b ≤ N)
    (hCx : Cx = ∑ s ∈ Finset.range N,
      q ^ (s + 2) • (vR s ≫ u ≫ (y ^ (-(s : ℤ) - 1)).hom))
    (hout : ∀ (n : Fin (H + b)) (m : ℕ), H + b ≤ m → J.mem 1 (AR n ≫ vR m))
    (hclC : J.mem 1 (Dx ≫ jR ≫ Cx)) (hclv : ∀ a : Fin H, J.mem 1 (Dx ≫ jR ≫ vR a))
    (hw : ∀ s < N, J.mem 0 (u ≫ (y ^ (-(s : ℤ) - 1)).hom))
    (hinv : ∀ g, caseCNegMap x y v u q sP H b ≫ g = 𝟙 _ → ∀ i k, J.mem 0 (g i k)) :
    IsIso (posMap sR sP Cx Dx vR rowP) := by
  have : IsIso (caseCNegMap x y v u q sP H b) := isIso_caseC_of_neg sP x y v u q hq hslide h0
  have hc := cap_contraction J hR hout
  refine isIso_posMap_of_cap rowP hR (J.isIso_gMap_of_sub_mem
    (hinv _ (IsIso.hom_inv_id _)) ?_ (fun n => ?_) (fun a => ?_) (fun n a => ?_))
  · rw [sub_sub_cancel_left]; exact J.neg_mem hclC
  · exact cap_bent J y u q hN hCx hc hw n
  · rw [hrow, sub_sub_cancel_left]; exact J.neg_mem (hclv a)
  · exact hc n a

/-- Case (b) with a probe unit window and its prescribed off-corner signs. -/
abbrev caseBNegMap (s : XP ⟶ YP) (k b : ℕ) :
    gObj XP O (Fin (k + b)) ⟶ gObj YP O (Fin k) :=
  gMap s (fun t : Fin (k + b) => u ≫ (y ^ ((t : ℕ) : ℤ)).hom)
    (fun r : Fin k => -(q ^ ((r : ℕ) + 1) • ((x ^ (-((r : ℕ) : ℤ) - 1)).hom ≫ v)))
    (fun t r => if (t : ℕ) = r then 𝟙 O else 0)

theorem isIso_caseBNegMap (hq : q * q = 1)
    (hslide : sP ≫ y.hom - q • (x.hom ≫ sP) = v ≫ u)
    {k b : ℕ} (h0 : ∃ j A, IsCupInverse sP (fun n : Fin b => u ≫ (y ^ (n : ℤ)).hom) j A) :
    IsIso (caseBNegMap x y v u q sP k b) := by
  have H := isIso_gMap_neg (isIso_caseB_of_neg sP x y v u q hq hslide (k := k) h0)
  simpa only [neg_neg] using H

/-- Negative fused window, reservoir unit window, negative probe height. -/
theorem isIso_negMap_of_cup_of_cup_window (hq : q * q = 1)
    (hslide : sP ≫ y.hom - q • (x.hom ≫ sP) = v ≫ u) {k b N : ℕ}
    (colP : Fin (k + b) → (O ⟶ YP)) (hcol : ∀ a, colP a = u ≫ (y ^ ((a : ℕ) : ℤ)).hom)
    {BR : Fin k → (YR ⟶ O)} (hR : IsCupInverse sR (fun n => uR n) jR BR)
    (h0 : ∃ j A, IsCupInverse sP (fun n : Fin b => u ≫ (y ^ (n : ℤ)).hom) j A)
    (hN : k ≤ N)
    (hDx : Dx = -∑ r ∈ Finset.range N,
      q ^ (r + 1) • ((x ^ (-(r : ℤ) - 1)).hom ≫ v ≫ uR r))
    (hout : ∀ (n : Fin k) (m : ℕ), k ≤ m → J.mem 1 (uR m ≫ BR n))
    (hclC : J.mem 1 (Dx ≫ jR ≫ Cx))
    (hclu : ∀ a : Fin (k + b), J.mem 1 (uR a ≫ jR ≫ Cx))
    (hz : ∀ r < N, J.mem 0 ((x ^ (-(r : ℤ) - 1)).hom ≫ v))
    (hinv : ∀ g, caseBNegMap x y v u q sP k b ≫ g = 𝟙 _ → ∀ i l, J.mem 0 (g i l)) :
    IsIso (negMap sR sP Cx Dx uR colP) := by
  have := isIso_caseBNegMap x y v u q hq hslide (k := k) h0
  have hc := cup_contraction J hR hout
  refine isIso_negMap_of_cup colP hR (J.isIso_gMap_of_sub_mem
    (hinv _ (IsIso.hom_inv_id _)) ?_ (fun a => ?_) (fun n => ?_) (fun a n => ?_))
  · rw [sub_sub_cancel_left]; exact J.neg_mem hclC
  · rw [hcol, sub_sub_cancel_left]; exact J.neg_mem (hclu a)
  · exact cup_bent J x v q hN hDx hc hz n
  · exact hc a n

end OddMath.QuiverHecke.SwappedAssembly.ProbeWindow
