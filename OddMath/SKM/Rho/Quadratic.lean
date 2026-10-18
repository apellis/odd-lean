import OddMath.SKM.Rho.Upward
import OddMath.SKM.Rho.Powers

/-!
# Quadratic for ρ

Supporting calculations for Brundan–Ellis, *Super Kac–Moody 2-categories*,
arXiv:1701.04133v2, Proposition 9.8 with the corrected crossing sign.
These calculations use a purely even commutative coefficient ring and the
existing super Kac–Moody presentation.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.SKM.RhoCoefficients
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D} {hc : Sc.Homogeneous}

theorem dotLeft_pow (t : k) (ν μ : X) (i j : I)
    (h : wt D μ (ups [i,j]) = ν) (n : ℕ) :
    cpow (rhoDotLeft (Sc := Sc) (sy := sy) (hc := hc) t ν μ i j h) n =
      psiCoeff t (D.parity i) ^ n • cl D Sc ν [dn j,dn i] [dn j,dn i]
        ((ddotsL i n).map (whL [dn j] [])) :=
by
  have H : cpow (rhoDotLeft (Sc := Sc) (sy := sy) (hc := hc) t ν μ i j h) n =
      cpow (psiCoeff t (D.parity i) • cl D Sc ν [dn j,dn i] [dn j,dn i]
        ((ddotL i).map (whL [dn j] []))) n := by
    induction n with
    | zero => rfl
    | succ n ih => exact congrArg (fun f => f ≫
        (psiCoeff t (D.parity i) • cl D Sc ν [dn j,dn i] [dn j,dn i]
          ((ddotL i).map (whL [dn j] [])))) ih
  exact H.trans (placed_dot_power (D := D) (Sc := Sc) ν [dn j] [] i (psiCoeff t (D.parity i)) n)

theorem dotRight_pow (t : k) (ν μ : X) (i j : I)
    (h : wt D μ (ups [i,j]) = ν) (n : ℕ) :
    cpow (rhoDotRight (Sc := Sc) (sy := sy) (hc := hc) t ν μ i j h) n =
      psiCoeff t (D.parity j) ^ n • cl D Sc ν [dn j,dn i] [dn j,dn i]
        ((ddotsL j n).map (whL [] [dn i])) :=
by
  have H : cpow (rhoDotRight (Sc := Sc) (sy := sy) (hc := hc) t ν μ i j h) n =
      cpow (psiCoeff t (D.parity j) • cl D Sc ν [dn j,dn i] [dn j,dn i]
        ((ddotL j).map (whL [] [dn i]))) n := by
    induction n with
    | zero => rfl
    | succ n ih => exact congrArg (fun f => f ≫
        (psiCoeff t (D.parity j) • cl D Sc ν [dn j,dn i] [dn j,dn i]
          ((ddotL j).map (whL [] [dn i])))) ih
  exact H.trans (placed_dot_power (D := D) (Sc := Sc) ν [] [dn i] j (psiCoeff t (D.parity j)) n)

theorem dot_polynomial_comm (ν : X) (i j : I) (p q : ℕ)
    (hp : (p : ZMod 2) * D.parity i = 0) :
    cl D Sc ν [dn j,dn i] [dn j,dn i]
      ((ddotsL j q).map (whL [] [dn i]) ++ (ddotsL i p).map (whL [dn j] [])) =
    cl D Sc ν [dn j,dn i] [dn j,dn i]
      ((ddotsL i p).map (whL [dn j] []) ++ (ddotsL j q).map (whL [] [dn i])) := by
  have H := cl_interchange (D := D) (Sc := Sc) (μ := ν)
    (S := [dn j,dn i]) (T := [dn j,dn i]) [] [] (sChain_ddotsL j q) (sChain_ddotsL i p)
  simpa only [List.nil_append, List.append_nil, parsum_ddotsL, hp, mul_zero,
    zsign_zero, one_smul] using H

theorem quadratic_raw (t : k) (ht : t ^ 2 = -1) (ν : X) (i j : I)
    (hij : i ≠ j) (hd : D.d i j ≠ 0) :
    zsign k (D.parity i * D.parity j) •
      cl D Sc ν [dn j,dn i] [dn j,dn i] (dcrossL j i ++ dcrossL i j) =
    ((Sc.t i j : k) * psiCoeff t (D.parity i) ^ D.dn i j) •
      cl D Sc ν [dn j,dn i] [dn j,dn i] ((ddotsL i (D.dn i j)).map (whL [dn j] [])) +
    ((Sc.t j i : k) * psiCoeff t (D.parity j) ^ D.dn j i) •
      cl D Sc ν [dn j,dn i] [dn j,dn i] ((ddotsL j (D.dn j i)).map (whL [] [dn i])) +
    ∑ p ∈ Finset.Ioo 0 (D.dn i j), ∑ q ∈ Finset.Ioo 0 (D.dn j i),
      (Sc.s i j p q * (psiCoeff t (D.parity j) ^ q * psiCoeff t (D.parity i) ^ p)) •
      cl D Sc ν [dn j,dn i] [dn j,dn i]
        ((ddotsL j q).map (whL [] [dn i]) ++ (ddotsL i p).map (whL [dn j] [])) := by
  rw [mul_comm (D.parity i) (D.parity j),
    lemma32_ne Sc j i ν hij.symm (fun h => hd ((D.d_eq_zero_iff i j).mpr h))]
  rw [coeff_pow_even t ht _ _ (parity_mul_dn D i j),
    coeff_pow_even t ht _ _ (parity_mul_dn D j i)]
  rw [Finset.sum_comm]
  congr 1
  · simp only [mul_comm]; exact add_comm _ _
  · apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro q hq
    rw [Sc.s_symm j i q p]
    by_cases hs : Sc.s i j p q = 0
    · simp [hs]
    obtain ⟨hpi,hqj⟩ := Sc.parity_of_ne_zero hs
    rw [coeff_pow_even t ht _ _ (by simpa [mul_comm] using hqj),
      coeff_pow_even t ht _ _ (by simpa [mul_comm] using hpi),
      dot_polynomial_comm ν i j p q hpi, zsign_add]
    congr 1
    ring

def rhoForget2 (ν μ : X) (i j : I) (h : wt D μ (ups [i,j]) = ν) :
    (rhoUpAt (Sc := Sc) (sy := sy) (hc := hc) ν μ [i,j] h ⟶ rhoUpAt ν μ [i,j] h) →ₗ[k]
      ((pres D Sc).obj (ob D ν [dn j,dn i]) ⟶ (pres D Sc).obj (ob D ν [dn j,dn i])) where
  toFun f := f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem crossing_connected_quadratic (t : k) (ht : t ^ 2 = -1) (ν μ : X) (i j : I)
    (h : wt D μ (ups [i,j]) = ν) (hij : i ≠ j) (hd : D.d i j ≠ 0) :
    correctedCrossing (Sc := Sc) (sy := sy) (hc := hc) t ν μ i j h ≫
      correctedCrossing t ν μ j i (by simpa [ups, wt, sh, add_comm, add_left_comm, add_assoc] using h) =
    (Sc.t i j : k) • cpow (rhoDotLeft t ν μ i j h) (D.dn i j) +
    (Sc.t j i : k) • cpow (rhoDotRight t ν μ i j h) (D.dn j i) +
    ∑ p ∈ Finset.Ioo 0 (D.dn i j), ∑ q ∈ Finset.Ioo 0 (D.dn j i),
      Sc.s i j p q • (cpow (rhoDotRight t ν μ i j h) q ≫ cpow (rhoDotLeft t ν μ i j h) p) := by
  apply (show Function.Injective (rhoForget2 (Sc := Sc) (sy := sy) (hc := hc) ν μ i j h)
    from fun _ _ e => e)
  simp only [map_add, map_sum, map_smul]
  rw [crossing_cross_comp, rhoCross_comp t ht]
  simp only [dotLeft_pow, dotRight_pow, Linear.smul_comp, Linear.comp_smul, smul_smul]
  simp only [rhoForget2, LinearMap.coe_mk, AddHom.coe_mk]
  have hp (p : ℕ) : SChain [dn j,dn i]
      ((ddotsL i p).map (whL [dn j] [])) [dn j,dn i] :=
    (sChain_ddotsL i p).wh [dn j] [] rfl rfl
  have hq (q : ℕ) : SChain [dn j,dn i]
      ((ddotsL j q).map (whL [] [dn i])) [dn j,dn i] :=
    (sChain_ddotsL j q).wh [] [dn i] rfl rfl
  have H := quadratic_raw (Sc := Sc) t ht ν i j hij hd
  simp only [← cl_comp (D := D) (Sc := Sc) (μ := ν) (hq _) (hp _)] at H
  convert H using 1
  simp only [smul_smul, mul_comm]
  congr 1

end OddMath.SKM.RhoCoefficients
