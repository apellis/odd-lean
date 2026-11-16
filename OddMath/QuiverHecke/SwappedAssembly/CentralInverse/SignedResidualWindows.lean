import OddMath.QuiverHecke.SwappedAssembly.CentralInverse.SeparatedClosures
import OddMath.QuiverHecke.SwappedAssembly.CentralInverse.ResidualComparisonNegative

/-! # Residual inversion at every pair of integral heights

SwappedHomInversion §§4–6 and ProbeWindowInverse §3: combine the six
height subcases with the separated-bend closure computation. The signed
heights determine all finite index sets. The only positive-filtration
inputs are the prescribed reservoir principal closures and off-window
contractions; the mixed closed errors are derived from the two series.
-/
namespace OddMath.QuiverHecke.SwappedAssembly.ProbeWindow
open CategoryTheory
variable {C : Type*} [Category C] [Preadditive C]

/-- A specified reservoir cap inverse, retaining its closed coefficients
and its off-window contractions in the coefficient ideal. -/
def ReservoirCapConditions (J : CoefficientIdeal C) {XR YR O : C}
    (sR : XR ⟶ YR) (vR : ℕ → (XR ⟶ O)) (uR : ℕ → (O ⟶ YR)) (h : ℕ) : Prop :=
  ∃ j A, IsCapInverse sR (fun n : Fin h => vR n) j A ∧
    (∀ r s, J.mem 1 (uR r ≫ j ≫ vR s)) ∧
    (∀ (n : Fin h) (m : ℕ), h ≤ m → J.mem 1 (A n ≫ vR m))

/-- The analogous specified reservoir unit inverse. -/
def ReservoirCupConditions (J : CoefficientIdeal C) {XR YR O : C}
    (sR : XR ⟶ YR) (vR : ℕ → (XR ⟶ O)) (uR : ℕ → (O ⟶ YR)) (h : ℕ) : Prop :=
  ∃ j B, IsCupInverse sR (fun n : Fin h => uR n) j B ∧
    (∀ r s, J.mem 1 (uR r ≫ j ≫ vR s)) ∧
    (∀ (n : Fin h) (m : ℕ), h ≤ m → J.mem 1 (uR m ≫ B n))

/-- All positive fused-height cases, including a negative probe height.
The three closed residual errors are consequences, not hypotheses. -/
theorem isIso_posMap_of_signed_windows (J : CoefficientIdeal C)
  (hJ0 : ∀ {A B : C} (f : A ⟶ B), J.mem 0 f)
  {XR YR XP YP O : C} {sR : XR ⟶ YR} {sP : XP ⟶ YP}
  {Cx : XR ⟶ YP} {Dx : XP ⟶ YR} (vR : ℕ → (XR ⟶ O)) (uR : ℕ → (O ⟶ YR))
  (x : Aut XP) (y : Aut YP) (v : XP ⟶ O) (u : O ⟶ YP) (q : ℤ)
  (hq : q * q = 1) (hslide : sP ≫ y.hom - q • (x.hom ≫ sP) = v ≫ u)
  (r p : ℤ) {N : ℕ}
  (hN : max r.toNat (-r).toNat ≤ N)
  (hDx : Dx = -∑ a ∈ Finset.range N,
    q ^ (a + 1) • ((x ^ (-(a : ℤ) - 1)).hom ≫ v ≫ uR a))
  (hCx : Cx = ∑ a ∈ Finset.range N,
    q ^ (a + 2) • (vR a ≫ u ≫ (y ^ (-(a : ℤ) - 1)).hom))
  (hRcap : 0 ≤ r → ReservoirCapConditions J sR vR uR r.toNat)
  (hRcup : r ≤ 0 → ReservoirCupConditions J sR vR uR (-r).toNat)
  (hPcap : 0 ≤ p → ∃ j A, IsCapInverse sP
    (fun n : Fin p.toNat => (x ^ (n : ℤ)).hom ≫ v) j A)
  (hPcup : p ≤ 0 → ∃ j B, IsCupInverse sP
    (fun n : Fin (-p).toNat => u ≫ (y ^ (n : ℤ)).hom) j B)

    (hH : 0 ≤ r + p) :
    IsIso (posMap sR sP Cx Dx vR
      (fun a : Fin (r + p).toNat => (x ^ (a : ℤ)).hom ≫ v)) := by
  by_cases hr : 0 ≤ r
  · have HR := hRcap hr
    by_cases hp : 0 ≤ p
    · obtain ⟨j, A, hR, hcl, hout⟩ := HR
      have hcount : (r + p).toNat = r.toNat + p.toNat := by omega
      rw [hcount]
      exact isIso_posMap_of_cap_of_window J x y v u q hq hslide _ (fun _ => rfl)
        hR (hPcap hp) (by omega) hCx hout
        (separated_closed_error J x y v u q hDx hCx hcl (fun _ _ => hJ0 _) (fun _ _ => hJ0 _))
        (fun _ => separated_cap_closure J x v q hDx hcl (fun _ _ => hJ0 _) _)
        (fun _ _ => hJ0 _) (fun _ _ _ _ => hJ0 _)
    · have hcount : r.toNat = (r + p).toNat + (-p).toNat := by omega
      rw [hcount] at HR
      obtain ⟨j, A, hR, hcl, hout⟩ := HR
      exact isIso_posMap_of_cap_of_cup_window J x y v u q hq hslide _ (fun _ => rfl)
        hR (hPcup (by omega)) (by omega) hCx hout
        (separated_closed_error J x y v u q hDx hCx hcl (fun _ _ => hJ0 _) (fun _ _ => hJ0 _))
        (fun _ => separated_cap_closure J x v q hDx hcl (fun _ _ => hJ0 _) _)
        (fun _ _ => hJ0 _) (fun _ _ _ _ => hJ0 _)
  · have hp : 0 ≤ p := by omega
    have HP := hPcap hp
    have hcount : p.toNat = (r + p).toNat + (-r).toNat := by omega
    rw [hcount] at HP
    obtain ⟨j, B, hR, hcl, hout⟩ := hRcup (by omega)
    exact isIso_posMap_of_cup_of_window J x y v u q hq hslide _ (fun _ => rfl)
      hR HP (by omega) hDx hout
      (separated_closed_error J x y v u q hDx hCx hcl (fun _ _ => hJ0 _) (fun _ _ => hJ0 _))
      (fun _ => separated_cap_closure J x v q hDx hcl (fun _ _ => hJ0 _) _)
      (fun _ _ => hJ0 _) (fun _ _ _ _ => hJ0 _)

/-- All negative fused-height cases. The result retains the positive
principal convention; `isIso_negMap_neg_principals` supplies precisely
the signs of the negative augmented central matrix. -/
theorem isIso_negMap_of_signed_windows (J : CoefficientIdeal C)
  (hJ0 : ∀ {A B : C} (f : A ⟶ B), J.mem 0 f)
  {XR YR XP YP O : C} {sR : XR ⟶ YR} {sP : XP ⟶ YP}
  {Cx : XR ⟶ YP} {Dx : XP ⟶ YR} (vR : ℕ → (XR ⟶ O)) (uR : ℕ → (O ⟶ YR))
  (x : Aut XP) (y : Aut YP) (v : XP ⟶ O) (u : O ⟶ YP) (q : ℤ)
  (hq : q * q = 1) (hslide : sP ≫ y.hom - q • (x.hom ≫ sP) = v ≫ u)
  (r p : ℤ) {N : ℕ}
  (hN : max r.toNat (-r).toNat ≤ N)
  (hDx : Dx = -∑ a ∈ Finset.range N,
    q ^ (a + 1) • ((x ^ (-(a : ℤ) - 1)).hom ≫ v ≫ uR a))
  (hCx : Cx = ∑ a ∈ Finset.range N,
    q ^ (a + 2) • (vR a ≫ u ≫ (y ^ (-(a : ℤ) - 1)).hom))
  (hRcap : 0 ≤ r → ReservoirCapConditions J sR vR uR r.toNat)
  (hRcup : r ≤ 0 → ReservoirCupConditions J sR vR uR (-r).toNat)
  (hPcap : 0 ≤ p → ∃ j A, IsCapInverse sP
    (fun n : Fin p.toNat => (x ^ (n : ℤ)).hom ≫ v) j A)
  (hPcup : p ≤ 0 → ∃ j B, IsCupInverse sP
    (fun n : Fin (-p).toNat => u ≫ (y ^ (n : ℤ)).hom) j B)

    (hH : r + p ≤ 0) :
    IsIso (negMap sR sP Cx Dx uR
      (fun a : Fin (-(r + p)).toNat => u ≫ (y ^ (a : ℤ)).hom)) := by
  by_cases hr : 0 ≤ r
  · have hp : p ≤ 0 := by omega
    have HP := hPcup hp
    have hcount : (-p).toNat = r.toNat + (-(r + p)).toNat := by omega
    rw [hcount] at HP
    obtain ⟨j, A, hR, hcl, hout⟩ := hRcap hr
    exact isIso_negMap_of_cap_of_window J x y v u q hq hslide _ (fun _ => rfl)
      hR HP (by omega) hCx hout
      (separated_closed_error J x y v u q hDx hCx hcl (fun _ _ => hJ0 _) (fun _ _ => hJ0 _))
      (fun _ => separated_unit_closure J y u q hCx hcl (fun _ _ => hJ0 _) _)
      (fun _ _ => hJ0 _) (fun _ _ _ _ => hJ0 _)
  · have HR := hRcup (by omega)
    by_cases hp : 0 ≤ p
    · have hcount : (-r).toNat = (-(r + p)).toNat + p.toNat := by omega
      rw [hcount] at HR
      obtain ⟨j, B, hR, hcl, hout⟩ := HR
      exact isIso_negMap_of_cup_of_window J x y v u q hq hslide _ (fun _ => rfl)
        hR (hPcap hp) (by omega) hDx hout
        (separated_closed_error J x y v u q hDx hCx hcl (fun _ _ => hJ0 _) (fun _ _ => hJ0 _))
        (fun _ => separated_unit_closure J y u q hCx hcl (fun _ _ => hJ0 _) _)
        (fun _ _ => hJ0 _) (fun _ _ _ _ => hJ0 _)
    · obtain ⟨j, B, hR, hcl, hout⟩ := HR
      have hcount : (-(r + p)).toNat = (-r).toNat + (-p).toNat := by omega
      rw [hcount]
      exact isIso_negMap_of_cup_of_cup_window J x y v u q hq hslide _ (fun _ => rfl)
        hR (hPcup (by omega)) (by omega) hDx hout
        (separated_closed_error J x y v u q hDx hCx hcl (fun _ _ => hJ0 _) (fun _ _ => hJ0 _))
        (fun _ => separated_unit_closure J y u q hCx hcl (fun _ _ => hJ0 _) _)
        (fun _ _ => hJ0 _) (fun _ _ _ _ => hJ0 _)

end OddMath.QuiverHecke.SwappedAssembly.ProbeWindow
