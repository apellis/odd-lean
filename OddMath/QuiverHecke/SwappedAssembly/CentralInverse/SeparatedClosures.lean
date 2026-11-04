import OddMath.QuiverHecke.SwappedAssembly.CentralInverse.ResidualComparison

/-! # Closed errors of the separated mixed bends

SwappedHomInversion §4, equations (6) and (9): the finite separated bend
series turn the chosen principal reservoir closures into all three closed
errors of the residual matrix. Only the two outside probe windows need
filtration-zero membership. No grading of a surrounding Hom is used.
-/
namespace OddMath.QuiverHecke.SwappedAssembly.ProbeWindow
open CategoryTheory
open scoped BigOperators
variable {C : Type*} [Category C] [Preadditive C]

/-- Closing the separated `Dx` series against any reservoir cap gives a
finite sum of the prescribed principal closures. -/
theorem separated_cap_closure (J : CoefficientIdeal C)
    {XR YR XP O : C} (x : Aut XP) (v : XP ⟶ O) (q : ℤ)
    {uR : ℕ → (O ⟶ YR)} {jR : YR ⟶ XR} {vR : ℕ → (XR ⟶ O)}
    {Dx : XP ⟶ YR} {N : ℕ}
    (hDx : Dx = -∑ r ∈ Finset.range N,
      q ^ (r + 1) • ((x ^ (-(r : ℤ) - 1)).hom ≫ v ≫ uR r))
    (hcl : ∀ r s, J.mem 1 (uR r ≫ jR ≫ vR s))
    (hz : ∀ r < N, J.mem 0 ((x ^ (-(r : ℤ) - 1)).hom ≫ v)) (s : ℕ) :
    J.mem 1 (Dx ≫ jR ≫ vR s) := by
  rw [hDx, Preadditive.neg_comp, Preadditive.sum_comp]
  apply J.neg_mem
  apply J.sum_mem
  intro r hr
  rw [Preadditive.zsmul_comp]
  apply J.zsmul_mem
  simpa only [Category.assoc] using J.comp_mem (hz r (Finset.mem_range.mp hr)) (hcl r s)

/-- Closing the separated `Cx` series against any reservoir unit gives a
finite sum of the same chosen principal closures. -/
theorem separated_unit_closure (J : CoefficientIdeal C)
    {XR YR YP O : C} (y : Aut YP) (u : O ⟶ YP) (q : ℤ)
    {uR : ℕ → (O ⟶ YR)} {jR : YR ⟶ XR} {vR : ℕ → (XR ⟶ O)}
    {Cx : XR ⟶ YP} {N : ℕ}
    (hCx : Cx = ∑ s ∈ Finset.range N,
      q ^ (s + 2) • (vR s ≫ u ≫ (y ^ (-(s : ℤ) - 1)).hom))
    (hcl : ∀ r s, J.mem 1 (uR r ≫ jR ≫ vR s))
    (hw : ∀ s < N, J.mem 0 (u ≫ (y ^ (-(s : ℤ) - 1)).hom)) (r : ℕ) :
    J.mem 1 (uR r ≫ jR ≫ Cx) := by
  rw [hCx, Preadditive.comp_sum, Preadditive.comp_sum]
  apply J.sum_mem
  intro s hs
  rw [Preadditive.comp_zsmul, Preadditive.comp_zsmul]
  apply J.zsmul_mem
  simpa only [Category.assoc] using J.comp_mem (hcl r s) (hw s (Finset.mem_range.mp hs))

/-- The mixed closed error is a finite double sum of chosen principal
closures, with the probe negative powers on its two sides. -/
theorem separated_closed_error (J : CoefficientIdeal C)
    {XR YR XP YP O : C} (x : Aut XP) (y : Aut YP) (v : XP ⟶ O) (u : O ⟶ YP) (q : ℤ)
    {uR : ℕ → (O ⟶ YR)} {jR : YR ⟶ XR} {vR : ℕ → (XR ⟶ O)}
    {Dx : XP ⟶ YR} {Cx : XR ⟶ YP} {ND NC : ℕ}
    (hDx : Dx = -∑ r ∈ Finset.range ND,
      q ^ (r + 1) • ((x ^ (-(r : ℤ) - 1)).hom ≫ v ≫ uR r))
    (hCx : Cx = ∑ s ∈ Finset.range NC,
      q ^ (s + 2) • (vR s ≫ u ≫ (y ^ (-(s : ℤ) - 1)).hom))
    (hcl : ∀ r s, J.mem 1 (uR r ≫ jR ≫ vR s))
    (hz : ∀ r < ND, J.mem 0 ((x ^ (-(r : ℤ) - 1)).hom ≫ v))
    (hw : ∀ s < NC, J.mem 0 (u ≫ (y ^ (-(s : ℤ) - 1)).hom)) :
    J.mem 1 (Dx ≫ jR ≫ Cx) := by
  rw [hCx, Preadditive.comp_sum, Preadditive.comp_sum]
  apply J.sum_mem
  intro s hs
  rw [Preadditive.comp_zsmul, Preadditive.comp_zsmul]
  apply J.zsmul_mem
  simpa only [Category.assoc] using J.comp_mem
    (separated_cap_closure J x v q hDx hcl hz s) (hw s (Finset.mem_range.mp hs))

/-- Negating both pure source summands leaves every unit column intact.
This supplies the precise sign comparison for the negative augmented map. -/
def pureSourceSign (XR XP O : C) (G : ℕ) :
    tObj XR XP O (Fin G) ⟶ tObj XR XP O (Fin G) :=
  tMap (-𝟙 XR) 0 0 0 (-𝟙 XP) 0 0 0 (fun i j => if i = j then 𝟙 O else 0)

theorem pureSourceSign_involutive (XR XP O : C) (G : ℕ) :
    pureSourceSign XR XP O G ≫ pureSourceSign XR XP O G = 𝟙 _ := by
  rw [pureSourceSign, tMap_comp, tMap_id]
  apply tMap_congr <;> intros <;> simp [comp_ite]

instance pureSourceSign_isIso (XR XP O : C) (G : ℕ) : IsIso (pureSourceSign XR XP O G) :=
  ⟨_, pureSourceSign_involutive XR XP O G, pureSourceSign_involutive XR XP O G⟩

theorem pureSourceSign_comp_negMap {XR YR XP YP O : C}
    (sR : XR ⟶ YR) (sP : XP ⟶ YP) (Cx : XR ⟶ YP) (Dx : XP ⟶ YR)
    (uR : ℕ → (O ⟶ YR)) {G : ℕ} (colP : Fin G → (O ⟶ YP)) :
    pureSourceSign XR XP O G ≫ negMap sR sP Cx Dx uR colP =
      negMap (-sR) (-sP) (-Cx) (-Dx) uR colP := by
  rw [pureSourceSign, negMap, negMap, tMap_comp]
  apply tMap_congr <;> intros <;> simp [ite_comp]

/-- The negative central principal signs preserve invertibility, without
changing the probe slide or any normalized unit column. -/
theorem isIso_negMap_neg_principals {XR YR XP YP O : C}
    (sR : XR ⟶ YR) (sP : XP ⟶ YP) (Cx : XR ⟶ YP) (Dx : XP ⟶ YR)
    (uR : ℕ → (O ⟶ YR)) {G : ℕ} (colP : Fin G → (O ⟶ YP))
    (h : IsIso (negMap sR sP Cx Dx uR colP)) :
    IsIso (negMap (-sR) (-sP) (-Cx) (-Dx) uR colP) := by
  rw [← pureSourceSign_comp_negMap]
  infer_instance

end OddMath.QuiverHecke.SwappedAssembly.ProbeWindow
