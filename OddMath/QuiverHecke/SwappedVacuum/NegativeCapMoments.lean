import OddMath.QuiverHecke.SwappedVacuum.InverseCapMoments

/-! # The extreme cap at negative height

Research issue #345, toward Brundan–Ellis, *Super Kac–Moody 2-categories*,
§8. These are the polynomial calculations (9)–(10) of
`docs/Nondegeneracy/SwappedVacuumNonpositiveBubbles.md`: coefficient
extraction after the monic probe polynomial kills the prescribed mate
and extracts the final low-unit column. Attachment to the actual
augmented inverse is separate.
-/
noncomputable section
namespace OddMath.QuiverHecke.SwappedVacuum
open CategoryTheory Finset
universe u v w
variable {k : Type w} [CommRing k] {C : Type u} [Category.{v} C]
  [Preadditive C] [Linear k C] {V X Y : C}

/-- Evaluation of the probe polynomial before coefficient extraction,
with the chronological order of all maps fixed. -/
theorem coefficient_polynomial_moment (y : End Y) (u : V ⟶ Y) (ell : Y ⟶ V)
    (c : ℕ → k) (P a : ℕ) :
    u ≫ (y ^ a) ≫ capPolynomial c P y ≫ ell =
      ∑ n ∈ range (P + 1), c n • (u ≫ (y ^ (n + a)) ≫ ell) := by
  rw [capPolynomial, Preadditive.sum_comp, Preadditive.comp_sum, Preadditive.comp_sum]
  apply sum_congr rfl
  intro n hn
  rw [Linear.smul_comp, Linear.comp_smul, Linear.comp_smul]
  congr 1
  rw [pow_add, End.mul_def, Category.assoc]

/-- Below the reservoir degree the probe polynomial's extraction cap
annihilates the literal signed mate. -/
theorem negative_cap_annihilates_mate (q : k) (x : End X) (y : End Y)
    (s : X ⟶ Y) (u : V ⟶ Y) (v : X ⟶ V) (ell : Y ⟶ V)
    (N P : ℕ) (hPN : P < N) (c : ℕ → k)
    (hsupport : ∀ n ≤ P, c n * q ^ n = c n)
    (hslide : s ≫ y - q • (x ≫ s) = v ≫ u)
    (hwindow : ∀ a < N, u ≫ (y ^ a) ≫ ell = if a + 1 = N then 𝟙 V else 0)
    (hprobe : capPolynomial c P x = 0) :
    s ≫ capPolynomial c P y ≫ ell = 0 := by
  have hterm (n : ℕ) (hn : n ∈ range (P + 1)) :
      c n • (s ≫ (y ^ n) ≫ ell) = c n • ((x ^ n) ≫ s ≫ ell) := by
    have hnP : n ≤ P := Nat.le_of_lt_succ (mem_range.mp hn)
    have hnN : n < N := lt_of_le_of_lt hnP hPN
    rw [slide_coefficient_window q x y s u v ell N (by omega) hslide hwindow n hnN.le,
      ite_eq_right (ne_of_lt hnN), add_zero, smul_smul, hsupport n hnP]
  calc
    s ≫ capPolynomial c P y ≫ ell =
        ∑ n ∈ range (P + 1), c n • (s ≫ (y ^ n) ≫ ell) := by
      rw [capPolynomial, Preadditive.sum_comp, Preadditive.comp_sum]
      apply sum_congr rfl
      intro n hn
      rw [Linear.smul_comp, Linear.comp_smul]
    _ = ∑ n ∈ range (P + 1), c n • ((x ^ n) ≫ s ≫ ell) := sum_congr rfl hterm
    _ = capPolynomial c P x ≫ s ≫ ell := by
      rw [capPolynomial, Preadditive.sum_comp]
      apply sum_congr rfl
      intro n hn
      rw [Linear.smul_comp]
    _ = 0 := by rw [hprobe]; simp

/-- The same candidate cap is the last coordinate on the low-unit window.
This is the inverse-row test, rather than an assumed bubble moment. -/
theorem negative_cap_unit_window (y : End Y) (u : V ⟶ Y) (ell : Y ⟶ V)
    (N P : ℕ) (c : ℕ → k) (hmonic : c P = 1)
    (hwindow : ∀ a < N, u ≫ (y ^ a) ≫ ell = if a + 1 = N then 𝟙 V else 0)
    (a : ℕ) (ha : a + P < N) :
    u ≫ (y ^ a) ≫ capPolynomial c P y ≫ ell =
      if a + P + 1 = N then 𝟙 V else 0 := by
  rw [coefficient_polynomial_moment]
  by_cases htop : a + P + 1 = N
  · rw [ite_eq_left htop, Finset.sum_eq_single P]
    · rw [hwindow (P + a) (by omega), ite_eq_left (by omega), hmonic, one_smul]
    · intro n hn hnP
      have hn' : n < P := by have := mem_range.mp hn; omega
      rw [hwindow (n + a) (by omega), ite_eq_right (by omega), smul_zero]
    · simp
  · rw [ite_eq_right htop]
    apply sum_eq_zero
    intro n hn
    have hnP : n ≤ P := Nat.le_of_lt_succ (mem_range.mp hn)
    rw [hwindow (n + a) (by omega), ite_eq_right (by omega), smul_zero]

end OddMath.QuiverHecke.SwappedVacuum
