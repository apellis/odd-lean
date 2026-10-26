import OddMath.SKM.RouquierMateSeries

/-!
# All-length ordered dot conjugation

This ports the dot-conjugation identities used in
`Categorification/TwoRep/RouqCoproduct.lean` and `RouqCoproductNeg.lean`.
Its downstream consumer is the negative-window comparison in
`docs/Nondegeneracy/SeparatedFactorInversion.md`, equations (3) and (4).

The correction terms are retained at every length. In particular these
identities do not assert invertibility of an uncorrected cap/cup window
beyond its allowed range. No nilpotence hypothesis is needed here.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory
open scoped BigOperators
variable {C : Type*} [Category C] [Preadditive C] {X Y : C}

/-- Conjugating by an inverse source dot retains all finite cap–cup terms. -/
theorem mate_dot_conjugation_source (x w : End X) (y : End Y) (b f : X ⟶ Y)
    (q : ℤ) (h : x ≫ f - q • (f ≫ y) = b) (hw : w ≫ x = 𝟙 X) (n : ℕ) :
    q ^ n • ((w ^ n) ≫ f ≫ (y ^ n)) =
      f - ∑ j ∈ Finset.range n, q ^ j • ((w ^ (j + 1)) ≫ b ≫ (y ^ j)) := by
  have h' := congrArg (fun z => w ≫ z) h
  have hr : f = w ≫ b + q • (w ≫ f ≫ y) := by
    have hh : f - q • (w ≫ f ≫ y) = w ≫ b := by
      simpa only [Preadditive.comp_sub, Preadditive.comp_zsmul,
        ← Category.assoc w x, hw, Category.id_comp, Category.assoc] using h'
    exact sub_eq_iff_eq_add.mp hh
  have he := mate_signed_series_with_tail w y (w ≫ b) f q hr n
  have hc : (∑ j ∈ Finset.range n, q ^ j • ((w ^ j) ≫ (w ≫ b) ≫ (y ^ j))) =
      ∑ j ∈ Finset.range n, q ^ j • ((w ^ (j + 1)) ≫ b ≫ (y ^ j)) := by
    apply Finset.sum_congr rfl
    intro j _
    simp only [pow_succ' w j, End.mul_def, Category.assoc]
  rw [hc] at he
  exact eq_sub_iff_add_eq.mpr ((add_comm _ _).trans he.symm)

/-- The inverse-target conjugation has the opposite correction sign and the
shifted exponent `j+1`. The identity holds at every length. -/
theorem mate_dot_conjugation_target (x : End X) (y w : End Y) (b f : X ⟶ Y)
    (q : ℤ) (hq : q * q = 1) (h : x ≫ f - q • (f ≫ y) = b)
    (hw : y ≫ w = 𝟙 Y) (n : ℕ) :
    q ^ n • ((x ^ n) ≫ f ≫ (w ^ n)) =
      f + ∑ j ∈ Finset.range n, q ^ (j + 1) • ((x ^ j) ≫ b ≫ (w ^ (j + 1))) := by
  have h' := congrArg (fun z => q • (z ≫ w)) h
  have hh : q • (x ≫ f ≫ w) - f = q • (b ≫ w) := by
    simpa only [Preadditive.sub_comp, Preadditive.zsmul_comp, smul_sub,
      smul_smul, hq, one_smul, Category.assoc, hw, Category.comp_id] using h'
  have hr : f = -(q • (b ≫ w)) + q • (x ≫ f ≫ w) := by
    have hf : f = q • (x ≫ f ≫ w) - q • (b ≫ w) :=
      eq_sub_iff_add_eq.mpr ((add_comm _ _).trans (sub_eq_iff_eq_add.mp hh).symm)
    simpa only [sub_eq_add_neg, add_comm] using hf
  have he := mate_signed_series_with_tail x w (-(q • (b ≫ w))) f q hr n
  have hc : (∑ j ∈ Finset.range n, q ^ j • ((x ^ j) ≫ (-(q • (b ≫ w))) ≫ (w ^ j))) =
      -(∑ j ∈ Finset.range n, q ^ (j + 1) • ((x ^ j) ≫ b ≫ (w ^ (j + 1)))) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Preadditive.comp_neg, Preadditive.neg_comp, Preadditive.comp_zsmul,
      Preadditive.zsmul_comp, smul_neg, smul_smul, pow_succ q j,
      pow_succ w j, End.mul_def, Category.assoc]
  rw [hc] at he
  have he' := congrArg (fun z => z +
    ∑ j ∈ Finset.range n, q ^ (j + 1) • ((x ^ j) ≫ b ≫ (w ^ (j + 1)))) he
  have hcancel (a b : X ⟶ Y) : (-a + b) + a = b := by abel
  simpa only [hcancel] using he'.symm

end OddMath.SKM
