import OddMath.SKM.RouquierMateSlide

/-!
# Finite ordered solutions of the two projected mate slides

This ports the finite-series step of `Categorification/TwoRep/RouqCoproduct.lean`
with the super sign retained. Its downstream consumer is
`SuperRouquierLoc.MateProjectionFormula`. These are algebraic consequences of
specified dot slides and nilpotence, not a construction of the Hom-sector
comparison maps. Only the probe dot is inverted.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams
open scoped BigOperators

variable {C : Type*} [Category C] [Preadditive C] {X Y : C}

/-- Iterate the ordered affine recurrence without commuting any factors. -/
theorem mate_series_with_tail (s : End X) (t : End Y) (b f : X ⟶ Y)
    (h : f = b + s ≫ f ≫ t) (n : ℕ) :
    f = (∑ j ∈ Finset.range n, (s ^ j) ≫ b ≫ (t ^ j)) +
      (s ^ n) ≫ f ≫ (t ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      f = (∑ j ∈ Finset.range n, (s ^ j) ≫ b ≫ (t ^ j)) +
          (s ^ n) ≫ f ≫ (t ^ n) := ih
      _ = (∑ j ∈ Finset.range n, (s ^ j) ≫ b ≫ (t ^ j)) +
          (s ^ n) ≫ (b + s ≫ f ≫ t) ≫ (t ^ n) := by rw [← h]
      _ = (∑ j ∈ Finset.range (n + 1), (s ^ j) ≫ b ≫ (t ^ j)) +
          (s ^ (n + 1)) ≫ f ≫ (t ^ (n + 1)) := by
        simp only [Finset.sum_range_succ, Preadditive.comp_add, Preadditive.add_comp,
          pow_succ' s n, pow_succ t n, End.mul_def, Category.assoc, add_assoc]

/-- A nilpotent side kills the tail; the other side need not be nilpotent. -/
theorem mate_series (s : End X) (t : End Y) (b f : X ⟶ Y)
    (h : f = b + s ≫ f ≫ t) (n : ℕ) (hn : s ^ n = 0 ∨ t ^ n = 0) :
    f = ∑ j ∈ Finset.range n, (s ^ j) ≫ b ≫ (t ^ j) := by
  have he := mate_series_with_tail s t b f h n
  rcases hn with hs | ht
  · simpa [hs] using he
  · simpa [ht] using he

/-- Signed recurrence with an explicit ordered tail. Integer coefficients act
on the Hom group, not on the endomorphism-ring structure. -/
theorem mate_signed_series_with_tail (s : End X) (t : End Y) (b f : X ⟶ Y)
    (q : ℤ) (h : f = b + q • (s ≫ f ≫ t)) (n : ℕ) :
    f = (∑ j ∈ Finset.range n, q ^ j • ((s ^ j) ≫ b ≫ (t ^ j))) +
      q ^ n • ((s ^ n) ≫ f ≫ (t ^ n)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      f = (∑ j ∈ Finset.range n, q ^ j • ((s ^ j) ≫ b ≫ (t ^ j))) +
          q ^ n • ((s ^ n) ≫ f ≫ (t ^ n)) := ih
      _ = (∑ j ∈ Finset.range n, q ^ j • ((s ^ j) ≫ b ≫ (t ^ j))) +
          q ^ n • ((s ^ n) ≫ (b + q • (s ≫ f ≫ t)) ≫ (t ^ n)) := by rw [← h]
      _ = (∑ j ∈ Finset.range (n + 1), q ^ j • ((s ^ j) ≫ b ≫ (t ^ j))) +
          q ^ (n + 1) • ((s ^ (n + 1)) ≫ f ≫ (t ^ (n + 1))) := by
        simp only [Finset.sum_range_succ, Preadditive.comp_add, Preadditive.add_comp,
          Preadditive.comp_zsmul, Preadditive.zsmul_comp, smul_add, smul_smul,
          pow_succ' s n, pow_succ t n, pow_succ q n, End.mul_def,
          Category.assoc, add_assoc]

/-- The finite signed series, killed on either nilpotent side. -/
theorem mate_signed_series (s : End X) (t : End Y) (b f : X ⟶ Y)
    (q : ℤ) (h : f = b + q • (s ≫ f ≫ t)) (n : ℕ)
    (hn : s ^ n = 0 ∨ t ^ n = 0) :
    f = ∑ j ∈ Finset.range n, q ^ j • ((s ^ j) ≫ b ≫ (t ^ j)) := by
  have he := mate_signed_series_with_tail s t b f q h n
  rcases hn with hs | ht
  · simpa [hs] using he
  · simpa [ht] using he

/-- The C-block series: invert the source probe dot and use nilpotence only
of the target reservoir dot. The coefficient order is never reversed. -/
theorem mate_series_probe_source (x w : End X) (y : End Y) (b f : X ⟶ Y)
    (q : ℤ) (h : x ≫ f - q • (f ≫ y) = b) (hw : w ≫ x = 𝟙 X)
    (n : ℕ) (hn : y ^ n = 0) :
    f = ∑ j ∈ Finset.range n, q ^ j • ((w ^ (j + 1)) ≫ b ≫ (y ^ j)) := by
  have h' := congrArg (fun z => w ≫ z) h
  have hr : f = w ≫ b + q • (w ≫ f ≫ y) := by
    have hh : f - q • (w ≫ f ≫ y) = w ≫ b := by
      simpa only [Preadditive.comp_sub, Preadditive.comp_zsmul,
        ← Category.assoc w x, hw, Category.id_comp, Category.assoc] using h'
    exact sub_eq_iff_eq_add.mp hh
  rw [mate_signed_series w y (w ≫ b) f q hr n (Or.inr hn)]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  simp only [pow_succ' w j, End.mul_def, Category.assoc]

/-- The D-block series: invert only the target probe dot. The minus sign and
one-step shift of the sign exponent are forced by solving the second slide. -/
theorem mate_series_probe_target (x : End X) (y w : End Y) (b f : X ⟶ Y)
    (q : ℤ) (hq : q * q = 1) (h : x ≫ f - q • (f ≫ y) = b)
    (hw : y ≫ w = 𝟙 Y) (n : ℕ) (hn : x ^ n = 0) :
    f = -(∑ j ∈ Finset.range n, q ^ (j + 1) • ((x ^ j) ≫ b ≫ (w ^ (j + 1)))) := by
  have h' := congrArg (fun z => q • (z ≫ w)) h
  have hh : q • (x ≫ f ≫ w) - f = q • (b ≫ w) := by
    simpa only [Preadditive.sub_comp, Preadditive.zsmul_comp, smul_sub,
      smul_smul, hq, one_smul, Category.assoc, hw, Category.comp_id] using h'
  have hr : f = -(q • (b ≫ w)) + q • (x ≫ f ≫ w) := by
    have hf : f = q • (x ≫ f ≫ w) - q • (b ≫ w) :=
      eq_sub_iff_add_eq.mpr ((add_comm _ _).trans (sub_eq_iff_eq_add.mp hh).symm)
    simpa only [sub_eq_add_neg, add_comm] using hf
  rw [mate_signed_series x w (-(q • (b ≫ w))) f q hr n (Or.inl hn)]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Preadditive.comp_neg, Preadditive.neg_comp, Preadditive.comp_zsmul,
    Preadditive.zsmul_comp, smul_neg, smul_smul, pow_succ q j,
    pow_succ w j, End.mul_def, Category.assoc]

end OddMath.SKM
