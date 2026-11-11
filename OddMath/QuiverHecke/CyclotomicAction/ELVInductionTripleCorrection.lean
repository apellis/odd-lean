/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionTriplePolynomial

/-! # The whole ordered induction correction

Brundan–Ellis (1.9): the parameter-supported three-dot source correction
is supernatural of the outer colour parity. Its entire induced linear
operator equals the ordered correction with the original parameters.
No polynomial-naturality, braid or comparison premise is imposed.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
variable {k C E : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
  (F : C ⥤ E) [F.Additive] [F.Linear k] [IsSuperfunctor k F]

omit [F.Additive] [F.Linear k] [IsSuperfunctor k F] in
private theorem correction_zero_supernatural (p : ZMod 2) :
    IsSupernatural k p (F := F) (G := F) (fun _ => 0) where
  mem _ := Submodule.zero_mem _
  naturality _ := by simp

omit [F.Additive] [F.Linear k] [IsSuperfunctor k F] in
private theorem correction_smul_supernatural {p : ZMod 2}
    {a : ∀ s, F.obj s ⟶ F.obj s} (ha : IsSupernatural k p a) (d : k) :
    IsSupernatural k p (fun s => d • a s) where
  mem s := Submodule.smul_mem _ d (ha.mem s)
  naturality hf := by
    simp only [Linear.comp_smul, Linear.smul_comp, ha.naturality hf, smul_smul]
    rw [mul_comm d]

omit [F.Additive] [F.Linear k] [IsSuperfunctor k F] in
private theorem correction_sum_supernatural {ι : Type*} (S : Finset ι) {p : ZMod 2}
    {a : ι → ∀ s, F.obj s ⟶ F.obj s}
    (ha : ∀ x ∈ S, IsSupernatural k p (a x)) :
    IsSupernatural k p (fun s => ∑ x ∈ S, a x s) where
  mem s := Submodule.sum_mem _ (fun x hx => (ha x hx).mem s)
  naturality hf := by
    simp only [Preadditive.comp_sum, Preadditive.sum_comp, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    exact (ha x hx).naturality hf

omit [F.Additive] [F.Linear k] [IsSuperfunctor k F] in
private theorem correction_add_supernatural {p : ZMod 2}
    {a b : ∀ s, F.obj s ⟶ F.obj s} (ha : IsSupernatural k p a) (hb : IsSupernatural k p b) :
    IsSupernatural k p (fun s => a s + b s) where
  mem s := Submodule.add_mem _ (ha.mem s) (hb.mem s)
  naturality hf := by
    simp only [Preadditive.comp_add, Preadditive.add_comp, ha.naturality hf,
      hb.naturality hf, smul_add]

omit [IsSuperfunctor k F] in
private theorem correction_pow_supernatural {p : ZMod 2}
    {a : ∀ s, End (F.obj s)} (ha : IsSupernatural k p a) (n : ℕ) :
    IsSupernatural k ((n : ZMod 2) * p) (fun s => a s ^ n) := by
  induction n with
  | zero => simpa using isSupernatural_id (R := k) (F := F)
  | succ n ih =>
    simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul, pow_succ', End.mul_def] using ih.comp ha

variable {I X : Type u} [AddCommGroup X] (D : SKM.Datum I X) (Sc : SKM.Scalars D k)
  (i j : I) {a b c : ∀ s, End (F.obj s)}
  (ha : IsSupernatural k (D.parity i) a) (hb : IsSupernatural k (D.parity j) b)
  (hc : IsSupernatural k (D.parity i) c)

include ha hb hc in
omit [IsSuperfunctor k F] in
/-- The supported source summand has the outer parity, including every reflected term. -/
theorem tripleSourceSum_supernatural (r s : ℕ) (d : k)
    (hd : d ≠ 0 → (r : ZMod 2) * D.parity i = 0 ∧ (s : ZMod 2) * D.parity j = 0) :
    IsSupernatural k (D.parity i) (fun v =>
      tripleDotCorrectionSum D (R := End (F.obj v)) i j r s d (c v) (b v) (a v)) := by
  by_cases hd0 : d = 0
  · simpa only [tripleDotCorrectionSum, hd0, mul_zero, zero_smul, Finset.sum_const_zero] using
      correction_zero_supernatural F (D.parity i)
  obtain ⟨hr, hs⟩ := hd hd0
  apply correction_sum_supernatural F (Finset.range r)
  intro l hl
  have hdeg : ((l : ZMod 2) * D.parity i + (s : ZMod 2) * D.parity j) +
      ((r - 1 - l : ℕ) : ZMod 2) * D.parity i = D.parity i := by
    calc
      _ = ((r - 1 - l : ℕ) : ZMod 2) * D.parity i +
          ((s : ZMod 2) * D.parity j + (l : ZMod 2) * D.parity i) := by ring
      _ = _ := mixed_braid_total_parity (D.parity i) (D.parity j) r s l hr hs (Finset.mem_range.mp hl)
  have hm := ((correction_pow_supernatural F hc l).comp
    (correction_pow_supernatural F hb s)).comp (correction_pow_supernatural F ha (r - 1 - l))
  rw [hdeg] at hm
  have hm' : IsSupernatural k (D.parity i) (fun v =>
      a v ^ (r - 1 - l) * b v ^ s * c v ^ l) := by
    simpa only [End.mul_def, Category.assoc] using hm
  exact correction_smul_supernatural F hm' (SKM.zsign k (D.parity i * (D.parity j + l)) * d)

include ha hb hc in
omit [IsSuperfunctor k F] in
/-- The full source correction is natural without an additional naturality hypothesis. -/
theorem tripleSourcePolynomial_supernatural (hij : i ≠ j) :
    IsSupernatural k (D.parity i) (fun v =>
      tripleDotCorrectionPolynomial D Sc (R := End (F.obj v)) i j (c v) (b v) (a v)) := by
  apply correction_add_supernatural F
  · exact tripleSourceSum_supernatural F D i j ha hb hc (D.dn i j) 0 (Sc.t i j : k)
      (fun _ => ⟨CyclotomicAction.dn_cast_mul_parity D hij, by simp⟩)
  · apply correction_sum_supernatural F (Finset.range (D.dn i j))
    intro r _
    apply correction_sum_supernatural F (Finset.range (D.dn j i))
    intro s _
    exact tripleSourceSum_supernatural F D i j ha hb hc r s (Sc.s i j r s)
      (fun hz => elvParameter_support D Sc hz)

/-- Whole linear operators retain the ordered original-Sc correction. -/
theorem transformLinear_triplePolynomial_eq (hij : i ≠ j)
    (N : Superfunctor k C (SVec k)) (w : E) :
    tripleDotCorrectionPolynomial D Sc i j
        (transformLinear ha N w) (transformLinear hb N w) (transformLinear hc N w) =
      sign k (D.parity i * D.parity j) •
        transformLinear (tripleSourcePolynomial_supernatural F D (parameterTwist D Sc) i j ha hb hc hij) N w := by
  apply hom_ext
  intro v g z
  rw [LinearMap.smul_apply, transformLinear_tensor,
    transformLinear_triplePolynomial_tensor F D Sc i j ha hb hc hij N w v g z]
  rfl

end OddMath.QuiverHecke.ELVOld.BalancedInduction
