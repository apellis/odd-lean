/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.ELVCyclotomicSeparation

/-! # Separation for signed last-position ELV boundary polynomials

The explicit candidate ideal of SwappedVacuumCoordinates §§5–6 retains
the entire coefficient ideal and both colour-correct last-position
polynomials. We prove its bounded separation directly, without identifying
it with an action kernel or transporting any affine presentation.
-/
noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams
open scoped Classical TensorProduct
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k)

/-- A dot power at a specified native strand position. -/
def boundaryPositionDotPower (t : List I) (p j : ℕ) :
    (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t) :=
  cl D Sc t t ((List.replicate j p).map PG.dot)
    (by simpa only [tgt_map_dot] using
      sChain_pl t ((List.replicate j p).map PG.dot))

def boundaryPositionPolynomial (t : List I) (p N : ℕ)
    (c : Fin (N + 1) → SKM.SYM D k) :
    coefficientObj D Sc t ⟶ coefficientObj D Sc t :=
  ∑ j : Fin (N + 1),
    sourceCoefficientHom D Sc (c j) (boundaryPositionDotPower D Sc t p j.val)

/-- Every valid position has the same weighted bound; crossings are absent. -/
theorem boundaryPositionPolynomial_mem_score (t : List I) (p N : ℕ)
    (c : Fin (N + 1) → SKM.SYM D k) (hp : p < t.length)
    (hc : ∀ j, c j ∈ SKM.SYM.CoefficientAtLeast D k (N - j.val)) :
    boundaryPositionPolynomial D Sc t p N c ∈
      ExtendedScore D Sc t t (N : ℤ) := by
  apply Submodule.sum_mem
  intro j _
  have hm : ∀ q ∈ List.replicate j.val p, q < t.length := by
    intro q hq
    have hqp : q = p := (List.mem_replicate.mp hq).2
    exact hqp.symm ▸ hp
  have he := highCoefficient_word_mem_score D Sc (hc j)
    ((List.replicate j.val p).map PG.dot)
    (show SChain t (pl t ((List.replicate j.val p).map PG.dot)) t from
      by simpa only [tgt_map_dot] using
        sChain_pl t ((List.replicate j.val p).map PG.dot))
  rw [positionedScore_dots hm, List.length_replicate] at he
  have hval : ((N - j.val : ℕ) : ℤ) + j.val = N := by
    have := j.isLt
    omega
  rw [hval] at he
  exact he

/-- Signed reversal contributes the binomial sign to each odd dot power.
Coefficients remain on the left and the full exterior algebra is retained. -/
def signedLastOddPolynomial (i : {i : I // D.parity i = 1})
    (tail : List I) (N : ℕ) :
    coefficientObj D Sc (tail ++ [i.1]) ⟶ coefficientObj D Sc (tail ++ [i.1]) :=
  boundaryPositionPolynomial D Sc (tail ++ [i.1]) tail.length N
    (fun j => ((-1 : k) ^ (j.val.choose 2)) • SKM.SYM.elvMonicCoefficient D k i N j)

theorem signedLastOddPolynomial_mem_score (i : {i : I // D.parity i = 1})
    (tail : List I) (N : ℕ) :
    signedLastOddPolynomial D Sc i tail N ∈
      ExtendedScore D Sc (tail ++ [i.1]) (tail ++ [i.1]) (N : ℤ) := by
  apply boundaryPositionPolynomial_mem_score D Sc _ _ _ _ (by simp)
  intro j
  exact Submodule.smul_mem _ _
    (SKM.SYM.elvMonicCoefficient_mem_coefficientAtLeast D k i N j)

def lastEvenPolynomial (i : I) (tail : List I) (N : ℕ) :
    coefficientObj D Sc (tail ++ [i]) ⟶ coefficientObj D Sc (tail ++ [i]) :=
  boundaryPositionPolynomial D Sc (tail ++ [i]) tail.length N
    (SKM.SYM.evenMonicCoefficient D k i N)

theorem lastEvenPolynomial_mem_score (i : I) (hi : D.parity i = 0)
    (tail : List I) (N : ℕ) :
    lastEvenPolynomial D Sc i tail N ∈
      ExtendedScore D Sc (tail ++ [i]) (tail ++ [i]) (N : ℤ) :=
  boundaryPositionPolynomial_mem_score D Sc _ _ _ _ (by simp)
    (SKM.SYM.evenMonicCoefficient_mem_coefficientAtLeast D k i hi N)

/-- Explicit candidate inverse-image generators; this definition asserts
no presentation equivalence or action-kernel equality. -/
def SignedLastELVGenerator (cutoff : I → ℕ) (t : List I)
    (r : coefficientObj D Sc t ⟶ coefficientObj D Sc t) : Prop :=
  (∃ a : SKM.SYM D k, a ∈ SKM.SYM.elvCoefficientIdeal D k cutoff ∧
    r = sourceCoefficientHom D Sc a (𝟙 ((pres D Sc).obj (ob D t)))) ∨
  (∃ i : {i : I // D.parity i = 1}, ∃ tail, ∃ h : t = tail ++ [i.1],
    r = eqToHom (congrArg (coefficientObj D Sc) h) ≫
      signedLastOddPolynomial D Sc i tail (cutoff i.1) ≫
      eqToHom (congrArg (coefficientObj D Sc) h.symm)) ∨
  (∃ i : I, D.parity i = 0 ∧ ∃ tail, ∃ h : t = tail ++ [i],
    r = eqToHom (congrArg (coefficientObj D Sc) h) ≫
      lastEvenPolynomial D Sc i tail (cutoff i) ≫
      eqToHom (congrArg (coefficientObj D Sc) h.symm))

theorem signedLastELVGenerator_mem_score {cutoff : I → ℕ} {N : ℕ}
    (hN : ∀ i, N ≤ cutoff i) {t : List I}
    {r : coefficientObj D Sc t ⟶ coefficientObj D Sc t}
    (hr : SignedLastELVGenerator D Sc cutoff t r) :
    r ∈ ExtendedScore D Sc t t (N : ℤ) := by
  rcases hr with ⟨a, ha, rfl⟩ | ⟨i, tail, h, rfl⟩ | ⟨i, hi, tail, h, rfl⟩
  · have hw := (SKM.SYM.mem_coefficientIdeal_iff D k _ _).mp
      (SKM.SYM.elvCoefficientIdeal_le_weight D k hN ha)
    have hm := highCoefficient_word_mem_score D Sc (t := t) (t' := t)
      (SKM.SYM.coefficientAtLeast_antitone D k (Nat.le_succ N) hw) [] (sChain_pl t [])
    simpa [coefficient_cl_nil, positionedScore, wordScore, crossCount] using hm
  · subst t
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    exact extendedScore_antitone D Sc (by exact_mod_cast hN i.1)
      (signedLastOddPolynomial_mem_score D Sc i tail (cutoff i.1))
  · subst t
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    exact extendedScore_antitone D Sc (by exact_mod_cast hN i)
      (lastEvenPolynomial_mem_score D Sc i hi tail (cutoff i))

/-- Two-sided sandwiches by arbitrary coefficient-extended affine morphisms. -/
def SignedLastELVRelationSpan (cutoff : I → ℕ) (t t' : List I) :
    Submodule k (coefficientObj D Sc t ⟶ coefficientObj D Sc t') :=
  Submodule.span k {f | ∃ v : List I, v.length = t.length ∧
    ∃ r : coefficientObj D Sc v ⟶ coefficientObj D Sc v,
      SignedLastELVGenerator D Sc cutoff v r ∧
    ∃ a : coefficientObj D Sc t ⟶ coefficientObj D Sc v,
    ∃ b : coefficientObj D Sc v ⟶ coefficientObj D Sc t', a ≫ r ≫ b = f}

theorem signedLastELVRelationSpan_le_weighted {cutoff : I → ℕ} {N : ℕ}
    (hN : ∀ i, N ≤ cutoff i) (t t' : List I) :
    SignedLastELVRelationSpan D Sc cutoff t t' ≤ WeightedRelationSpan D Sc t t' N := by
  apply Submodule.span_le.mpr
  rintro _ ⟨v, hv, r, hr, a, b, rfl⟩
  exact Submodule.subset_span
    ⟨v, hv, r, signedLastELVGenerator_mem_score D Sc hN hr, a, b, rfl⟩

/-- The signed last-boundary quotient preserves each sufficiently small
full coefficient/PBW window, without comparing first- and last-boundary ideals. -/
theorem signedLastELV_quotient_injective_on_extendedAtMost
    {cutoff : I → ℕ} {t t' : List I} {d N : ℕ}
    (hN : ∀ i, N ≤ cutoff i) (hd : d + 2 * t.length.choose 2 < N) :
    Function.Injective (fun x : ExtendedAtMost D Sc t t' d =>
      (SignedLastELVRelationSpan D Sc cutoff t t').mkQ
        (x : coefficientObj D Sc t ⟶ coefficientObj D Sc t')) := by
  intro x y hxy
  apply Subtype.ext
  apply sub_eq_zero.mp
  have hm : (x : coefficientObj D Sc t ⟶ coefficientObj D Sc t') - y ∈
      SignedLastELVRelationSpan D Sc cutoff t t' := (Submodule.Quotient.eq _).mp hxy
  exact Submodule.disjoint_def.mp
    (disjoint_extendedAtMost_extendedAtLeast D Sc (by omega)) _
    (Submodule.sub_mem _ x.property y.property)
    (weightedRelationSpan_le_extendedAtLeast D Sc t t' N
      (signedLastELVRelationSpan_le_weighted D Sc hN t t' hm))

/-- Every fixed colourwise parity schedule detects the full abstract
coefficient extension. This is algebraic separation, not an action. -/
theorem signedLastELV_parity_quotients_jointly_detect (ε : I → ℕ)
    {t t' : List I} (f : coefficientObj D Sc t ⟶ coefficientObj D Sc t')
    (hf : ∀ m, (SignedLastELVRelationSpan D Sc
      (fun i => 2 * m + ε i) t t').mkQ f = 0) : f = 0 := by
  obtain ⟨d, hd⟩ := exists_mem_extendedAtMost D Sc t t' f
  let m := d + 2 * t.length.choose 2 + 1
  have hinj := signedLastELV_quotient_injective_on_extendedAtMost D Sc
    (cutoff := fun i => 2 * m + ε i) (t := t) (t' := t') (d := d) (N := 2 * m)
    (fun _ => by omega) (by omega)
  have h := hinj (a₁ := ⟨f, hd⟩) (a₂ := 0) (by simpa using hf m)
  exact congrArg Subtype.val h

end OddMath.QuiverHecke
