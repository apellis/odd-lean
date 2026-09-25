import OddMath.Frontier.ProjectorRank
import OddMath.Frontier.BoxPartitionCount
import OddMath.Frontier.NilHeckeGradedEnd
import Mathlib.RingTheory.LaurentSeries

/-! EKL arXiv:1111.1320v1, §2.1.2, displays (2.15)–(2.20), p.6, Proposition 2.2 and (2.28),
p.6–8, and the rank count (2.52), p.13, in `q`-series form.

Conventions. `deg xᵢ = 2`, so polynomial degree `d` is paper degree `2d`. Graded ranks are
power series in `q` (`qrk V = Σ rk(V_{2d}) q^{2d}`); the balanced `q`-integers
`[m] = q^{m-1} + q^{m-3} + ⋯ + q^{1-m}` of (2.15) live in Laurent series. Proved:
* `qrk(OΛ_a) · ∏ᵢ(1 - q^{2i}) = 1` (the first line of (2.18), for `OΛ_a`);
* `qrk(OΛ_a) · [a]! · (1 - q²)^a = q^{-a(a-1)/2}` (Proposition 2.2, i.e. (2.20)/(2.28));
* `qrk(OPol_a) = qrk(OΛ_a) · Σ_{σ ∈ S_a} q^{2ℓ(σ)}` and `Σ_σ q^{2ℓ(σ)} = q^{a(a-1)/2}[a]!`
  ((2.19) with the exponent corrected, and (2.52));
* the printed (2.19), with `q^{ℓ(σ)}`, is false for every `a ≥ 2`. -/
namespace OddMath.Frontier.EKLSectionTwo
open PowerSeries BoxPartitionCount
open scoped BigOperators
noncomputable section

/-! ### The substitution `t = q²` -/

/-- Doubling of exponents, `ℕ → ℕ`. -/
def twiceHom : ℕ →+ ℕ where
  toFun m := 2 * m
  map_zero' := rfl
  map_add' a b := by ring

theorem twiceHom_injective : Function.Injective twiceHom := fun a b h => by
  simp only [twiceHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at h; omega

theorem twiceHom_le (a b : ℕ) : twiceHom a ≤ twiceHom b ↔ a ≤ b := by
  simp only [twiceHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk]; omega

/-- The ring homomorphism `f(t) ↦ f(q²)` on integer power series. -/
def tsq : ℤ⟦X⟧ →+* ℤ⟦X⟧ :=
  (HahnSeries.toPowerSeries (R := ℤ)).toRingHom.comp
    ((HahnSeries.embDomainRingHom twiceHom twiceHom_injective twiceHom_le).comp
      (HahnSeries.toPowerSeries (R := ℤ)).symm.toRingHom)

theorem coeff_tsq (f : ℤ⟦X⟧) (m : ℕ) :
    coeff ℤ m (tsq f) = if Even m then coeff ℤ (m / 2) f else 0 := by
  change coeff ℤ m (HahnSeries.toPowerSeries (HahnSeries.embDomain _ _)) = _
  rw [HahnSeries.coeff_toPowerSeries]
  split_ifs with hm
  · obtain ⟨k, rfl⟩ := hm
    have hk : k + k = twiceHom k := by simp [twiceHom]; ring
    rw [hk, HahnSeries.embDomain_mk_coeff]
    change (HahnSeries.toPowerSeries.symm f).coeff k = _
    rw [HahnSeries.coeff_toPowerSeries_symm]
    congr 1
    simp [twiceHom]
  · rw [HahnSeries.embDomain_notin_range]
    rintro ⟨k, hk⟩
    apply hm
    exact ⟨k, by simp [twiceHom] at hk; omega⟩

theorem tsq_X : tsq X = X ^ 2 := by
  ext m
  rw [coeff_tsq, coeff_X_pow, coeff_X]
  by_cases hm : m = 2
  · subst hm; simp
  · rw [if_neg hm]
    split_ifs with h1 h2
    · obtain ⟨k, rfl⟩ := h1; omega
    · rfl
    · rfl

/-! ### Graded ranks -/

/-- `Σ_d rk(OΛ_a)_{2d} t^d`, `a = n+2`, from the literal degree pieces of the joint kernel. -/
def symRank (n : ℕ) : ℤ⟦X⟧ :=
  PowerSeries.mk fun d => (Module.finrank ℤ (ElementaryBasis.degreePiece n d) : ℤ)

/-- `Σ_d rk(OPol_N)_{2d} t^d`, from the literal monomial degree pieces. -/
def polRank (N : ℕ) : ℤ⟦X⟧ :=
  PowerSeries.mk fun d => (Module.finrank ℤ (ProjectorRank.Vd N d) : ℤ)

/-- `Σ_{σ ∈ S_a} t^{ℓ(σ)}`, `a = n+2`, with `ℓ` the inversion number. -/
def lengthSeries (n : ℕ) : ℤ⟦X⟧ := ∑ w : NilCoxeterWords.Perm n, X ^ NilCoxeterWords.length w

theorem card_index (N d : ℕ) : Fintype.card (ElementaryBasis.Index N d) = pcount N d := by
  classical
  rw [pcount, ← Fintype.card_coe]
  exact Fintype.card_congr (Equiv.subtypeEquivRight fun a => by
    rw [mem_partitions])

theorem symRank_eq (n : ℕ) : symRank n = pgf (n+2) := by
  ext d
  simp [symRank, pgf, ElementaryBasis.graded_rank, card_index]

theorem polRank_eq (N : ℕ) : polRank N = mgf N := by
  ext d
  simp [polRank, mgf, ProjectorRank.finrank_Vd, ProjectorRank.expSet]

theorem lengthSeries_eq (n : ℕ) :
    lengthSeries n = ∏ j ∈ Finset.range (n+2), ∑ k ∈ Finset.range (j+1), (X : ℤ⟦X⟧) ^ k :=
  NilHeckeGrading.inversion_generating X (n+2)

theorem lengthSeries_mul (n : ℕ) : lengthSeries n * (1 - X) ^ (n+2) = qPoch (n+2) := by
  rw [lengthSeries_eq, qPoch, show (1 - X : ℤ⟦X⟧) ^ (n+2) = ∏ _j ∈ Finset.range (n+2), (1 - X) by
    simp, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun j _ => geom_sum_mul_neg X (j+1)

/-- (2.18), first line, for `OΛ_a` in `t = q²`: `qrk(OΛ_a) = ∏_{i=1}^a 1/(1 - t^i)`. -/
theorem symRank_mul_qPoch (n : ℕ) : symRank n * qPoch (n+2) = 1 := by
  rw [symRank_eq]; exact pgf_mul_qPoch _

/-- (2.20) in `t = q²`: `qrk(OΛ_a) · Σ_σ t^{ℓ(σ)} · (1 - t)^a = 1`. -/
theorem symRank_mul_length (n : ℕ) : symRank n * lengthSeries n * (1 - X) ^ (n+2) = 1 := by
  rw [mul_assoc, lengthSeries_mul, symRank_mul_qPoch]

/-- (2.19) corrected and (2.52), in `t = q²`: `qrk(OPol_a) = qrk(OΛ_a) · Σ_σ t^{ℓ(σ)}`. -/
theorem polRank_eq_mul (n : ℕ) : polRank (n+2) = symRank n * lengthSeries n := by
  have h1 := mgf_mul (n+2)
  have h2 := symRank_mul_length n
  rw [polRank_eq]
  linear_combination (symRank n * lengthSeries n) * h1 - mgf (n+2) * h2

/-! ### Series in `q` -/

/-- `qrk(OΛ_a) = Σ_d rk(OΛ_a)_{2d} q^{2d}`. -/
def qrkSym (n : ℕ) : ℤ⟦X⟧ := tsq (symRank n)

/-- `qrk(OPol_a) = Σ_d rk(OPol_a)_{2d} q^{2d}`. -/
def qrkPol (N : ℕ) : ℤ⟦X⟧ := tsq (polRank N)

theorem qrkSym_mul_qPoch (n : ℕ) :
    qrkSym n * ∏ i ∈ Finset.range (n+2), (1 - X ^ (2 * (i+1))) = 1 := by
  have h := congrArg tsq (symRank_mul_qPoch n)
  rw [map_mul, map_one, qPoch, map_prod] at h
  simpa [tsq_X, ← pow_mul] using h

/-- (2.19) corrected: `qrk(OPol_a) = qrk(OΛ_a) · Σ_{σ ∈ S_a} q^{2ℓ(σ)}`. -/
theorem qrkPol_eq (n : ℕ) :
    qrkPol (n+2) = qrkSym n * ∑ w : NilCoxeterWords.Perm n, X ^ (2 * NilCoxeterWords.length w) := by
  rw [qrkPol, qrkSym, polRank_eq_mul, map_mul, lengthSeries, map_sum]
  simp [tsq_X, ← pow_mul]

theorem coeff_zero_symRank (n : ℕ) : coeff ℤ 0 (symRank n) = 1 := by
  have h := congrArg (constantCoeff ℤ) (symRank_mul_qPoch n)
  rw [map_mul, map_one, qPoch, map_prod] at h
  simpa using h

theorem length_simple (n : ℕ) (i : Fin (n+1)) :
    NilCoxeterWords.length (NilCoxeterWords.simple i) = 1 := by
  have h := NilCoxeterWords.length_ascend (1 : NilCoxeterWords.Perm n) i (by
    simp [NilCoxeterWords.Descent, Fin.lt_def])
  rw [one_mul] at h
  rw [h, Nat.add_left_eq_self]
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => if_neg fun hab => ?_
  exact lt_asymm hab.1 hab.2

/-- The printed (2.19), `qrk(Λ_a) = qrk(Pol_a) / Σ_σ q^{ℓ(σ)}`, fails for every `a ≥ 2`
(with `OΛ_a`, `OPol_a` in place of `Λ_a`, `Pol_a`, which have the same graded ranks):
the coefficients of `q¹` differ. -/
theorem printed_qrk_quotient_false (n : ℕ) :
    qrkSym n * ∑ w : NilCoxeterWords.Perm n, X ^ NilCoxeterWords.length w ≠ qrkPol (n+2) := by
  intro h
  have hc := congrArg (coeff ℤ 1) h
  rw [qrkPol, coeff_tsq, coeff_mul, Finset.Nat.sum_antidiagonal_succ,
    Finset.Nat.antidiagonal_zero, Finset.sum_singleton, qrkSym, coeff_tsq, coeff_tsq] at hc
  simp only [Even.zero, if_true, Nat.zero_div, Nat.not_even_one, if_false, zero_add,
    zero_mul, add_zero, coeff_zero_symRank, one_mul, map_sum, coeff_X_pow] at hc
  have hpos : (1 : ℤ) ≤ ∑ w : NilCoxeterWords.Perm n,
      (if 1 = NilCoxeterWords.length w then (1 : ℤ) else 0) := by
    have := Finset.single_le_sum (f := fun w : NilCoxeterWords.Perm n =>
      if 1 = NilCoxeterWords.length w then (1 : ℤ) else 0)
      (fun w _ => by dsimp only; split_ifs <;> norm_num) (Finset.mem_univ (NilCoxeterWords.simple 0))
    simpa [length_simple] using this
  omega

/-! ### Balanced `q`-integers and Proposition 2.2 -/

/-- Laurent series in `q` with integer coefficients. -/
abbrev LS := HahnSeries ℤ ℤ

/-- The monomial `q^k`, `k ∈ ℤ`. -/
def qpow (k : ℤ) : LS := HahnSeries.single k 1

/-- Balanced `q`-integer (2.15): `[m] = Σ_{j<m} q^{m-1-2j}`. -/
def qint (m : ℕ) : LS := ∑ j ∈ Finset.range m, qpow ((m : ℤ) - 1 - 2 * j)

/-- Balanced `q`-factorial (2.15): `[a]! = [a][a-1]⋯[1]`. -/
def qfactorial (a : ℕ) : LS := ∏ i ∈ Finset.range a, qint (i+1)

/-- Power series in `q` as Laurent series. -/
abbrev ofPS : ℤ⟦X⟧ →+* LS := HahnSeries.ofPowerSeries ℤ ℤ

theorem qpow_add (a b : ℤ) : qpow (a + b) = qpow a * qpow b := by
  simp only [qpow, HahnSeries.single_mul_single, mul_one]

theorem qpow_zero : qpow 0 = 1 := rfl

theorem ofPS_X_pow (k : ℕ) : ofPS (X ^ k) = qpow k := by
  rw [HahnSeries.ofPowerSeries_X_pow]; rfl

/-- `(q - q⁻¹)[m] = q^m - q^{-m}`: the defining quotient of (2.15). -/
theorem qint_mul (m : ℕ) : (qpow 1 - qpow (-1)) * qint m = qpow m - qpow (-m) := by
  induction m with
  | zero => simp [qint, qpow]
  | succ m ih =>
    have hs : qint (m+1) = qpow m + qpow (-1) * qint m := by
      simp only [qint, Finset.mul_sum, ← qpow_add]
      rw [Finset.sum_range_succ', add_comm]
      congr 1
      · congr 1; push_cast; ring
      · refine Finset.sum_congr rfl fun j _ => ?_
        congr 1; push_cast; ring
    have e1 : qpow 1 * qpow m = qpow ((m + 1 : ℕ) : ℤ) := by rw [← qpow_add]; push_cast; ring_nf
    have e3 : qpow (-1) * qpow (-m) = qpow (-((m + 1 : ℕ) : ℤ)) := by
      rw [← qpow_add]; push_cast; ring_nf
    rw [hs]
    linear_combination qpow (-1) * ih + e1 - e3

/-- `[j+1] = q^{-j} Σ_{k ≤ j} q^{2k}`. -/
theorem qint_eq (j : ℕ) :
    qint (j+1) = qpow (-j) * ofPS (tsq (∑ k ∈ Finset.range (j+1), X ^ k)) := by
  rw [map_sum, map_sum, Finset.mul_sum, qint, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [map_pow, tsq_X, ← pow_mul, ofPS_X_pow, ← qpow_add]
  have hk' := Finset.mem_range.mp hk
  congr 1
  rw [show j + 1 - 1 - k = j - k by omega]
  push_cast [Nat.cast_sub (show k ≤ j by omega)]
  ring

theorem prod_qpow (a : ℕ) :
    ∏ j ∈ Finset.range a, qpow (-(j : ℤ)) = qpow (-((a.choose 2 : ℕ) : ℤ)) := by
  induction a with
  | zero => simp [qpow_zero]
  | succ a ih =>
    rw [Finset.prod_range_succ, ih, ← qpow_add, Nat.choose_succ_succ, Nat.choose_one_right]
    congr 1; push_cast; ring

/-- `∏_{j<m} (1 + t + ⋯ + t^j)`, the unbalanced `t`-factorial. -/
def tfact (m : ℕ) : ℤ⟦X⟧ := ∏ j ∈ Finset.range m, ∑ k ∈ Finset.range (j+1), (X : ℤ⟦X⟧) ^ k

theorem tfact_mul (m : ℕ) : tfact m * (1 - X) ^ m = qPoch m := by
  rw [tfact, qPoch, show (1 - X : ℤ⟦X⟧) ^ m = ∏ _j ∈ Finset.range m, (1 - X) by simp,
    ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun j _ => geom_sum_mul_neg X (j+1)

/-- The balanced factorial is the shifted `t`-factorial at `t = q²`:
`[m]! = q^{-m(m-1)/2} ∏_{j<m} (1 + q² + ⋯ + q^{2j})`. -/
theorem qfactorial_eq_tfact (m : ℕ) :
    qfactorial m = qpow (-((m.choose 2 : ℕ) : ℤ)) * ofPS (tsq (tfact m)) := by
  rw [tfact, map_prod, map_prod, qfactorial, ← prod_qpow, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun j _ => qint_eq j

/-- (2.52): `Σ_{σ ∈ S_a} q^{2ℓ(σ)} = q^{a(a-1)/2}[a]!`. -/
theorem qfactorial_eq (n : ℕ) :
    qfactorial (n+2) = qpow (-(((n+2).choose 2 : ℕ) : ℤ)) * ofPS (tsq (lengthSeries n)) := by
  rw [qfactorial_eq_tfact, lengthSeries_eq, tfact]

/-- EKL Proposition 2.2, (2.20)/(2.28): `qrk(OΛ_a) = q^{-a(a-1)/2} / ([a]! (1-q²)^a)`,
stated multiplicatively in Laurent series, for every `a = n+2 ≥ 2`. -/
theorem qrk_symmetric (n : ℕ) :
    ofPS (qrkSym n) * qfactorial (n+2) * (1 - qpow 2) ^ (n+2) =
      qpow (-(((n+2).choose 2 : ℕ) : ℤ)) := by
  have h := congrArg (fun f => ofPS (tsq f)) (symRank_mul_length n)
  simp only [map_mul, map_pow, map_sub, map_one, tsq_X] at h
  have hq : ofPS X ^ 2 = qpow 2 := by rw [← map_pow, ofPS_X_pow]; rfl
  rw [hq] at h
  rw [qfactorial_eq, qrkSym]
  calc _ = qpow (-(((n+2).choose 2 : ℕ) : ℤ)) *
        (ofPS (tsq (symRank n)) * ofPS (tsq (lengthSeries n)) * (1 - qpow 2) ^ (n+2)) := by ring
    _ = _ := by rw [h, mul_one]

/-! ### (2.67): the `q`-cardinality of `P(a,b)` -/

theorem gauss_tfact (a b : ℕ) : gauss a b * tfact a * tfact b = tfact (a + b) := by
  have h := gauss_mul_qPoch a b
  rw [← tfact_mul, ← tfact_mul, ← tfact_mul] at h
  have hne : ((1 - X : ℤ⟦X⟧) ^ (a + b)) ≠ 0 := by
    apply pow_ne_zero
    intro h0
    have := congrArg (constantCoeff ℤ) h0
    simp at this
  apply mul_right_cancel₀ hne
  rw [← h, pow_add]
  ring

/-- (2.67): `|P(a,b)|_q = Σ_{α ∈ P(a,b)} q^{2|α|-ab}` is the balanced binomial
`[a+b]!/([a]![b]!)`, stated multiplicatively. (`|P(a,b)| = C(a+b,a)` is
`BoxPartitionCount.card_box`.) -/
theorem box_qcard (a b : ℕ) :
    (∑ α ∈ box a b, qpow (2 * ((∑ i, α i : ℕ) : ℤ) - a * b)) * qfactorial a * qfactorial b =
      qfactorial (a + b) := by
  have hg : ∑ α ∈ box a b, qpow (2 * ((∑ i, α i : ℕ) : ℤ) - a * b) =
      qpow (-(a * b : ℤ)) * ofPS (tsq (gauss a b)) := by
    rw [gauss, map_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [map_pow, tsq_X, ← pow_mul, ofPS_X_pow, ← qpow_add]
    congr 1; push_cast; ring
  rw [hg, qfactorial_eq_tfact, qfactorial_eq_tfact, qfactorial_eq_tfact, ← gauss_tfact,
    map_mul, map_mul, map_mul, map_mul]
  have hc : ((a + b).choose 2 : ℤ) = (a.choose 2 : ℤ) + (b.choose 2 : ℤ) + a * b := by
    rw [Nat.choose_two_right, Nat.choose_two_right, Nat.choose_two_right]
    have h1 := Nat.div_mul_cancel (Nat.even_mul_pred_self a).two_dvd
    have h2 := Nat.div_mul_cancel (Nat.even_mul_pred_self b).two_dvd
    have h3 := Nat.div_mul_cancel (Nat.even_mul_pred_self (a + b)).two_dvd
    have : (a + b) * (a + b - 1) = a * (a - 1) + b * (b - 1) + 2 * (a * b) := by
      cases a <;> cases b <;> simp [Nat.succ_sub_one]
      ring
    omega
  have hq : qpow (-((a + b).choose 2 : ℕ) : ℤ) =
      qpow (-(a * b : ℤ)) * qpow (-((a.choose 2 : ℕ) : ℤ)) * qpow (-((b.choose 2 : ℕ) : ℤ)) := by
    rw [← qpow_add, ← qpow_add]; congr 1; rw [hc]; ring
  rw [hq]
  ring

end
end OddMath.Frontier.EKLSectionTwo
