import OddMath.Frontier.LongestDivided
import OddMath.Frontier.VariableEmbedding

/-!
# Prefix and shift embeddings of odd divided differences

EKL arXiv:1111.1320v1 §2.1.1 (2.1)–(2.5), (2.36); used in §4.3.1.

The rank-`n+2` skew-polynomial ring embeds into rank `n+3` in two order-preserving
ways: onto the first `n+2` variables (`prefixHom`), or onto the last `n+2`
variables (`shiftHom`).  In both cases the embedding is the zero extension of
`VariableEmbedding.embed`, hence a ring hom with no sign correction.

* Prefix: the extra variable `x_{n+2}` is a right spectator.  A monomial with last
  exponent `e` is the embedded prefix monomial times `x_{n+2}^e` with sign `+1`,
  and the operators `∂_i` for `i ≤ n` commute with the embedding past that spectator.
  Consequently the literal `D_{n+2}` word acting on the first `n+2` variables of
  rank `n+3` is the transported rank-`n+2` operator `D (n+2)`.
* Shift: the extra variable `x_0` is a left spectator.  Each `∂_{i+1}` passes
  `x_0^e` with sign `(-1)^e`, so the shifted `D_{n+2}` word collects
  `(-1)^{e·C(n+2,2)}`.

All operators are the inherited quotient/PBW operators `AllRankDivided.divided`.
-/

namespace OddMath.Frontier.PrefixEmbedding

open OddMath.SkewPolynomial (SkewPolynomial generator monomial expSingle)
open AllRankDivided LongestDivided

/-! ## Generator induction -/

/-- Every skew polynomial is reached from integer constants and generators by sums
and products (transported from the free algebra through the PBW surjection). -/
theorem induction_generators {N : ℕ} {P : SkewPolynomial N → Prop}
    (hconst : ∀ r : ℤ, P (r • 1)) (hgen : ∀ j, P (generator j))
    (hadd : ∀ f g, P f → P g → P (f + g)) (hmul : ∀ f g, P f → P g → P (f * g))
    (f : SkewPolynomial N) : P f := by
  obtain ⟨x, rfl⟩ := PbwRealization.Phi_surjective N f
  induction x using Quotient.inductionOn' with
  | h w =>
      change P (PbwL3.evalAlg N w)
      induction w using FreeAlgebra.induction with
      | grade0 r =>
          rw [AlgHom.commutes]
          exact hconst r
      | grade1 j => rw [PbwL3.evalAlg_ι]; exact hgen j
      | add a b ha hb => rw [map_add]; exact hadd _ _ ha hb
      | mul a b ha hb => rw [map_mul]; exact hmul _ _ ha hb

/-! ## The prefix embedding -/

/-- Zero extension onto the first `N` variables of rank `N+1`. -/
noncomputable def prefixHom (N : ℕ) : SkewPolynomial N →+* SkewPolynomial (N+1) where
  toFun := VariableEmbedding.embed Fin.castSuccOrderEmb
  map_zero' := VariableEmbedding.embed_zero _
  map_one' := VariableEmbedding.embed_one _
  map_add' := VariableEmbedding.embed_add _
  map_mul' := VariableEmbedding.embed_mul _

theorem expEmbed_castSucc {N : ℕ} (γ : Fin N → ℕ) :
    VariableEmbedding.expEmbed Fin.castSuccOrderEmb γ = Fin.snoc γ 0 := by
  funext j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · rw [VariableEmbedding.expEmbed_not_mem_range, Fin.snoc_last]
    rintro ⟨k, hk⟩
    exact Fin.castSucc_ne_last k hk
  · change VariableEmbedding.expEmbed Fin.castSuccOrderEmb γ (Fin.castSuccOrderEmb j) = _
    rw [VariableEmbedding.expEmbed_apply]
    simp

@[simp] theorem prefixHom_monomial {N : ℕ} (γ : Fin N → ℕ) (c : ℤ) :
    prefixHom N (monomial γ c) = monomial (Fin.snoc γ 0) c := by
  change VariableEmbedding.embed Fin.castSuccOrderEmb (monomial γ c) = _
  rw [VariableEmbedding.embed_monomial, expEmbed_castSucc]

theorem snoc_expSingle {N : ℕ} (j : Fin N) :
    (Fin.snoc (expSingle j) 0 : Fin (N+1) → ℕ) = expSingle j.castSucc := by
  funext k
  refine Fin.lastCases ?_ (fun k => ?_) k
  · simp [expSingle, (Fin.castSucc_ne_last j)]
  · simp [expSingle, Fin.castSucc_inj]

@[simp] theorem prefixHom_generator {N : ℕ} (j : Fin N) :
    prefixHom N (generator j) = generator j.castSucc := by
  change prefixHom N (monomial (expSingle j) 1) = monomial _ 1
  rw [prefixHom_monomial, snoc_expSingle]

/-- Integer constants are fixed by the prefix embedding. -/
@[simp] theorem prefixHom_const {N : ℕ} (r : ℤ) :
    prefixHom N (r • 1) = r • 1 := by
  rw [map_zsmul, map_one]

/-- The last variable stands to the right of every prefix variable: no crossing. -/
theorem crossingCount_snoc_last {N : ℕ} (γ : Fin N → ℕ) (e : ℕ) :
    OddMath.crossingCount (Fin.snoc γ 0 : Fin (N+1) → ℕ) (e • expSingle (Fin.last N)) = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j hj
  have hji : j < i := (Finset.mem_filter.mp hj).2
  have hj' : Fin.last N ≠ j := fun h => by
    subst h
    exact absurd (Fin.le_last i) (not_le.mpr hji)
  simp [expSingle, hj']

/-- A monomial with last exponent `e` factors as the embedded prefix monomial times
`x_N^e`, with sign `+1` since the last variable is on the right. -/
theorem monomial_snoc {N : ℕ} (γ : Fin N → ℕ) (e : ℕ) (c : ℤ) :
    monomial (Fin.snoc γ e) c = prefixHom N (monomial γ c) * generator (Fin.last N) ^ e := by
  rw [prefixHom_monomial, PbwL4.pow_form]
  change _ = OddMath.SkewPolynomial.mul _ _
  rw [OddMath.SkewPolynomial.mul_monomial, OddMath.skewSign, crossingCount_snoc_last,
    pow_zero, mul_one, mul_one]
  congr 1
  funext k
  refine Fin.lastCases ?_ (fun k => ?_) k
  · simp [expSingle]
  · simp [expSingle, (Fin.castSucc_ne_last k).symm]

/-! ## Compatibility with the adjacent operators -/

/-- The swap of adjacent prefix positions commutes with `castSucc`. -/
theorem swap_castSucc {n : ℕ} (i : Fin (n+1)) (j : Fin (n+2)) :
    Equiv.swap i.castSucc.castSucc i.castSucc.succ j.castSucc =
      (Equiv.swap i.castSucc i.succ j).castSucc := by
  rw [Fin.succ_castSucc]
  exact (Fin.castSucc_injective _).swap_apply _ _ _

/-- `∂_i` and `s_i` of rank `n+2` transported along the prefix embedding. -/
theorem prefix_divided_and_s {n : ℕ} (i : Fin (n+1)) (f : SkewPolynomial (n+2)) :
    divided i.castSucc (prefixHom (n+2) f) = prefixHom (n+2) (divided i f) ∧
      s i.castSucc (prefixHom (n+2) f) = prefixHom (n+2) (s i f) := by
  induction f using induction_generators with
  | hconst r =>
      simp only [prefixHom_const, map_zsmul, divided_one, smul_zero, map_one, map_zero, and_self]
  | hgen j =>
      rw [prefixHom_generator, divided_generator, divided_generator, s_generator,
        s_generator, map_neg, prefixHom_generator, swap_castSucc]
      refine ⟨?_, rfl⟩
      rw [Fin.succ_castSucc]
      simp only [Fin.castSucc_inj]
      split <;> simp
  | hadd f g hf hg =>
      simp only [map_add, hf.1, hf.2, hg.1, hg.2, and_self]
  | hmul f g hf hg =>
      simp only [map_mul, divided_mul, hf.1, hf.2, hg.1, hg.2, map_add, and_self]

theorem divided_prefixHom {n : ℕ} (i : Fin (n+1)) (f : SkewPolynomial (n+2)) :
    divided i.castSucc (prefixHom (n+2) f) = prefixHom (n+2) (divided i f) :=
  (prefix_divided_and_s i f).1

theorem s_prefixHom {n : ℕ} (i : Fin (n+1)) (f : SkewPolynomial (n+2)) :
    s i.castSucc (prefixHom (n+2) f) = prefixHom (n+2) (s i f) :=
  (prefix_divided_and_s i f).2

/-- Powers of the last variable are killed by every prefix operator. -/
theorem divided_last_pow {n : ℕ} (i : Fin (n+1)) (e : ℕ) :
    divided i.castSucc (generator (Fin.last (n+2)) ^ e) = 0 := by
  induction e with
  | zero => rw [pow_zero, divided_one]
  | succ e ih =>
      rw [pow_succ, divided_mul_spectator, ih, zero_mul]
      · exact (Fin.castSucc_ne_last _).symm
      · rw [Fin.succ_castSucc]
        exact (Fin.castSucc_ne_last _).symm

/-- EKL (2.4) with a right spectator: for `i ≤ n`, `∂_i` of rank `n+3` acts on
`ι(f) · x_{n+2}^e` through the rank-`n+2` operator `∂_i` on `f`. -/
theorem divided_prefix (n : ℕ) (i : Fin (n+1)) (f : SkewPolynomial (n+2)) (e : ℕ) :
    divided (i.castSucc : Fin (n+2)) (prefixHom (n+2) f * generator (Fin.last (n+2)) ^ e) =
      prefixHom (n+2) (divided i f) * generator (Fin.last (n+2)) ^ e := by
  rw [divided_mul, divided_last_pow, mul_zero, add_zero, divided_prefixHom]

/-- Any word in the prefix letters, transported along `castSucc`. -/
theorem applyWord_map_castSucc {n : ℕ} (w : List (Fin (n+1))) (f : SkewPolynomial (n+2))
    (e : ℕ) :
    applyWord (w.map Fin.castSucc) (prefixHom (n+2) f * generator (Fin.last (n+2)) ^ e) =
      prefixHom (n+2) (applyWord w f) * generator (Fin.last (n+2)) ^ e := by
  induction w with
  | nil => rfl
  | cons i w ih =>
      rw [List.map_cons, applyWord_cons, ih, divided_prefix]
      rfl

/-- The literal `D_{n+2}` word in rank `n+3` is the `castSucc` image of the one in
rank `n+2`. -/
theorem wordIn_succ_eq_map (n : ℕ) :
    wordIn (n+1) (n+2) (by omega) = (wordIn n (n+2) le_rfl).map Fin.castSucc := by
  apply List.map_injective_iff.mpr Fin.val_injective
  rw [wordIn_values, List.map_map]
  exact (wordIn_values n (n+2) le_rfl).symm

/-- The `D_{n+2}` word on the first `n+2` variables of rank `n+3`, with the last
variable as a right spectator, is the embedded rank-`n+2` operator `D (n+2)`. -/
theorem applyWord_prefix (n : ℕ) (f : SkewPolynomial (n+2)) (e : ℕ) :
    applyWord (wordIn (n+1) (n+2) (by omega))
        (prefixHom (n+2) f * generator (Fin.last (n+2)) ^ e) =
      prefixHom (n+2) (D (n+2) f) * generator (Fin.last (n+2)) ^ e := by
  rw [wordIn_succ_eq_map, applyWord_map_castSucc]
  rfl

/-- Monomial form of `applyWord_prefix`. -/
theorem D_prefix_monomial (n : ℕ) (γ : Fin (n+2) → ℕ) (e : ℕ) (c : ℤ) :
    applyWord (wordIn (n+1) (n+2) (by omega)) (monomial (Fin.snoc γ e) c) =
      prefixHom (n+2) (D (n+2) (monomial γ c)) * generator (Fin.last (n+2)) ^ e := by
  rw [monomial_snoc, applyWord_prefix]

/-! ## The shift embedding -/

/-- Zero extension onto the last `N` variables of rank `N+1`. -/
noncomputable def shiftHom (N : ℕ) : SkewPolynomial N →+* SkewPolynomial (N+1) where
  toFun := VariableEmbedding.embed (Fin.succOrderEmb N)
  map_zero' := VariableEmbedding.embed_zero _
  map_one' := VariableEmbedding.embed_one _
  map_add' := VariableEmbedding.embed_add _
  map_mul' := VariableEmbedding.embed_mul _

theorem expEmbed_succ {N : ℕ} (γ : Fin N → ℕ) :
    VariableEmbedding.expEmbed (Fin.succOrderEmb N) γ = Fin.cons 0 γ := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · rw [VariableEmbedding.expEmbed_not_mem_range, Fin.cons_zero]
    rintro ⟨k, hk⟩
    exact Fin.succ_ne_zero k hk
  · change VariableEmbedding.expEmbed (Fin.succOrderEmb N) γ (Fin.succOrderEmb N j) = _
    rw [VariableEmbedding.expEmbed_apply]
    simp

@[simp] theorem shiftHom_monomial {N : ℕ} (γ : Fin N → ℕ) (c : ℤ) :
    shiftHom N (monomial γ c) = monomial (Fin.cons 0 γ) c := by
  change VariableEmbedding.embed (Fin.succOrderEmb N) (monomial γ c) = _
  rw [VariableEmbedding.embed_monomial, expEmbed_succ]

theorem cons_expSingle {N : ℕ} (j : Fin N) :
    (Fin.cons 0 (expSingle j) : Fin (N+1) → ℕ) = expSingle j.succ := by
  funext k
  refine Fin.cases ?_ (fun k => ?_) k
  · simp [expSingle, Fin.succ_ne_zero j]
  · simp [expSingle, Fin.succ_inj]

@[simp] theorem shiftHom_generator {N : ℕ} (j : Fin N) :
    shiftHom N (generator j) = generator j.succ := by
  change shiftHom N (monomial (expSingle j) 1) = monomial _ 1
  rw [shiftHom_monomial, cons_expSingle]

/-- Integer constants are fixed by the shift embedding. -/
@[simp] theorem shiftHom_const {N : ℕ} (r : ℤ) :
    shiftHom N (r • 1) = r • 1 := by
  rw [map_zsmul, map_one]

/-- The first variable stands to the left of every shifted variable: no crossing. -/
theorem crossingCount_first_cons {N : ℕ} (γ : Fin N → ℕ) (e : ℕ) :
    OddMath.crossingCount (e • expSingle (0 : Fin (N+1))) (Fin.cons 0 γ : Fin (N+1) → ℕ) = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j hj
  have hji : j < i := (Finset.mem_filter.mp hj).2
  have hi : (0 : Fin (N+1)) ≠ i := fun h => by
    subst h
    exact absurd (Fin.zero_le j) (not_le.mpr hji)
  simp [expSingle, hi]

/-- A monomial with first exponent `e` factors as `x_0^e` times the shifted monomial,
with sign `+1` since the first variable is on the left. -/
theorem monomial_cons {N : ℕ} (γ : Fin N → ℕ) (e : ℕ) (c : ℤ) :
    monomial (Fin.cons e γ) c = generator (0 : Fin (N+1)) ^ e * shiftHom N (monomial γ c) := by
  rw [shiftHom_monomial, PbwL4.pow_form]
  change _ = OddMath.SkewPolynomial.mul _ _
  rw [OddMath.SkewPolynomial.mul_monomial, OddMath.skewSign, crossingCount_first_cons,
    pow_zero, mul_one, one_mul]
  congr 1
  funext k
  refine Fin.cases ?_ (fun k => ?_) k
  · simp [expSingle]
  · simp [expSingle, (Fin.succ_ne_zero k).symm]

/-- The swap of adjacent shifted positions commutes with `succ`. -/
theorem swap_succ {n : ℕ} (i : Fin (n+1)) (j : Fin (n+2)) :
    Equiv.swap i.succ.castSucc i.succ.succ j.succ = (Equiv.swap i.castSucc i.succ j).succ := by
  rw [← Fin.succ_castSucc]
  exact (Fin.succ_injective _).swap_apply _ _ _

/-- `∂_i` and `s_i` of rank `n+2` transported along the shift embedding. -/
theorem shift_divided_and_s {n : ℕ} (i : Fin (n+1)) (f : SkewPolynomial (n+2)) :
    divided i.succ (shiftHom (n+2) f) = shiftHom (n+2) (divided i f) ∧
      s i.succ (shiftHom (n+2) f) = shiftHom (n+2) (s i f) := by
  induction f using induction_generators with
  | hconst r =>
      simp only [shiftHom_const, map_zsmul, divided_one, smul_zero, map_one, map_zero, and_self]
  | hgen j =>
      rw [shiftHom_generator, divided_generator, divided_generator, s_generator,
        s_generator, map_neg, shiftHom_generator, swap_succ]
      refine ⟨?_, rfl⟩
      rw [← Fin.succ_castSucc]
      simp only [Fin.succ_inj]
      split <;> simp
  | hadd f g hf hg =>
      simp only [map_add, hf.1, hf.2, hg.1, hg.2, and_self]
  | hmul f g hf hg =>
      simp only [map_mul, divided_mul, hf.1, hf.2, hg.1, hg.2, map_add, and_self]

theorem divided_shiftHom {n : ℕ} (i : Fin (n+1)) (f : SkewPolynomial (n+2)) :
    divided i.succ (shiftHom (n+2) f) = shiftHom (n+2) (divided i f) :=
  (shift_divided_and_s i f).1

theorem s_shiftHom {n : ℕ} (i : Fin (n+1)) (f : SkewPolynomial (n+2)) :
    s i.succ (shiftHom (n+2) f) = shiftHom (n+2) (s i f) :=
  (shift_divided_and_s i f).2

theorem first_ne_castSucc_succ {n : ℕ} (i : Fin (n+1)) :
    (0 : Fin (n+3)) ≠ i.succ.castSucc := by
  rw [← Fin.succ_castSucc]
  exact (Fin.succ_ne_zero _).symm

/-- Powers of the first variable are killed by every shifted operator. -/
theorem divided_first_pow {n : ℕ} (i : Fin (n+1)) (e : ℕ) :
    divided i.succ (generator (0 : Fin (n+3)) ^ e) = 0 := by
  induction e with
  | zero => rw [pow_zero, divided_one]
  | succ e ih =>
      rw [pow_succ, divided_mul_spectator _ _ (first_ne_castSucc_succ i)
        (Fin.succ_ne_zero _).symm, ih, zero_mul]

/-- Each shifted reflection negates the first variable. -/
theorem s_first_pow {n : ℕ} (i : Fin (n+1)) (e : ℕ) :
    s i.succ (generator (0 : Fin (n+3)) ^ e) = (-1 : ℤ)^e • generator (0 : Fin (n+3)) ^ e := by
  rw [map_pow, s_generator, Equiv.swap_apply_of_ne_of_ne (first_ne_castSucc_succ i)
    (Fin.succ_ne_zero _).symm, neg_pow, zsmul_eq_mul]
  push_cast
  rfl

/-- EKL (2.4) with a left spectator: `∂_{i+1}` of rank `n+3` acts on
`x_0^e · σ(f)` through `∂_i` on `f`, with sign `(-1)^e`. -/
theorem divided_shift (n : ℕ) (i : Fin (n+1)) (f : SkewPolynomial (n+2)) (e : ℕ) :
    divided i.succ (generator (0 : Fin (n+3)) ^ e * shiftHom (n+2) f) =
      (-1 : ℤ)^e • (generator (0 : Fin (n+3)) ^ e * shiftHom (n+2) (divided i f)) := by
  rw [divided_mul, divided_first_pow, zero_mul, zero_add, s_first_pow, divided_shiftHom,
    smul_mul_assoc]

/-- Any word in the shifted letters: each letter passes `x_0^e` with sign `(-1)^e`. -/
theorem applyWord_map_succ {n : ℕ} (w : List (Fin (n+1))) (f : SkewPolynomial (n+2))
    (e : ℕ) :
    applyWord (w.map Fin.succ) (generator (0 : Fin (n+3)) ^ e * shiftHom (n+2) f) =
      (-1 : ℤ)^(e * w.length) •
        (generator (0 : Fin (n+3)) ^ e * shiftHom (n+2) (applyWord w f)) := by
  induction w with
  | nil => simp
  | cons i w ih =>
      rw [List.map_cons, applyWord_cons, ih, map_smul, divided_shift, smul_smul,
        ← pow_add, List.length_cons, Nat.mul_succ]
      rfl

theorem coxeterWord_length (k : ℕ) : (coxeterWord k).length = k.choose 2 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [coxeterWord, List.length_append, ih, List.length_reverse, List.length_range,
        Nat.choose_succ_succ, Nat.choose_one_right, add_comm]

theorem wordIn_length (n k : ℕ) (h : k ≤ n+2) : (wordIn n k h).length = k.choose 2 := by
  rw [← coxeterWord_length, ← wordIn_values n k h, List.length_map]

/-- The shifted `D_{n+2}` word on the last `n+2` variables of rank `n+3`, with the
first variable as a left spectator, is the embedded `D (n+2)` up to the sign
`(-1)^{e·C(n+2,2)}`. -/
theorem applyWord_shift (n : ℕ) (f : SkewPolynomial (n+2)) (e : ℕ) :
    applyWord ((wordIn n (n+2) le_rfl).map Fin.succ)
        (generator (0 : Fin (n+3)) ^ e * shiftHom (n+2) f) =
      (-1 : ℤ)^(e * (n+2).choose 2) •
        (generator (0 : Fin (n+3)) ^ e * shiftHom (n+2) (D (n+2) f)) := by
  rw [applyWord_map_succ, wordIn_length]
  rfl

/-- Monomial form of `applyWord_shift`. -/
theorem D_shift_monomial (n : ℕ) (γ : Fin (n+2) → ℕ) (e : ℕ) (c : ℤ) :
    applyWord ((wordIn n (n+2) le_rfl).map Fin.succ) (monomial (Fin.cons e γ) c) =
      (-1 : ℤ)^(e * (n+2).choose 2) •
        (generator (0 : Fin (n+3)) ^ e * shiftHom (n+2) (D (n+2) (monomial γ c))) := by
  rw [monomial_cons, applyWord_shift]

end OddMath.Frontier.PrefixEmbedding
