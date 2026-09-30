import OddMath.Frontier.EQPdgLima

/-!
# `p`-Lima partitions and trivial bead configurations

Source: A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2,
Appendix A.4.2.

A partition is *`p`-Lima* if it is built out of `p × p` squares, i.e. it is obtained from a
partition `ν` by replacing every box by a `p × p` square: `λ_r = p ν_{⌊r/p⌋}` for all rows
`r ≥ 0` (`IsPLima`; a partition with at most `n` parts is stored as `λ : Fin n → ℕ` and padded
with zeros, `lamExt`).

For `λ` with at most `n` parts let `α = λ + δ` (`α_i = λ_{n-1-i} + i`, `lamDelta`). This file
proves `trivial_iff_isPLima`: every full block `[n mod p + mp, n mod p + (m+1)p)` contains a
number of entries of `α` divisible by `p` iff `λ` is `p`-Lima. Both are equivalent to the
explicit shape `Shape`: `α_i = i` for `i < n mod p` and `α_i = p μ_g + i` on the `g`-th group
`n mod p + gp ≤ i < n mod p + (g+1)p`.
-/

namespace OddMath.Frontier.EQPdg

open Finset

noncomputable section

variable {n : ℕ}

/-- `λ` padded with zeros: row `r` of the partition. -/
def lamExt (lam : Fin n → ℕ) (r : ℕ) : ℕ := if h : r < n then lam ⟨r, h⟩ else 0

/-- `λ` is `p`-Lima: built out of `p × p` squares, `λ_r = p ν_{⌊r/p⌋}` for all `r`. -/
def IsPLima (p : ℕ) (lam : Fin n → ℕ) : Prop := ∃ ν : ℕ → ℕ, ∀ r, lamExt lam r = p * ν (r / p)

/-- The explicit shape of a trivial bead configuration. -/
def Shape (p : ℕ) (α : Fin n → ℕ) : Prop :=
  ∃ μ : ℕ → ℕ, ∀ i : Fin n, α i = if (i : ℕ) < n % p then (i : ℕ) else p * μ ((i - n % p) / p) + i

/-! ## Arithmetic helpers -/

theorem div_helper {p N q s : ℕ} (hp : 0 < p) (hs : s < p) (hq : q < N) :
    (p * N - 1 - (p * q + s)) / p = N - 1 - q := by
  have h1 : p * N - 1 - (p * q + s) = (p - 1 - s) + p * (N - 1 - q) := by
    have : p * N = p * (N - 1 - q) + p * q + p := by
      rw [← Nat.mul_add, ← Nat.mul_succ]; congr 1; omega
    rw [this]; omega
  rw [h1, Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt (by omega), zero_add]

theorem div_eq_of_bounds {x p q : ℕ} (h1 : p * q ≤ x) (h2 : x < p * q + p) : x / p = q :=
  Nat.div_eq_of_lt_le (by rw [mul_comm]; exact h1) (by rw [Nat.succ_mul, mul_comm]; exact h2)

theorem lamExt_lt (lam : Fin n → ℕ) {r : ℕ} (h : r < n) : lamExt lam r = lam ⟨r, h⟩ := by
  simp [lamExt, h]

theorem lamExt_ge (lam : Fin n → ℕ) {r : ℕ} (h : ¬ r < n) : lamExt lam r = 0 := by
  simp [lamExt, h]

theorem n_eq (n p : ℕ) : n = p * (n / p) + n % p := (Nat.div_add_mod n p).symm

/-! ## `p`-Lima ↔ shape -/

theorem isPLima_iff_shape (p : ℕ) (hp : 0 < p) (lam : Fin n → ℕ) :
    IsPLima p lam ↔ Shape p (lamDelta lam) := by
  have hn := n_eq n p
  have hρ : n % p < p := Nat.mod_lt _ hp
  set N := n / p
  set ρ := n % p
  constructor
  · rintro ⟨ν, hν⟩
    have hνN : ν N = 0 := by
      have h := hν (p * N + p - 1)
      rw [lamExt_ge lam (by generalize p * N = M at *; omega)] at h
      have : (p * N + p - 1) / p = N :=
        div_eq_of_bounds (by generalize p * N = M at *; omega) (by generalize p * N = M at *; omega)
      rw [this] at h
      exact (Nat.mul_eq_zero.mp h.symm).resolve_left (by omega)
    refine ⟨fun g => ν (N - 1 - g), fun i => ?_⟩
    have hi := i.2
    have key := hν (n - 1 - i)
    rw [lamExt_lt lam (by omega)] at key
    simp only [lamDelta]
    rw [show lam i.rev = lam ⟨n - 1 - i, by omega⟩ from congrArg lam (Fin.ext (by simp; omega)),
      key]
    split_ifs with h
    · have : (n - 1 - i) / p = N :=
        div_eq_of_bounds (by generalize p * N = M at *; omega) (by generalize p * N = M at *; omega)
      rw [this, hνN]; simp
    · obtain ⟨g, s, hs, hgs⟩ : ∃ g s, s < p ∧ (i : ℕ) - ρ = p * g + s :=
        ⟨((i : ℕ) - ρ) / p, ((i : ℕ) - ρ) % p, Nat.mod_lt _ hp, (Nat.div_add_mod _ _).symm⟩
      have hgN : g < N := by
        by_contra hg
        have : p * N ≤ p * g := Nat.mul_le_mul_left _ (by omega)
        omega
      have e1 : n - 1 - (i : ℕ) = p * N - 1 - (p * g + s) := by omega
      have e2 : ((i : ℕ) - ρ) / p = g := by
        rw [hgs, Nat.mul_add_div hp, Nat.div_eq_of_lt hs, add_zero]
      rw [e1, div_helper hp hs hgN, e2]
  · rintro ⟨μ, hμ⟩
    refine ⟨fun q => if q < N then μ (N - 1 - q) else 0, fun r => ?_⟩
    by_cases hr : r < n
    · rw [lamExt_lt lam hr]
      have h := hμ ⟨n - 1 - r, by omega⟩
      simp only [lamDelta] at h
      rw [show (⟨n - 1 - r, _⟩ : Fin n).rev = ⟨r, hr⟩ from Fin.ext (by simp; omega)] at h
      split_ifs at h with h1
      · have hrN : r / p = N :=
          div_eq_of_bounds (by generalize p * N = M at *; omega)
            (by generalize p * N = M at *; omega)
        simp only [hrN, lt_irrefl, ↓reduceIte, mul_zero]
        omega
      · obtain ⟨q, s, hs, hqs⟩ : ∃ q s, s < p ∧ r = p * q + s :=
          ⟨r / p, r % p, Nat.mod_lt _ hp, (Nat.div_add_mod _ _).symm⟩
        have hq : r / p = q := by
          rw [hqs, Nat.mul_add_div hp, Nat.div_eq_of_lt hs, add_zero]
        have hqN : q < N := by
          by_contra hq'
          have : p * N ≤ p * q := Nat.mul_le_mul_left _ (by omega)
          omega
        simp only [hq, hqN, ↓reduceIte]
        have e1 : n - 1 - r - ρ = p * N - 1 - (p * q + s) := by omega
        rw [e1, div_helper hp hs hqN] at h
        omega
    · rw [lamExt_ge lam hr]
      have : ¬ r / p < N := by
        intro h
        have : r / p + 1 ≤ N := h
        have := Nat.lt_mul_div_succ r hp
        have : p * (r / p + 1) ≤ p * N := Nat.mul_le_mul_left _ ‹_›
        omega
      simp [this]

/-! ## Trivial bead configurations ↔ shape -/

section Beads

variable (p : ℕ)

theorem strictMono_gap {α : Fin n → ℕ} (hα : StrictMono α) {i j : ℕ} (hi : i < n) (hj : j < n)
    (hij : i ≤ j) : α ⟨i, hi⟩ + (j - i) ≤ α ⟨j, hj⟩ := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
  induction d with
  | zero => simp
  | succ d ih =>
    have h1 := ih (by omega) (by omega)
    have h2 : α ⟨i + d, by omega⟩ < α ⟨i + (d + 1), hj⟩ := hα (by simp [Fin.lt_def])
    omega

theorem le_strictMono {α : Fin n → ℕ} (hα : StrictMono α) (i : Fin n) : (i : ℕ) ≤ α i := by
  have := strictMono_gap hα (i := 0) (j := i) (Nat.lt_of_le_of_lt (Nat.zero_le _) i.2) i.2
    (Nat.zero_le _)
  simp at this; exact le_trans (by omega) this

/-- Shape implies trivial. -/
theorem trivial_of_shape (hp : 0 < p) {α : Fin n → ℕ} (hsh : Shape p α) :
    ¬ NTv p (cv p α) := by
  obtain ⟨μ, hμ⟩ := hsh
  have hn := n_eq n p
  set N := n / p
  set ρ := n % p
  rintro ⟨m, hm⟩
  apply hm
  have hmem : ∀ i : Fin n, α i ∈ Ico (bot n p m) (bot n p m + p) ↔
      ρ ≤ (i : ℕ) ∧ μ (((i : ℕ) - ρ) / p) + ((i : ℕ) - ρ) / p = m := by
    intro i
    rw [mem_block_iff hp, hμ i]
    split_ifs with h
    · constructor
      · rintro ⟨h1, _⟩; omega
      · rintro ⟨h1, _⟩; omega
    · have e : p * μ (((i : ℕ) - ρ) / p) + (i : ℕ) - ρ = ((i : ℕ) - ρ) + p * μ (((i : ℕ) - ρ) / p) := by
        omega
      rw [e, Nat.add_mul_div_left _ _ hp]
      constructor
      · rintro ⟨_, h2⟩; exact ⟨by omega, by omega⟩
      · rintro ⟨h1, h2⟩; exact ⟨by omega, by omega⟩
  unfold cv cnt
  rw [Finset.card_eq_sum_card_fiberwise (f := fun i : Fin n => ((i : ℕ) - ρ) / p) (t := range N)]
  · refine Finset.dvd_sum fun g hg => ?_
    rw [Finset.mem_range] at hg
    by_cases hgm : μ g + g = m
    · have hG : ((univ.filter (fun i : Fin n => α i ∈ Ico (bot n p m) (bot n p m + p))).filter
          (fun i : Fin n => ((i : ℕ) - ρ) / p = g)).card = p := by
        calc _ = (Ico (ρ + p * g) (ρ + p * g + p)).card := by
              refine Finset.card_bij (fun i _ => (i : ℕ)) ?_ ?_ ?_
              · intro i hi
                simp only [Finset.mem_filter, Finset.mem_univ, true_and, hmem] at hi
                obtain ⟨⟨h1, _⟩, h3⟩ := hi
                subst h3
                rw [Finset.mem_Ico]
                have := Nat.div_add_mod ((i : ℕ) - ρ) p
                have := Nat.mod_lt ((i : ℕ) - ρ) hp
                constructor <;> (generalize p * (((i : ℕ) - ρ) / p) = M at *; omega)
              · intro a _ b _ h
                exact Fin.ext h
              · intro x hx
                rw [Finset.mem_Ico] at hx
                have hxn : x < n := by
                  have : p * (g + 1) ≤ p * N := Nat.mul_le_mul_left _ hg
                  rw [Nat.mul_succ] at this
                  omega
                have e : (x - ρ) / p = g :=
                  div_eq_of_bounds (by generalize p * g = M at *; omega)
                    (by generalize p * g = M at *; omega)
                refine ⟨⟨x, hxn⟩, ?_, rfl⟩
                simp only [Finset.mem_filter, Finset.mem_univ, true_and, hmem]
                exact ⟨⟨by omega, by rw [e, hgm]⟩, e⟩
          _ = p := by rw [Nat.card_Ico]; omega
      rw [hG]
    · have : (univ.filter (fun i : Fin n => α i ∈ Ico (bot n p m) (bot n p m + p))).filter
          (fun i : Fin n => ((i : ℕ) - ρ) / p = g) = ∅ := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, hmem, Finset.notMem_empty,
          iff_false, not_and]
        rintro ⟨_, h2⟩ h3
        rw [h3] at h2; exact hgm h2
      rw [this, Finset.card_empty]
      exact dvd_zero _
  · intro i hi
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq, hmem] at hi
    simp only [Finset.coe_range, Set.mem_Iio]
    have hi2 := i.2
    by_contra hge
    have : p * N ≤ p * (((i : ℕ) - ρ) / p) := Nat.mul_le_mul_left _ (by omega)
    have := Nat.div_mul_le_self ((i : ℕ) - ρ) p
    rw [mul_comm] at this
    omega

end Beads

section Beads2

variable (p : ℕ)

theorem succ_mod_of_lt {x p : ℕ} (h : x % p + 1 < p) : (x + 1) % p = x % p + 1 := by
  have e : x + 1 = (x % p + 1) + p * (x / p) := by have := Nat.div_add_mod x p; omega
  rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h]

theorem succ_div_of_lt {x p : ℕ} (h : x % p + 1 < p) : (x + 1) / p = x / p := by
  have := Nat.div_add_mod x p
  exact div_eq_of_bounds (by generalize p * (x / p) = M at *; omega)
    (by generalize p * (x / p) = M at *; omega)

theorem succ_mod_of_eq {x p : ℕ} (hp : 0 < p) (h : x % p = p - 1) : (x + 1) % p = 0 := by
  have e : x + 1 = p * (x / p + 1) := by
    have := Nat.div_add_mod x p
    rw [Nat.mul_succ]; omega
  rw [e, Nat.mul_mod_right]

/-- Full blocks: in a trivial configuration, a block containing an entry is completely
occupied. -/
theorem full_block (hp : 0 < p) {α : Fin n → ℕ} (hinj : Function.Injective α)
    (htriv : ¬ NTv p (cv p α)) (i : Fin n) (y : ℕ) (hi : n % p ≤ α i) (hy : n % p ≤ y)
    (hyi : (y - n % p) / p = (α i - n % p) / p) : ∃ j, α j = y := by
  set m := (α i - n % p) / p
  have hmi : α i ∈ Ico (bot n p m) (bot n p m + p) := (mem_block_iff hp m _).mpr ⟨hi, rfl⟩
  have hym : y ∈ Ico (bot n p m) (bot n p m + p) := (mem_block_iff hp m y).mpr ⟨hy, hyi⟩
  set S := univ.filter (fun j => α j ∈ Ico (bot n p m) (bot n p m + p))
  have hsub : S.image α ⊆ Ico (bot n p m) (bot n p m + p) := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    simpa [S] using hj
  have hcard : (S.image α).card = S.card := Finset.card_image_of_injective _ hinj
  have hle : S.card ≤ p := by
    have := Finset.card_le_card hsub
    rw [Nat.card_Ico, hcard] at this; omega
  have hpos : 0 < S.card := Finset.card_pos.mpr ⟨i, by simpa [S] using hmi⟩
  have hdvd : p ∣ S.card := by
    by_contra h; exact htriv ⟨m, h⟩
  have hSp : S.card = p := by
    obtain ⟨c, hc⟩ := hdvd
    rcases c with _ | _ | c
    · omega
    · simpa using hc
    · have : p * (c + 1 + 1) = p * c + 2 * p := by ring
      omega
  have heq : S.image α = Ico (bot n p m) (bot n p m + p) :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hcard, Nat.card_Ico, hSp]; omega)
  rw [← heq] at hym
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hym
  exact ⟨j, hj⟩

/-- The bottom region `[0, n mod p)` is fully occupied. -/
theorem card_below (hp : 0 < p) {α : Fin n → ℕ} (hinj : Function.Injective α)
    (htriv : ¬ NTv p (cv p α)) : (univ.filter (fun j => α j < n % p)).card = n % p := by
  have hdiv : ∀ m, p ∣ cnt p m α := fun m => by
    by_contra h; exact htriv ⟨m, h⟩
  have hr : n % p < p := Nat.mod_lt _ hp
  set L := univ.filter (fun j => α j < n % p)
  set G := univ.filter (fun j => ¬ α j < n % p)
  have hLG : L.card + G.card = n := by
    rw [Finset.card_filter_add_card_filter_not, Finset.card_univ, Fintype.card_fin]
  have hG : p ∣ G.card := by
    set M := univ.sup α + 1
    rw [Finset.card_eq_sum_card_fiberwise (f := fun j => (α j - n % p) / p) (t := range M)]
    · refine Finset.dvd_sum fun m _ => ?_
      convert hdiv m using 1
      unfold cnt
      congr 1
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, G, mem_block_iff hp, not_lt]
    · intro j _
      simp only [Finset.coe_range, Set.mem_Iio]
      have : α j ≤ univ.sup α := Finset.le_sup (Finset.mem_univ j)
      have : (α j - n % p) / p ≤ α j := le_trans (Nat.div_le_self _ _) (Nat.sub_le _ _)
      omega
  have hL : L.card ≤ n % p := by
    calc L.card = (L.image α).card := (Finset.card_image_of_injective _ hinj).symm
      _ ≤ (range (n % p)).card := by
          refine Finset.card_le_card fun x hx => ?_
          obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
          simpa [L] using hj
      _ = n % p := Finset.card_range _
  obtain ⟨g, hg⟩ := hG
  have hmod : L.card % p = n % p := by
    have h' : (L.card + G.card) % p = n % p := by rw [hLG]
    rwa [hg, Nat.add_mul_mod_self_left] at h'
  rw [Nat.mod_eq_of_lt (by omega)] at hmod
  exact hmod

/-- Trivial (and strictly increasing) implies shape. -/
theorem shape_of_trivial (hp : 0 < p) {α : Fin n → ℕ} (hα : StrictMono α)
    (htriv : ¬ NTv p (cv p α)) : Shape p α := by
  have hinj := hα.injective
  have hn := n_eq n p
  have hρp : n % p < p := Nat.mod_lt _ hp
  set N := n / p
  set ρ := n % p
  -- the bottom region
  have F2 : ∀ i : Fin n, (i : ℕ) < ρ → α i = i := by
    have hL : (univ.filter (fun j => α j < ρ)).card = ρ := card_below p hp hinj htriv
    have hlt : ∀ i : Fin n, (i : ℕ) < ρ → α i < ρ := by
      intro i hi
      by_contra hge
      rw [not_lt] at hge
      have hsub : univ.filter (fun j => α j < ρ) ⊆ univ.filter (fun j : Fin n => (j : ℕ) < i) := by
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
        by_contra hji
        rw [not_lt] at hji
        have : α i ≤ α j := hα.monotone (Fin.le_def.mpr hji)
        omega
      have h1 := Finset.card_le_card hsub
      have h2 : (univ.filter (fun j : Fin n => (j : ℕ) < i)).card ≤ i := by
        calc _ = ((univ.filter (fun j : Fin n => (j : ℕ) < i)).image Fin.val).card :=
              (Finset.card_image_of_injective _ Fin.val_injective).symm
          _ ≤ (range i).card := by
              refine Finset.card_le_card fun x hx => ?_
              obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
              simpa using hj
          _ = i := Finset.card_range _
      omega
    intro i hi
    have hρn : ρ - 1 < n := by have := i.2; omega
    have h1 := hlt ⟨ρ - 1, hρn⟩ (by simp; omega)
    have h2 := strictMono_gap hα i.2 hρn (show (i : ℕ) ≤ ρ - 1 by omega)
    simp only [Fin.eta] at h2
    have h3 := le_strictMono hα i
    omega
  -- residues
  have P : ∀ k (hk : ρ + k < n), ρ ≤ α ⟨ρ + k, hk⟩ ∧ (α ⟨ρ + k, hk⟩ - ρ) % p = k % p := by
    intro k
    induction k with
    | zero =>
      intro hk
      have hge : ρ ≤ α ⟨ρ + 0, hk⟩ := le_trans (by simp) (le_strictMono hα ⟨ρ + 0, hk⟩)
      refine ⟨hge, ?_⟩
      set a := α ⟨ρ + 0, hk⟩
      set b := a - (a - ρ) % p
      have hmodle : (a - ρ) % p ≤ a - ρ := Nat.mod_le _ _
      have hb1 : ρ ≤ b := by omega
      have hb2 : (b - ρ) / p = (a - ρ) / p := by
        have e : b - ρ = p * ((a - ρ) / p) := by
          have := Nat.div_add_mod (a - ρ) p; omega
        rw [e, Nat.mul_div_cancel_left _ hp]
      obtain ⟨j, hj⟩ := full_block p hp hinj htriv ⟨ρ + 0, hk⟩ b hge hb1 hb2
      have hjle : j ≤ ⟨ρ + 0, hk⟩ := by
        rw [← hα.le_iff_le, hj]; omega
      by_cases hjρ : (j : ℕ) < ρ
      · have := F2 j hjρ; omega
      · have : j = ⟨ρ + 0, hk⟩ := by
          apply le_antisymm hjle; rw [Fin.le_def]; simp; omega
        subst this
        simp only [Nat.zero_mod]
        omega
    | succ k ih =>
      intro hk
      obtain ⟨hge, hres⟩ := ih (by omega)
      set i : Fin n := ⟨ρ + k, by omega⟩
      set i' : Fin n := ⟨ρ + (k + 1), hk⟩
      have hii' : i < i' := by rw [Fin.lt_def]; simp [i, i']
      have hlt := hα hii'
      set a := α i - ρ
      by_cases hc : k % p + 1 < p
      · have hc' : a % p + 1 < p := by rw [hres]; exact hc
        obtain ⟨j, hj⟩ := full_block p hp hinj htriv i (α i + 1) hge (by omega) (by
          rw [show α i + 1 - ρ = a + 1 by omega, succ_div_of_lt hc'])
        have hij : i < j := by rw [← hα.lt_iff_lt, hj]; omega
        have hi'j : i' ≤ j := by rw [Fin.le_def]; rw [Fin.lt_def] at hij; simp [i, i'] at hij ⊢; omega
        have := hα.monotone hi'j
        have heq : α i' = α i + 1 := by omega
        refine ⟨by omega, ?_⟩
        rw [heq, show α i + 1 - ρ = a + 1 by omega, succ_mod_of_lt hc', hres,
          succ_mod_of_lt hc]
      · have hc' : k % p = p - 1 := by have := Nat.mod_lt k hp; omega
        have ha : a % p = p - 1 := by rw [hres, hc']
        set a' := α i' - ρ
        set b := α i' - a' % p
        have hmodle : a' % p ≤ a' := Nat.mod_le _ _
        have hb1 : ρ ≤ b := by omega
        have hb2 : (b - ρ) / p = (α i' - ρ) / p := by
          have e : b - ρ = p * (a' / p) := by
            have := Nat.div_add_mod a' p; omega
          rw [e, Nat.mul_div_cancel_left _ hp]
        obtain ⟨j, hj⟩ := full_block p hp hinj htriv i' b (by omega) hb1 hb2
        have hbgt : α i < b := by
          -- `α i` is the top of its block, `α i' ≥ α i + 1` lies in a later block
          have h1 := Nat.div_add_mod a p
          have h2 := Nat.div_add_mod a' p
          have h3 : a + 1 ≤ a' := by omega
          have h4 : a / p + 1 ≤ a' / p := by
            have e : a + 1 = p * (a / p + 1) := by rw [Nat.mul_succ]; omega
            have h5 := Nat.div_le_div_right (c := p) h3
            rwa [e, Nat.mul_div_cancel_left _ hp] at h5
          have : p * (a / p + 1) ≤ p * (a' / p) := Nat.mul_le_mul_left _ h4
          rw [Nat.mul_succ] at this
          generalize p * (a / p) = M1 at *
          generalize p * (a' / p) = M2 at *
          omega
        have hij : i < j := by rw [← hα.lt_iff_lt, hj]; exact hbgt
        have hji' : j ≤ i' := by rw [← hα.le_iff_le, hj]; omega
        have hj' : j = i' := by
          apply le_antisymm hji'
          rw [Fin.le_def]; rw [Fin.lt_def] at hij; simp [i, i'] at hij ⊢; omega
        subst hj'
        refine ⟨by omega, ?_⟩
        rw [succ_mod_of_eq hp hc']
        omega
  -- consecutive entries within a group
  have C : ∀ k (hk : ρ + k + 1 < n), k % p + 1 < p →
      α ⟨ρ + k + 1, hk⟩ = α ⟨ρ + k, by omega⟩ + 1 := by
    intro k hk hc
    obtain ⟨hge, hres⟩ := P k (by omega)
    have hc' : (α ⟨ρ + k, by omega⟩ - ρ) % p + 1 < p := by rw [hres]; exact hc
    obtain ⟨j, hj⟩ := full_block p hp hinj htriv ⟨ρ + k, by omega⟩ (α ⟨ρ + k, by omega⟩ + 1) hge
      (by omega) (by
        rw [show α ⟨ρ + k, by omega⟩ + 1 - ρ = (α ⟨ρ + k, by omega⟩ - ρ) + 1 by omega,
          succ_div_of_lt hc'])
    have hij : (⟨ρ + k, by omega⟩ : Fin n) < j := by rw [← hα.lt_iff_lt, hj]; omega
    have hi'j : (⟨ρ + k + 1, hk⟩ : Fin n) ≤ j := by
      rw [Fin.le_def]; rw [Fin.lt_def] at hij; simp at hij ⊢; omega
    have h1 := hα.monotone hi'j
    have h2 := hα (show (⟨ρ + k, by omega⟩ : Fin n) < ⟨ρ + k + 1, hk⟩ by
      rw [Fin.lt_def]; simp)
    omega
  -- the shape
  refine ⟨fun g => if h : ρ + p * g < n then (α ⟨ρ + p * g, h⟩ - (ρ + p * g)) / p else 0,
    fun i => ?_⟩
  split_ifs with hi
  · exact F2 i hi
  · rw [not_lt] at hi
    set k := (i : ℕ) - ρ
    set g := k / p
    set s := k % p
    have hks : k = p * g + s := (Nat.div_add_mod k p).symm
    have hsp : s < p := Nat.mod_lt _ hp
    have hg : ρ + p * g < n := by have := i.2; omega
    simp only [hg, ↓reduceDIte]
    -- walk from the start of the group
    have walk : ∀ t (ht : t ≤ s), α ⟨ρ + p * g + t, by have := i.2; omega⟩ =
        α ⟨ρ + p * g, hg⟩ + t := by
      intro t
      induction t with
      | zero => intro _; rfl
      | succ t iht =>
        intro ht
        have hmod : (p * g + t) % p + 1 < p := by
          rw [Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]; omega
        have := C (p * g + t) (by have := i.2; omega) hmod
        have e1 : (⟨ρ + p * g + (t + 1), by have := i.2; omega⟩ : Fin n) =
            ⟨ρ + (p * g + t) + 1, by have := i.2; omega⟩ := Fin.ext (by simp; omega)
        have e2 : (⟨ρ + (p * g + t), by have := i.2; omega⟩ : Fin n) =
            ⟨ρ + p * g + t, by have := i.2; omega⟩ := Fin.ext (by simp; omega)
        rw [e1, this, e2, iht (by omega)]
        ring
    have hw := walk s le_rfl
    rw [show (⟨ρ + p * g + s, _⟩ : Fin n) = i from Fin.ext (by simp; omega)] at hw
    obtain ⟨hge, hres⟩ := P (p * g) hg
    rw [Nat.mul_mod_right] at hres
    have hbig := le_strictMono hα ⟨ρ + p * g, hg⟩
    simp only at hbig
    have hdvd : p ∣ α ⟨ρ + p * g, hg⟩ - (ρ + p * g) := by
      have h1 : p ∣ α ⟨ρ + p * g, hg⟩ - ρ := Nat.dvd_of_mod_eq_zero hres
      have h2 : α ⟨ρ + p * g, hg⟩ - (ρ + p * g) = (α ⟨ρ + p * g, hg⟩ - ρ) - p * g := by omega
      rw [h2]
      exact Nat.dvd_sub h1 (dvd_mul_right _ _)
    rw [hw, Nat.mul_div_cancel' hdvd]
    omega

/-- **Trivial bead configurations are exactly the shapes** (for strictly increasing `α`). -/
theorem trivial_iff_shape (hp : 0 < p) {α : Fin n → ℕ} (hα : StrictMono α) :
    ¬ NTv p (cv p α) ↔ Shape p α :=
  ⟨shape_of_trivial p hp hα, trivial_of_shape p hp⟩

/-- **For a partition `λ` with at most `n` parts: the bead configuration `λ + δ` is trivial
(every full block has a number of beads divisible by `p`) iff `λ` is `p`-Lima.** -/
theorem trivial_iff_isPLima (hp : 0 < p) {lam : Fin n → ℕ} (hlam : Antitone lam) :
    ¬ NTv p (cv p (lamDelta lam)) ↔ IsPLima p lam := by
  rw [trivial_iff_shape p hp (strictMono_lamDelta hlam), isPLima_iff_shape p hp]

end Beads2

end

end OddMath.Frontier.EQPdg
