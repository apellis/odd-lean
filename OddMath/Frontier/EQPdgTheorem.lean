import OddMath.Frontier.EQPdgLimaPart

/-!
# Ellis–Qi, Theorem A.4 (1) in `n` variables

Source: A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2,
Appendix A.4.2, Theorem A.4 (1).

Let `𝕜` be a field of characteristic `p > 0` and `Sym_n = 𝕜[x_1, …, x_n]^{S_n}` with the
p-differential `d(x_i) = x_i²` (`dSym`). Then

* `thmA4_1_pos`: `H_{/j}(Sym_n) = 0` for `1 ≤ j ≤ p - 2`;
* `thmA4_1_zero`: the classes of the Schur polynomials `s_λ`, `λ` a `p`-Lima partition with at
  most `n` parts (built out of `p × p` squares, `IsPLima`), form a basis of `H_{/0}(Sym_n)`.

The paper states the theorem for the inverse limit `Sym`; this is the version in `n` variables
(with the boundary condition `ℓ(λ) ≤ n`; a `p`-Lima partition with at most `n` rows has at most
`p ⌊n/p⌋` rows). Slash cohomology is `Ker(d^{k+1})/(Im(d^{p-k-1}) + Ker(d^k))` (see
`EQPdgSlash` for the misprint in the printed definition).
-/

namespace OddMath.Frontier.EQPdg

open Finset

noncomputable section

variable {n : ℕ}

/-- The partition `λ` with `λ + δ = α`: `λ_r = α_{n-1-r} - (n-1-r)`. -/
def lamOfAlpha (α : Fin n → ℕ) : Fin n → ℕ := fun r => α r.rev - r.rev

theorem antitone_lamOfAlpha {α : Fin n → ℕ} (hα : StrictMono α) : Antitone (lamOfAlpha α) := by
  intro r r' hrr'
  simp only [lamOfAlpha]
  have hle : (r'.rev : ℕ) ≤ r.rev := by
    rw [← Fin.le_def]; exact Fin.rev_le_rev.mpr hrr'
  have := strictMono_gap hα r'.rev.2 r.rev.2 hle
  simp only [Fin.eta] at this
  omega

theorem lamDelta_lamOfAlpha {α : Fin n → ℕ} (hα : StrictMono α) : lamDelta (lamOfAlpha α) = α := by
  funext i
  simp only [lamDelta, lamOfAlpha, Fin.rev_rev]
  have := le_strictMono hα i
  omega

theorem lamOfAlpha_lamDelta (lam : Fin n → ℕ) : lamOfAlpha (lamDelta lam) = lam := by
  funext r
  simp [lamOfAlpha, lamDelta]

variable (p : ℕ) [hp : Fact p.Prime]

/-- `p`-Lima partitions with at most `n` parts correspond to trivial Schur indices. -/
def pLimaEquiv : {lam : Fin n → ℕ // Antitone lam ∧ IsPLima p lam} ≃ ↥(ntSet (n := n) p)ᶜ where
  toFun lam := ⟨⟨lamDelta lam.1, strictMono_lamDelta lam.2.1⟩,
    (trivial_iff_isPLima p hp.out.pos lam.2.1).mpr lam.2.2⟩
  invFun α := ⟨lamOfAlpha α.1.1, antitone_lamOfAlpha α.1.2, by
    have h := (trivial_iff_isPLima p hp.out.pos (antitone_lamOfAlpha α.1.2)).mp
    rw [lamDelta_lamOfAlpha α.1.2] at h
    exact h α.2⟩
  left_inv lam := Subtype.ext (lamOfAlpha_lamDelta lam.1)
  right_inv α := Subtype.ext (Subtype.ext (lamDelta_lamOfAlpha α.1.2))

variable {k : Type*} [Field k] [CharP k p]

/-- **Ellis–Qi, Theorem A.4 (1), `H_{/j} = 0`** (in `n` variables): `H_{/j}(Sym_n) = 0` for
`1 ≤ j ≤ p - 2`. -/
theorem thmA4_1_pos (j : ℕ) (hj1 : 1 ≤ j) (hj2 : j ≤ p - 2) :
    Subsingleton (SlashCohomology (dSym (k := k) (n := n)) p j) :=
  slash_sym_pos p j hj1 hj2

omit hp [CharP k p] in
/-- The Schur polynomial `s_λ` as an element of `Sym_n`. -/
def schurSym (lam : Fin n → ℕ) : (SymSub : Submodule k (MvPolynomial (Fin n) k)) :=
  ⟨schur lam, mem_SymSub.mpr (schurA_isSymmetric _)⟩

omit [CharP k p] in
theorem schurSym_eq (lam : {lam : Fin n → ℕ // Antitone lam ∧ IsPLima p lam}) :
    schurSym (k := k) lam.1 = schurBasis ((pLimaEquiv (n := n) p) lam).1 := by
  apply Subtype.ext
  rw [schurBasis_apply]
  rfl

/-- `d(s_λ) = 0` for `p`-Lima `λ`. -/
theorem dSym_schurSym_pLima (lam : {lam : Fin n → ℕ // Antitone lam ∧ IsPLima p lam}) :
    (dSym (k := k) (n := n) ^ (0 + 1)) (schurSym lam.1) = 0 := by
  rw [schurSym_eq p lam]
  have := symT_le_ker (k := k) (n := n) p (Submodule.subset_span ⟨(pLimaEquiv p) lam, rfl⟩)
  simpa using this

/-- **Ellis–Qi, Theorem A.4 (1), `H_{/0}`** (in `n` variables): the classes `[s_λ]` of the
Schur polynomials of the `p`-Lima partitions `λ` with at most `n` parts form a basis of
`H_{/0}(Sym_n)`. -/
theorem thmA4_1_zero :
    ∃ b : Module.Basis {lam : Fin n → ℕ // Antitone lam ∧ IsPLima p lam} k
        (SlashCohomology (dSym (k := k) (n := n)) p 0),
      ∀ lam, b lam = slashClass dSym p 0 (schurSym lam.1) (dSym_schurSym_pLima p lam) := by
  obtain ⟨b, hb⟩ := slash_sym_zero_basis (k := k) (n := n) p
  refine ⟨b.reindex (pLimaEquiv p).symm, fun lam => ?_⟩
  rw [Module.Basis.reindex_apply, Equiv.symm_symm, hb]
  simp only [slashClass]
  congr 2
  exact (schurSym_eq p lam).symm

end

end OddMath.Frontier.EQPdg
