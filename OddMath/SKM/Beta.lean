/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.GrassmannianOdd

/-!
# The homomorphisms `β_{λ;i}` (Brundan–Ellis, (1.19), (1.20), (5.1), (5.2))

J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, (1.19)–(1.20) in the
introduction and (5.1)–(5.2) in §5.

`Sym` is the algebra of symmetric functions over `k`, realized as the polynomial algebra in the
elementary symmetric functions `e₁, e₂, …` (`Sym.e`, with `e₀ = 1`); the complete symmetric
functions `Sym.h n` are defined by the relations `∑_{r+s=n} (-1)^s e_r h_s = 0` (`n > 0`),
`h₀ = 1` (Macdonald (I.2.6′), quoted in the paper; here they are the definition, `Sym.e_h_rel`).
`SymD` is `Sym[d]`: `Sym` with an adjoined generator `d` with `d² = 0`. Since `d` is the only odd
generator, `Sym[d]` is commutative as an ordinary algebra, and a homomorphism of superalgebras
out of it is a homomorphism of algebras sending `d` to an odd element.

* `beta` (`i` even, (1.19)): the unique algebra homomorphism `Sym → End(1_λ)` with
  `e_n ↦ c_{λ;i}⁻¹ (n + *)`-dotted counterclockwise bubble; it exists because these bubbles
  commute (the super interchange law). `beta_h`: it sends `h_n` to `(-1)^n c_{λ;i}` times the
  `(n + *)`-dotted clockwise bubble — this is (5.5), and (5.1), (5.2) for even `i`
  (`eq_5_1_even`, `eq_5_2_even`).
* `betaD` (`i` odd, (1.20)): `Sym[d] → End(1_λ)` with `e_n ↦ c_{λ;i}⁻¹ (2n + *)`-dotted
  counterclockwise bubble and `d ↦` the odd bubble (well defined by (1.24)); `betaD_h`,
  `betaD_de`, `betaD_dh` give the images of `h_n`, `d e_n`, `d h_n` stated in (1.20); (5.1), (5.2)
  for odd `i`: `eq_5_1_odd_even`, `eq_5_1_odd_odd`, `eq_5_2_odd_even`, `eq_5_2_odd_odd`.

Multiplication in `End(1_λ)` is Mathlib's: `f * g = g ≫ f`.
-/

noncomputable section

namespace OddMath.SKM

open CategoryTheory StringDiagrams Presentation Finset MvPolynomial

open scoped IsMulCommutative

universe u v w

/-! ## Symmetric functions -/

variable (k : Type w) [CommRing k]

/-- The algebra of symmetric functions over `k`, as the polynomial algebra in `e₁, e₂, …`
(`X n` is `e_{n+1}`). -/
abbrev Sym : Type w := MvPolynomial ℕ k

namespace Sym

variable {k}

/-- The elementary symmetric function `e_n` (`e₀ = 1`). -/
def e (n : ℕ) : Sym k := if n = 0 then 1 else X (n - 1)

@[simp] theorem e_zero : (e 0 : Sym k) = 1 := rfl

theorem e_succ (n : ℕ) : (e (n + 1) : Sym k) = MvPolynomial.X n := by simp [e]

/-- The complete symmetric function `h_n`, defined by `h₀ = 1` and
`h_n = -∑_{s<n} (-1)^{n+s} e_{n-s} h_s`, i.e. `∑_{r+s=n} (-1)^s e_r h_s = 0` for `n > 0`. -/
def h : ℕ → Sym k
  | 0 => 1
  | n + 1 => -∑ s : Fin (n + 1), (-1) ^ (n + 1 + (s : ℕ)) * e (n + 1 - s) * h s

@[simp] theorem h_zero : (h 0 : Sym k) = 1 := by simp [h]

theorem h_succ (n : ℕ) : (h (n + 1) : Sym k) =
    -∑ s ∈ range (n + 1), (-1) ^ (n + 1 + s) * e (n + 1 - s) * h s := by
  rw [h, ← Fin.sum_univ_eq_sum_range (fun s => (-1) ^ (n + 1 + s) * e (n + 1 - s) * h s)]

/-- **Macdonald (I.2.6′)** (quoted in Brundan–Ellis §1): `∑_{r+s=n} (-1)^s e_r h_s = 0` for
`n > 0`. -/
theorem e_h_rel (n : ℕ) (hn : 0 < n) :
    ∑ s ∈ range (n + 1), (-1) ^ s * e (n - s) * (h s : Sym k) = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [sum_range_succ, Nat.sub_self, e_zero, mul_one, h_succ, mul_neg, mul_sum]
  rw [← sub_eq_add_neg, sub_eq_zero]
  refine sum_congr rfl fun s hs => ?_
  rw [mem_range] at hs
  rw [← mul_assoc, ← mul_assoc, ← pow_add, show m + 1 + (m + 1 + s) = s + 2 * (m + 1) by ring,
    pow_add, pow_mul, neg_one_sq, one_pow, mul_one]

end Sym

/-- `Sym[d]`: `Sym` with an adjoined generator `d`, `d² = 0` (`X none` is `d`, `X (some n)` is
`e_{n+1}`). -/
abbrev SymD : Type w := MvPolynomial (Option ℕ) k ⧸ Ideal.span {(X none : MvPolynomial (Option ℕ) k) ^ 2}

namespace SymD

variable {k}

/-- The quotient map. -/
abbrev mk : MvPolynomial (Option ℕ) k →ₐ[k] SymD k := Ideal.Quotient.mkₐ k _

/-- The inclusion `Sym → Sym[d]`. -/
def ofSym : Sym k →ₐ[k] SymD k := mk.comp (rename some)

/-- The odd generator `d`. -/
def d : SymD k := mk (X none)

theorem d_sq : (d : SymD k) ^ 2 = 0 := by
  rw [d, ← map_pow, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span rfl

end SymD

/-! ## `β_{λ;i}` -/

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X} {k}
  {Sc : Scalars D k} (cs : CScalars Sc)

/-- Closed 2-morphisms of parity `0` commute with all homogeneous closed 2-morphisms. -/
theorem commute_of_mem_zero {μ : X} {q : ZMod 2} {f g : End ((pres D Sc).obj (ob D μ []))}
    (hf : f ∈ closedPar D Sc μ 0) (hg : g ∈ closedPar D Sc μ q) : Commute f g := by
  show g ≫ f = f ≫ g
  rw [comm_of_mem hf hg, zero_mul, zsign_zero, one_smul]

/-- The generators of the image of `β_{λ;i}`, `i` even: `e_{n+1} ↦ c⁻¹ bubLs(n + 1)`. -/
def betaGen (i : I) (μ : X) (n : ℕ) : End ((pres D Sc).obj (ob D μ [])) :=
  (↑(cs.c μ i)⁻¹ : k) • bubLs cs i μ ((n : ℤ) + 1)

theorem bubLs_mem_even (i : I) (μ : X) (hi : D.parity i = 0) (n : ℤ) :
    bubLs cs i μ n ∈ closedPar D Sc μ 0 := by
  have := bubL_mem cs i μ (n + D.h i μ - 1)
  rwa [hi, zero_mul] at this

theorem betaGen_pairwise (i : I) (μ : X) (hi : D.parity i = 0) :
    (Set.range (betaGen cs i μ)).Pairwise Commute := by
  rintro _ ⟨m, rfl⟩ _ ⟨n, rfl⟩ _
  exact commute_of_mem_zero (Submodule.smul_mem _ _ (bubLs_mem_even cs i μ hi _))
    (Submodule.smul_mem _ _ (bubLs_mem_even cs i μ hi _))

/-- **`β_{λ;i}` for even `i`** (Brundan–Ellis (1.19)): the algebra homomorphism
`Sym → End(1_λ)` with `e_n ↦ c_{λ;i}⁻¹ ·` (counterclockwise bubble with `n + *` dots). -/
def beta (i : I) (μ : X) (hi : D.parity i = 0) : Sym k →ₐ[k] End ((pres D Sc).obj (ob D μ [])) :=
  haveI := Algebra.isMulCommutative_adjoin k (betaGen_pairwise cs i μ hi)
  (Algebra.adjoin k (Set.range (betaGen cs i μ))).val.comp
    (aeval fun n => ⟨betaGen cs i μ n, Algebra.subset_adjoin ⟨n, rfl⟩⟩)

theorem beta_X (i : I) (μ : X) (hi : D.parity i = 0) (n : ℕ) :
    beta cs i μ hi (MvPolynomial.X n) = betaGen cs i μ n := by
  simp [beta]

theorem beta_e (i : I) (μ : X) (hi : D.parity i = 0) (n : ℕ) :
    beta cs i μ hi (Sym.e n) = (↑(cs.c μ i)⁻¹ : k) • bubLs cs i μ n := by
  rcases n with _ | n
  · rw [Sym.e_zero, map_one, Nat.cast_zero, bubLs_zero, smul_smul, Units.inv_mul, one_smul]; rfl
  · rw [Sym.e_succ, beta_X, betaGen]; push_cast; rfl

/-- Uniqueness in (1.19): `β_{λ;i}` is the only algebra homomorphism with the given images of
the `e_n`. -/
theorem beta_unique (i : I) (μ : X) (hi : D.parity i = 0)
    (φ : Sym k →ₐ[k] End ((pres D Sc).obj (ob D μ [])))
    (hφ : ∀ n, φ (Sym.e n) = (↑(cs.c μ i)⁻¹ : k) • bubLs cs i μ n) : φ = beta cs i μ hi :=
  MvPolynomial.algHom_ext fun n => by rw [← Sym.e_succ, hφ, beta_e]

/-- The images of the complete symmetric functions under a homomorphism `φ : Sym → End(1_λ)`
with `φ(e_n) = u⁻¹ L(n)`, `L(0) = u`, `R(0) = u⁻¹` and `∑_{r+s=n} R(s) ≫ L(r) = 0` for `n > 0`:
`φ(h_n) = (-1)^n u R(n)`. -/
theorem image_h {μ : X} (φ : Sym k →ₐ[k] End ((pres D Sc).obj (ob D μ [])))
    (L R : ℕ → End ((pres D Sc).obj (ob D μ []))) (u : kˣ) (hL0 : L 0 = (u : k) • 𝟙 _)
    (hR0 : R 0 = (↑u⁻¹ : k) • 𝟙 _) (he : ∀ n, φ (Sym.e n) = (↑u⁻¹ : k) • L n)
    (hkey : ∀ n, 0 < n → ∑ r ∈ range (n + 1), R (n - r) ≫ L r = 0) (n : ℕ) :
    φ (Sym.h n) = ((-1) ^ n * (u : k)) • R n := by
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  rcases n with _ | n
  · rw [Sym.h_zero, map_one, hR0, pow_zero, one_mul, smul_smul, Units.mul_inv, one_smul]; rfl
  · have K' : ∑ s ∈ range (n + 1), R s ≫ L (n + 1 - s) = -((u : k) • R (n + 1)) := by
      have K := hkey (n + 1) (by omega)
      rw [sum_range_succ', Nat.sub_zero, hL0, Linear.comp_smul, Category.comp_id] at K
      rw [← eq_neg_of_add_eq_zero_left K, ← sum_range_reflect]
      refine sum_congr rfl fun r hr => ?_
      rw [mem_range] at hr
      congr 2 <;> omega
    rw [Sym.h_succ, map_neg, map_sum]
    have hterm : ∀ s ∈ range (n + 1), φ ((-1) ^ (n + 1 + s) * Sym.e (n + 1 - s) *
        Sym.h s) = ((-1) ^ (n + 1) : k) • (R s ≫ L (n + 1 - s)) := by
      intro s hs
      rw [mem_range] at hs
      have e1 : ((-1 : Sym k) ^ (n + 1 + s) * Sym.e (n + 1 - s) * Sym.h s) =
          ((-1 : k) ^ (n + 1 + s)) • (Sym.e (n + 1 - s) * Sym.h s) := by
        rw [Algebra.smul_def, map_pow, map_neg, map_one, mul_assoc]
      rw [e1, map_smul, map_mul, he, IH s (by omega), End.mul_def, Linear.smul_comp,
        Linear.comp_smul, smul_smul, smul_smul]
      congr 1
      rw [mul_assoc, mul_assoc, Units.mul_inv, mul_one, ← pow_add, show n + 1 + s + s =
        (n + 1) + 2 * s by ring, pow_add, pow_mul, neg_one_sq, one_pow, mul_one]
    rw [sum_congr rfl hterm, ← smul_sum, K', smul_neg, neg_neg, smul_smul, pow_succ]

/-- For even `i`, `β_{λ;i}(h_n) = (-1)^n c_{λ;i}` times the clockwise bubble with `n + *` dots
(Brundan–Ellis (1.19); this is equivalent to (5.5)). -/
theorem beta_h (i : I) (μ : X) (hi : D.parity i = 0) (n : ℕ) :
    beta cs i μ hi (Sym.h n) = ((-1) ^ n * (cs.c μ i : k)) • bubRs cs i μ n := by
  refine image_h (beta cs i μ hi) (fun n => bubLs cs i μ n) (fun n => bubRs cs i μ n) (cs.c μ i)
    (by simpa using bubLs_zero cs i μ) (by simpa using bubRs_zero cs i μ)
    (beta_e cs i μ hi) (fun n hn => ?_) n
  have K := bubble_key cs i μ n hn
  simp only [hi, isg, zero_mul, zsign_zero, one_smul] at K
  rw [← K]
  refine sum_congr rfl fun r hr => ?_
  rw [mem_range] at hr
  push_cast [Nat.cast_sub (show r ≤ n by omega)]; rfl

/-- **Brundan–Ellis (5.1)**, `i` even: the counterclockwise bubble with `n + *` dots is
`c_{λ;i} β_{λ;i}(e_n)`. -/
theorem eq_5_1_even (i : I) (μ : X) (hi : D.parity i = 0) (n : ℕ) :
    bubLs cs i μ n = (cs.c μ i : k) • beta cs i μ hi (Sym.e n) := by
  rw [beta_e, smul_smul, Units.mul_inv, one_smul]

/-- **Brundan–Ellis (5.2)**, `i` even: the clockwise bubble with `n + *` dots is
`c_{λ;i}⁻¹ β_{λ;i}((-1)^n h_n)`. -/
theorem eq_5_2_even (i : I) (μ : X) (hi : D.parity i = 0) (n : ℕ) :
    bubRs cs i μ n = (↑(cs.c μ i)⁻¹ : k) • beta cs i μ hi ((-1) ^ n * Sym.h n) := by
  have e1 : ((-1 : Sym k) ^ n * Sym.h n) = ((-1 : k) ^ n) • Sym.h n := by
    rw [Algebra.smul_def, map_pow, map_neg, map_one]
  have hc : (↑(cs.c μ i)⁻¹ : k) * (-1) ^ n * ((-1) ^ n * (cs.c μ i : k)) = 1 := by
    rw [mul_assoc, ← mul_assoc ((-1 : k) ^ n), ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow,
      one_mul, Units.inv_mul]
  rw [e1, map_smul, beta_h, smul_smul, smul_smul, hc, one_smul]


/-! ## `β_{λ;i}` for odd `i` -/

theorem bubLs_mem (i : I) (μ : X) (n : ℤ) :
    bubLs cs i μ n ∈ closedPar D Sc μ (D.parity i * (n : ZMod 2)) := by
  have := bubL_mem cs i μ (n + D.h i μ - 1)
  rw [bubLs]
  convert this using 2
  rw [show n + D.h i μ - 1 + D.h i μ + 1 = n + 2 * D.h i μ by ring]
  push_cast; rw [show (2 : ZMod 2) = 0 from rfl]; ring

theorem bubLs_two_mul_mem (i : I) (μ : X) (n : ℤ) :
    bubLs cs i μ (2 * n) ∈ closedPar D Sc μ 0 := by
  convert bubLs_mem cs i μ (2 * n) using 2
  push_cast; rw [show (2 : ZMod 2) = 0 from rfl]; ring

/-- The generators of the image of `β_{λ;i}`, `i` odd: `d ↦` the odd bubble,
`e_{n+1} ↦ c⁻¹ bubLs(2n + 2)`. -/
def betaDGen (i : I) (μ : X) : Option ℕ → End ((pres D Sc).obj (ob D μ []))
  | none => oddBubble cs i μ
  | some n => (↑(cs.c μ i)⁻¹ : k) • bubLs cs i μ (2 * ((n : ℤ) + 1))

theorem betaDGen_pairwise (i : I) (μ : X) : (Set.range (betaDGen cs i μ)).Pairwise Commute := by
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ _
  rcases a with _ | m <;> rcases b with _ | n
  · exact Commute.refl _
  · exact (commute_of_mem_zero (Submodule.smul_mem _ _ (bubLs_two_mul_mem cs i μ _))
      (oddBubble_mem cs i μ)).symm
  · exact commute_of_mem_zero (Submodule.smul_mem _ _ (bubLs_two_mul_mem cs i μ _))
      (oddBubble_mem cs i μ)
  · exact commute_of_mem_zero (Submodule.smul_mem _ _ (bubLs_two_mul_mem cs i μ _))
      (Submodule.smul_mem _ _ (bubLs_two_mul_mem cs i μ _))

/-- The homomorphism `MvPolynomial (Option ℕ) k → End(1_λ)` on generators. -/
def betaDPoly (i : I) (μ : X) :
    MvPolynomial (Option ℕ) k →ₐ[k] End ((pres D Sc).obj (ob D μ [])) :=
  haveI := Algebra.isMulCommutative_adjoin k (betaDGen_pairwise cs i μ)
  (Algebra.adjoin k (Set.range (betaDGen cs i μ))).val.comp
    (aeval fun o => ⟨betaDGen cs i μ o, Algebra.subset_adjoin ⟨o, rfl⟩⟩)

theorem betaDPoly_X (i : I) (μ : X) (o : Option ℕ) :
    betaDPoly cs i μ (MvPolynomial.X o) = betaDGen cs i μ o := by
  simp [betaDPoly]

/-- **`β_{λ;i}` for odd `i`** (Brundan–Ellis (1.20)): the homomorphism `Sym[d] → End(1_λ)` with
`e_n ↦ c_{λ;i}⁻¹ ·` (counterclockwise bubble with `2n + *` dots) and `d ↦` the odd bubble; it is
well defined since the odd bubble squares to zero (1.24). -/
def betaD (i : I) (μ : X) (hi : D.parity i = 1) : SymD k →ₐ[k] End ((pres D Sc).obj (ob D μ [])) :=
  Ideal.Quotient.liftₐ _ (betaDPoly cs i μ) fun a ha => by
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, map_pow, betaDPoly_X, betaDGen, sq, End.mul_def, End.mul_def,
      oddBubble_sq cs i μ hi, Limits.zero_comp]

theorem betaD_mk (i : I) (μ : X) (hi : D.parity i = 1) (p : MvPolynomial (Option ℕ) k) :
    betaD cs i μ hi (SymD.mk p) = betaDPoly cs i μ p := rfl

theorem betaD_d (i : I) (μ : X) (hi : D.parity i = 1) :
    betaD cs i μ hi SymD.d = oddBubble cs i μ := by
  rw [SymD.d, betaD_mk, betaDPoly_X, betaDGen]

theorem betaD_e (i : I) (μ : X) (hi : D.parity i = 1) (n : ℕ) :
    betaD cs i μ hi (SymD.ofSym (Sym.e n)) = (↑(cs.c μ i)⁻¹ : k) • bubLs cs i μ (2 * n) := by
  rcases n with _ | n
  · rw [Sym.e_zero, map_one, map_one, Nat.cast_zero, mul_zero, bubLs_zero, smul_smul,
      Units.inv_mul, one_smul]; rfl
  · rw [Sym.e_succ, SymD.ofSym, AlgHom.comp_apply, rename_X, betaD_mk, betaDPoly_X, betaDGen]
    push_cast; rfl

/-- `β_{λ;i}(h_n) = (-1)^n c_{λ;i}` times the clockwise bubble with `2n + *` dots (odd `i`;
Brundan–Ellis (1.20); equivalent to (5.6)). -/
theorem betaD_h (i : I) (μ : X) (hi : D.parity i = 1) (n : ℕ) :
    betaD cs i μ hi (SymD.ofSym (Sym.h n)) = ((-1) ^ n * (cs.c μ i : k)) • bubRs cs i μ (2 * n) := by
  refine image_h ((betaD cs i μ hi).comp SymD.ofSym) (fun n => bubLs cs i μ (2 * n))
    (fun n => bubRs cs i μ (2 * n)) (cs.c μ i)
    (by simpa using bubLs_zero cs i μ) (by simpa using bubRs_zero cs i μ)
    (betaD_e cs i μ hi) (fun n hn => ?_) n
  rw [← eq_5_6 cs i μ hi n hn]
  refine sum_congr rfl fun r hr => ?_
  rw [mem_range] at hr
  push_cast [Nat.cast_sub (show r ≤ n by omega)]; rfl

/-- Uniqueness in (1.20): `β_{λ;i}` is the only algebra homomorphism `Sym[d] → End(1_λ)` with the
given images of `d` and the `e_n`. -/
theorem betaD_unique (i : I) (μ : X) (hi : D.parity i = 1)
    (φ : SymD k →ₐ[k] End ((pres D Sc).obj (ob D μ [])))
    (hd : φ SymD.d = oddBubble cs i μ)
    (hφ : ∀ n, φ (SymD.ofSym (Sym.e n)) = (↑(cs.c μ i)⁻¹ : k) • bubLs cs i μ (2 * n)) :
    φ = betaD cs i μ hi := by
  refine Ideal.Quotient.algHom_ext k (MvPolynomial.algHom_ext fun o => ?_)
  rcases o with _ | n
  · exact (hd.trans (betaD_d cs i μ hi).symm)
  · have h1 := hφ (n + 1)
    have h2 := betaD_e cs i μ hi (n + 1)
    rw [Sym.e_succ, SymD.ofSym, AlgHom.comp_apply, rename_X] at h1 h2
    exact h1.trans h2.symm

theorem betaD_de (i : I) (μ : X) (hi : D.parity i = 1) (n : ℕ) :
    betaD cs i μ hi (SymD.d * SymD.ofSym (Sym.e n)) =
      (↑(cs.c μ i)⁻¹ : k) • bubLs cs i μ (2 * n + 1) := by
  rw [map_mul, betaD_d, betaD_e, End.mul_def, Linear.smul_comp, eq_5_7_a cs i μ hi,
    comm_of_mem (bubLs_two_mul_mem cs i μ _) (oddBubble_mem cs i μ), zero_mul, zsign_zero,
    one_smul]

theorem betaD_dh (i : I) (μ : X) (hi : D.parity i = 1) (n : ℕ) :
    betaD cs i μ hi (SymD.d * SymD.ofSym (Sym.h n)) =
      ((-1) ^ n * (cs.c μ i : k)) • bubRs cs i μ (2 * n + 1) := by
  have hm : bubRs cs i μ (2 * (n : ℤ)) ∈ closedPar D Sc μ 0 := by
    have := bubR_mem cs i μ (2 * n - D.h i μ - 1)
    rw [bubRs]
    convert this using 2
    rw [show 2 * (n : ℤ) - D.h i μ - 1 + D.h i μ + 1 = 2 * n by ring]
    push_cast; rw [show (2 : ZMod 2) = 0 from rfl]; ring
  rw [map_mul, betaD_d, betaD_h, End.mul_def, Linear.smul_comp, eq_5_7_b cs i μ hi,
    comm_of_mem hm (oddBubble_mem cs i μ), zero_mul, zsign_zero, one_smul]

/-- **Brundan–Ellis (5.1)**, `i` odd, `n = 2m` even: the counterclockwise bubble with `2m + *`
dots is `c_{λ;i} β_{λ;i}(e_m)`. -/
theorem eq_5_1_odd_even (i : I) (μ : X) (hi : D.parity i = 1) (m : ℕ) :
    bubLs cs i μ (2 * m) = (cs.c μ i : k) • betaD cs i μ hi (SymD.ofSym (Sym.e m)) := by
  rw [betaD_e, smul_smul, Units.mul_inv, one_smul]

/-- **Brundan–Ellis (5.1)**, `i` odd, `n = 2m + 1` odd: `c_{λ;i} β_{λ;i}(d e_m)`. -/
theorem eq_5_1_odd_odd (i : I) (μ : X) (hi : D.parity i = 1) (m : ℕ) :
    bubLs cs i μ (2 * m + 1) =
      (cs.c μ i : k) • betaD cs i μ hi (SymD.d * SymD.ofSym (Sym.e m)) := by
  rw [betaD_de, smul_smul, Units.mul_inv, one_smul]

theorem inv_mul_sign_mul (u : kˣ) (m : ℕ) :
    (↑u⁻¹ : k) * (-1) ^ m * ((-1) ^ m * (u : k)) = 1 := by
  rw [mul_assoc, ← mul_assoc ((-1 : k) ^ m), ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow,
    one_mul, Units.inv_mul]

/-- **Brundan–Ellis (5.2)**, `i` odd, `n = 2m`: the clockwise bubble with `2m + *` dots is
`c_{λ;i}⁻¹ β_{λ;i}((-1)^m h_m)`. -/
theorem eq_5_2_odd_even (i : I) (μ : X) (hi : D.parity i = 1) (m : ℕ) :
    bubRs cs i μ (2 * m) =
      (↑(cs.c μ i)⁻¹ : k) • betaD cs i μ hi (SymD.ofSym ((-1) ^ m * Sym.h m)) := by
  have e1 : ((-1 : Sym k) ^ m * Sym.h m) = ((-1 : k) ^ m) • Sym.h m := by
    rw [Algebra.smul_def, map_pow, map_neg, map_one]
  rw [e1, map_smul, map_smul, betaD_h, smul_smul, smul_smul, inv_mul_sign_mul, one_smul]

/-- **Brundan–Ellis (5.2)**, `i` odd, `n = 2m + 1`: `c_{λ;i}⁻¹ β_{λ;i}((-1)^m d h_m)`. -/
theorem eq_5_2_odd_odd (i : I) (μ : X) (hi : D.parity i = 1) (m : ℕ) :
    bubRs cs i μ (2 * m + 1) =
      (↑(cs.c μ i)⁻¹ : k) • betaD cs i μ hi (SymD.d * SymD.ofSym ((-1) ^ m * Sym.h m)) := by
  have e1 : ((-1 : Sym k) ^ m * Sym.h m) = ((-1 : k) ^ m) • Sym.h m := by
    rw [Algebra.smul_def, map_pow, map_neg, map_one]
  rw [e1, map_smul, mul_smul_comm, map_smul, betaD_dh, smul_smul, smul_smul, inv_mul_sign_mul,
    one_smul]

end OddMath.SKM
