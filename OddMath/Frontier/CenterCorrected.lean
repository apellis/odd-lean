import OddMath.Frontier.CenterPoly
import OddMath.Frontier.CenterONH

/-!
# Corrected EKL Proposition 2.15: the center of `OΛ_N` and of `ONH_N`, every rank

EKL arXiv:1111.1320v1, Prop. 2.15, p. 13, asserts that the center of the ring `OΛ_N` of
odd symmetric polynomials, and the center of the odd nilHecke ring `ONH_N`, is the ring
`S_N` of symmetric polynomials in the squared variables `x_1^2, …, x_N^2`. That statement
is correct for even `N` and false for every odd `N`. The corrected statement, proved here
for every `N ≥ 2` on the actual objects, is:

* `Z(OΛ_N) = S_N` for `N` even, and `Z(OΛ_N) = S_N ⊕ V · S_N` for `N` odd, where
  `V = x_1 x_2 ⋯ x_N` is the product of all the variables (the sum is direct:
  `decomposition_unique`);
* `Z(ONH_N)` is the image of `Z(OΛ_N)` under the dot inclusion `Pol_N → ONH_N`;
* the printed statement holds, for `OΛ_N` and for `ONH_N`, exactly when `N` is even.

Objects. `Pol_N` is the integer skew polynomial ring with relations `x_i x_j = - x_j x_i`
(`i ≠ j`); `OΛ_N` is the joint kernel of the odd divided differences `∂_1, …, ∂_{N-1}`, a
subring of `Pol_N`; `ONH_N` is the odd nilHecke ring given by generators and relations;
`S_N` is the image of the symmetric polynomials under `X_j ↦ x_j^2`. Indices in Lean start
at `0`, and the rank is written `N = n + 2`.

Convention dependencies (the library's fixed sign conventions): `s_i(x_j) = -x_{s_i j}`;
`∂_i(fg) = ∂_i(f) g + s_i(f) ∂_i(g)`; `∂_i(x_i) = ∂_i(x_{i+1}) = 1`.
-/

namespace OddMath.Frontier.CenterCorrected
open OddMath.SkewPolynomial (SkewPolynomial)
open OddMath.Frontier.OddSymmetricKernel
open OddMath.Frontier.NilHeckeAction

/-- **Corrected EKL Prop. 2.15 for `OΛ_N`, every rank `N = n + 2`.** An odd symmetric
polynomial `z` is central in `OΛ_N` if and only if `z = a + V b` with `a, b` symmetric
polynomials in the squared variables, where the `V b` term is present only for odd `N`
(`V = x_1 ⋯ x_N`). Equivalently `Z(OΛ_N) = S_N` for even `N` and `S_N ⊕ V S_N` for odd
`N`. -/
theorem center_oddSymmetric (n : ℕ) (z : kernelSubring n) :
    z ∈ Subring.center (kernelSubring n) ↔
      ∃ a ∈ CenterPoly.sq n, ∃ b ∈ CenterPoly.sq n,
        (z : SkewPolynomial (n+2)) = a + (if Odd (n+2) then CenterPoly.V n * b else 0) := by
  rw [CenterONH.center_kernel, ← CenterPoly.kernel_inter_center]
  exact ⟨fun h => ⟨z.2, h⟩, fun h => h.2⟩

/-- **Corrected EKL Prop. 2.15 for `ONH_N`, every rank `N = n + 2`.** An element of the
odd nilHecke ring is central if and only if it is the dot image of `a + V b` with `a, b`
symmetric polynomials in the squared variables, where the `V b` term is present only for
odd `N`. Equivalently `Z(ONH_N)` is the dot image of `Z(OΛ_N)`. -/
theorem center_nilHecke (n : ℕ) (x : Presented n) :
    x ∈ Subring.center (Presented n) ↔
      ∃ a ∈ CenterPoly.sq n, ∃ b ∈ CenterPoly.sq n,
        x = OddMath.Frontier.CenterONH.polynomialInclusion n
          (a + (if Odd (n+2) then CenterPoly.V n * b else 0)) := by
  rw [CenterONH.center_nilHecke]
  constructor
  · rintro ⟨z, hzK, hzC, rfl⟩
    obtain ⟨a, ha, b, hb, hz⟩ := (CenterPoly.kernel_inter_center n z).mp ⟨hzK, hzC⟩
    exact ⟨a, ha, b, hb, by rw [hz]⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    obtain ⟨hK, hC⟩ := (CenterPoly.kernel_inter_center n _).mpr ⟨a, ha, b, hb, rfl⟩
    exact ⟨_, hK, hC, rfl⟩

/-- The sum `S_N + V · S_N` is direct: the decomposition `a + V b` with `a, b ∈ S_N` is
unique (in every rank; `a` has only entrywise-even exponents, `V b` only entrywise-odd). -/
theorem decomposition_unique (n : ℕ) {a b a' b' : SkewPolynomial (n+2)}
    (ha : a ∈ CenterPoly.sq n) (hb : b ∈ CenterPoly.sq n)
    (ha' : a' ∈ CenterPoly.sq n) (hb' : b' ∈ CenterPoly.sq n)
    (h : a + CenterPoly.V n * b = a' + CenterPoly.V n * b') : a = a' ∧ b = b' := by
  obtain ⟨p, _, rfl⟩ := (CenterPoly.mem_sq _).mp ha
  obtain ⟨q, _, rfl⟩ := (CenterPoly.mem_sq _).mp hb
  obtain ⟨p', _, rfl⟩ := (CenterPoly.mem_sq _).mp ha'
  obtain ⟨q', _, rfl⟩ := (CenterPoly.mem_sq _).mp hb'
  obtain ⟨hp, hq⟩ := CenterPoly.separate p q p' q' h
  exact ⟨hp ▸ rfl, hq ▸ rfl⟩

/-- **The printed statement for `OΛ_N` holds exactly in even rank.** For `N = n + 2`, the
assertion "`z ∈ OΛ_N` is central in `OΛ_N` iff `z` is a symmetric polynomial in the
squared variables" is true if and only if `N` is even. For odd `N` the product
`V = x_1 ⋯ x_N` is a central element of `OΛ_N` outside `S_N`. -/
theorem printed_iff_even (n : ℕ) :
    (∀ z : kernelSubring n,
      z ∈ Subring.center (kernelSubring n) ↔ (z : SkewPolynomial (n+2)) ∈ CenterPoly.sq n) ↔
      Even (n+2) := by
  constructor
  · intro hall
    by_contra hev
    have hodd := Nat.not_even_iff_odd.mp hev
    obtain ⟨hk, hc, hn⟩ := CenterPoly.odd_rank n hodd
    exact hn ((hall ⟨CenterPoly.V n, hk⟩).mp ((CenterONH.center_kernel _).mpr hc))
  · intro h z
    rw [CenterONH.center_kernel, ← CenterPoly.even_rank n h]
    exact ⟨fun hc => ⟨z.2, hc⟩, fun h' => h'.2⟩

/-- **The printed statement for `ONH_N` holds exactly in even rank.** For `N = n + 2`, the
assertion "the center of `ONH_N` is the dot image of the symmetric polynomials in the
squared variables" is true if and only if `N` is even. For odd `N` the dot image of
`V = x_1 ⋯ x_N` is central and is not the dot image of any element of `S_N`. -/
theorem printed_iff_even_nilHecke (n : ℕ) :
    (∀ x : Presented n,
      x ∈ Subring.center (Presented n) ↔
        ∃ a ∈ CenterPoly.sq n, x = OddMath.Frontier.CenterONH.polynomialInclusion n a) ↔
      Even (n+2) := by
  constructor
  · intro hall
    by_contra hev
    have hodd := Nat.not_even_iff_odd.mp hev
    obtain ⟨hk, hc, hn⟩ := CenterPoly.odd_rank n hodd
    obtain ⟨a, ha, he⟩ := (hall (CenterONH.polynomialInclusion n (CenterPoly.V n))).mp
      ((CenterONH.center_nilHecke _).mpr ⟨CenterPoly.V n, hk, hc, rfl⟩)
    exact hn (CenterONH.polynomialInclusion_injective he ▸ ha)
  · intro h x
    rw [CenterONH.center_nilHecke]
    constructor
    · rintro ⟨z, hzK, hzC, rfl⟩
      exact ⟨z, (CenterPoly.even_rank n h z).mp ⟨hzK, hzC⟩, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨hK, hC⟩ := (CenterPoly.even_rank n h a).mpr ha
      exact ⟨a, hK, hC, rfl⟩

end OddMath.Frontier.CenterCorrected
