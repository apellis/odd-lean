import OddMath.SKM.Bubbles

/-!
# The zero-weight odd bubble as an inverse-mate coefficient

Brundan–Ellis, arXiv:1701.04133v2, (2.10), (2.12), (2.18).
This identifies the precise coefficient to compute in a coupled action.
It does not construct that action or assume its bubble map is faithful.
-/

noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Presentation
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} (cs : CScalars Sc)

/-- At odd colour and weight zero, every normalized nonnegatively dotted
left bubble is a dotted-cap coefficient of the inverse source mate. -/
theorem normalized_bubL_zero_inverse_mate (i : I) (μ : X) (n : ℕ)
    (hi : D.parity i = 1) (hh : D.h i μ = 0)
    (t : (pres D Sc).obj (ob D μ [dn i, up i]) ⟶
      (pres D Sc).obj (ob D μ [up i, dn i]))
    (ht : t ≫ cl D Sc μ [up i, dn i] [dn i, up i] (sigmaL i i) = 𝟙 _) :
    (↑(cs.c μ i)⁻¹ : k) • bubL cs i μ n =
      cl D Sc μ [] [dn i, up i] (etaL i 0) ≫ t ≫
        cl D Sc μ [up i, dn i] [] (epsL i n) := by
  have hs := eq_2_12_a (Sc := Sc) i μ
  rw [hh] at hs
  simp only [Int.toNat_zero, Finset.range_zero, Finset.sum_empty, zero_sub] at hs
  rw [← cl_comp (sChain_sigmaL i i) (sChain_lcrossL i i)] at hs
  have hl : cl D Sc μ [dn i, up i] [up i, dn i] (lcrossL i i) = -t := by
    have h := congrArg (fun f => t ≫ f) hs
    simpa [← Category.assoc, ht, cl_nil] using h
  simp only [bubL, Int.natCast_nonneg, ite_true, Int.toNat_natCast, etaP, hh,
    lt_irrefl, ite_false, neg_zero, Int.toNat_zero, ipar, hi, Int.cast_zero,
    zero_add, mul_one, zsign, ite_false]
  rw [← cl_comp (sChain_etaL i 0) (sChain_lcrossL i i), hl]
  simp [Linear.smul_comp, smul_smul]

/-- At odd colour and weight zero, the normalized odd bubble is exactly
`cup ≫ inverse(source mate) ≫ cap`, with a positive sign. Only the stated
one-sided inverse equation is needed for this coefficient identity. -/
theorem oddBubble_zero_inverse_mate (i : I) (μ : X)
    (hi : D.parity i = 1) (hh : D.h i μ = 0)
    (t : (pres D Sc).obj (ob D μ [dn i, up i]) ⟶
      (pres D Sc).obj (ob D μ [up i, dn i]))
    (ht : t ≫ cl D Sc μ [up i, dn i] [dn i, up i] (sigmaL i i) = 𝟙 _) :
    oddBubble cs i μ =
      cl D Sc μ [] [dn i, up i] (etaL i 0) ≫ t ≫
        cl D Sc μ [up i, dn i] [] (epsL i 0) := by
  simpa only [oddBubble, hh, le_refl, ite_true, Nat.cast_zero] using
    normalized_bubL_zero_inverse_mate cs i μ 0 hi hh t ht

/-- Multiplication by a fixed coefficient series with constant term one
is injective on every finite coefficient window, even in a noncommutative
ring with zero divisors. This is the algebraic consumer of a proved ordered
bubble convolution formula; it does not supply that formula for an action. -/
theorem bubble_convolution_right_cancel_upto {R : Type*} [Ring R]
    (A A' P : ℕ → R) (N : ℕ) (hP : P 0 = 1)
    (h : ∀ n ≤ N,
      ∑ r ∈ Finset.range (n + 1), A (n - r) * P r =
      ∑ r ∈ Finset.range (n + 1), A' (n - r) * P r) :
    ∀ n ≤ N, A n = A' n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    have he := h n hn
    rw [Finset.sum_range_succ', Finset.sum_range_succ', Nat.sub_zero,
      hP, mul_one, mul_one] at he
    have hs :
        ∑ r ∈ Finset.range n, A (n - (r + 1)) * P (r + 1) =
        ∑ r ∈ Finset.range n, A' (n - (r + 1)) * P (r + 1) := by
      apply Finset.sum_congr rfl
      intro r hr
      have hrn := Finset.mem_range.mp hr
      rw [ih (n - (r + 1)) (by omega) (by omega)]
    rw [hs] at he
    exact add_left_cancel he

end OddMath.SKM
