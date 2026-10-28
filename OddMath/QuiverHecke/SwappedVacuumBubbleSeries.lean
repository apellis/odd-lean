/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedVacuumBlock

/-!
# The normalized bubble formula from the right-bubble moments

Research issue #345, toward the Nondegeneracy Conjecture of Brundan–Ellis,
*Super Kac–Moody 2-categories* (arXiv:1701.04133v2), §8. This file proves the
last step of the bubble computation of `SwappedVacuumBubbles.md` and
`SwappedVacuumNonpositiveBubbles.md` (§5, (15)): the elementary bubble images are
obtained from the right-bubble moments by the identity `E(z) H(-z) = 1`.

Fix probe exponents `M` and reservoir levels `N`, and write `G_i(z)` for the raw
generating series `1 + Σ e_(i,n) z^(n+1)`. Let `θ = SYM.probeSubstitution M N`,
so that `θ G_i(z) = G_i(-z) u_i(z)` with `u_i = (1 ∓ z)^(-M_i)`. The moment
series of colour `i` is `K_i(z) = u_i(z)⁻¹ G_i(-z)⁻¹` (`momentSeries`): this is
`(1-z)^P/E(-z)` at even colours and `(1+z)^M/C(-z)` at odd colours, the right-hand
side of (12) in both notes. The hypothesis `VacuumMoments` says that the
normalized right bubbles `c_(μ,i) · bubRs(l)` (even) and `c_(μ,i) · bubRs(2l)`
(odd) act on the source sector as the raw coefficients of `K_i`, and that the odd
bubble acts as `(-1)^(N_i+1) δ_i`.

The main result `VacuumMoments.bubbles_eq` derives (A16) from it: the
source-placed bubble algebra acts through `raw ∘ θ`. The proof uses Brundan–Ellis
(1.19)/(5.4) in the form `beta_h`, `betaD_h` (valid in the presentation, so for
every action), and the uniqueness of the left inverse of a series with constant
term one (`eq_of_sum_mul_eq_zero`).

The moment formula is uniform in the height: at even colours of height zero
(probe height zero, moments from the principal inverse of the equal-colour
crossing) the right moments are again `(1-z)^P/E(-z)`, with the sign `-q` of the
corrected even crossing entry on the leftward cup only, as the infinite
Grassmannian relation requires.
-/

noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams Finset
open scoped Classical TensorProduct
universe u

/-! ### Left inverses of series with constant term one -/

/-- Two sequences `x, y` with `x₀ = y₀ = 1`, each a left inverse of the series
`K` with `K₀ = 1` (`Σ_(s ≤ n) x_(n-s) K_s = 0` for `n > 0`), are equal. -/
theorem eq_of_sum_mul_eq_zero {R : Type*} [Ring R] {x y K : ℕ → R} (hK : K 0 = 1)
    (hx0 : x 0 = 1) (hy0 : y 0 = 1)
    (hx : ∀ n, 0 < n → ∑ s ∈ range (n + 1), x (n - s) * K s = 0)
    (hy : ∀ n, 0 < n → ∑ s ∈ range (n + 1), y (n - s) * K s = 0) (n : ℕ) : x n = y n := by
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    rcases n with _ | n
    · rw [hx0, hy0]
    · have h1 := hx (n + 1) n.succ_pos
      have h2 := hy (n + 1) n.succ_pos
      rw [sum_range_succ', Nat.sub_zero, hK, mul_one] at h1 h2
      have hsum : ∑ s ∈ range (n + 1), x (n + 1 - (s + 1)) * K (s + 1) =
          ∑ s ∈ range (n + 1), y (n + 1 - (s + 1)) * K (s + 1) :=
        sum_congr rfl fun s hs => by
          rw [mem_range] at hs
          rw [IH _ (by omega)]
      rw [hsum] at h1
      exact add_left_cancel (h1.trans h2.symm)

/-- The coefficients of a product of power series, in the form of
`eq_of_sum_mul_eq_zero`. -/
theorem coeff_mul_eq_sum_range {R : Type*} [CommRing R] (f g : PowerSeries R) (n : ℕ) :
    PowerSeries.coeff n (f * g) =
      ∑ s ∈ range (n + 1), PowerSeries.coeff (n - s) f * PowerSeries.coeff s g := by
  rw [PowerSeries.coeff_mul, ← Finset.Nat.sum_antidiagonal_swap]
  simp only [Prod.fst_swap, Prod.snd_swap]
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => PowerSeries.coeff j f * PowerSeries.coeff i g) n

/-- Applying an algebra map `φ` to `Σ_(r+s=n) (-1)^s e_r h_s = 0`: if
`φ(h_s) = (-1)^s K_s`, then `φ(e)` is a left inverse of the series `K`. -/
theorem sum_e_mul_eq_zero {k R : Type*} [CommRing k] [Ring R] [Algebra k R]
    (φ : SKM.Sym k →ₐ[k] R) (K : ℕ → R)
    (hK : ∀ s, φ (SKM.Sym.h s) = ((-1 : k) ^ s) • K s)
    (n : ℕ) (hn : 0 < n) : ∑ s ∈ range (n + 1), φ (SKM.Sym.e (n - s)) * K s = 0 := by
  have h := congrArg φ (SKM.Sym.e_h_rel n hn)
  rw [map_sum, map_zero] at h
  rw [← h]
  refine sum_congr rfl fun s _ => ?_
  have hs : ((-1 : SKM.Sym k) ^ s) = ((-1 : k) ^ s) • (1 : SKM.Sym k) := by
    rw [Algebra.smul_def, mul_one, map_pow, map_neg, map_one]
  rw [hs, smul_mul_assoc, one_mul, smul_mul_assoc, map_smul, map_mul, hK, mul_smul_comm, smul_smul,
    ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul]

/-! ### The substituted and moment series -/

namespace VacuumSeries
variable {I : Type u} (k : Type u) [CommRing k]

/-- The series `G_i(-z) u_i(z)` whose coefficients are the substituted generators. -/
def substitutedSeries (u : I → PowerSeries k) (i : I) :
    PowerSeries (MvPolynomial (I × ℕ) k) :=
  PowerSeries.rescale (-1) (OddMath.SKM.SYM.generatorSeries k i) *
    PowerSeries.map (algebraMap k (MvPolynomial (I × ℕ) k)) (u i)

/-- The moment series `w_i(z) G_i(-z)⁻¹`, with `w_i = u_i⁻¹`. -/
def momentSeries (w : I → PowerSeries k) (i : I) : PowerSeries (MvPolynomial (I × ℕ) k) :=
  PowerSeries.map (algebraMap k (MvPolynomial (I × ℕ) k)) (w i) *
    PowerSeries.invOfUnit (PowerSeries.rescale (-1) (OddMath.SKM.SYM.generatorSeries k i)) 1

theorem constantCoeff_rescale_generatorSeries (i : I) :
    PowerSeries.constantCoeff
      (PowerSeries.rescale (-1) (OddMath.SKM.SYM.generatorSeries k i)) =
        ((1 : (MvPolynomial (I × ℕ) k)ˣ) : _) := by
  rw [OddMath.SKM.SYM.constantCoeff_rescale, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [OddMath.SKM.SYM.generatorSeries, OddMath.SKM.SYM.generatorCoeff]

theorem substitutedSeries_mul_momentSeries {u w : I → PowerSeries k} (huw : ∀ i, u i * w i = 1)
    (i : I) : substitutedSeries k u i * momentSeries k w i = 1 := by
  have h := PowerSeries.mul_invOfUnit _ _ (constantCoeff_rescale_generatorSeries k i)
  have h' : PowerSeries.map (algebraMap k (MvPolynomial (I × ℕ) k)) (u i) *
      PowerSeries.map (algebraMap k (MvPolynomial (I × ℕ) k)) (w i) = 1 := by
    rw [← map_mul, huw i, map_one]
  calc substitutedSeries k u i * momentSeries k w i
      = (PowerSeries.rescale (-1) (OddMath.SKM.SYM.generatorSeries k i) *
          PowerSeries.invOfUnit (PowerSeries.rescale (-1)
            (OddMath.SKM.SYM.generatorSeries k i)) 1) *
        (PowerSeries.map (algebraMap k (MvPolynomial (I × ℕ) k)) (u i) *
          PowerSeries.map (algebraMap k (MvPolynomial (I × ℕ) k)) (w i)) := by
        unfold substitutedSeries momentSeries; ring
    _ = 1 := by rw [h, h', one_mul]

theorem coeff_zero_substitutedSeries {u : I → PowerSeries k}
    (hu : ∀ i, PowerSeries.constantCoeff (u i) = 1) (i : I) :
    PowerSeries.coeff 0 (substitutedSeries k u i) = 1 := by
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, substitutedSeries, map_mul,
    constantCoeff_rescale_generatorSeries, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply, hu i]
  simp

theorem coeff_succ_substitutedSeries (u : I → PowerSeries k) (i : I) (n : ℕ) :
    PowerSeries.coeff (n + 1) (substitutedSeries k u i) =
      OddMath.SKM.SYM.polynomialSubstitution k u (MvPolynomial.X (i, n)) := by
  simp [substitutedSeries, OddMath.SKM.SYM.polynomialSubstitution]

end VacuumSeries

/-! ### The moment hypothesis and (A16) -/

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  {D : SKM.Datum I X} {Sc : SKM.Scalars D k} (cs : SKM.CScalars Sc)

/-- The right-bubble moments of the source sector at probe exponents `M` and
reservoir levels `N`, in terms of the raw coefficient action `raw`: (12) and
(14) of `SwappedVacuumNonpositiveBubbles.md`, and their positive-height analogues
in `SwappedVacuumBubbles.md`. -/
structure VacuumMoments {μ : X} (A : UpwardModuleAction D Sc μ) (t : List I)
    (raw : SKM.SYM D k →ₐ[k] Module.End k (A.V t)) (M N : I → ℕ) : Prop where
  /-- Even colours: `Σ c·bubRs(l) z^l = (1-z)^(M_i)/E_i(-z)`. -/
  even : ∀ i (_ : D.parity i = 0) (s : ℕ),
    A.closedAct t ((cs.c μ i : k) • SKM.bubRs cs i μ s) =
      raw (SKM.SYM.polynomialInclude D k (PowerSeries.coeff s
        (VacuumSeries.momentSeries k (SKM.SYM.probeSeriesInv D k M) i)))
  /-- Odd colours: `Σ c·bubRs(2l) z^l = (1+z)^(M_i)/C_i(-z)`. -/
  odd : ∀ i (_ : D.parity i = 1) (s : ℕ),
    A.closedAct t ((cs.c μ i : k) • SKM.bubRs cs i μ (2 * s)) =
      raw (SKM.SYM.polynomialInclude D k (PowerSeries.coeff s
        (VacuumSeries.momentSeries k (SKM.SYM.probeSeriesInv D k M) i)))
  /-- The odd bubble acts as `(-1)^(N_i+1) δ_i`. -/
  oddBubble : ∀ i : {i : I // D.parity i = 1},
    A.closedAct t (SKM.oddBubble cs i μ) = raw (SKM.SYM.probeSign D k N i • SKM.SYM.delta D k i)

namespace VacuumMoments
variable {cs} {μ : X} {A : UpwardModuleAction D Sc μ} {t : List I}
  {raw : SKM.SYM D k →ₐ[k] Module.End k (A.V t)} {M N : I → ℕ}

/-- The raw images of the coefficients of the substituted series are a left
inverse of the moments. -/
theorem raw_sum_mul_eq_zero (i : I) (K : ℕ → Module.End k (A.V t))
    (hK : ∀ s, K s = raw (SKM.SYM.polynomialInclude D k (PowerSeries.coeff s
      (VacuumSeries.momentSeries k (SKM.SYM.probeSeriesInv D k M) i)))) (n : ℕ) (hn : 0 < n) :
    ∑ s ∈ range (n + 1), raw (SKM.SYM.polynomialInclude D k (PowerSeries.coeff (n - s)
      (VacuumSeries.substitutedSeries k (SKM.SYM.probeSeries D k M) i))) * K s = 0 := by
  simp_rw [hK, ← map_mul, ← map_sum]
  rw [← coeff_mul_eq_sum_range,
    VacuumSeries.substitutedSeries_mul_momentSeries k (SKM.SYM.probeSeries_mul_inv D k M),
    PowerSeries.coeff_one]
  simp [hn.ne']

/-- The generator images of `θ` are the coefficients of the substituted series. -/
theorem probeSubstitution_e (i : I) (n : ℕ) :
    SKM.SYM.probeSubstitution D k M N (SKM.SYM.e D k i n) =
      SKM.SYM.polynomialInclude D k (PowerSeries.coeff (n + 1)
        (VacuumSeries.substitutedSeries k (SKM.SYM.probeSeries D k M) i)) := by
  rw [VacuumSeries.coeff_succ_substitutedSeries]
  exact SKM.SYM.substitutionHom_e D k _ _ i n

/-- One colour: if the bubble generator `e_(i,n)` acts as `φ(e_(n+1))` for an algebra
map `φ` with `φ(h_s) = (-1)^s K_s`, and `K` is the moment series, then `e_(i,n)` acts
as `θ(e_(i,n))`. -/
theorem bubbles_e_of_moments (i : I) (n : ℕ) (φ : SKM.Sym k →ₐ[k] Module.End k (A.V t))
    (K : ℕ → Module.End k (A.V t)) (hK0 : K 0 = 1)
    (hφ : ∀ s, φ (SKM.Sym.h s) = ((-1 : k) ^ s) • K s)
    (hK : ∀ s, K s = raw (SKM.SYM.polynomialInclude D k (PowerSeries.coeff s
      (VacuumSeries.momentSeries k (SKM.SYM.probeSeriesInv D k M) i))))
    (hb : A.bubbles cs t (SKM.SYM.e D k i n) = φ (SKM.Sym.e (n + 1))) :
    A.bubbles cs t (SKM.SYM.e D k i n) =
      raw (SKM.SYM.probeSubstitution D k M N (SKM.SYM.e D k i n)) := by
  have key := eq_of_sum_mul_eq_zero (x := fun r => φ (SKM.Sym.e r))
    (y := fun r => raw (SKM.SYM.polynomialInclude D k (PowerSeries.coeff r
      (VacuumSeries.substitutedSeries k (SKM.SYM.probeSeries D k M) i)))) hK0
    (by rw [SKM.Sym.e_zero, map_one])
    (by rw [VacuumSeries.coeff_zero_substitutedSeries k (SKM.SYM.constantCoeff_probeSeries D k M),
      map_one, map_one]) (sum_e_mul_eq_zero φ K hφ) (raw_sum_mul_eq_zero i K hK) (n + 1)
  rw [hb, key, probeSubstitution_e]

/-- The normalized right bubbles `c · bubRs(m s)` acting on the source sector. -/
def rightMoment (A : UpwardModuleAction D Sc μ) (t : List I) (i : I) (m s : ℕ) :
    Module.End k (A.V t) :=
  A.closedAct t ((cs.c μ i : k) • SKM.bubRs cs i μ ((m * s : ℕ) : ℤ))

theorem rightMoment_zero (A : UpwardModuleAction D Sc μ) (t : List I) (i : I) (m : ℕ) :
    rightMoment (cs := cs) A t i m 0 = 1 := by
  simp only [rightMoment, mul_zero, Nat.cast_zero, SKM.bubRs_zero, smul_smul, Units.mul_inv,
    one_smul]
  exact map_one _

/-- Even colours: from the moments to the elementary images. -/
theorem bubbles_e_even (i : I) (hi : D.parity i = 0)
    (hK : ∀ s : ℕ, A.closedAct t ((cs.c μ i : k) • SKM.bubRs cs i μ s) =
      raw (SKM.SYM.polynomialInclude D k (PowerSeries.coeff s
        (VacuumSeries.momentSeries k (SKM.SYM.probeSeriesInv D k M) i)))) (n : ℕ) :
    A.bubbles cs t (SKM.SYM.e D k i n) =
      raw (SKM.SYM.probeSubstitution D k M N (SKM.SYM.e D k i n)) :=
  bubbles_e_of_moments i n ((A.closedAct t).comp (SKM.beta cs i μ hi))
    (rightMoment (cs := cs) A t i 1) (rightMoment_zero (cs := cs) A t i 1)
    (fun s => by
      simp only [rightMoment, one_mul, AlgHom.comp_apply, SKM.beta_h, map_smul, smul_smul])
    (fun s => by simpa only [rightMoment, one_mul] using hK s)
    (by rw [UpwardModuleAction.bubbles, AlgHom.comp_apply, SKM.betaSYM_e_even cs μ i hi,
      ← SKM.Sym.e_succ, AlgHom.comp_apply])

/-- Odd colours: from the moments to the elementary images. -/
theorem bubbles_e_odd (i : I) (hi : D.parity i = 1)
    (hK : ∀ s : ℕ, A.closedAct t ((cs.c μ i : k) • SKM.bubRs cs i μ (2 * s)) =
      raw (SKM.SYM.polynomialInclude D k (PowerSeries.coeff s
        (VacuumSeries.momentSeries k (SKM.SYM.probeSeriesInv D k M) i)))) (n : ℕ) :
    A.bubbles cs t (SKM.SYM.e D k i n) =
      raw (SKM.SYM.probeSubstitution D k M N (SKM.SYM.e D k i n)) :=
  bubbles_e_of_moments i n
    ((A.closedAct t).comp ((SKM.betaD cs i μ hi).comp SKM.SymD.ofSym))
    (rightMoment (cs := cs) A t i 2) (rightMoment_zero (cs := cs) A t i 2)
    (fun s => by
      simp only [rightMoment, AlgHom.comp_apply, SKM.betaD_h, map_smul, smul_smul]
      push_cast; rfl)
    (fun s => by simpa only [rightMoment, Nat.cast_mul, Nat.cast_ofNat] using hK s)
    (by rw [UpwardModuleAction.bubbles, AlgHom.comp_apply, SKM.betaSYM_e_odd cs μ i hi,
      ← SKM.Sym.e_succ, AlgHom.comp_apply, AlgHom.comp_apply])

/-- **(A16)** from the moments: the source-placed bubble algebra acts through
`raw ∘ θ`. -/
theorem bubbles_eq (h : VacuumMoments cs A t raw M N) (a : SKM.SYM D k) :
    A.bubbles cs t a = raw (SKM.SYM.probeSubstitution D k M N a) := by
  have e : A.bubbles cs t = raw.comp (SKM.SYM.probeSubstitution D k M N).toAlgHom := by
    apply SKM.SYM.hom_ext
    rintro (⟨i, n⟩ | i)
    · show A.bubbles cs t (SKM.SYM.e D k i n) = _
      by_cases hi : D.parity i = 0
      · exact bubbles_e_even i hi (h.even i hi) n
      · have hi' := SKM.zmod2_eq_one_of_ne_zero hi
        exact bubbles_e_odd i hi' (h.odd i hi') n
    · show A.bubbles cs t (SKM.SYM.delta D k i) = _
      rw [UpwardModuleAction.bubbles, AlgHom.comp_apply, SKM.betaSYM_delta, h.oddBubble i]
      show _ = raw (SKM.SYM.substitutionHom D k (SKM.SYM.probeSeries D k M)
        (SKM.SYM.probeSign D k N) (SKM.SYM.delta D k i))
      rw [SKM.SYM.substitutionHom_delta]
  rw [e]; rfl

/-- **(A16)** at the vacuum schedule: the field `SwappedVacuumBlock.bubbles_eq`. -/
theorem vacuum_bubbles_eq {d : ℕ}
    (h : VacuumMoments cs A t raw (probeExponent D μ t d) (reservoirLevel D μ t d))
    (a : SKM.SYM D k) : A.bubbles cs t a = raw (vacuumSubstitution D k μ t d a) :=
  h.bubbles_eq a

end VacuumMoments

end OddMath.QuiverHecke
