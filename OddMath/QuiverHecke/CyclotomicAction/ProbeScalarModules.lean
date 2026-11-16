import OddMath.QuiverHecke.CyclotomicAction.SignedIntertwiner
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import OddMath.QuiverHecke.CyclotomicAction.SuperQuotient
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.Nilpotent.Basic
import OddMath.QuiverHecke.CyclotomicAction.PrefixScalarRelations
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.Polynomial.Coeff
import OddMath.QuiverHecke.CyclotomicAction.EndpointPolynomials
import OddMath.QuiverHecke.CyclotomicAction.TruncatedAppend
import OddMath.QuiverHecke.CyclotomicAction.ContentModules
import OddMath.QuiverHecke.CyclotomicAction.ParabolicTransport
import OddMath.QuiverHecke.CyclotomicAction.GlobalInduction
import OddMath.QuiverHecke.CyclotomicAction.AppendMackey
import Mathlib.Tactic.FinCases
import OddMath.QuiverHecke.CyclotomicAction.VacuumGrading
import OddMath.QuiverHecke.CyclotomicAction.MovingShiftRelations
import OddMath.QuiverHecke.CyclotomicAction.ModuleInduction
import Mathlib.LinearAlgebra.Quotient.Bilinear
import StringDiagrams.Super.SVecQuotient
import OddMath.QuiverHecke.CyclotomicAction.CyclotomicQuotientTop
import OddMath.QuiverHecke.CyclotomicAction.AppendBalance

/-!
# Probe scalar modules

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # Kernel propagation for probe dots

The equal-colour step of `InvertibleDotProbe.md` §3 needs only the kernel
of the next dot. The nilHecke intertwiner carries that kernel into the
kernel of the preceding dot; its square then detects the original vector.
The kernel statements use no finite-dimensionality or generalized zero-primary
decomposition. The final unit corollaries use finite-dimensionality only to
turn injective multiplication into bijective multiplication.
-/
namespace OddMath.QuiverHecke.SignedNilHecke
variable {B : Type*} [Ring B]

theorem EvenTwo.right_mul_eq_zero {u v T z : B} (h : EvenTwo u v T)
    (hu : Function.Injective (fun x : B => u * x)) (hz : v * z = 0) : z = 0 := by
  have hp : phiEven u v T * z = 0 := by
    apply hu
    change u * (phiEven u v T * z) = u * 0
    rw [mul_zero, ← mul_assoc, h.x_mul_phiEven, mul_assoc, hz, mul_zero]
  have hs := congrArg (fun a : B => a * z) h.phiEven_mul_phiEven
  simpa only [mul_assoc, hp, mul_zero, one_mul] using hs.symm

theorem EvenTwo.right_mul_injective {u v T : B} (h : EvenTwo u v T)
    (hu : Function.Injective (fun x : B => u * x)) :
    Function.Injective (fun x : B => v * x) := by
  intro x y hxy
  change v * x = v * y at hxy
  apply sub_eq_zero.mp
  exact h.right_mul_eq_zero hu (by rw [mul_sub, hxy, sub_self])

theorem OddTwo.right_mul_eq_zero {u v T z : B} (h : OddTwo u v T)
    (hu : Function.Injective (fun x : B => u * x)) (hz : v * z = 0) : z = 0 := by
  have hp : phiOdd u v T * z = 0 := by
    apply hu
    change u * (phiOdd u v T * z) = u * 0
    rw [mul_zero, ← mul_assoc, h.x_mul_phiOdd, neg_mul, mul_assoc, hz,
      mul_zero, neg_zero]
  have hvu : v * (u * z) = 0 := by
    rw [← mul_assoc, h.vu', neg_mul, mul_assoc, hz, mul_zero, neg_zero]
  have hs := congrArg (fun a : B => a * z) h.phiOdd_mul_phiOdd
  have huu : u * (u * z) = 0 := by
    simpa only [mul_assoc, hp, mul_zero, sub_mul, mul_sub, hz,
      zero_sub, mul_neg, hvu, neg_zero, sub_neg_eq_add, zero_add] using hs.symm
  apply hu
  change u * z = u * 0
  rw [mul_zero]
  exact hu (by simpa only [mul_zero] using huu)

theorem OddTwo.right_mul_injective {u v T : B} (h : OddTwo u v T)
    (hu : Function.Injective (fun x : B => u * x)) :
    Function.Injective (fun x : B => v * x) := by
  intro x y hxy
  change v * x = v * y at hxy
  apply sub_eq_zero.mp
  exact h.right_mul_eq_zero hu (by rw [mul_sub, hxy, sub_self])

section FiniteDimensional
variable {k : Type*} [Field k] [Algebra k B] [FiniteDimensional k B]
include k

end FiniteDimensional

end OddMath.QuiverHecke.SignedNilHecke

end

section

/-! # Probe dot propagation in actual cyclotomic word corners

The equal-colour step of `InvertibleDotProbe.md` §3 uses the existing
cyclotomic algebra and its literal word idempotent corner. The affine
word endomorphism map is unital into this corner, even when the corner
vanishes. No second quotient presentation is introduced.
-/
noncomputable section
open CategoryTheory StringDiagrams
open scoped Classical
namespace OddMath.QuiverHecke
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X]
  {k : Type w} [CommRing k] (D : SKM.Datum I X) (Sc : SKM.Scalars D k)
  [Fintype I] (a : I → Polynomial k)

def cyclotomicWordIdempotent {n : ℕ} (s : Word I (n + 1)) :
    CyclotomicAlgebra D Sc a n :=
  cyclotomicMk D Sc a n (Hn.wordIdempotent s)

theorem cyclotomicWordIdempotent_idem {n : ℕ} (s : Word I (n + 1)) :
    IsIdempotentElem (cyclotomicWordIdempotent D Sc a s) := by
  change cyclotomicMk D Sc a n _ * cyclotomicMk D Sc a n _ = _
  rw [← map_mul, Hn.wordIdempotent_sq]
  rfl

abbrev CyclotomicWordCorner {n : ℕ} (s : Word I (n + 1)) :=
  (cyclotomicWordIdempotent_idem D Sc a s).Corner

/-- Literal diagonal insertion followed by the actual cyclotomic quotient,
with its codomain restricted to the word corner whose identity is e_s. -/
def cyclotomicWordEnd {n : ℕ} (s : Word I (n + 1)) :
    End (wordObj D Sc s) →+* CyclotomicWordCorner D Sc a s where
  toFun f := ⟨cyclotomicMk D Sc a n (Hn.cornerInclusion s f), by
    apply (Subsemigroup.mem_corner_iff (cyclotomicWordIdempotent_idem D Sc a s)).mpr
    constructor
    · change cyclotomicMk D Sc a n (FiniteHomMatrix.single s s (𝟙 _)) *
        cyclotomicMk D Sc a n (FiniteHomMatrix.single s s f) = _
      rw [← map_mul, FiniteHomMatrix.single_mul_single, Category.comp_id]
      rfl
    · change cyclotomicMk D Sc a n (FiniteHomMatrix.single s s f) *
        cyclotomicMk D Sc a n (FiniteHomMatrix.single s s (𝟙 _)) = _
      rw [← map_mul, FiniteHomMatrix.single_mul_single, Category.id_comp]
      rfl⟩
  map_one' := Subtype.ext rfl
  map_zero' := Subtype.ext (by
    change cyclotomicMk D Sc a n (Hn.cornerInclusion s 0) = 0
    rw [map_zero, map_zero])
  map_add' f g := Subtype.ext (by
    change cyclotomicMk D Sc a n (Hn.cornerInclusion s (f + g)) =
      cyclotomicMk D Sc a n (Hn.cornerInclusion s f) +
        cyclotomicMk D Sc a n (Hn.cornerInclusion s g)
    rw [map_add, map_add])
  map_mul' f g := Subtype.ext (by
    change cyclotomicMk D Sc a n (Hn.cornerInclusion s (f * g)) =
      cyclotomicMk D Sc a n (Hn.cornerInclusion s f) *
        cyclotomicMk D Sc a n (Hn.cornerInclusion s g)
    rw [map_mul, map_mul])

def probeBlockWord (pre post : List I) (i : I) :
    Word I ((pre.length + post.length + 1) + 1) :=
  ⟨pre ++ [i,i] ++ post, by simp; omega⟩

/-- The actual defining first-dot relation, now in the unital word corner. -/
theorem cyclotomicWordEnd_generator {n : ℕ} (s : Word I (n + 1)) :
    cyclotomicWordEnd D Sc a s
      (Polynomial.aeval (dotE D Sc s.val 0)
        (a (s.val.get ⟨0, by rw [s.property]; omega⟩))) = 0 := by
  apply Subtype.ext
  change cyclotomicMk D Sc a n (cyclotomicGenerator D Sc a s) = 0
  exact cyclotomicMk_generator D Sc a s

abbrev cyclotomicBlockDot (pre post : List I) (i : I) (r : ℕ) :
    CyclotomicWordCorner D Sc a (probeBlockWord pre post i) :=
  cyclotomicWordEnd D Sc a (probeBlockWord pre post i)
    (dotE D Sc (pre ++ [i,i] ++ post) r)

abbrev cyclotomicBlockCross (pre post : List I) (i : I) :
    CyclotomicWordCorner D Sc a (probeBlockWord pre post i) :=
  cyclotomicWordEnd D Sc a (probeBlockWord pre post i)
    (crossE D Sc (pre ++ [i,i] ++ post) pre.length)

private theorem oddTwo_map {R S : Type*} [Ring R] [Ring S] (q : R →+* S)
    {u v T : R} (h : SignedNilHecke.OddTwo u v T) :
    SignedNilHecke.OddTwo (q u) (q v) (q T) where
  t_u := by simpa only [map_add, map_mul, map_one] using congrArg q h.t_u
  u_t := by simpa only [map_add, map_mul, map_one] using congrArg q h.u_t
  u_v := by simpa only [map_mul, map_neg] using congrArg q h.u_v
  t_t := by simpa only [map_mul, map_zero] using congrArg q h.t_t

private theorem evenTwo_map {R S : Type*} [Ring R] [Ring S] (q : R →+* S)
    {u v T : R} (h : SignedNilHecke.EvenTwo u v T) :
    SignedNilHecke.EvenTwo (q u) (q v) (q T) where
  t_u := by simpa only [map_sub, map_mul, map_one] using congrArg q h.t_u
  u_t := by simpa only [map_sub, map_mul, map_one] using congrArg q h.u_t
  u_v := by simpa only [map_mul] using congrArg q h.u_v
  t_t := by simpa only [map_mul, map_zero] using congrArg q h.t_t

theorem cyclotomicBlock_oddTwo (pre post : List I) (i : I) (hi : D.parity i = 1) :
    SignedNilHecke.OddTwo (cyclotomicBlockDot D Sc a pre post i pre.length)
      (cyclotomicBlockDot D Sc a pre post i (pre.length + 1))
      (cyclotomicBlockCross D Sc a pre post i) := by
  exact oddTwo_map (cyclotomicWordEnd D Sc a (probeBlockWord pre post i))
    (oddTwo_block D Sc pre post i hi)

theorem cyclotomicBlock_evenTwo (pre post : List I) (i : I) (hi : D.parity i = 0) :
    SignedNilHecke.EvenTwo (cyclotomicBlockDot D Sc a pre post i pre.length)
      (cyclotomicBlockDot D Sc a pre post i (pre.length + 1))
      (cyclotomicBlockCross D Sc a pre post i) := by
  exact evenTwo_map (cyclotomicWordEnd D Sc a (probeBlockWord pre post i))
    (evenTwo_block D Sc pre post i hi)

end OddMath.QuiverHecke
end

end

section

/-! # First-dot units for cofinal cyclotomic probes

The specializations `(u²-1)^m` at odd colours and `(u-1)^m` at even
colours in `InvertibleDotProbe.md` §3 give literal units in the actual
cyclotomic word corner. Exponents and powers may vary with colour.
-/
noncomputable section
open CategoryTheory StringDiagrams
open scoped Classical
namespace OddMath.QuiverHecke
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X]
  {k : Type w} [CommRing k] (D : SKM.Datum I X) (Sc : SKM.Scalars D k)
  [Fintype I]

def probePolynomial (e m : I → ℕ) (i : I) : Polynomial k :=
  (Polynomial.X ^ e i - 1) ^ m i

/-- The first-position relation itself supplies a unit; its proof does not
require finite dimensionality, a nonzero word, or a flat specialization. -/
theorem probePolynomial_firstDot_isUnit (e m : I → ℕ) {n : ℕ}
    (s : Word I (n + 1))
    (he : e (s.val.get ⟨0, by rw [s.property]; omega⟩) ≠ 0) :
    IsUnit (cyclotomicWordEnd D Sc (probePolynomial e m) s (dotE D Sc s.val 0)) := by
  let i := s.val.get ⟨0, by rw [s.property]; omega⟩
  let x := cyclotomicWordEnd D Sc (probePolynomial e m) s (dotE D Sc s.val 0)
  have hx : IsNilpotent (x ^ e i - 1) := by
    refine ⟨m i, ?_⟩
    have h := cyclotomicWordEnd_generator D Sc (probePolynomial e m) s
    simpa only [probePolynomial, map_pow, map_sub, Polynomial.aeval_X, map_one, map_zero,
      i, x] using h
  have hunit : IsUnit (x ^ e i) := by
    simpa only [add_sub_cancel] using hx.isUnit_one_add
  exact (isUnit_pow_iff he).mp hunit

/-- The exponent dictated by the parity of the simple root. -/
def probeDotExponent (i : I) : ℕ := if D.parity i = 1 then 2 else 1

theorem probe_firstDot_isUnit (m : I → ℕ) {n : ℕ} (s : Word I (n + 1)) :
    IsUnit (cyclotomicWordEnd D Sc (probePolynomial (probeDotExponent D) m) s
      (dotE D Sc s.val 0)) := by
  apply probePolynomial_firstDot_isUnit
  simp only [probeDotExponent]
  split_ifs <;> decide

end OddMath.QuiverHecke
end

end

section

/-! # Binomial scalar specialization of ELV cyclotomic coefficients
This gives the prescribed colourwise probe specialization of
InvertibleDotProbe.md Section 1: odd exterior parameters vanish, and the
elementary parameters specialize to binomial coefficients. The literal
source first-dot polynomials become the prescribed probes in both parities.
-/
noncomputable section
open CategoryTheory StringDiagrams
open OddMath.SKM.SYM
open scoped Classical
namespace OddMath.QuiverHecke
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (m : I → ℕ)

/-- The colourwise degree of the prescribed probe polynomial. -/
def probeCutoff (i : I) : ℕ := probeDotExponent D i * m i

/-- Elementary coefficient values giving the odd/even binomial probes. -/
def probeScalarValues (p : I × ℕ) : k :=
  if D.parity p.1 = 1 then
    (-1 : k) ^ (p.2 + 1) * (Nat.choose (m p.1) (p.2 + 1) : k)
  else (Nat.choose (m p.1) (p.2 + 1) : k)

theorem probeCutoff_elementaryRank (i : I) :
    elvElementaryRank D (probeCutoff D m) i = m i := by
  rcases Supercategory.parity_eq_zero_or_one (D.parity i) with hi | hi
  · simp [elvElementaryRank, probeCutoff, probeDotExponent, hi]
  · simp [elvElementaryRank, probeCutoff, probeDotExponent, hi, Nat.mul_comm]

theorem probeScalarValues_vanish (i : I) (r : ℕ)
    (hr : elvElementaryRank D (probeCutoff D m) i ≤ r) :
    probeScalarValues (k := k) D m (i,r) = 0 := by
  rw [probeCutoff_elementaryRank] at hr
  have hc : Nat.choose (m i) (r+1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
  simp [probeScalarValues, hc]

theorem scalarEvaluation_probe_elvChi (i : {i : I // D.parity i = 1}) (r : ℕ) :
    scalarEvaluation D (probeScalarValues (k := k) D m) (elvChi D k i r) =
      (-1 : k)^r * (Nat.choose (m i.1) r : k) := by
  cases r with
  | zero => simp [elvChi]
  | succ r => simp [elvChi, probeScalarValues, i.property]

theorem scalarEvaluation_probe_evenCoefficient (i : I) (hi : D.parity i = 0) (r : ℕ) :
    scalarEvaluation D (probeScalarValues (k := k) D m) (evenCyclotomicCoefficient D k i r) =
      (Nat.choose (m i) r : k) := by
  cases r with
  | zero => simp [evenCyclotomicCoefficient]
  | succ r => simp [evenCyclotomicCoefficient, probeScalarValues, hi]

private theorem binomial_probe_coeff (N r : ℕ) :
    ((Polynomial.X - 1 : Polynomial k)^N).coeff r =
      (-1 : k)^(N-r) * (Nat.choose N r : k) := by
  simpa only [Polynomial.C_neg, Polynomial.C_1, sub_eq_add_neg] using
    Polynomial.coeff_X_add_C_pow (-1 : k) N r

private theorem odd_binomial_probe_coeff (N r : ℕ) :
    ((Polynomial.X^2 - 1 : Polynomial k)^N).coeff r =
      if 2 ∣ r then (-1 : k)^(N-r/2) * (Nat.choose N (r/2) : k) else 0 := by
  have he : (Polynomial.X^2 - 1 : Polynomial k)^N =
      Polynomial.expand k 2 ((Polynomial.X - 1)^N) := by
    simp only [map_pow, map_sub, Polynomial.expand_X, map_one]
  rw [he, Polynomial.coeff_expand (by decide)]
  simp only [binomial_probe_coeff]

private theorem scalarCoefficientPolynomial_coeff_fin (values : I × ℕ → k)
    (N : ℕ) (c : Fin (N+1) → SKM.SYM D k) (j : Fin (N+1)) :
    (scalarCoefficientPolynomial D values N c).coeff j.val = scalarEvaluation D values (c j) := by
  simp only [scalarCoefficientPolynomial, Polynomial.finsetSum_coeff,
    Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  rw [Finset.sum_eq_single j]
  · simp
  · intro z _ hz
    have hjz : j.val ≠ z.val := fun he => hz (Fin.ext he.symm)
    simp [hjz]
  · simp

private theorem scalarCoefficientPolynomial_coeff_large (values : I × ℕ → k)
    (N : ℕ) (c : Fin (N+1) → SKM.SYM D k) (r : ℕ) (hr : N < r) :
    (scalarCoefficientPolynomial D values N c).coeff r = 0 := by
  simp only [scalarCoefficientPolynomial, Polynomial.finsetSum_coeff,
    Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  apply Finset.sum_eq_zero
  intro j _
  have hjr : r ≠ j.val := by have := j.isLt; omega
  simp [hjr]

/-- Even source coefficients specialize to the prescribed binomial probe. -/
theorem scalarCoefficientPolynomial_probe_even (i : I) (hi : D.parity i = 0) :
    scalarCoefficientPolynomial D (probeScalarValues (k := k) D m) (m i)
      (evenMonicCoefficient D k i (m i)) = (Polynomial.X - 1)^m i := by
  apply Polynomial.ext
  intro r
  by_cases hr : r ≤ m i
  · let j : Fin (m i+1) := ⟨r, by omega⟩
    rw [show r = j.val from rfl, scalarCoefficientPolynomial_coeff_fin,
      binomial_probe_coeff]
    simp only [evenMonicCoefficient, map_smul, scalarEvaluation_probe_evenCoefficient D m i hi]
    change (-1 : k)^(m i-j.val) * (Nat.choose (m i) (m i-j.val) : k) = _
    rw [Nat.choose_symm hr]
  · rw [scalarCoefficientPolynomial_coeff_large D _ _ _ r (by omega), binomial_probe_coeff,
      Nat.choose_eq_zero_of_lt (by omega : m i < r), Nat.cast_zero, mul_zero]

private theorem probe_half_sub (N r : ℕ) (hr : r ≤ 2*N) (he : r % 2 = 0) :
    (2*N-r)/2 = N-r/2 := by omega

/-- Odd source coefficients specialize to the prescribed even-exponent binomial probe. -/
theorem scalarCoefficientPolynomial_probe_odd (i : {i : I // D.parity i = 1}) :
    scalarCoefficientPolynomial D (probeScalarValues (k := k) D m) (2*m i.1)
      (elvMonicCoefficient D k i (2*m i.1)) = (Polynomial.X^2 - 1)^m i.1 := by
  apply Polynomial.ext
  intro r
  by_cases hr : r ≤ 2*m i.1
  · let j : Fin (2*m i.1+1) := ⟨r, by omega⟩
    rw [show r = j.val from rfl, scalarCoefficientPolynomial_coeff_fin, odd_binomial_probe_coeff]
    have he : Even (2*m i.1*(j.val+1)) := ⟨m i.1*(j.val+1), by ring⟩
    simp only [elvMonicCoefficient, he.neg_one_pow, one_smul]
    by_cases hj : j.val % 2 = 0
    · have hrem : (2*m i.1-j.val) % 2 = 0 := by change r % 2 = 0 at hj; dsimp [j]; omega
      have hdiv : (2*m i.1-j.val)/2 = m i.1-j.val/2 :=
        probe_half_sub (m i.1) j.val (by change r ≤ 2*m i.1; exact hr) hj
      have hle : j.val/2 ≤ m i.1 := by dsimp [j]; omega
      rw [elvCoefficient, ite_eq_left hrem, scalarEvaluation_probe_elvChi, hdiv,
        ite_eq_left (Nat.dvd_of_mod_eq_zero hj), Nat.choose_symm hle]
    · have hrem : (2*m i.1-j.val) % 2 ≠ 0 := by dsimp [j] at *; omega
      have hnd : ¬ 2 ∣ j.val := fun hd => hj (Nat.mod_eq_zero_of_dvd hd)
      simp [elvCoefficient, hrem, hnd]
  · rw [scalarCoefficientPolynomial_coeff_large D _ _ _ r (by omega), odd_binomial_probe_coeff]
    split_ifs with hd
    · have hrem : r % 2 = 0 := Nat.mod_eq_zero_of_dvd hd
      have hlt : m i.1 < r/2 := by omega
      rw [Nat.choose_eq_zero_of_lt hlt, Nat.cast_zero, mul_zero]
    · rfl

/-- The actual monic coefficient family at the prescribed probe cutoff. -/
def probeMonicCoefficient (i : I) (j : Fin (probeCutoff D m i+1)) : SKM.SYM D k :=
  if hi : D.parity i = 1 then elvMonicCoefficient D k ⟨i,hi⟩ (probeCutoff D m i) j
  else evenMonicCoefficient D k i (probeCutoff D m i) j

private theorem scalarCoefficientPolynomial_reindex {N M : ℕ} (hNM : N = M)
    (values : I × ℕ → k) (c : Fin (N+1) → SKM.SYM D k) (d : Fin (M+1) → SKM.SYM D k)
    (hcd : ∀ j, c j = d (Fin.cast (congrArg (fun n => n+1) hNM) j)) :
    scalarCoefficientPolynomial D values N c = scalarCoefficientPolynomial D values M d := by
  subst M
  congr 1
  funext j
  simpa only [Fin.cast_refl, id_eq] using hcd j

theorem scalarCoefficientPolynomial_probe (i : I) :
    scalarCoefficientPolynomial D (probeScalarValues (k := k) D m) (probeCutoff D m i)
      (probeMonicCoefficient (k := k) D m i) = probePolynomial (k := k) (probeDotExponent D) m i := by
  rcases Supercategory.parity_eq_zero_or_one (D.parity i) with hi | hi
  · have hcut : probeCutoff D m i = m i := by simp [probeCutoff, probeDotExponent, hi]
    have hc : ∀ j : Fin (probeCutoff D m i+1), probeMonicCoefficient (k := k) D m i j =
        evenMonicCoefficient D k i (m i) (Fin.cast (congrArg (fun n => n+1) hcut) j) := by
      intro j
      unfold probeMonicCoefficient
      simp only [hi, zero_ne_one, ↓reduceDIte]
      unfold evenMonicCoefficient
      simp only [Fin.val_cast, hcut]
    rw [scalarCoefficientPolynomial_reindex D hcut _ _ _ hc,
      scalarCoefficientPolynomial_probe_even D m i hi]
    simp [probePolynomial, probeDotExponent, hi]
  · have hcut : probeCutoff D m i = 2*m i := by simp [probeCutoff, probeDotExponent, hi]
    have hc : ∀ j : Fin (probeCutoff D m i+1), probeMonicCoefficient (k := k) D m i j =
        elvMonicCoefficient D k ⟨i,hi⟩ (2*m i) (Fin.cast (congrArg (fun n => n+1) hcut) j) := by
      intro j
      unfold probeMonicCoefficient
      simp only [hi, ↓reduceDIte]
      unfold elvMonicCoefficient
      simp only [Fin.val_cast, hcut]
    rw [scalarCoefficientPolynomial_reindex D hcut _ _ _ hc,
      scalarCoefficientPolynomial_probe_odd D m ⟨i,hi⟩]
    simp [probePolynomial, probeDotExponent, hi]

variable (Sc : SKM.Scalars D k)

/-- The existing signed Hom specialization at the prescribed binomial values. -/
abbrev elvProbeAffineSpecialization :=
  elvAffineScalarSpecialization D Sc (probeCutoff D m) (probeScalarValues (k := k) D m)
    (probeScalarValues_vanish D m)

end OddMath.QuiverHecke
end

end

section

/-! # Rectangular cyclotomic entries and probe cancellation

The distinct-colour step of `InvertibleDotProbe.md` §3 uses crossings
between different word corners. A dot is a unit in its own corner, not
a left-regular element of the entire cyclotomic algebra. The cancellation
below retains the actual word idempotents and rectangular entries.
-/
noncomputable section
open CategoryTheory StringDiagrams
open scoped Classical
namespace OddMath.QuiverHecke
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X]
  {k : Type w} [CommRing k] (D : SKM.Datum I X) (Sc : SKM.Scalars D k)
  [Fintype I] (a : I → Polynomial k)

def cyclotomicWordEntry {n : ℕ} (s t : Word I (n + 1))
    (f : wordObj D Sc s ⟶ wordObj D Sc t) : CyclotomicAlgebra D Sc a n :=
  cyclotomicMk D Sc a n (FiniteHomMatrix.single t s f)

theorem cyclotomicWordEntry_comp {n : ℕ} (s t u : Word I (n + 1))
    (f : wordObj D Sc s ⟶ wordObj D Sc t) (g : wordObj D Sc t ⟶ wordObj D Sc u) :
    cyclotomicWordEntry D Sc a s u (f ≫ g) =
      cyclotomicWordEntry D Sc a t u g * cyclotomicWordEntry D Sc a s t f := by
  change cyclotomicMk D Sc a n _ =
    cyclotomicMk D Sc a n _ * cyclotomicMk D Sc a n _
  rw [← map_mul, FiniteHomMatrix.single_mul_single]

theorem cyclotomicWordEntry_left_support {n : ℕ} (s t : Word I (n + 1))
    (f : wordObj D Sc s ⟶ wordObj D Sc t) :
    cyclotomicWordIdempotent D Sc a t * cyclotomicWordEntry D Sc a s t f =
      cyclotomicWordEntry D Sc a s t f := by
  change cyclotomicMk D Sc a n (FiniteHomMatrix.single t t (𝟙 _)) *
    cyclotomicMk D Sc a n (FiniteHomMatrix.single t s f) = _
  rw [← map_mul, FiniteHomMatrix.single_mul_single, Category.comp_id]
  rfl

theorem cyclotomicWordEntry_right_support {n : ℕ} (s t : Word I (n + 1))
    (f : wordObj D Sc s ⟶ wordObj D Sc t) :
    cyclotomicWordEntry D Sc a s t f * cyclotomicWordIdempotent D Sc a s =
      cyclotomicWordEntry D Sc a s t f := by
  change cyclotomicMk D Sc a n (FiniteHomMatrix.single t s f) *
    cyclotomicMk D Sc a n (FiniteHomMatrix.single s s (𝟙 _)) = _
  rw [← map_mul, FiniteHomMatrix.single_mul_single, Category.id_comp]
  rfl

end OddMath.QuiverHecke
end

end

section

/-! # Descent of the prescribed scalar probe specialization
The canonical binomial coefficient values send each original ELV relation to
the prescribed ordinary first-dot relation. The signed scalar Hom functor
therefore descends through the existing cyclotomic ideals, compatibly with
append. This is the probe-factor specialization of InvertibleDotProbe.md
Sections 1 and 5; positive-weight coefficient truncation is not used.
-/
noncomputable section
open CategoryTheory StringDiagrams
open OddMath.SKM.SYM
open scoped Classical
namespace OddMath.QuiverHecke
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (m : I → ℕ) (Sc : SKM.Scalars D k)
local notation "cut" => probeCutoff D m
local notation "a" => probePolynomial (k := k) (probeDotExponent D) m
local notation "F" => elvProbeAffineSpecialization D m Sc

/-- Every original first relation maps to its prescribed probe first relation. -/
theorem elvProbeAffineSpecialization_relation (i : I) (v : List I) :
    (F).map (ELV.relation D Sc cut i v) = firstDotPoly D Sc a i v := by
  unfold ELV.relation
  split_ifs with hi
  · change (F).map (elvQuotientMap D Sc cut _ _ (elvCyclotomic D Sc ⟨i,hi⟩ v (cut i))) = _
    rw [elvAffineScalarSpecialization_elvCyclotomic]
    have hc : elvMonicCoefficient D k ⟨i,hi⟩ (cut i) = probeMonicCoefficient (k := k) D m i := by
      funext j
      simp [probeMonicCoefficient, hi]
    rw [hc, scalarCoefficientPolynomial_probe]
    rfl
  · change (F).map (elvQuotientMap D Sc cut _ _ (evenCyclotomic D Sc i v (cut i))) = _
    rw [elvAffineScalarSpecialization_evenCyclotomic]
    have hc : evenMonicCoefficient D k i (cut i) = probeMonicCoefficient (k := k) D m i := by
      funext j
      simp [probeMonicCoefficient, hi]
    rw [hc, scalarCoefficientPolynomial_probe]
    rfl

/-- The existing scalar Hom map as a linear map, before cyclotomic descent. -/
def elvProbeScalarHom (v w : List I) :
    ELV.hom D Sc cut v w →ₗ[k]
      ((pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D w)) :=
  (F).toFunctor.mapLinearMap k

theorem elvProbeScalarHom_comp {v t w : List I}
    (f : ELV.hom D Sc cut v t) (g : ELV.hom D Sc cut t w) :
    elvProbeScalarHom D m Sc v w (f ≫ g) =
      elvProbeScalarHom D m Sc v t f ≫ elvProbeScalarHom D m Sc t w g :=
  (F).toFunctor.map_comp f g

theorem elvProbeScalarHom_id (v : List I) :
    elvProbeScalarHom D m Sc v v (𝟙 (ELV.obj D Sc cut v)) = 𝟙 ((pres D Sc).obj (ob D v)) :=
  (F).toFunctor.map_id _

theorem elvProbeScalarHom_relation (i : I) (v : List I) :
    elvProbeScalarHom D m Sc (i::v) (i::v) (ELV.relation D Sc cut i v) =
      firstDotPoly D Sc a i v :=
  elvProbeAffineSpecialization_relation D m Sc i v

/-- The actual ELV cyclotomic ideal maps into the existing ordinary Hom ideal. -/
theorem elvProbeAffineSpecialization_ideal {v w : List I}
    {f : ELV.hom D Sc cut v w} (hf : f ∈ ELV.ideal D Sc cut v w) :
    elvProbeScalarHom D m Sc v w f ∈ cycHom D Sc a v w := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨i, t, p, q, rfl⟩ := hf
    rw [elvProbeScalarHom_comp, elvProbeScalarHom_comp, elvProbeScalarHom_relation]
    exact Submodule.subset_span ⟨i, t, elvProbeScalarHom D m Sc _ _ p, elvProbeScalarHom D m Sc _ _ q, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add f g _ _ hf hg => rw [map_add]; exact Submodule.add_mem _ hf hg
  | smul c f _ hf => rw [map_smul]; exact Submodule.smul_mem _ c hf

/-- The scalar Hom functor descends through the original cyclotomic ideals. -/
def elvProbeOldHom (v w : List I) :
    ELV.Old D Sc cut v w →ₗ[k]
      (((pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D w)) ⧸ cycHom D Sc a v w) :=
  (ELV.ideal D Sc cut v w).liftQ
    ((cycHom D Sc a v w).mkQ.comp (elvProbeScalarHom D m Sc v w)) (by
      intro f hf
      change (cycHom D Sc a v w).mkQ ((F).map f) = 0
      exact (Submodule.Quotient.mk_eq_zero _).mpr (elvProbeAffineSpecialization_ideal D m Sc hf))

@[simp] theorem elvProbeOldHom_mk (v w : List I) (f : ELV.hom D Sc cut v w) :
    elvProbeOldHom D m Sc v w ((ELV.ideal D Sc cut v w).mkQ f) =
      (cycHom D Sc a v w).mkQ ((F).map f) := rfl

theorem elvProbeOldHom_surjective (v w : List I) :
    Function.Surjective (elvProbeOldHom D m Sc v w) := by
  intro y
  obtain ⟨f, rfl⟩ := (cycHom D Sc a v w).mkQ_surjective y
  obtain ⟨g, hg⟩ := elvAffineScalarSpecialization_surjective D Sc cut
    (probeScalarValues D m) (probeScalarValues_vanish D m) v w f
  refine ⟨(ELV.ideal D Sc cut v w).mkQ g, ?_⟩
  rw [elvProbeOldHom_mk, hg]

/-- Append on the original ELV old quotient, using its existing ideal stability. -/
def elvProbeOldRightContext (σ v w : List I) :
    ELV.Old D Sc cut v w →ₗ[k] ELV.Old D Sc cut (v++σ) (w++σ) :=
  (ELV.ideal D Sc cut v w).liftQ
    ((ELV.ideal D Sc cut (v++σ) (w++σ)).mkQ.comp (ELV.rightContext D Sc cut σ v w)) (by
      intro f hf
      change (ELV.ideal D Sc cut (v++σ) (w++σ)).mkQ _ = 0
      exact (Submodule.Quotient.mk_eq_zero _).mpr (ELV.ideal_rightContext D Sc cut σ hf))

/-- Append on the existing ordinary cyclotomic Hom quotient. -/
def probeCycHomRightContext (σ v w : List I) :
    (((pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D w)) ⧸ cycHom D Sc a v w) →ₗ[k]
      (((pres D Sc).obj (ob D (v++σ)) ⟶ (pres D Sc).obj (ob D (w++σ))) ⧸
        cycHom D Sc a (v++σ) (w++σ)) :=
  (cycHom D Sc a v w).liftQ
    ((cycHom D Sc a (v++σ) (w++σ)).mkQ.comp (ELV.affineRightContext D Sc σ v w)) (by
      intro f hf
      change (cycHom D Sc a (v++σ) (w++σ)).mkQ _ = 0
      exact (Submodule.Quotient.mk_eq_zero _).mpr (cycHom_whiskerRight D Sc hf σ))

/-- The descended scalar Hom map commutes with append. -/
theorem elvProbeOldHom_rightContext (σ v w : List I) (f : ELV.Old D Sc cut v w) :
    elvProbeOldHom D m Sc (v++σ) (w++σ) (elvProbeOldRightContext D m Sc σ v w f) =
      probeCycHomRightContext D m Sc σ v w (elvProbeOldHom D m Sc v w f) := by
  obtain ⟨f, rfl⟩ := (ELV.ideal D Sc cut v w).mkQ_surjective f
  change (cycHom D Sc a (v++σ) (w++σ)).mkQ
      ((F).map (ELV.rightContext D Sc cut σ v w f)) =
    (cycHom D Sc a (v++σ) (w++σ)).mkQ
      (ELV.affineRightContext D Sc σ v w ((F).map f))
  congr 1
  exact elvAffineScalarSpecialization_rightContext D Sc cut
    (probeScalarValues D m) (probeScalarValues_vanish D m) σ v w f

variable [Fintype I]

/-- The existing ordinary Hom quotient maps to its literal probe matrix entry. -/
def probeCycHomWordEntry {n : ℕ} (s t : Word I (n+1)) :
    (((pres D Sc).obj (ob D s.val) ⟶ (pres D Sc).obj (ob D t.val)) ⧸
      cycHom D Sc a s.val t.val) →ₗ[k] CyclotomicAlgebra D Sc a n :=
  (cycHom D Sc a s.val t.val).liftQ
    { toFun := cyclotomicWordEntry D Sc a s t
      map_add' := by
        intro f g
        change cyclotomicMk D Sc a n (FiniteHomMatrix.single t s (f+g)) = _
        rw [FiniteHomMatrix.single_add, map_add]
        rfl
      map_smul' := by
        intro c f
        change cyclotomicMk D Sc a n (FiniteHomMatrix.single t s (c • f)) = _
        rw [FiniteHomMatrix.single_smul, map_smul]
        rfl } (by
      intro f hf
      change cyclotomicMk D Sc a n (FiniteHomMatrix.single t s f) = 0
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      exact single_mem_cyclotomicIdeal D Sc a n t s hf)

/-- The scalar Hom functor descends into the actual probe cyclotomic algebra. -/
def elvProbeWordEntry {n : ℕ} (s t : Word I (n+1)) :
    ELV.Old D Sc cut s.val t.val →ₗ[k] CyclotomicAlgebra D Sc a n :=
  (probeCycHomWordEntry D m Sc s t).comp (elvProbeOldHom D m Sc s.val t.val)

@[simp] theorem elvProbeWordEntry_mk {n : ℕ} (s t : Word I (n+1))
    (f : ELV.hom D Sc cut s.val t.val) :
    elvProbeWordEntry D m Sc s t ((ELV.ideal D Sc cut s.val t.val).mkQ f) =
      cyclotomicWordEntry D Sc a s t ((F).map f) := rfl

end OddMath.QuiverHecke
end

end

section

/-! # Scalar probe specialization of the untruncated ELV content ring
This supplies the ring input for the probe-factor base change of
InvertibleDotProbe.md Sections 1 and 5. The source is the untruncated
ELV.ContentRing. The target uses the existing heightAlgebra, including
the vacuum height. Module-action and prescribed inverse-matrix comparison
are separate.
-/
noncomputable section
open CategoryTheory StringDiagrams
open OddMath.QuiverHecke.CyclotomicAction
open scoped Classical
namespace OddMath.QuiverHecke
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (m : I → ℕ) (Sc : SKM.Scalars D k) [Fintype I]
local notation "cut" => probeCutoff D m
local notation "a" => probePolynomial (k := k) (probeDotExponent D) m

/-- The existing affine/cyclotomic quotient map at every height. -/
def probeHeightMk : (n : ℕ) → Hn D Sc n →ₐ[k] heightAlgebra D Sc a n
  | 0 => AlgHom.id k _
  | n+1 => cyclotomicMk D Sc a n

private def probeHeightAffineEntry {n : ℕ} (s t : Word I n) :
    ((pres D Sc).obj (ob D s.val) ⟶ (pres D Sc).obj (ob D t.val)) →ₗ[k]
      heightAlgebra D Sc a n where
  toFun f := probeHeightMk D m Sc n (FiniteHomMatrix.single t s f)
  map_add' f g := by
    rw [FiniteHomMatrix.single_add, map_add]
  map_smul' c f := by
    rw [FiniteHomMatrix.single_smul, map_smul]
    rfl

private def elvProbeHeightRawEntry {n : ℕ} (s t : Word I n) :
    ELV.hom D Sc cut s.val t.val →ₗ[k] heightAlgebra D Sc a n :=
  (probeHeightAffineEntry D m Sc s t).comp (elvProbeScalarHom D m Sc s.val t.val)

private theorem elvProbeHeightRawEntry_ideal {n : ℕ} (s t : Word I n)
    (f : ELV.hom D Sc cut s.val t.val) (hf : f ∈ ELV.ideal D Sc cut s.val t.val) :
    elvProbeHeightRawEntry D m Sc s t f = 0 := by
  cases n with
  | zero =>
    rcases s with ⟨sv, hsv⟩
    have hs : sv = [] := List.length_eq_zero_iff.mp hsv
    subst sv
    have hf0 : f = 0 := by simpa only [ELV.ideal_nil, Submodule.mem_bot] using hf
    rw [hf0, map_zero]
  | succ n =>
    change cyclotomicMk D Sc a n
      (FiniteHomMatrix.single t s (elvProbeScalarHom D m Sc s.val t.val f)) = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact single_mem_cyclotomicIdeal D Sc a n t s
      (elvProbeAffineSpecialization_ideal D m Sc hf)

/-- Literal specialized matrix entries at every height, including zero. -/
def elvProbeHeightWordEntry {n : ℕ} (s t : Word I n) :
    ELV.Old D Sc cut s.val t.val →ₗ[k] heightAlgebra D Sc a n :=
  (ELV.ideal D Sc cut s.val t.val).liftQ (elvProbeHeightRawEntry D m Sc s t)
    (by intro f hf; exact elvProbeHeightRawEntry_ideal D m Sc s t f hf)

@[simp] theorem elvProbeHeightWordEntry_mk {n : ℕ} (s t : Word I n)
    (f : ELV.hom D Sc cut s.val t.val) :
    elvProbeHeightWordEntry D m Sc s t ((ELV.ideal D Sc cut s.val t.val).mkQ f) =
      probeHeightMk D m Sc n
        (FiniteHomMatrix.single t s (elvProbeScalarHom D m Sc s.val t.val f)) := rfl

theorem elvProbeHeightWordEntry_comp {n : ℕ} (s t z : Word I n)
    (f : ELV.Old D Sc cut s.val t.val) (g : ELV.Old D Sc cut t.val z.val) :
    elvProbeHeightWordEntry D m Sc s z (ELV.oldComp D Sc cut s.val t.val z.val f g) =
      elvProbeHeightWordEntry D m Sc t z g * elvProbeHeightWordEntry D m Sc s t f := by
  obtain ⟨f, rfl⟩ := (ELV.ideal D Sc cut s.val t.val).mkQ_surjective f
  obtain ⟨g, rfl⟩ := (ELV.ideal D Sc cut t.val z.val).mkQ_surjective g
  rw [ELV.oldComp_mk, elvProbeHeightWordEntry_mk, elvProbeHeightWordEntry_mk,
    elvProbeHeightWordEntry_mk, ← map_mul, FiniteHomMatrix.single_mul_single]
  exact congrArg (fun h : (pres D Sc).obj (ob D s.val) ⟶ (pres D Sc).obj (ob D z.val) =>
    probeHeightMk D m Sc n (FiniteHomMatrix.single z s h)) (elvProbeScalarHom_comp D m Sc f g)

theorem elvProbeHeightWordEntry_mul_of_ne {n : ℕ} (s t z w : Word I n) (htz : t ≠ z)
    (f : ELV.Old D Sc cut t.val s.val) (g : ELV.Old D Sc cut w.val z.val) :
    elvProbeHeightWordEntry D m Sc t s f * elvProbeHeightWordEntry D m Sc w z g = 0 := by
  obtain ⟨f, rfl⟩ := (ELV.ideal D Sc cut t.val s.val).mkQ_surjective f
  obtain ⟨g, rfl⟩ := (ELV.ideal D Sc cut w.val z.val).mkQ_surjective g
  rw [elvProbeHeightWordEntry_mk, elvProbeHeightWordEntry_mk, ← map_mul]
  have hm : (FiniteHomMatrix.single s t (elvProbeScalarHom D m Sc t.val s.val f) : Hn D Sc n) *
      FiniteHomMatrix.single z w (elvProbeScalarHom D m Sc w.val z.val g) = 0 :=
    FiniteHomMatrix.single_mul_single_of_ne s t z w htz _ _
  exact (congrArg (probeHeightMk D m Sc n) hm).trans (map_zero _)

theorem elvProbeHeightWordEntry_id {n : ℕ} (s : Word I n) :
    elvProbeHeightWordEntry D m Sc s s ((ELV.ideal D Sc cut s.val s.val).mkQ
      (𝟙 (ELV.obj D Sc cut s.val))) = probeHeightMk D m Sc n (Hn.wordIdempotent s) := by
  rw [elvProbeHeightWordEntry_mk]
  exact congrArg (fun h : End ((pres D Sc).obj (ob D s.val)) =>
    probeHeightMk D m Sc n (FiniteHomMatrix.single s s h)) (elvProbeScalarHom_id D m Sc s.val)

/-- A content permutation viewed in the existing fixed-height word type. -/
def probeContentWord (ν : List I) (v : ELV.ContentWords ν) : Word I ν.length :=
  ⟨v.val, v.property.length_eq⟩

omit [Fintype I] in
theorem probeContentWord_injective (ν : List I) : Function.Injective (probeContentWord ν) := by
  intro v w h
  apply Subtype.ext
  exact congrArg (fun z : Word I ν.length => z.val) h

/-- Specialization on the canonical matrix-entry Hom type. -/
def elvProbeContentEntry (ν : List I) (p : ELV.ContentWords ν × ELV.ContentWords ν) :
    (ELV.contentObject D Sc cut ν p.2 ⟶ ELV.contentObject D Sc cut ν p.1) →ₗ[k]
      heightAlgebra D Sc a ν.length where
  toFun f := elvProbeHeightWordEntry D m Sc (probeContentWord ν p.2) (probeContentWord ν p.1) f
  map_add' f g := map_add _ f g
  map_smul' c f := map_smul _ c f

/-- The finite content-matrix map, assembled from the literal height entries. -/
def elvProbeContentLinear (ν : List I) :
    ELV.ContentRing D Sc cut ν →ₗ[k] heightAlgebra D Sc a ν.length :=
  DFinsupp.lsum k (elvProbeContentEntry D m Sc ν)

@[simp] theorem elvProbeContentLinear_single (ν : List I) (v w : ELV.ContentWords ν)
    (f : ELV.contentObject D Sc cut ν w ⟶ ELV.contentObject D Sc cut ν v) :
    elvProbeContentLinear D m Sc ν (FiniteHomMatrix.single v w f) =
      elvProbeContentEntry D m Sc ν (v,w) f := by
  let : DecidableEq (ELV.ContentWords ν) := Classical.decEq _
  exact DFinsupp.lsum_single (S := k) (elvProbeContentEntry D m Sc ν) (v,w) f

private theorem elvProbeContentLinear_single_product (ν : List I) (s t u v : ELV.ContentWords ν)
    (f : ELV.contentObject D Sc cut ν t ⟶ ELV.contentObject D Sc cut ν s)
    (g : ELV.contentObject D Sc cut ν v ⟶ ELV.contentObject D Sc cut ν u) :
    elvProbeContentLinear D m Sc ν (FiniteHomMatrix.single s t f * FiniteHomMatrix.single u v g) =
      elvProbeContentLinear D m Sc ν (FiniteHomMatrix.single s t f) *
        elvProbeContentLinear D m Sc ν (FiniteHomMatrix.single u v g) := by
  by_cases h : t = u
  · subst u
    rw [FiniteHomMatrix.single_mul_single, elvProbeContentLinear_single,
      elvProbeContentLinear_single, elvProbeContentLinear_single]
    exact elvProbeHeightWordEntry_comp D m Sc (probeContentWord ν v)
      (probeContentWord ν t) (probeContentWord ν s) g f
  · rw [FiniteHomMatrix.single_mul_single_of_ne s t u v h, map_zero,
      elvProbeContentLinear_single, elvProbeContentLinear_single]
    have hn : probeContentWord ν t ≠ probeContentWord ν u :=
      fun he => h (probeContentWord_injective ν he)
    exact (elvProbeHeightWordEntry_mul_of_ne D m Sc (probeContentWord ν s) (probeContentWord ν t)
      (probeContentWord ν u) (probeContentWord ν v) hn f g).symm

theorem elvProbeContentLinear_mul (ν : List I) (x y : ELV.ContentRing D Sc cut ν) :
    elvProbeContentLinear D m Sc ν (x*y) =
      elvProbeContentLinear D m Sc ν x * elvProbeContentLinear D m Sc ν y := by
  induction x using FiniteHomMatrix.induction with
  | hz => simp only [zero_mul, map_zero]
  | ha x z hx hz => simp only [add_mul, map_add, hx, hz]
  | hs s t f =>
    induction y using FiniteHomMatrix.induction with
    | hz => simp only [mul_zero, map_zero]
    | ha y z hy hz => simp only [mul_add, map_add, hy, hz]
    | hs u v g => exact elvProbeContentLinear_single_product D m Sc ν s t u v f g

/-- The untruncated content-ring specialization before restriction to its unit corner. -/
def elvProbeContentNonUnital (ν : List I) :
    ELV.ContentRing D Sc cut ν →ₙₐ[k] heightAlgebra D Sc a ν.length where
  toFun := elvProbeContentLinear D m Sc ν
  map_zero' := map_zero _
  map_add' := map_add _
  map_smul' := map_smul _
  map_mul' := elvProbeContentLinear_mul D m Sc ν

/-- The literal content idempotent in the existing height algebra. -/
def probeHeightContentIdempotent (ν : List I) : heightAlgebra D Sc a ν.length :=
  probeHeightMk D m Sc ν.length (contentIdempotent D Sc ν.length (ν : Multiset I))

theorem probeHeightContentIdempotent_idem (ν : List I) :
    IsIdempotentElem (probeHeightContentIdempotent D m Sc ν) := by
  change probeHeightMk D m Sc ν.length _ * probeHeightMk D m Sc ν.length _ =
    probeHeightMk D m Sc ν.length _
  rw [← map_mul, contentIdempotent_sq]

/-- The actual content corner, uniformly including the vacuum height. -/
abbrev ProbeHeightContentCorner (ν : List I) :=
  (probeHeightContentIdempotent_idem D m Sc ν).Corner

omit [Fintype I] in
private def probeContentWordEquiv (ν : List I) :
    ELV.ContentWords ν ≃ {w : Word I ν.length // wordContent w = (ν : Multiset I)} where
  toFun v := ⟨probeContentWord ν v, Multiset.coe_eq_coe.mpr v.property⟩
  invFun w := ⟨w.val.val, Multiset.coe_eq_coe.mp w.property⟩
  left_inv _v := Subtype.ext rfl
  right_inv _w := Subtype.ext (Subtype.ext rfl)

theorem elvProbeContentNonUnital_one (ν : List I) :
    elvProbeContentNonUnital D m Sc ν 1 = probeHeightContentIdempotent D m Sc ν := by
  change elvProbeContentLinear D m Sc ν (FiniteHomMatrix.localUnit Finset.univ) =
    probeHeightMk D m Sc ν.length (contentIdempotent D Sc ν.length (ν : Multiset I))
  rw [FiniteHomMatrix.localUnit, map_sum]
  simp only [FiniteHomMatrix.idem, elvProbeContentLinear_single]
  unfold contentIdempotent FiniteHomMatrix.localUnit
  rw [map_sum, Finset.sum_subtype (p := fun w : Word I ν.length => wordContent w = (ν : Multiset I))
    _ (by intro w; simp)]
  exact Fintype.sum_equiv (probeContentWordEquiv ν) _ _ (fun v => elvProbeHeightWordEntry_id D m Sc (probeContentWord ν v))

@[simp] theorem probeHeightContentIdempotent_nil :
    probeHeightContentIdempotent D m Sc [] = (1 : heightAlgebra D Sc a 0) := by
  change contentIdempotent D Sc 0 0 = (1 : Hn D Sc 0)
  change FiniteHomMatrix.localUnit (Finset.univ.filter (fun w : Word I 0 => wordContent w = 0)) =
    FiniteHomMatrix.localUnit Finset.univ
  congr 1

private def probeHeightContentSubmodule (ν : List I) : Submodule k (heightAlgebra D Sc a ν.length) where
  carrier := (Subsemigroup.corner (probeHeightContentIdempotent D m Sc ν) : Set _)
  zero_mem' := (Subsemigroup.mem_corner_iff (probeHeightContentIdempotent_idem D m Sc ν)).mpr
    ⟨mul_zero _, zero_mul _⟩
  add_mem' := by
    intro x y hx hy
    have hx := (Subsemigroup.mem_corner_iff (probeHeightContentIdempotent_idem D m Sc ν)).mp hx
    have hy := (Subsemigroup.mem_corner_iff (probeHeightContentIdempotent_idem D m Sc ν)).mp hy
    apply (Subsemigroup.mem_corner_iff (probeHeightContentIdempotent_idem D m Sc ν)).mpr
    constructor
    · rw [mul_add, hx.1, hy.1]
    · rw [add_mul, hx.2, hy.2]
  smul_mem' := by
    intro c x hx
    have hx := (Subsemigroup.mem_corner_iff (probeHeightContentIdempotent_idem D m Sc ν)).mp hx
    apply (Subsemigroup.mem_corner_iff (probeHeightContentIdempotent_idem D m Sc ν)).mpr
    constructor
    · rw [mul_smul_comm, hx.1]
    · rw [smul_mul_assoc, hx.2]

instance probeHeightContentCornerModule (ν : List I) :
    Module k (ProbeHeightContentCorner D m Sc ν) :=
  inferInstanceAs (Module k (probeHeightContentSubmodule D m Sc ν))

instance probeHeightContentCornerAlgebra (ν : List I) :
    Algebra k (ProbeHeightContentCorner D m Sc ν) :=
  Algebra.ofModule
    (fun c x y => Subtype.ext (smul_mul_assoc c x.val y.val))
    (fun c x y => by apply Subtype.ext; change x.val * (c • y.val) = _; rw [mul_smul_comm]; rfl)

/-- The untruncated ELV old content ring maps to the literal ordinary probe content corner. -/
def elvProbeContentSpecialization (ν : List I) :
    ELV.ContentRing D Sc cut ν →ₐ[k] ProbeHeightContentCorner D m Sc ν where
  toFun x := ⟨elvProbeContentNonUnital D m Sc ν x, by
    apply (Subsemigroup.mem_corner_iff (probeHeightContentIdempotent_idem D m Sc ν)).mpr
    constructor
    · rw [← elvProbeContentNonUnital_one, ← map_mul, one_mul]
    · rw [← elvProbeContentNonUnital_one, ← map_mul, mul_one]⟩
  map_zero' := Subtype.ext (map_zero (elvProbeContentNonUnital D m Sc ν))
  map_one' := Subtype.ext (elvProbeContentNonUnital_one D m Sc ν)
  map_add' x y := Subtype.ext (map_add (elvProbeContentNonUnital D m Sc ν) x y)
  map_mul' x y := Subtype.ext (map_mul (elvProbeContentNonUnital D m Sc ν) x y)
  commutes' c := by
    apply Subtype.ext
    change elvProbeContentNonUnital D m Sc ν
        (algebraMap k (ELV.ContentRing D Sc cut ν) c) =
      (algebraMap k (ProbeHeightContentCorner D m Sc ν) c).val
    rw [Algebra.algebraMap_eq_smul_one, map_smul, elvProbeContentNonUnital_one]
    rw [Algebra.algebraMap_eq_smul_one]
    rfl

@[simp] theorem elvProbeContentSpecialization_val (ν : List I) (x : ELV.ContentRing D Sc cut ν) :
    (elvProbeContentSpecialization D m Sc ν x).val = elvProbeContentNonUnital D m Sc ν x := rfl

end OddMath.QuiverHecke
end

end

section

/-! # Parity of cofinal probe polynomials

Odd-colour probes have support in even exponents. This gives the exact
polynomial-parity input of the existing cyclotomic supermodule construction,
over an arbitrary commutative ring, including the zero polynomial/ring cases.
-/
noncomputable section
namespace OddMath.QuiverHecke
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X]
  {k : Type w} [CommRing k]

/-- The cofinal binomial probe is a polynomial expansion. -/
theorem probePolynomial_eq_expand (e m : I → ℕ) (i : I) :
    (probePolynomial e m i : Polynomial k) =
      Polynomial.expand k (e i) ((Polynomial.X - 1) ^ m i) := by
  simp only [probePolynomial, map_pow, map_sub, Polynomial.expand_X, map_one]

/-- Every nonzero coefficient has exponent divisible by the chosen probe step. -/
theorem probePolynomial_support_dvd (e m : I → ℕ) (i : I)
    (he : 0 < e i) {n : ℕ}
    (hn : (probePolynomial e m i : Polynomial k).coeff n ≠ 0) :
    e i ∣ n := by
  by_contra hd
  apply hn
  rw [probePolynomial_eq_expand, Polynomial.coeff_expand he, ite_eq_right hd]

private theorem probe_parity_cases (p : ZMod 2) : p = 0 ∨ p = 1 := by
  fin_cases p
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- The prescribed odd/even cofinal probes supply the actual supermodule
polynomial-parity premise, without a nontriviality or finite-colour hypothesis. -/
theorem probePolynomial_parity (D : SKM.Datum I X) (m : I → ℕ) :
    CyclotomicPolynomialParity (k := k) D
      (probePolynomial (probeDotExponent D) m) := by
  intro i n hn
  rcases probe_parity_cases (D.parity i) with hi | hi
  · simp only [hi, nsmul_zero]
  · have he : probeDotExponent D i = 2 := by simp [probeDotExponent, hi]
    have hd : 2 ∣ n := by
      simpa only [he] using
        (probePolynomial_support_dvd (probeDotExponent D) m i
          (by rw [he]; decide) hn)
    rw [probePolynomial_eq_expand, Polynomial.natDegree_expand, hi, he]
    obtain ⟨r, rfl⟩ := hd
    have hz : (2 : ℕ) • (1 : ZMod 2) = 0 := by decide
    simp only [Nat.mul_comm 2 r, mul_smul, hz, smul_zero]

end OddMath.QuiverHecke
end

end

section

/-! # Parity of the actual all-height scalar probe entries
The untruncated old ELV quotient specializes to the existing graded height
algebra. This is the parity input for restriction of actual probe modules.
-/
noncomputable section
open CategoryTheory StringDiagrams
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (m : I → ℕ) (Sc : SKM.Scalars D k) [Fintype I]
local notation "cut" => probeCutoff D m
local notation "a" => probePolynomial (k := k) (probeDotExponent D) m

/-- The all-height quotient map preserves the prescribed super grading. -/
theorem probeHeightMk_parity (ha : CyclotomicPolynomialParity D a) (n : ℕ)
    {p : ZMod 2} {x : Hn D Sc n} (hx : x ∈ affineParity D Sc n p) :
    probeHeightMk D m Sc n x ∈ heightParity D Sc a ha n p := by
  cases n with
  | zero => exact hx
  | succ n => exact cyclotomicMk_parity D Sc a ha n hx

/-- Actual old quotient entries retain total super parity, including exterior
coefficients that the scalar specialization sends to zero. -/
theorem elvProbeHeightWordEntry_parity (ha : CyclotomicPolynomialParity D a)
    {n : ℕ} (s t : Word I n) {p : ZMod 2}
    {f : ELV.Old D Sc cut s.val t.val}
    (hf : f ∈ ELV.oldParity D Sc cut s.val t.val p) :
    elvProbeHeightWordEntry D m Sc s t f ∈ heightParity D Sc a ha n p := by
  obtain ⟨f, hf, rfl⟩ := hf
  rw [elvProbeHeightWordEntry_mk]
  apply probeHeightMk_parity D m Sc ha n
  exact FiniteHomMatrix.single_mem_component t s
    ((elvProbeAffineSpecialization D m Sc).map_mem hf)

/-- The canonical probe parity proof supplies the preceding bridge directly. -/
theorem elvProbeHeightWordEntry_probeParity {n : ℕ} (s t : Word I n)
    {p : ZMod 2} {f : ELV.Old D Sc cut s.val t.val}
    (hf : f ∈ ELV.oldParity D Sc cut s.val t.val p) :
    elvProbeHeightWordEntry D m Sc s t f ∈
      heightParity D Sc a (probePolynomial_parity D m) n p :=
  elvProbeHeightWordEntry_parity D m Sc (probePolynomial_parity D m) s t hf

/-- The specialized rectangular entry lands in its actual target word summand. -/
theorem elvProbeHeightWordEntry_target {n : ℕ} (s t : Word I n)
    (f : ELV.Old D Sc cut s.val t.val) :
    probeHeightMk D m Sc n (Hn.wordIdempotent t) *
      elvProbeHeightWordEntry D m Sc s t f = elvProbeHeightWordEntry D m Sc s t f := by
  rw [← elvProbeHeightWordEntry_id D m Sc t,
    ← elvProbeHeightWordEntry_comp D m Sc s t t]
  obtain ⟨f, rfl⟩ := (ELV.ideal D Sc cut s.val t.val).mkQ_surjective f
  rw [ELV.oldComp_mk, Category.comp_id]

end OddMath.QuiverHecke
end

end

section

/-! # Actual probe modules on the untruncated old content category
A left module over the prescribed ordinary probe height algebra yields a genuine
old ELV supermodule. Its value at a word is the actual word-idempotent summand;
old arrows act by the checked scalar specialization entries.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (m : I → ℕ) (Sc : SKM.Scalars D k) [Fintype I]
local notation "cut" => probeCutoff D m
local notation "a" => probePolynomial (k := k) (probeDotExponent D) m
variable (ν : List I)
local notation "ha" => probePolynomial_parity (k := k) D m
local notation "C" => ELV.OldContentCategory D Sc cut ν
local notation "word" => fun v : C => probeContentWord ν (ELV.oldContentWord D Sc cut ν v)

def probeOldWordIdempotent (v : C) : heightAlgebra D Sc a ν.length :=
  probeHeightMk D m Sc ν.length (Hn.wordIdempotent (word v))

theorem probeOldWordIdempotent_parity (v : C) :
    probeOldWordIdempotent D m Sc ν v ∈ heightParity D Sc a ha ν.length 0 := by
  apply probeHeightMk_parity D m Sc ha ν.length
  exact FiniteHomMatrix.single_mem_component _ _ (id_mem _)

variable {B : Type u} [Ring B] [Algebra k B] {GB : ZMod 2 → Submodule k B}
  (M : SuperBimodule
    (heightParity D Sc (probePolynomial (k := k) (probeDotExponent D) m)
      (probePolynomial_parity D m) ν.length) GB)

/-- The actual fixed submodule of the specialized word idempotent. -/
def probeOldWordSubmodule (v : C) : Submodule k M.toSVec where
  carrier := {x | M.lact (probeOldWordIdempotent D m Sc ν v) x = x}
  zero_mem' := map_zero _
  add_mem' {x y} hx hy := by
    change M.lact _ x = x at hx
    change M.lact _ y = y at hy
    change M.lact _ (x + y) = x + y
    rw [map_add, hx, hy]
  smul_mem' r x hx := by
    change M.lact _ x = x at hx
    change M.lact _ (r • x) = r • x
    rw [map_smul, hx]

theorem probeOldWordSubmodule_odd (v : C) (x : M.toSVec)
    (hx : x ∈ probeOldWordSubmodule D m Sc ν M v) :
    M.toSVec.odd x ∈ probeOldWordSubmodule D m Sc ν M v := by
  have h := SVec.apply_proj_of_mem
    (M.lact_mem 0 _ (probeOldWordIdempotent_parity D m Sc ν v)) 1 x
  change M.lact _ (M.toSVec.odd x) = M.toSVec.odd x
  change M.lact _ x = x at hx
  simpa only [add_zero, SVec.proj_one, hx] using h

/-- A word component of an ordinary probe module, with its inherited grading. -/
def probeOldWordSVec (v : C) : SVec k :=
  SVec.sub M.toSVec (probeOldWordSubmodule D m Sc ν M v)
    (probeOldWordSubmodule_odd D m Sc ν M v)

def probeOldWordEntry {v w : C} (f : v ⟶ w) : heightAlgebra D Sc a ν.length :=
  elvProbeHeightWordEntry D m Sc (word v) (word w) f

theorem probeOldWordEntry_target {v w : C} (f : v ⟶ w) :
    probeOldWordIdempotent D m Sc ν w * probeOldWordEntry D m Sc ν f =
      probeOldWordEntry D m Sc ν f :=
  elvProbeHeightWordEntry_target D m Sc (word v) (word w) f

theorem probeOldWordAction_mem {v w : C} (f : v ⟶ w)
    (x : M.toSVec) (_hx : x ∈ probeOldWordSubmodule D m Sc ν M v) :
    M.lact (probeOldWordEntry D m Sc ν f) x ∈
      probeOldWordSubmodule D m Sc ν M w := by
  have h := congrArg (fun z => M.lact z x) (probeOldWordEntry_target D m Sc ν f)
  change M.lact _ (M.lact _ x) = M.lact _ x
  simpa only [M.lact_mul, SVec.comp_apply] using h

/-- Old morphisms act on actual probe word components by left multiplication. -/
def probeOldWordAction {v w : C} (f : v ⟶ w) :
    probeOldWordSVec D m Sc ν M v ⟶ probeOldWordSVec D m Sc ν M w :=
  SVec.restrictHom (M.lact (probeOldWordEntry D m Sc ν f))
    (probeOldWordAction_mem D m Sc ν M f)

theorem probeOldWordEntry_id (v : C) :
    probeOldWordEntry D m Sc ν (𝟙 v) = probeOldWordIdempotent D m Sc ν v :=
  elvProbeHeightWordEntry_id D m Sc (word v)

theorem probeOldWordEntry_comp {v w z : C} (f : v ⟶ w) (g : w ⟶ z) :
    probeOldWordEntry D m Sc ν (f ≫ g) =
      probeOldWordEntry D m Sc ν g * probeOldWordEntry D m Sc ν f :=
  elvProbeHeightWordEntry_comp D m Sc (word v) (word w) (word z) f g

/-- Restriction of a genuine ordinary probe module to the old ELV content category. -/
def probeOldModuleFunctor : C ⥤ SVec k where
  obj := probeOldWordSVec D m Sc ν M
  map f := probeOldWordAction D m Sc ν M f
  map_id v := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change M.lact (probeOldWordEntry D m Sc ν (𝟙 v)) x.val = x.val
    rw [probeOldWordEntry_id]
    exact x.property
  map_comp f g := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change M.lact (probeOldWordEntry D m Sc ν (f ≫ g)) x.val =
      M.lact (probeOldWordEntry D m Sc ν g) (M.lact (probeOldWordEntry D m Sc ν f) x.val)
    rw [probeOldWordEntry_comp, M.lact_mul]
    rfl

instance probeOldModuleFunctor_additive : (probeOldModuleFunctor D m Sc ν M).Additive where
  map_add {v w} f g := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change M.lact (elvProbeHeightWordEntry D m Sc (word v) (word w) (f + g)) x.val =
      M.lact (elvProbeHeightWordEntry D m Sc (word v) (word w) f) x.val +
        M.lact (elvProbeHeightWordEntry D m Sc (word v) (word w) g) x.val
    rw [map_add, map_add]
    rfl

instance probeOldModuleFunctor_linear : (probeOldModuleFunctor D m Sc ν M).Linear k where
  map_smul {v w} f r := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change M.lact (elvProbeHeightWordEntry D m Sc (word v) (word w) (r • f)) x.val =
      r • M.lact (elvProbeHeightWordEntry D m Sc (word v) (word w) f) x.val
    rw [map_smul, map_smul]
    rfl

instance probeOldModuleFunctor_super : IsSuperfunctor k (probeOldModuleFunctor D m Sc ν M) where
  map_mem := by
    intro v w p f hf
    exact SVec.restrictHom_mem
      (M.lact_mem p _ (elvProbeHeightWordEntry_probeParity D m Sc (word v) (word w) hf))
      (probeOldWordAction_mem D m Sc ν M f)

/-- The actual probe module, as an even additive linear superfunctor. -/
def probeOldModule : Superfunctor k C (SVec k) :=
  ⟨probeOldModuleFunctor D m Sc ν M⟩

@[simp] theorem probeOldModule_map_apply {v w : C} (f : v ⟶ w)
    (x : probeOldWordSVec D m Sc ν M v) :
    ((show probeOldWordSubmodule D m Sc ν M w from
      (probeOldModule D m Sc ν M).map f x) : M.toSVec) =
      M.lact (probeOldWordEntry D m Sc ν f) x.val := rfl

end OddMath.QuiverHecke
end

end

section

/-! # Scalar-evaluated actual old probe modules
The coefficient condition is proved for the actual probe module. It then
forces every old module map to factor through the prescribed scalar Hom
specialization, directly by the tensor universal property, without a flatness premise.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped TensorProduct
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (m : I → ℕ) (Sc : SKM.Scalars D k)
local notation "cut" => probeCutoff D m
local notation "A" => SKM.SYM.ELVCoefficientAlgebra (k := k) D cut
local notation "ev" => SKM.SYM.elvScalarEvaluation D cut (probeScalarValues D m) (probeScalarValues_vanish D m)
variable (ν : List I)
local notation "C" => ELV.OldContentCategory D Sc cut ν

/-- The actual full coefficient at an old-content word identity. -/
def probeOldCoefficient (v : C) (c : A) : v ⟶ v :=
  (ELV.ideal D Sc cut v.obj.word v.obj.word).mkQ (c ⊗ₜ[k] (𝟙 _))

/-- Scalar evaluation of coefficients, as a property of the actual old module. -/
def ProbeEvaluatesCoefficients
    (N : Superfunctor k (ELV.OldContentCategory D Sc (probeCutoff D m) ν) (SVec k)) : Prop :=
  ∀ (v : C) (c : A), N.toFunctor.map (probeOldCoefficient D m Sc ν v c) = ev c • 𝟙 (N.obj v)

omit ν in
/-- The scalar Hom map evaluates an arbitrary pure coefficient tensor literally. -/
theorem elvProbeScalarHom_tmul {v w : List I} (c : A)
    (f : (pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D w)) :
    elvProbeScalarHom D m Sc v w (c ⊗ₜ[k] f) = ev c • f := by
  change (elvAffineScalarSpecialization D Sc cut (probeScalarValues D m)
    (probeScalarValues_vanish D m)).map
      (BoxProd.tmulHom (X := ELV.obj D Sc cut v) (Y := ELV.obj D Sc cut w)
        (SuperalgebraCat.ofElem c) f) = _
  rw [elvAffineScalarSpecialization_tmul, SuperalgebraCat.toElem_ofElem]

variable
  (N : Superfunctor k (ELV.OldContentCategory D Sc (probeCutoff D m) ν) (SVec k))

/-- The existing old module action on raw full-coefficient Homs. -/
def probeOldModuleRawAction (v w : C) :
    ELV.hom D Sc cut v.obj.word w.obj.word →ₗ[k] (N.obj v ⟶ N.obj w) :=
  (N.toFunctor.mapLinearMap k (X := v) (Y := w)).comp
    (ELV.ideal D Sc cut v.obj.word w.obj.word).mkQ

@[simp] theorem probeOldModuleRawAction_apply (v w : C)
    (f : ELV.hom D Sc cut v.obj.word w.obj.word) :
    probeOldModuleRawAction D m Sc ν N v w f =
      N.toFunctor.map (show v ⟶ w from
        (ELV.ideal D Sc cut v.obj.word w.obj.word).mkQ f) := rfl

/-- Coefficient evaluation forces raw module action to factor through the
actual scalar specialization. No tensor-kernel or flatness assumption is used. -/
theorem probeOldModuleRawAction_factor (hN : ProbeEvaluatesCoefficients D m Sc ν N)
    (v w : C) (f : ELV.hom D Sc cut v.obj.word w.obj.word) :
    probeOldModuleRawAction D m Sc ν N v w f =
      probeOldModuleRawAction D m Sc ν N v w
        (ELV.affineUnit D Sc cut v.obj.word w.obj.word
          (elvProbeScalarHom D m Sc v.obj.word w.obj.word f)) := by
  have hlin : probeOldModuleRawAction D m Sc ν N v w =
      ((probeOldModuleRawAction D m Sc ν N v w).comp
        (ELV.affineUnit D Sc cut v.obj.word w.obj.word)).comp
          (elvProbeScalarHom D m Sc v.obj.word w.obj.word) := by
    apply TensorProduct.ext
    apply LinearMap.ext
    intro c
    apply LinearMap.ext
    intro g
    change A at c
    change ((pres D Sc).obj (ob D v.obj.word) ⟶ (pres D Sc).obj (ob D w.obj.word)) at g
    change probeOldModuleRawAction D m Sc ν N v w (c ⊗ₜ[k] g) =
      probeOldModuleRawAction D m Sc ν N v w
        (ELV.affineUnit D Sc cut v.obj.word w.obj.word
          (elvProbeScalarHom D m Sc v.obj.word w.obj.word (c ⊗ₜ[k] g)))
    have hraw : ELV.affineUnit D Sc cut v.obj.word w.obj.word g ≫
        (c ⊗ₜ[k] (𝟙 ((pres D Sc).obj (ob D w.obj.word))) : ELV.hom D Sc cut w.obj.word w.obj.word) =
          (c ⊗ₜ[k] g : ELV.hom D Sc cut v.obj.word w.obj.word) := by
      simpa only [Category.comp_id] using
        (ELV.affineUnit_comp_coefficient D Sc cut (v := v.obj.word) (w := w.obj.word) (z := w.obj.word)
          g (𝟙 ((pres D Sc).obj (ob D w.obj.word))) c)
    have hcomp : (show v ⟶ w from
        (ELV.ideal D Sc cut v.obj.word w.obj.word).mkQ (c ⊗ₜ[k] g)) =
      (show v ⟶ w from
        (ELV.ideal D Sc cut v.obj.word w.obj.word).mkQ
          (ELV.affineUnit D Sc cut v.obj.word w.obj.word g)) ≫
            probeOldCoefficient D m Sc ν w c :=
      congrArg (ELV.ideal D Sc cut v.obj.word w.obj.word).mkQ hraw.symm
    rw [probeOldModuleRawAction_apply, hcomp, N.toFunctor.map_comp, hN w c]
    rw [elvProbeScalarHom_tmul, map_smul, map_smul]
    rw [Linear.comp_smul, Category.comp_id]
    rfl
  exact LinearMap.congr_fun hlin f

variable [Fintype I]

theorem probeOldCoefficient_image (v : C) (c : A) :
    probeOldWordEntry D m Sc ν (probeOldCoefficient D m Sc ν v c) =
      ev c • probeOldWordIdempotent D m Sc ν v := by
  change probeHeightMk D m Sc ν.length
    (FiniteHomMatrix.single (⟨v.obj.word,v.wordPerm.length_eq⟩ : Word I ν.length)
      (⟨v.obj.word,v.wordPerm.length_eq⟩ : Word I ν.length)
      (elvProbeScalarHom D m Sc v.obj.word v.obj.word
        (c ⊗ₜ[k] (𝟙 ((pres D Sc).obj (ob D v.obj.word)))))) = _
  rw [elvProbeScalarHom_tmul, FiniteHomMatrix.single_smul, map_smul]
  rfl

variable {B : Type u} [Ring B] [Algebra k B] {GB : ZMod 2 → Submodule k B}
  (M : SuperBimodule
    (heightParity D Sc (probePolynomial (k := k) (probeDotExponent D) m)
      (probePolynomial_parity D m) ν.length) GB)

/-- The concrete probe module satisfies the scalar coefficient condition. -/
theorem probeOldModule_evaluatesCoefficients :
    ProbeEvaluatesCoefficients D m Sc ν (probeOldModule D m Sc ν M) := by
  intro v c
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change M.lact (probeOldWordEntry D m Sc ν (probeOldCoefficient D m Sc ν v c)) x.val =
    ev c • x.val
  rw [probeOldCoefficient_image, map_smul]
  change ev c • M.lact (probeOldWordIdempotent D m Sc ν v) x.val = ev c • x.val
  rw [x.property]

end OddMath.QuiverHecke
end

end

section

/-! # Literal ordinary Hom descent for scalar-evaluated old modules
The image of the original full old ideal is exactly the existing ordinary
cycHom ideal. Actual scalar-evaluated old modules therefore act on that
ordinary Hom quotient, using the proved representation factorization.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped TensorProduct
namespace OddMath.QuiverHecke
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (m : I → ℕ) (Sc : SKM.Scalars D k)
local notation "cut" => probeCutoff D m
local notation "a" => probePolynomial (k := k) (probeDotExponent D) m

/-- The scalar image of the full old ideal is the entire ordinary Hom ideal. -/
theorem elvProbeScalarHom_ideal_image (v w : List I) :
    (ELV.ideal D Sc cut v w).map (elvProbeScalarHom D m Sc v w) = cycHom D Sc a v w := by
  apply le_antisymm
  · rintro _ ⟨g,hg,rfl⟩
    exact elvProbeAffineSpecialization_ideal D m Sc hg
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,t,p,q,rfl⟩
    have hunit {s u : List I}
        (f : (pres D Sc).obj (ob D s) ⟶ (pres D Sc).obj (ob D u)) :
        elvProbeScalarHom D m Sc s u (ELV.affineUnit D Sc cut s u f) = f := by
      change elvProbeScalarHom D m Sc s u ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cut) ⊗ₜ[k] f) = _
      rw [elvProbeScalarHom_tmul, map_one, one_smul]
    refine ⟨ELV.affineUnit D Sc cut _ _ p ≫ ELV.relation D Sc cut i t ≫
      ELV.affineUnit D Sc cut _ _ q, ?_, ?_⟩
    · exact Submodule.subset_span ⟨i,t,
        ELV.affineUnit D Sc cut _ _ p, ELV.affineUnit D Sc cut _ _ q,rfl⟩
    · rw [elvProbeScalarHom_comp, elvProbeScalarHom_comp,
        hunit, hunit, elvProbeScalarHom_relation]

variable (ν : List I)
local notation "C" => ELV.OldContentCategory D Sc cut ν
variable
  (N : Superfunctor k (ELV.OldContentCategory D Sc (probeCutoff D m) ν) (SVec k))

/-- No ordinary first-dot relation survives in an actual scalar-evaluated old module. -/
theorem probeOldModuleRawAction_kills_cycHom
    (hN : ProbeEvaluatesCoefficients D m Sc ν N) (v w : C) :
    cycHom D Sc a v.obj.word w.obj.word ≤
      LinearMap.ker ((probeOldModuleRawAction D m Sc ν N v w).comp
        (ELV.affineUnit D Sc cut v.obj.word w.obj.word)) := by
  intro f hf
  rw [← elvProbeScalarHom_ideal_image D m Sc] at hf
  obtain ⟨g,hg,rfl⟩ := hf
  change probeOldModuleRawAction D m Sc ν N v w
    (ELV.affineUnit D Sc cut _ _ (elvProbeScalarHom D m Sc _ _ g)) = 0
  rw [← probeOldModuleRawAction_factor D m Sc ν N hN]
  have hz : (ELV.ideal D Sc cut v.obj.word w.obj.word).mkQ g = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr hg
  rw [probeOldModuleRawAction_apply, hz, N.toFunctor.map_zero]

/-- The literal ordinary cycHom quotient acts on the actual old module values. -/
def probeOrdinaryModuleHom (hN : ProbeEvaluatesCoefficients D m Sc ν N) (v w : C) :
    (((pres D Sc).obj (ob D v.obj.word) ⟶ (pres D Sc).obj (ob D w.obj.word)) ⧸
      cycHom D Sc a v.obj.word w.obj.word) →ₗ[k] (N.obj v ⟶ N.obj w) :=
  (cycHom D Sc a v.obj.word w.obj.word).liftQ
    ((probeOldModuleRawAction D m Sc ν N v w).comp
      (ELV.affineUnit D Sc cut v.obj.word w.obj.word))
    (probeOldModuleRawAction_kills_cycHom D m Sc ν N hN v w)

@[simp] theorem probeOrdinaryModuleHom_mk (hN : ProbeEvaluatesCoefficients D m Sc ν N)
    (v w : C) (f : (pres D Sc).obj (ob D v.obj.word) ⟶ (pres D Sc).obj (ob D w.obj.word)) :
    probeOrdinaryModuleHom D m Sc ν N hN v w ((cycHom D Sc a v.obj.word w.obj.word).mkQ f) =
      probeOldModuleRawAction D m Sc ν N v w (ELV.affineUnit D Sc cut v.obj.word w.obj.word f) := rfl

/-- This is descent of the existing actual old arrow action, not a new representation choice. -/
theorem probeOrdinaryModuleHom_old (hN : ProbeEvaluatesCoefficients D m Sc ν N)
    (v w : C) (f : v ⟶ w) :
    probeOrdinaryModuleHom D m Sc ν N hN v w
      (elvProbeOldHom D m Sc v.obj.word w.obj.word f) = N.toFunctor.map f := by
  obtain ⟨f,rfl⟩ := (ELV.ideal D Sc cut v.obj.word w.obj.word).mkQ_surjective f
  rw [elvProbeOldHom_mk, probeOrdinaryModuleHom_mk]
  change probeOldModuleRawAction D m Sc ν N v w
    (ELV.affineUnit D Sc cut v.obj.word w.obj.word
      (elvProbeScalarHom D m Sc v.obj.word w.obj.word f)) =
        probeOldModuleRawAction D m Sc ν N v w f
  exact (probeOldModuleRawAction_factor D m Sc ν N hN v w f).symm

end OddMath.QuiverHecke
end

end

section

/-! # The literal ordinary probe content category
Homs are the existing ordinary cycHom quotients. Canonical scalar
specialization is full, and actual scalar-evaluated old modules descend
through it with their original arrow action.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (a : I → Polynomial k)

/-- Fixed-content words with the existing ordinary cyclotomic Hom quotients. -/
structure OrdinaryContentCategory (D : SKM.Datum I X) (Sc : SKM.Scalars D k)
    (a : I → Polynomial k) (ν : List I) where
  word : List I
  wordPerm : word.Perm ν

def ordinaryContentComp (v t w : List I) :
    (((pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D t)) ⧸ cycHom D Sc a v t) →ₗ[k]
    (((pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D w)) ⧸ cycHom D Sc a t w) →ₗ[k]
    (((pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D w)) ⧸ cycHom D Sc a v w) :=
  LinearMap.liftQ₂ _ _
    ({ toFun := fun f =>
        { toFun := fun g => (cycHom D Sc a v w).mkQ (f ≫ g)
          map_add' := by intros; simp only [Preadditive.comp_add, map_add]
          map_smul' := by intros; simp only [Linear.comp_smul, map_smul, RingHom.id_apply] }
       map_add' := by intros; ext g; simp only [LinearMap.coe_mk, AddHom.coe_mk,
         Preadditive.add_comp, map_add, LinearMap.add_apply]
       map_smul' := by intros; ext g; simp only [LinearMap.coe_mk, AddHom.coe_mk,
         Linear.smul_comp, map_smul, LinearMap.smul_apply, RingHom.id_apply] } :
      ((pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D t)) →ₗ[k]
      ((pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D w)) →ₗ[k] _)
    (by
      intro f hf
      ext g
      exact (Submodule.Quotient.mk_eq_zero _).mpr (cycHom_comp_right D Sc hf g))
    (by
      intro g hg
      ext f
      exact (Submodule.Quotient.mk_eq_zero _).mpr (cycHom_comp_left D Sc f hg))

@[simp] theorem ordinaryContentComp_mk (v t w : List I)
    (f : (pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D t))
    (g : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D w)) :
    ordinaryContentComp D Sc a v t w ((cycHom D Sc a v t).mkQ f) ((cycHom D Sc a t w).mkQ g) =
      (cycHom D Sc a v w).mkQ (f ≫ g) := rfl

instance ordinaryContentCategory (ν : List I) : Category (OrdinaryContentCategory D Sc a ν) where
  Hom v w := ((pres D Sc).obj (ob D v.word) ⟶ (pres D Sc).obj (ob D w.word)) ⧸ cycHom D Sc a v.word w.word
  id v := (cycHom D Sc a v.word v.word).mkQ (𝟙 _)
  comp {v t w} f g := ordinaryContentComp D Sc a v.word t.word w.word f g
  id_comp := by
    intro v w f
    obtain ⟨f,rfl⟩ := (cycHom D Sc a v.word w.word).mkQ_surjective f
    exact congrArg (cycHom D Sc a v.word w.word).mkQ (Category.id_comp f)
  comp_id := by
    intro v w f
    obtain ⟨f,rfl⟩ := (cycHom D Sc a v.word w.word).mkQ_surjective f
    exact congrArg (cycHom D Sc a v.word w.word).mkQ (Category.comp_id f)
  assoc := by
    intro v t w z f g h
    obtain ⟨f,rfl⟩ := (cycHom D Sc a v.word t.word).mkQ_surjective f
    obtain ⟨g,rfl⟩ := (cycHom D Sc a t.word w.word).mkQ_surjective g
    obtain ⟨h,rfl⟩ := (cycHom D Sc a w.word z.word).mkQ_surjective h
    exact congrArg (cycHom D Sc a v.word z.word).mkQ (Category.assoc f g h)

instance ordinaryContentPreadditive (ν : List I) : Preadditive (OrdinaryContentCategory D Sc a ν) where
  homGroup v w := inferInstanceAs (AddCommGroup (((pres D Sc).obj (ob D v.word) ⟶
    (pres D Sc).obj (ob D w.word)) ⧸ cycHom D Sc a v.word w.word))
  add_comp := by intro v w z f g h; exact LinearMap.map_add₂ (ordinaryContentComp D Sc a v.word w.word z.word) f g h
  comp_add := by intro v w z f g h; exact (ordinaryContentComp D Sc a v.word w.word z.word f).map_add g h

instance ordinaryContentLinear (ν : List I) : Linear k (OrdinaryContentCategory D Sc a ν) where
  homModule v w := inferInstanceAs (Module k (((pres D Sc).obj (ob D v.word) ⟶
    (pres D Sc).obj (ob D w.word)) ⧸ cycHom D Sc a v.word w.word))
  smul_comp := by intro v w z r f g; exact LinearMap.map_smul₂ (ordinaryContentComp D Sc a v.word w.word z.word) r f g
  comp_smul := by intro v w z f r g; exact (ordinaryContentComp D Sc a v.word w.word z.word f).map_smul r g

variable (m : I → ℕ) (ν : List I)
local notation "cut" => probeCutoff D m
local notation "probe" => probePolynomial (k := k) (probeDotExponent D) m
local notation "C" => ELV.OldContentCategory D Sc cut ν
local notation "Q" => OrdinaryContentCategory D Sc probe ν

/-- Actual scalar specialization, on the literal ordinary quotient category. -/
def probeOldOrdinaryFunctor : C ⥤ Q where
  obj v := ⟨v.obj.word,v.wordPerm⟩
  map {v w} := elvProbeOldHom D m Sc v.obj.word w.obj.word
  map_id v := by
    change (cycHom D Sc probe v.obj.word v.obj.word).mkQ
      (elvProbeScalarHom D m Sc v.obj.word v.obj.word (𝟙 (ELV.obj D Sc cut v.obj.word))) = _
    rw [elvProbeScalarHom_id]
    rfl
  map_comp {v t w} f g := by
    obtain ⟨f,rfl⟩ := (ELV.ideal D Sc cut v.obj.word t.obj.word).mkQ_surjective f
    obtain ⟨g,rfl⟩ := (ELV.ideal D Sc cut t.obj.word w.obj.word).mkQ_surjective g
    change (cycHom D Sc probe v.obj.word w.obj.word).mkQ
      (elvProbeScalarHom D m Sc v.obj.word w.obj.word (f ≫ g)) =
      ordinaryContentComp D Sc probe v.obj.word t.obj.word w.obj.word
        ((cycHom D Sc probe v.obj.word t.obj.word).mkQ (elvProbeScalarHom D m Sc _ _ f))
        ((cycHom D Sc probe t.obj.word w.obj.word).mkQ (elvProbeScalarHom D m Sc _ _ g))
    rw [ordinaryContentComp_mk, elvProbeScalarHom_comp]

instance : (probeOldOrdinaryFunctor D Sc m ν).Full where
  map_surjective {v w} f := elvProbeOldHom_surjective D m Sc v.obj.word w.obj.word f
instance : (probeOldOrdinaryFunctor D Sc m ν).Additive where
  map_add {v w} f g := (elvProbeOldHom D m Sc v.obj.word w.obj.word).map_add f g
instance : (probeOldOrdinaryFunctor D Sc m ν).Linear k where
  map_smul {v w} f r := (elvProbeOldHom D m Sc v.obj.word w.obj.word).map_smul r f

/-- The same actual word, viewed in the source old content category. -/
def probeOrdinaryOldObject (v : Q) : C := ⟨⟨v.word⟩,v.wordPerm⟩

@[simp] theorem probeOldOrdinaryFunctor_obj_lift (v : Q) :
    (probeOldOrdinaryFunctor D Sc m ν).obj (probeOrdinaryOldObject D Sc m ν v) = v := by
  cases v
  rfl

variable
  (N : Superfunctor k (ELV.OldContentCategory D Sc (probeCutoff D m) ν) (SVec k))
  (hN : ProbeEvaluatesCoefficients D m Sc ν N)

/-- The actual descended ordinary module on precisely the original old module values. -/
def probeOrdinaryModuleFunctor : Q ⥤ SVec k where
  obj v := N.obj (probeOrdinaryOldObject D Sc m ν v)
  map {v w} := probeOrdinaryModuleHom D m Sc ν N hN
    (probeOrdinaryOldObject D Sc m ν v) (probeOrdinaryOldObject D Sc m ν w)
  map_id v := by
    change probeOldModuleRawAction D m Sc ν N
      (probeOrdinaryOldObject D Sc m ν v) (probeOrdinaryOldObject D Sc m ν v)
      (ELV.affineUnit D Sc cut v.word v.word (𝟙 _)) = _
    rw [ELV.affineUnit_id]
    exact N.toFunctor.map_id _
  map_comp {v t w} f g := by
    obtain ⟨f,rfl⟩ := (cycHom D Sc probe v.word t.word).mkQ_surjective f
    obtain ⟨g,rfl⟩ := (cycHom D Sc probe t.word w.word).mkQ_surjective g
    change probeOldModuleRawAction D m Sc ν N
      (probeOrdinaryOldObject D Sc m ν v) (probeOrdinaryOldObject D Sc m ν w)
      (ELV.affineUnit D Sc cut v.word w.word (f ≫ g)) =
      probeOldModuleRawAction D m Sc ν N
        (probeOrdinaryOldObject D Sc m ν v) (probeOrdinaryOldObject D Sc m ν t)
        (ELV.affineUnit D Sc cut v.word t.word f) ≫
      probeOldModuleRawAction D m Sc ν N
        (probeOrdinaryOldObject D Sc m ν t) (probeOrdinaryOldObject D Sc m ν w)
        (ELV.affineUnit D Sc cut t.word w.word g)
    rw [ELV.affineUnit_comp]
    exact N.toFunctor.map_comp
      (show probeOrdinaryOldObject D Sc m ν v ⟶ probeOrdinaryOldObject D Sc m ν t from
        (ELV.ideal D Sc cut v.word t.word).mkQ (ELV.affineUnit D Sc cut v.word t.word f))
      (show probeOrdinaryOldObject D Sc m ν t ⟶ probeOrdinaryOldObject D Sc m ν w from
        (ELV.ideal D Sc cut t.word w.word).mkQ (ELV.affineUnit D Sc cut t.word w.word g))

instance : (probeOrdinaryModuleFunctor D Sc m ν N hN).Additive where
  map_add {v w} f g := (probeOrdinaryModuleHom D m Sc ν N hN
    (probeOrdinaryOldObject D Sc m ν v) (probeOrdinaryOldObject D Sc m ν w)).map_add f g
instance : (probeOrdinaryModuleFunctor D Sc m ν N hN).Linear k where
  map_smul {v w} f r := (probeOrdinaryModuleHom D m Sc ν N hN
    (probeOrdinaryOldObject D Sc m ν v) (probeOrdinaryOldObject D Sc m ν w)).map_smul r f

/-- Restriction along the full scalar functor recovers the existing old module exactly. -/
theorem probeOrdinaryModuleFunctor_restrict :
    probeOldOrdinaryFunctor D Sc m ν ⋙ probeOrdinaryModuleFunctor D Sc m ν N hN = N.toFunctor := by
  apply CategoryTheory.Functor.ext
  case h_obj =>
    intro v
    rfl
  case h_map =>
    intro v w f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    exact probeOrdinaryModuleHom_old D m Sc ν N hN v w f

end OddMath.QuiverHecke
end

end

section

/-! # The literal commuting append square for scalar probe specialization
Ordinary right append acts on the existing cycHom quotients. The full scalar
functors commute with canonical old append exactly, providing the concrete
square for the induction-composition comparison.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
namespace OddMath.QuiverHecke
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ) (ν : List I)
local notation "cut" => probeCutoff D m
local notation "a" => probePolynomial (k := k) (probeDotExponent D) m
local notation "C" => OrdinaryContentCategory D Sc a ν

/-- Right append on the literal ordinary quotient content category. -/
def probeOrdinaryAppend (i : I) : C ⥤ OrdinaryContentCategory D Sc a (i :: ν) where
  obj v := ⟨v.word ++ [i], (v.wordPerm.append (List.Perm.refl [i])).trans
    (List.perm_append_comm : (ν ++ [i]).Perm ([i] ++ ν))⟩
  map {v w} := probeCycHomRightContext D m Sc [i] v.word w.word
  map_id v := by
    change (cycHom D Sc a (v.word ++ [i]) (v.word ++ [i])).mkQ
      ((𝟙 ((pres D Sc).obj (ob D v.word))) ▷ ((pres D Sc).obj (ob D [i]))) = _
    exact congrArg (cycHom D Sc a (v.word ++ [i]) (v.word ++ [i])).mkQ
      (MonoidalSupercategory.id_whiskerRight (R := k) _ _)
  map_comp {v t w} f g := by
    obtain ⟨f,rfl⟩ := (cycHom D Sc a v.word t.word).mkQ_surjective f
    obtain ⟨g,rfl⟩ := (cycHom D Sc a t.word w.word).mkQ_surjective g
    change (cycHom D Sc a (v.word ++ [i]) (w.word ++ [i])).mkQ
      ((f ≫ g) ▷ ((pres D Sc).obj (ob D [i]))) =
      (cycHom D Sc a (v.word ++ [i]) (w.word ++ [i])).mkQ
        ((f ▷ ((pres D Sc).obj (ob D [i]))) ≫ (g ▷ ((pres D Sc).obj (ob D [i]))))
    exact congrArg (cycHom D Sc a (v.word ++ [i]) (w.word ++ [i])).mkQ
      (MonoidalSupercategory.comp_whiskerRight (R := k) f g _)

instance (i : I) : (probeOrdinaryAppend D Sc m ν i).Additive where
  map_add {v w} f g := (probeCycHomRightContext D m Sc [i] v.word w.word).map_add f g
instance (i : I) : (probeOrdinaryAppend D Sc m ν i).Linear k where
  map_smul {v w} f r := (probeCycHomRightContext D m Sc [i] v.word w.word).map_smul r f

/-- The square uses the actual old append, actual full scalar functors and
actual ordinary quotient append, with no assumed natural comparison. -/
theorem probeOldOrdinaryFunctor_append (i : I) :
    ELV.oldContentAppend D Sc cut ν i ⋙ probeOldOrdinaryFunctor D Sc m (i :: ν) =
      probeOldOrdinaryFunctor D Sc m ν ⋙ probeOrdinaryAppend D Sc m ν i := by
  apply CategoryTheory.Functor.ext
  case h_obj =>
    intro v
    rfl
  case h_map =>
    intro v w f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    exact elvProbeOldHom_rightContext D m Sc [i] v.obj.word w.obj.word f

end OddMath.QuiverHecke
end

end

section

/-! # Super grading of the literal ordinary probe quotient category
Parity descends from the actual old ideal through the even scalar
specialization. This upgrades the checked full scalar, append and module
functors without a new homogeneous-generator hypothesis.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
namespace OddMath.QuiverHecke
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
local notation "cut" => probeCutoff D m
local notation "a" => probePolynomial (k := k) (probeDotExponent D) m

theorem elvProbeScalarHom_proj {v w : List I} (p : ZMod 2)
    (f : ELV.hom D Sc cut v w) :
    elvProbeScalarHom D m Sc v w (proj k p f) =
      proj k p (elvProbeScalarHom D m Sc v w f) :=
  Supercategory.map_proj (elvProbeAffineSpecialization D m Sc).toFunctor p f

/-- The ordinary relation ideal inherits parity projection stability from the old ideal. -/
theorem probeCycHom_proj_mem {v w : List I}
    {f : (pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D w)}
    (hf : f ∈ cycHom D Sc a v w) (p : ZMod 2) :
    proj k p f ∈ cycHom D Sc a v w := by
  rw [← elvProbeScalarHom_ideal_image D m Sc] at hf
  obtain ⟨g,hg,rfl⟩ := hf
  have h := elvProbeAffineSpecialization_ideal D m Sc (ELV.ideal_proj_mem D Sc cut hg p)
  rw [elvProbeScalarHom_proj] at h
  exact h

private def probeOrdinaryGradedIdeal (v w : List I) :
    SVec.GradedSubmodule (homSVec k (H D Sc) ((pres D Sc).obj (ob D v)) ((pres D Sc).obj (ob D w))) where
  toSubmodule := cycHom D Sc a v w
  odd_mem _f hf := probeCycHom_proj_mem D Sc m hf 1

/-- The literal ordinary Hom quotient with its inherited superspace structure. -/
def probeOrdinaryHomSpace (v w : List I) : SVec k :=
  SVec.quot (homSVec k (H D Sc) ((pres D Sc).obj (ob D v)) ((pres D Sc).obj (ob D w)))
    (probeOrdinaryGradedIdeal D Sc m v w)

theorem probeOrdinaryHomSpace_mk_mem {v w : List I} {p : ZMod 2}
    {f : (pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D w)}
    (hf : f ∈ parity (R := k) _ _ p) :
    (cycHom D Sc a v w).mkQ f ∈ (probeOrdinaryHomSpace D Sc m v w).part p :=
  SVec.quotMkFun_mem_part _ _ ((mem_homSVec_part_iff k).mpr hf)

theorem probeOrdinaryHomSpace_lift {v w : List I} {p : ZMod 2}
    {f : (((pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D w)) ⧸ cycHom D Sc a v w)}
    (hf : f ∈ (probeOrdinaryHomSpace D Sc m v w).part p) :
    ∃ g : (pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D w),
      g ∈ parity (R := k) _ _ p ∧ (cycHom D Sc a v w).mkQ g = f := by
  obtain ⟨g,rfl⟩ := (cycHom D Sc a v w).mkQ_surjective f
  refine ⟨proj k p g, proj_mem p g, ?_⟩
  have h := (SVec.mem_part_iff _).mp hf
  change (SVec.quot _ (probeOrdinaryGradedIdeal D Sc m v w)).proj p
    (SVec.quotMkFun _ (probeOrdinaryGradedIdeal D Sc m v w) g) = _ at h
  rw [SVec.quot_proj_mk, homSVec_proj] at h
  exact h

instance probeOrdinarySupercategory (ν : List I) :
    Supercategory k (OrdinaryContentCategory D Sc a ν) where
  parity v w := (probeOrdinaryHomSpace D Sc m v.word w.word).part
  isInternal v w := SVec.isInternal_part _
  id_mem v := probeOrdinaryHomSpace_mk_mem D Sc m (id_mem _)
  comp_mem := by
    intro v t w p q f g hf hg
    obtain ⟨fr,hfr,rfl⟩ := probeOrdinaryHomSpace_lift D Sc m hf
    obtain ⟨gr,hgr,rfl⟩ := probeOrdinaryHomSpace_lift D Sc m hg
    exact probeOrdinaryHomSpace_mk_mem D Sc m (Supercategory.comp_mem hfr hgr)

instance probeOldOrdinaryFunctor_super (ν : List I) :
    IsSuperfunctor k (probeOldOrdinaryFunctor D Sc m ν) where
  map_mem := by
    intro v w p f hf
    obtain ⟨fr,hfr,rfl⟩ := hf
    apply probeOrdinaryHomSpace_mk_mem D Sc m
    exact (elvProbeAffineSpecialization D m Sc).map_mem hfr

instance probeOrdinaryAppend_super (ν : List I) (i : I) :
    IsSuperfunctor k (probeOrdinaryAppend D Sc m ν i) where
  map_mem := by
    intro v w p f hf
    obtain ⟨fr,hfr,rfl⟩ := probeOrdinaryHomSpace_lift D Sc m hf
    exact probeOrdinaryHomSpace_mk_mem D Sc m
      (MonoidalSupercategory.whiskerRight_mem ((pres D Sc).obj (ob D [i])) hfr)

def probeOldOrdinarySuperfunctor (ν : List I) :
    Superfunctor k (ELV.OldContentCategory D Sc cut ν) (OrdinaryContentCategory D Sc a ν) :=
  ⟨probeOldOrdinaryFunctor D Sc m ν⟩

variable (ν : List I)
  (N : Superfunctor k (ELV.OldContentCategory D Sc (probeCutoff D m) ν) (SVec k))
  (hN : ProbeEvaluatesCoefficients D m Sc ν N)

instance probeOrdinaryModuleFunctor_super :
    IsSuperfunctor k (probeOrdinaryModuleFunctor D Sc m ν N hN) where
  map_mem := by
    intro v w p f hf
    obtain ⟨fr,hfr,rfl⟩ := probeOrdinaryHomSpace_lift D Sc m hf
    apply N.map_mem
    exact Submodule.mem_map_of_mem (ELVPScalar.affineUnit_mem D Sc cut hfr)

def probeOrdinaryModuleSuperfunctor :
    Superfunctor k (OrdinaryContentCategory D Sc a ν) (SVec k) :=
  ⟨probeOrdinaryModuleFunctor D Sc m ν N hN⟩

theorem probeOrdinaryModuleSuperfunctor_restrict :
    (probeOldOrdinarySuperfunctor D Sc m ν).comp
      (probeOrdinaryModuleSuperfunctor D Sc m ν N hN) = N := by
  apply Superfunctor.ext
  exact probeOrdinaryModuleFunctor_restrict D Sc m ν N hN

end OddMath.QuiverHecke
end

end

section

/-! # Old append induction preserves actual scalar coefficient evaluation
The full coefficient slide and the existing coend balance prove preservation,
including the odd coefficient kernel. No scalar evaluation is applied to a
positive-weight coefficient truncation.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped TensorProduct
namespace OddMath.QuiverHecke
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (m : I → ℕ) (Sc : SKM.Scalars D k)
local notation "cut" => probeCutoff D m
local notation "A" => SKM.SYM.ELVCoefficientAlgebra (k := k) D cut
local notation "ev" => SKM.SYM.elvScalarEvaluation D cut (probeScalarValues D m) (probeScalarValues_vanish D m)
variable (ν : List I)
local notation "C" => ELV.OldContentCategory D Sc cut ν

@[simp] theorem probeOldCoefficient_zero (v : C) :
    probeOldCoefficient D m Sc ν v 0 = 0 := by
  change (ELV.ideal D Sc cut _ _).mkQ (0 ⊗ₜ[k] (𝟙 _)) = 0
  rw [TensorProduct.zero_tmul, map_zero]

theorem probeOldCoefficient_add (v : C) (c d : A) :
    probeOldCoefficient D m Sc ν v (c + d) =
      probeOldCoefficient D m Sc ν v c + probeOldCoefficient D m Sc ν v d := by
  change (ELV.ideal D Sc cut _ _).mkQ ((c+d) ⊗ₜ[k] (𝟙 _)) = _
  rw [TensorProduct.add_tmul, map_add]
  rfl

/-- The complete output parity twist is retained in the actual content quotient. -/
theorem probeOldCoefficient_slide {v w : C} {p : ZMod 2} {c : A}
    (hc : c ∈ SKM.SYM.elvCoefficientParity D cut p) (f : v ⟶ w) :
    f ≫ probeOldCoefficient D m Sc ν w c =
      probeOldCoefficient D m Sc ν v c ≫ twist k p f := by
  obtain ⟨f, rfl⟩ := (ELV.ideal D Sc cut v.obj.word w.obj.word).mkQ_surjective f
  have htw : twist k p (X := v) (Y := w)
      ((ELV.ideal D Sc cut v.obj.word w.obj.word).mkQ f) =
    (ELV.ideal D Sc cut v.obj.word w.obj.word).mkQ
      (twist k p (X := ELV.obj D Sc cut v.obj.word) (Y := ELV.obj D Sc cut w.obj.word) f) := by
    change twist k p (X := v.obj) (Y := w.obj) _ = _
    simp only [twist_apply, ELV.oldCategory_proj, ELV.oldProj_mk, map_add, map_smul]
  rw [htw]
  exact congrArg (ELV.ideal D Sc cut v.obj.word w.obj.word).mkQ
    (ELVPScalar.scalar_slide_homogeneous D Sc cut hc f)

@[simp] theorem probeOldCoefficient_append (i : I) (v : C) (c : A) :
    (ELV.oldContentAppend D Sc cut ν i).map (probeOldCoefficient D m Sc ν v c) =
      probeOldCoefficient D m Sc (i :: ν) ((ELV.oldContentAppend D Sc cut ν i).obj v) c := by
  change (ELV.ideal D Sc cut _ _).mkQ
    (ELV.rightContext D Sc cut [i] v.obj.word v.obj.word
      (ELVPScalar.scalar D Sc cut v.obj.word c)) = _
  rw [ELVPScalar.rightContext_scalar]
  rfl

/-- The concrete scalar-evaluation class is closed under the actual old
content append induction, including its odd coefficient kernel. -/
theorem probeOldInduced_evaluatesCoefficients (i : I)
    (N : Superfunctor k (ELV.OldContentCategory D Sc (probeCutoff D m) ν) (SVec k))
    (hN : ProbeEvaluatesCoefficients D m Sc ν N) :
    ProbeEvaluatesCoefficients D m Sc (i :: ν)
      (ELV.BalancedInduction.induced (ELV.oldContentAppend D Sc cut ν i) N) := by
  intro t c
  let J := ELV.oldContentAppend D Sc cut ν i
  let L := ELV.BalancedInduction.induced J N
  change L.toFunctor.map (probeOldCoefficient D m Sc (i :: ν) t c) = ev c • 𝟙 (L.obj t)
  refine DirectSum.Decomposition.inductionOn (SKM.SYM.elvCoefficientParity D cut) ?_ ?_ ?_ c
  · rw [probeOldCoefficient_zero, L.toFunctor.map_zero, map_zero, zero_smul]
  · intro p c
    change ELV.BalancedInduction.postcompose J N.toFunctor
      (probeOldCoefficient D m Sc (i :: ν) t c.val) = ev c.val • LinearMap.id
    apply ELV.BalancedInduction.hom_ext
    intro v g b
    rw [ELV.BalancedInduction.postcompose_tensor,
      probeOldCoefficient_slide D m Sc (i :: ν) c.property]
    have hcoef : probeOldCoefficient D m Sc (i :: ν) (J.obj v) c.val =
        J.map (probeOldCoefficient D m Sc ν v c.val) :=
      (probeOldCoefficient_append D m Sc ν i v c.val).symm
    rw [hcoef, ELV.BalancedInduction.balance, hN v c.val]
    change ELV.BalancedInduction.tensor J N.toFunctor v (twist k p g) (ev c.val • b) =
      ev c.val • ELV.BalancedInduction.tensor J N.toFunctor v g b
    rcases parity_eq_zero_or_one p with rfl | rfl
    · rw [twist_zero]
      simp only [ELV.BalancedInduction.tensor, TensorProduct.tmul_smul, map_smul]
    · have hc : ev c.val = 0 := SKM.SYM.elvScalarEvaluation_odd_zero D cut
        (probeScalarValues D m) (probeScalarValues_vanish D m) c.property
      simp only [hc, zero_smul, ELV.BalancedInduction.tensor, TensorProduct.tmul_zero, map_zero]
  · intro c d hc hd
    rw [probeOldCoefficient_add, L.toFunctor.map_add, hc, hd, map_add, add_smul]

end OddMath.QuiverHecke
end

end

section

/-! # Scalar quotient and ordinary probe append induction
The proved scalar-kernel closure, the full quotient counit and composition
of balanced induction identify old scalar append induction with literal
ordinary quotient append induction. No height-algebra identification or
weighted coefficient-truncation specialization is used.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ) (ν : List I)
local notation "a" => probePolynomial (k := k) (probeDotExponent D) m
local notation "cut" => probeCutoff D m
local notation "Q" => probeOldOrdinaryFunctor D Sc m ν
local notation "C" => ELV.OldContentCategory D Sc cut ν
local notation "O" => OrdinaryContentCategory D Sc a ν

/-- Restriction uses the existing full scalar Superfunctor. -/
def probeOrdinaryRestriction (M : Superfunctor k O (SVec k)) : Superfunctor k C (SVec k) :=
  (probeOldOrdinarySuperfunctor D Sc m ν).comp M

variable (M : Superfunctor k (OrdinaryContentCategory D Sc
  (probePolynomial (k := k) (probeDotExponent D) m) ν) (SVec k))

private def probeQuotientCounitInverse (w : O) :
    M.obj w →ₗ[k] ELV.BalancedInduction.Obj Q (Q ⋙ M.toFunctor) w :=
  ELV.BalancedInduction.unit Q (Q ⋙ M.toFunctor) (probeOrdinaryOldObject D Sc m ν w)

private theorem probeQuotientCounit_right_inv (w : O) :
    (ELV.BalancedInduction.counit Q M.toFunctor w).comp
      (probeQuotientCounitInverse D Sc m ν M w) = LinearMap.id :=
  ELV.BalancedInduction.counit_unit Q M.toFunctor (probeOrdinaryOldObject D Sc m ν w)

private theorem probeQuotientCounit_left_inv (w : O) :
    (probeQuotientCounitInverse D Sc m ν M w).comp
      (ELV.BalancedInduction.counit Q M.toFunctor w) = LinearMap.id :=
  ELV.BalancedInduction.unit_counit_of_full Q M.toFunctor (probeOrdinaryOldObject D Sc m ν w)

/-- The full scalar quotient counit is an even isomorphism on modules. -/
def probeQuotientCounitIso :
    ELV.BalancedInduction.induced Q (probeOrdinaryRestriction D Sc m ν M) ≅ M :=
  ELV.moduleIsoOfEvenNatIso _ _
    (NatIso.ofComponents (fun w =>
      { hom := ELV.BalancedInduction.counit Q M.toFunctor w
        inv := probeQuotientCounitInverse D Sc m ν M w
        hom_inv_id := probeQuotientCounit_left_inv D Sc m ν M w
        inv_hom_id := probeQuotientCounit_right_inv D Sc m ν M w })
      (fun f => ELV.BalancedInduction.counit_naturality Q M.toFunctor f))
    (fun w => ELV.BalancedInduction.counit_mem Q M w)
    (fun w => ELV.BalancedInduction.unit_mem Q (probeOrdinaryRestriction D Sc m ν M)
      (probeOrdinaryOldObject D Sc m ν w))

variable
  (N : Superfunctor k (ELV.OldContentCategory D Sc (probeCutoff D m) ν) (SVec k))
  (hN : ProbeEvaluatesCoefficients D m Sc ν N)

/-- The scalar-evaluated old module has precisely its descended ordinary induction. -/
def probeQuotientInducedModuleIso :
    ELV.BalancedInduction.induced Q N ≅ probeOrdinaryModuleSuperfunctor D Sc m ν N hN :=
  ((ELV.BalancedInduction.induction Q).mapIso
    (eqToIso (probeOrdinaryModuleSuperfunctor_restrict D Sc m ν N hN))).symm ≪≫
      probeQuotientCounitIso D Sc m ν (probeOrdinaryModuleSuperfunctor D Sc m ν N hN)

/-- Actual old append induction, descended by proved scalar-kernel closure,
agrees with literal ordinary append induction of the descended module. -/
def probeAppendOrdinaryModuleIso (i : I) :
    probeOrdinaryModuleSuperfunctor D Sc m (i :: ν)
      (ELV.BalancedInduction.induced (ELV.oldContentAppend D Sc cut ν i) N)
      (probeOldInduced_evaluatesCoefficients D m Sc ν i N hN) ≅
    ELV.BalancedInduction.induced (probeOrdinaryAppend D Sc m ν i)
      (probeOrdinaryModuleSuperfunctor D Sc m ν N hN) :=
  let J := ELV.oldContentAppend D Sc cut ν i
  let T := probeOrdinaryAppend D Sc m ν i
  let U := probeOldOrdinaryFunctor D Sc m (i :: ν)
  let L := ELV.BalancedInduction.induced J N
  let hL := probeOldInduced_evaluatesCoefficients D m Sc ν i N hN
  (probeQuotientInducedModuleIso D Sc m (i :: ν) L hL).symm ≪≫
    (ELV.BalancedInduction.inductionComp J U).app N ≪≫
      ELV.BalancedInduction.inducedIsoOfFunctorEq (J ⋙ U) (Q ⋙ T)
        (probeOldOrdinaryFunctor_append D Sc m ν i) N ≪≫
      ((ELV.BalancedInduction.inductionComp Q T).app N).symm ≪≫
      (ELV.BalancedInduction.induction T).mapIso
        (probeQuotientInducedModuleIso D Sc m ν N hN)

end OddMath.QuiverHecke
end

end
