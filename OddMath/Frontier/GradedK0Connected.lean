import OddMath.Frontier.GradedK0Basic
import Mathlib.Algebra.GeomSum
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.Int.Basic

/-!
# Graded projectives over a connected graded ring

`A` is connected: `A d = 0` for `d < 0`, `A 0 = ℤ · 1`, and `ℤ → R` is injective.
For a degree-zero `e` on `(ι, s)` the entry `e i j` vanishes when `s i < s j` and is an
integer when `s i = s j`. Hence `e` is block triangular with respect to the shifts, and its
degree-zero reduction `ē` (`diagPart`, entries between equal shifts) is multiplicative.

Classification (`exists_free`). Every graded idempotent is Murray–von Neumann equivalent
to a graded free one `R^m{t}`:
* `e ~ ē`: the strictly triangular part is nilpotent, `z = e ē + (1 - e)(1 - ē)` is a unit
  with `e z = z ē`, and `u = z ē`, `v = ē z⁻¹` realise the equivalence;
* `ē` is an integer idempotent, block diagonal along the shift values; each block splits as
  `P Q` with `Q P = 1` because the image of an idempotent integer matrix is a free direct
  summand (`ℤ` is a PID).

Uniqueness (`card_shift_eq`). The multiplicity of `k` among the shifts `t` equals the rank of
the integer idempotent `ē_k` (`intBlock`, the block of indices with `s i = k`). The invariant
is the graded Hattori–Stallings rank `gdim (R^n{s}·e) = ∑ᵢ ε(e i i) T^{s i}`, where `ε`
reads off the integer of a degree-zero element.

Consequently `K0 A ≃ ℤ[T;T⁻¹]` as `ℤ[T;T⁻¹]`-modules (`classify`), sending `[P]` to its
graded rank and `[R{k}]` to `T k`; `K0 A` is free of rank one on `[R]` (`basis`).
-/

noncomputable section
open Matrix

namespace OddMath.Frontier.GradedK0

variable {R : Type*} [Ring R] {A : ℤ → AddSubgroup R}

variable (A) in
/-- A connected `ℤ`-graded ring: no negative degrees and degree zero equal to `ℤ · 1`. -/
structure Connected : Prop where
  neg : ∀ d < 0, ∀ x ∈ A d, x = 0
  zero : ∀ x ∈ A 0, ∃ z : ℤ, (z : R) = x
  inj : Function.Injective (Int.cast : ℤ → R)

open Classical in
/-- The integer represented by a degree-zero element (junk value `0` otherwise). -/
def intPart (x : R) : ℤ := if h : ∃ z : ℤ, (z : R) = x then h.choose else 0

theorem intPart_spec {x : R} (h : ∃ z : ℤ, (z : R) = x) : (intPart x : R) = x := by
  rw [intPart, dif_pos h]
  exact h.choose_spec

theorem intPart_intCast (hinj : Function.Injective (Int.cast : ℤ → R)) (z : ℤ) :
    intPart (z : R) = z :=
  hinj (intPart_spec ⟨z, rfl⟩)

theorem intCast_mem [SetLike.GradedMonoid A] (z : ℤ) : (z : R) ∈ A 0 := by
  rw [← zsmul_one]
  exact zsmul_mem SetLike.GradedOne.one_mem z

section IntPart

variable (hA : Connected A)
include hA

theorem intCast_intPart {x : R} (hx : x ∈ A 0) : (intPart x : R) = x :=
  intPart_spec (hA.zero x hx)

/-- Degree-zero elements are integers. -/
theorem eq_intCast {x : R} (hx : x ∈ A 0) : x = (intPart x : R) :=
  (intCast_intPart hA hx).symm

theorem intPart_zero : intPart (0 : R) = 0 := by
  simpa using intPart_intCast hA.inj (0 : ℤ)

theorem intPart_one : intPart (1 : R) = 1 := by
  simpa using intPart_intCast hA.inj (1 : ℤ)

theorem intPart_add {x y : R} (hx : x ∈ A 0) (hy : y ∈ A 0) :
    intPart (x + y) = intPart x + intPart y :=
  hA.inj (by rw [Int.cast_add, intCast_intPart hA hx, intCast_intPart hA hy,
    intCast_intPart hA (add_mem hx hy)])

theorem intPart_sum {α : Type*} (S : Finset α) (x : α → R) (hx : ∀ a ∈ S, x a ∈ A 0) :
    intPart (∑ a ∈ S, x a) = ∑ a ∈ S, intPart (x a) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [intPart_zero hA]
  | @insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      intPart_add hA (hx _ (Finset.mem_insert_self _ _))
        (sum_mem fun b hb => hx b (Finset.mem_insert_of_mem hb)),
      ih fun b hb => hx b (Finset.mem_insert_of_mem hb)]

/-- Products of elements of opposite degrees commute, and vanish off degree zero. -/
theorem mul_comm_of_opp {a b : ℤ} {x y : R} (hx : x ∈ A (a - b)) (hy : y ∈ A (b - a)) :
    x * y = y * x ∧ (a ≠ b → x * y = 0 ∧ y * x = 0) := by
  rcases lt_trichotomy a b with h | rfl | h
  · have : x = 0 := hA.neg _ (by omega) x hx
    subst this
    simp
  · rw [sub_self] at hx hy
    refine ⟨?_, fun h => absurd rfl h⟩
    rw [eq_intCast hA hx, eq_intCast hA hy, ← Int.cast_mul, ← Int.cast_mul, mul_comm]
  · have : y = 0 := hA.neg _ (by omega) y hy
    subst this
    simp

theorem intPart_mul_smul_T {a b : ℤ} {x y : R} (hx : x ∈ A (a - b)) (hy : y ∈ A (b - a)) :
    intPart (x * y) • (LaurentPolynomial.T a : LaurentPolynomial ℤ) =
      intPart (y * x) • LaurentPolynomial.T b := by
  obtain ⟨hc, hz⟩ := mul_comm_of_opp hA hx hy
  by_cases h : a = b
  · rw [h, hc]
  · rw [(hz h).1, (hz h).2, intPart_zero hA, zero_smul, zero_smul]

end IntPart

/-! ### Degree-zero reduction -/

section DiagPart

variable {ι κ : Type*}

theorem IsHom.eq_zero_of_lt (hA : Connected A) {s : ι → ℤ} {t : κ → ℤ}
    {u : Matrix ι κ R}
    (hu : IsHom A s t u) {i : ι} {j : κ} (h : s i < t j) : u i j = 0 :=
  hA.neg _ (by omega) _ (hu i j)

/-- The degree-zero reduction: entries between equal shifts. -/
def diagPart (s : ι → ℤ) (x : Matrix ι ι R) : Matrix ι ι R :=
  Matrix.of fun i j => if s i = s j then x i j else 0

theorem diagPart_apply (s : ι → ℤ) (x : Matrix ι ι R) (i j : ι) :
    diagPart s x i j = if s i = s j then x i j else 0 := rfl

variable {s : ι → ℤ}

theorem IsHom.diagPart {x : Matrix ι ι R} (hx : IsHom A s s x) : IsHom A s s (diagPart s x) := by
  intro i j
  rw [diagPart_apply]
  split_ifs
  exacts [hx i j, zero_mem _]

theorem diagPart_add (x y : Matrix ι ι R) :
    diagPart s (x + y) = diagPart s x + diagPart s y := by
  ext i j
  simp only [diagPart_apply, add_apply]
  split_ifs <;> simp

theorem diagPart_sub (x y : Matrix ι ι R) :
    diagPart s (x - y) = diagPart s x - diagPart s y := by
  ext i j
  simp only [diagPart_apply, sub_apply]
  split_ifs <;> simp

theorem diagPart_one [DecidableEq ι] : diagPart s (1 : Matrix ι ι R) = 1 := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [diagPart_apply]
  · simp [diagPart_apply, one_apply_ne h]

theorem diagPart_idem (x : Matrix ι ι R) : diagPart s (diagPart s x) = diagPart s x := by
  ext i j
  simp only [diagPart_apply]
  split_ifs <;> rfl

theorem diagPart_mul [Fintype ι] (hA : Connected A) {x y : Matrix ι ι R} (hx : IsHom A s s x)
    (hy : IsHom A s s y) : diagPart s (x * y) = diagPart s x * diagPart s y := by
  ext i k
  simp only [diagPart_apply, mul_apply]
  split_ifs with hik
  · refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hij : s i = s j
    · rw [if_pos hij, if_pos (hij ▸ hik)]
    · rw [if_neg hij, zero_mul]
      rcases lt_or_gt_of_ne hij with h | h
      · rw [hx.eq_zero_of_lt hA h, zero_mul]
      · rw [hy.eq_zero_of_lt hA (by omega), mul_zero]
  · refine (Finset.sum_eq_zero fun j _ => ?_).symm
    split_ifs with h1 h2 <;> first | simp | exact absurd (h1.trans h2) hik

/-- Degree-zero endomorphisms with vanishing reduction are nilpotent. -/
theorem exists_pow_eq_zero [Fintype ι] [DecidableEq ι] (hA : Connected A) {x : Matrix ι ι R}
    (hx : IsHom A s s x) (h0 : diagPart s x = 0) : ∃ N : ℕ, x ^ N = 0 := by
  have low : ∀ i j, s i ≤ s j → x i j = 0 := by
    intro i j hij
    rcases hij.lt_or_eq with h | h
    · exact hx.eq_zero_of_lt hA h
    · have := congrFun (congrFun h0 i) j
      rwa [diagPart_apply, if_pos h] at this
  have key : ∀ k : ℕ, ∀ i j, s i - s j < k → (x ^ k) i j = 0 := by
    intro k
    induction k with
    | zero =>
      intro i j h
      rw [pow_zero, one_apply_ne]
      rintro rfl
      simp at h
    | succ k ih =>
      intro i j h
      rw [pow_succ, mul_apply]
      refine Finset.sum_eq_zero fun m _ => ?_
      by_cases hm : s i - s m < k
      · rw [ih i m hm, zero_mul]
      · rw [low m j (by push_cast at h; omega), mul_zero]
  set M := ∑ i, |s i|
  have hi : ∀ i, |s i| ≤ M := fun i =>
    Finset.single_le_sum (f := fun j => |s j|) (fun j _ => abs_nonneg (s j)) (Finset.mem_univ i)
  have hM : 0 ≤ M := Finset.sum_nonneg fun j _ => abs_nonneg (s j)
  refine ⟨(2 * M + 1).toNat, ?_⟩
  ext i j
  refine key _ i j ?_
  rw [Int.toNat_of_nonneg (by omega)]
  have := hi i
  have := hi j
  have := le_abs_self (s i)
  have := neg_abs_le (s j)
  omega

/-- A graded idempotent is Murray–von Neumann equivalent to its degree-zero reduction. -/
theorem mvn_diagPart [Fintype ι] [DecidableEq ι] [SetLike.GradedMonoid A] (hA : Connected A)
    {e : Matrix ι ι R} (he : IsHom A s s e) (hee : e * e = e) : MvN A s e s (diagPart s e) := by
  set f := diagPart s e with hfdef
  have hf : IsHom A s s f := he.diagPart
  have hff : f * f = f := by rw [hfdef, ← diagPart_mul hA he he, hee]
  have h1e : IsHom A s s (1 - e) := IsHom.one.sub he
  have h1f : IsHom A s s (1 - f) := IsHom.one.sub hf
  set z := e * f + (1 - e) * (1 - f) with hzdef
  have hz : IsHom A s s z := (he.mul hf).add (h1e.mul h1f)
  have hf1 : (1 - f) * f = 0 := by rw [sub_mul, one_mul, hff, sub_self]
  have hf1' : f * (1 - f) = 0 := by rw [mul_sub, mul_one, hff, sub_self]
  have he1 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, hee, sub_self]
  have hdz : diagPart s z = 1 := by
    rw [hzdef, diagPart_add, diagPart_mul hA he hf, diagPart_mul hA h1e h1f, diagPart_sub,
      diagPart_sub, diagPart_one, ← hfdef, diagPart_idem, ← hfdef, hff, sub_mul, one_mul, hf1',
      sub_zero, add_sub_cancel]
  set n := 1 - z with hndef
  have hn : IsHom A s s n := IsHom.one.sub hz
  have hdn : diagPart s n = 0 := by rw [hndef, diagPart_sub, diagPart_one, hdz, sub_self]
  obtain ⟨N, hN⟩ := exists_pow_eq_zero hA hn hdn
  set w := ∑ i ∈ Finset.range N, n ^ i with hwdef
  have hz' : z = 1 - n := by rw [hndef, sub_sub_cancel]
  have hzw : z * w = 1 := by rw [hz', hwdef, mul_neg_geom_sum, hN, sub_zero]
  have hwz : w * z = 1 := by rw [hz', hwdef, geom_sum_mul_neg, hN, sub_zero]
  have hw : IsHom A s s w :=
    (homSubring A s).sum_mem fun i _ =>
      (homSubring A s).pow_mem (show n ∈ homSubring A s from hn) i
  have hez : e * z = e * f := by
    rw [hzdef, mul_add, ← mul_assoc, hee, ← mul_assoc, he1, zero_mul, add_zero]
  have hzf : z * f = e * f := by
    rw [hzdef, add_mul, mul_assoc, hff, mul_assoc, hf1, mul_zero, add_zero]
  have hez' : e * z = z * f := hez.trans hzf.symm
  have hwe : w * e = f * w := by
    calc w * e = w * e * (z * w) := by rw [hzw, mul_one]
      _ = w * (e * z) * w := by simp only [mul_assoc]
      _ = w * (z * f) * w := by rw [hez']
      _ = f * w := by rw [← mul_assoc w z f, hwz, one_mul]
  refine ⟨z * f, f * w, hz.mul hf, hf.mul hw, ?_, ?_, ?_, ?_⟩
  · calc z * f * (f * w) = z * f * w := by rw [← mul_assoc, mul_assoc z f f, hff]
      _ = e * z * w := by rw [hez']
      _ = e := by rw [mul_assoc, hzw, mul_one]
  · rw [mul_assoc, ← mul_assoc w, hwz, one_mul, hff]
  · rw [← mul_assoc e, hez', mul_assoc z f f, hff, mul_assoc, hff]
  · rw [← mul_assoc f f w, hff, mul_assoc, hwe, ← mul_assoc, hff]

end DiagPart

/-! ### Integer idempotents -/

section IntIdem

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- An idempotent integer matrix factors as `P Q` with `Q P = 1`, through its free image. -/
theorem int_idem_split (F : Matrix ι ι ℤ) (hF : F * F = F) :
    ∃ (P : Matrix ι (Fin (Module.finrank ℤ (LinearMap.range (toLin' F)))) ℤ)
      (Q : Matrix (Fin (Module.finrank ℤ (LinearMap.range (toLin' F)))) ι ℤ),
      P * Q = F ∧ Q * P = 1 := by
  set f := toLin' F with hfdef
  have hff : f ∘ₗ f = f := by rw [hfdef, ← toLin'_mul, hF]
  obtain ⟨r, b⟩ := (LinearMap.range f).basisOfPid (Pi.basisFun ℤ ι)
  have hr : Module.finrank ℤ (LinearMap.range f) = r := by
    rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  rw [hr]
  set incl := (LinearMap.range f).subtype
  set proj := f.rangeRestrict
  have h1 : incl ∘ₗ proj = f := rfl
  have h2 : proj ∘ₗ incl = LinearMap.id := by
    refine LinearMap.ext ?_
    rintro ⟨y, x, rfl⟩
    exact Subtype.ext (LinearMap.congr_fun hff x)
  refine ⟨LinearMap.toMatrix b (Pi.basisFun ℤ ι) incl,
    LinearMap.toMatrix (Pi.basisFun ℤ ι) b proj, ?_, ?_⟩
  · rw [← LinearMap.toMatrix_comp, h1, LinearMap.toMatrix_eq_toMatrix', hfdef,
      LinearMap.toMatrix'_toLin']
  · rw [← LinearMap.toMatrix_comp, h2, LinearMap.toMatrix_id]

/-- The trace of an idempotent integer matrix is the rank of its image. -/
theorem trace_eq_finrank (F : Matrix ι ι ℤ) (hF : F * F = F) :
    F.trace = Module.finrank ℤ (LinearMap.range (toLin' F)) := by
  obtain ⟨P, Q, hPQ, hQP⟩ := int_idem_split F hF
  conv_lhs => rw [← hPQ]
  rw [trace_mul_comm, hQP, trace_one, Fintype.card_fin]

end IntIdem

/-- Diagonal blocks of a block-triangular product. -/
theorem toBlock_mul_of_zero {ι : Type*} [Fintype ι] (p : ι → Prop) [DecidablePred p]
    (F G : Matrix ι ι ℤ) (hF : ∀ i j, p i → ¬ p j → F i j = 0) :
    (F * G).toBlock p p = F.toBlock p p * G.toBlock p p := by
  rw [toBlock_mul_eq_add p p p]
  have : (F.toBlock p fun i => ¬ p i) = 0 := by
    ext i j
    exact hF i j i.2 j.2
  rw [this, Matrix.zero_mul, add_zero]

/-! ### Classification -/

section Classification

variable {ι : Type*}

/-- The integer matrix of the degree-zero reduction. -/
def intMat (s : ι → ℤ) (e : Matrix ι ι R) : Matrix ι ι ℤ :=
  Matrix.of fun i j => if s i = s j then intPart (e i j) else 0

/-- The integer block of the degree-zero reduction on the indices of shift `k`. -/
def intBlock (s : ι → ℤ) (e : Matrix ι ι R) (k : ℤ) :
    Matrix {i // s i = k} {i // s i = k} ℤ :=
  (intMat s e).toBlock (fun i => s i = k) (fun i => s i = k)

theorem map_intCast_mem [SetLike.GradedMonoid A] {α β : Type*} (M : Matrix α β ℤ) (a : α)
    (b : β) :
    M.map (Int.castRingHom R) a b ∈ A 0 := by
  rw [map_apply, Int.coe_castRingHom]
  exact intCast_mem _

theorem intMat_eq_zero {s : ι → ℤ} {e : Matrix ι ι R} {i j : ι} (h : s i ≠ s j) :
    intMat s e i j = 0 := if_neg h

variable (hA : Connected A)
include hA

theorem diagPart_eq_map {s : ι → ℤ} {e : Matrix ι ι R} (he : IsHom A s s e) :
    diagPart s e = (intMat s e).map (Int.castRingHom R) := by
  ext i j
  simp only [diagPart_apply, intMat, map_apply, of_apply]
  split_ifs with h
  · have hm : e i j ∈ A 0 := mem_of_deg_eq (he i j) (by rw [h, sub_self])
    rw [Int.coe_castRingHom]
    exact (intCast_intPart hA hm).symm
  · simp

variable [Fintype ι]

theorem intMat_idem {s : ι → ℤ} {e : Matrix ι ι R} (he : IsHom A s s e) (hee : e * e = e) :
    intMat s e * intMat s e = intMat s e := by
  have hi : Function.Injective (Int.castRingHom R) := fun a b h => hA.inj h
  apply Matrix.map_injective hi
  show (intMat s e * intMat s e).map (Int.castRingHom R) = (intMat s e).map (Int.castRingHom R)
  rw [Matrix.map_mul, ← diagPart_eq_map hA he, ← diagPart_mul hA he he, hee]

theorem intBlock_idem [DecidableEq ι] {s : ι → ℤ} {e : Matrix ι ι R} (he : IsHom A s s e)
    (hee : e * e = e)
    (k : ℤ) : intBlock s e k * intBlock s e k = intBlock s e k := by
  unfold intBlock
  rw [← toBlock_mul_of_zero, intMat_idem hA he hee]
  intro i j hi hj
  exact intMat_eq_zero fun h => hj (h ▸ hi)

/-- Every graded idempotent over a connected graded ring is Murray–von Neumann equivalent to a
graded free module. -/
theorem mvn_free [DecidableEq ι] [SetLike.GradedMonoid A] {s : ι → ℤ} {e : Matrix ι ι R}
    (he : IsHom A s s e) (hee : e * e = e) :
    ∃ (m : ℕ) (t : Fin m → ℤ), MvN A s e t 1 := by
  set F := intMat s e with hFdef
  have hF : F * F = F := intMat_idem hA he hee
  have hE : IsHom A s s (F.map (Int.castRingHom R)) := by
    rw [← diagPart_eq_map hA he]
    exact he.diagPart
  have hEE : F.map (Int.castRingHom R) * F.map (Int.castRingHom R) =
      F.map (Int.castRingHom R) := by
    rw [← Matrix.map_mul, hF]
  have h1 : MvN A s e s (F.map (Int.castRingHom R)) := by
    rw [← diagPart_eq_map hA he]
    exact mvn_diagPart hA he hee
  let g : ι → Set.range s := Set.rangeFactorization s
  let σ := Equiv.sigmaFiberEquiv g
  let Fk : ∀ k : Set.range s, Matrix {i // g i = k} {i // g i = k} ℤ := fun k =>
    F.toBlock (fun i => g i = k) (fun i => g i = k)
  have hFk : ∀ k, Fk k * Fk k = Fk k := fun k => by
    simp only [Fk]
    rw [← toBlock_mul_of_zero, hF]
    intro i j hi hj
    refine intMat_eq_zero fun hij => hj ?_
    rw [← hi]
    exact Subtype.ext hij.symm
  choose P Q hPQ hQP using fun k => int_idem_split (Fk k) (hFk k)
  have hblock : F.submatrix σ σ = blockDiagonal' Fk := by
    ext ⟨k, i⟩ ⟨k', j⟩
    rw [blockDiagonal'_apply']
    split_ifs with h
    · subst h
      rfl
    · exact intMat_eq_zero fun hij =>
        h (i.2.symm.trans ((Subtype.ext hij : g i.1 = g j.1).trans j.2))
  have h2 : MvN A s (F.map (Int.castRingHom R)) (fun x : Σ k, {i // g i = k} => (x.1 : ℤ))
      (blockDiagonal' fun k => (Fk k).map (Int.castRingHom R)) := by
    refine MvN.of_equiv σ.symm hE hEE (fun i => rfl) (fun i j => ?_)
    rw [← blockDiagonal'_map _ _ (map_zero (Int.castRingHom R)), ← hblock]
    rfl
  have hB : (blockDiagonal' fun k => (Fk k).map (Int.castRingHom R)) *
      (blockDiagonal' fun k => (Fk k).map (Int.castRingHom R)) =
      blockDiagonal' fun k => (Fk k).map (Int.castRingHom R) := by
    rw [← blockDiagonal'_mul]
    refine congrArg blockDiagonal' (funext fun k => ?_)
    rw [← Matrix.map_mul, hFk]
  have hFP : ∀ k, Fk k * P k = P k := fun k => by
    calc Fk k * P k = P k * Q k * P k := by rw [hPQ k]
      _ = P k := by rw [Matrix.mul_assoc, hQP k, Matrix.mul_one]
  have hQF : ∀ k, Q k * Fk k = Q k := fun k => by
    calc Q k * Fk k = Q k * (P k * Q k) := by rw [hPQ k]
      _ = Q k := by rw [← Matrix.mul_assoc, hQP k, Matrix.one_mul]
  have h3 : MvN A (fun x : Σ k, {i // g i = k} => (x.1 : ℤ))
      (blockDiagonal' fun k => (Fk k).map (Int.castRingHom R))
      (fun x : Σ k, Fin (Module.finrank ℤ (LinearMap.range (toLin' (Fk k)))) => (x.1 : ℤ))
      1 := by
    refine ⟨blockDiagonal' fun k => (P k).map (Int.castRingHom R),
      blockDiagonal' fun k => (Q k).map (Int.castRingHom R),
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rintro ⟨k, i⟩ ⟨k', a⟩
      rw [blockDiagonal'_apply']
      split_ifs with h
      · subst h
        exact mem_of_deg_eq (map_intCast_mem _ _ _) (sub_self _).symm
      · exact zero_mem _
    · rintro ⟨k, a⟩ ⟨k', i⟩
      rw [blockDiagonal'_apply']
      split_ifs with h
      · subst h
        exact mem_of_deg_eq (map_intCast_mem _ _ _) (sub_self _).symm
      · exact zero_mem _
    · rw [← blockDiagonal'_mul]
      refine congrArg blockDiagonal' (funext fun k => ?_)
      rw [← Matrix.map_mul, hPQ]
    · rw [← blockDiagonal'_mul]
      simp only [← Matrix.map_mul, hQP, Matrix.map_one _ (map_zero _) (map_one _)]
      exact blockDiagonal'_one
    · rw [Matrix.mul_one, ← blockDiagonal'_mul]
      refine congrArg blockDiagonal' (funext fun k => ?_)
      rw [← Matrix.map_mul, hFP k]
    · rw [Matrix.one_mul, ← blockDiagonal'_mul]
      refine congrArg blockDiagonal' (funext fun k => ?_)
      rw [← Matrix.map_mul, hQF k]
  let τ := Fintype.equivFin (Σ k, Fin (Module.finrank ℤ (LinearMap.range (toLin' (Fk k)))))
  have h4 : MvN A (fun x : Σ k, Fin (Module.finrank ℤ (LinearMap.range (toLin' (Fk k)))) =>
      (x.1 : ℤ)) 1 (fun a => ((τ.symm a).1 : ℤ)) 1 :=
    MvN.of_equiv τ IsHom.one (mul_one 1) (fun x => by simp)
      (fun x y => by simp only [one_apply, EmbeddingLike.apply_eq_iff_eq])
  exact ⟨_, _, MvN.trans hee (mul_one 1) (mul_one 1)
    (MvN.trans hee hB (mul_one 1) (MvN.trans hee hEE hB h1 h2) h3) h4⟩

end Classification

/-! ### Graded rank -/

section GradedRank

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Graded Hattori–Stallings rank `∑ᵢ ε(e i i) T^{s i}` of `e` on `(ι, s)`. -/
def gdimAux (s : ι → ℤ) (e : Matrix ι ι R) : LaurentPolynomial ℤ :=
  ∑ i, intPart (e i i) • LaurentPolynomial.T (s i)

theorem gdimAux_shift (s : ι → ℤ) (e : Matrix ι ι R) (k : ℤ) :
    gdimAux (fun i => s i + k) e = LaurentPolynomial.T k * gdimAux s e := by
  rw [gdimAux, gdimAux, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_smul_comm, LaurentPolynomial.T_add, mul_comm]

theorem gdimAux_apply (s : ι → ℤ) (e : Matrix ι ι R) (k : ℤ) :
    gdimAux s e k = ∑ i ∈ Finset.univ.filter (fun i => s i = k), intPart (e i i) := by
  rw [Finset.sum_filter, gdimAux, Finsupp.finset_sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finsupp.smul_apply, LaurentPolynomial.T_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]

variable [SetLike.GradedMonoid A] (hA : Connected A)
include hA

omit [SetLike.GradedMonoid A] in
theorem gdimAux_one [DecidableEq κ] (t : κ → ℤ) :
    gdimAux t (1 : Matrix κ κ R) = ∑ a, LaurentPolynomial.T (t a) := by
  simp [gdimAux, intPart_one hA]

/-- The graded rank is a Murray–von Neumann invariant. -/
theorem gdimAux_eq_of_mvn {s : ι → ℤ} {e : Matrix ι ι R} {t : κ → ℤ}
    {f : Matrix κ κ R}
    (h : MvN A s e t f) : gdimAux s e = gdimAux t f := by
  obtain ⟨u, v, hu, hv, h1, h2, -, -⟩ := h
  subst h1 h2
  have c1 : ∀ i, intPart ((u * v) i i) = ∑ j, intPart (u i j * v j i) := fun i =>
    intPart_sum hA _ _ fun j _ =>
      mem_of_deg_eq (SetLike.GradedMul.mul_mem (hu i j) (hv j i)) (by ring)
  have c2 : ∀ j, intPart ((v * u) j j) = ∑ i, intPart (v j i * u i j) := fun j =>
    intPart_sum hA _ _ fun i _ =>
      mem_of_deg_eq (SetLike.GradedMul.mul_mem (hv j i) (hu i j)) (by ring)
  simp only [gdimAux, c1, c2, Finset.sum_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ =>
    intPart_mul_smul_T hA (hu i j) (hv j i)

end GradedRank

namespace GIdem

variable [SetLike.GradedMonoid A] (hA : Connected A)
include hA

/-- Classification: every graded idempotent over a connected graded ring is equivalent to a
graded free module `R^m{t}`. -/
theorem exists_free (P : GIdem A) : ∃ (m : ℕ) (t : Fin m → ℤ), P ≈ GIdem.free t :=
  mvn_free hA P.hom P.idem

/-- Uniqueness: the multiplicity of `k` in `t` is the rank of the integer idempotent `ē_k`,
the block of the degree-zero reduction of `e` on the indices of shift `k`. -/
theorem card_shift_eq {P : GIdem A} {m : ℕ} {t : Fin m → ℤ} (h : P ≈ GIdem.free t)
    (k : ℤ) :
    (Finset.univ.filter fun a => t a = k).card =
      Module.finrank ℤ (LinearMap.range (toLin' (intBlock P.s P.e k))) := by
  have h1 := congrArg (fun p : LaurentPolynomial ℤ => p k) (gdimAux_eq_of_mvn hA h)
  simp only [gdimAux_apply] at h1
  have h2 : (intBlock P.s P.e k).trace =
      ∑ i ∈ Finset.univ.filter (fun i => P.s i = k), intPart (P.e i i) := by
    rw [Matrix.trace, Finset.sum_subtype (Finset.univ.filter fun i => P.s i = k)
      (p := fun i => P.s i = k) (fun i => by simp) (fun i => intPart (P.e i i))]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [intBlock, intMat, toBlock_apply]
  have h3 := trace_eq_finrank _ (intBlock_idem hA P.hom P.idem k)
  have h4 : ∑ a ∈ Finset.univ.filter (fun a => t a = k),
      intPart ((1 : Matrix (Fin m) (Fin m) R) a a)
      = (Finset.univ.filter fun a => t a = k).card := by
    simp [intPart_one hA]
  exact_mod_cast (h4.symm.trans h1.symm).trans (h2.symm.trans h3)

/-- The shift multiset of a graded free module is an invariant. -/
theorem card_shift_eq_of_free {m m' : ℕ} {t : Fin m → ℤ} {t' : Fin m' → ℤ}
    (h : (GIdem.free t : GIdem A) ≈ GIdem.free t') (k : ℤ) :
    (Finset.univ.filter fun a => t a = k).card = (Finset.univ.filter fun a => t' a = k).card := by
  have h1 := congrArg (fun p : LaurentPolynomial ℤ => p k) (gdimAux_eq_of_mvn hA h)
  simp only [gdimAux_apply] at h1
  have h4 : ∀ {n} (t : Fin n → ℤ), ∑ a ∈ Finset.univ.filter (fun a => t a = k),
      intPart ((1 : Matrix (Fin n) (Fin n) R) a a) = (Finset.univ.filter fun a => t a = k).card :=
    fun t => by simp [intPart_one hA]
  exact_mod_cast (h4 t).symm.trans (h1.trans (h4 t'))

end GIdem

/-! ### `K₀` of a connected graded ring -/

namespace GProj

variable [SetLike.GradedMonoid A] (hA : Connected A)

/-- The graded rank on isomorphism classes. -/
def gdim : GProj A →+ LaurentPolynomial ℤ where
  toFun := Quotient.lift (fun P : GIdem A => gdimAux P.s P.e) fun _ _ h => gdimAux_eq_of_mvn hA h
  map_zero' := by
    show gdimAux (GIdem.zero (A := A)).s GIdem.zero.e = 0
    simp [gdimAux, GIdem.zero]
  map_add' := by
    refine ind fun P => ind fun Q => ?_
    show gdimAux (P.sum Q).s (P.sum Q).e = gdimAux P.s P.e + gdimAux Q.s Q.e
    rw [← gdimAux_eq_of_mvn hA (GIdem.mvn_sum P Q), gdimAux, gdimAux, gdimAux,
      Fintype.sum_sum_type]
    rfl

theorem gdim_mk (P : GIdem A) : gdim hA (mk P) = gdimAux P.s P.e := rfl

end GProj

namespace K0

variable [SetLike.GradedMonoid A] (hA : Connected A)

/-- The graded rank on `K₀`. -/
def gdim : K0 A →+ LaurentPolynomial ℤ := GrothendieckGroup.lift (GProj.gdim hA)

theorem gdim_of (P : GIdem A) : gdim hA (of P) = gdimAux P.s P.e :=
  GrothendieckGroup.lift_of _ _

theorem gdim_shift (k : ℤ) (x : K0 A) :
    gdim hA (shift k x) = LaurentPolynomial.T k * gdim hA x := by
  have : (gdim hA).comp (shift k) = (AddMonoidHom.mulLeft (LaurentPolynomial.T k)).comp (gdim hA) :=
    hom_ext fun P => by
      rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, shift_of, gdim_of, gdim_of,
        AddMonoidHom.coe_mulLeft]
      exact gdimAux_shift P.s P.e k
  exact DFunLike.congr_fun this x

theorem gdim_single (k : ℤ) :
    gdim hA (of (GIdem.single k : GIdem A)) = LaurentPolynomial.T k := by
  rw [gdim_of]
  simp [GIdem.single, GIdem.free, gdimAux_one hA]

/-- `K₀` of a connected graded ring is `ℤ[T;T⁻¹]`: the graded rank is an isomorphism of
`ℤ[T;T⁻¹]`-modules with inverse `p ↦ p • [R]`. -/
def classify : K0 A ≃ₗ[LaurentPolynomial ℤ] LaurentPolynomial ℤ :=
  LinearEquiv.ofLinear
    { toFun := gdim hA
      map_add' := map_add _
      map_smul' := map_smul_of_shift (gdim hA) fun k x => by rw [gdim_shift, smul_eq_mul] }
    (LinearMap.toSpanSingleton _ _ (of (GIdem.single 0)))
    (LinearMap.ext fun p => by
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.toSpanSingleton_apply,
        LinearMap.coe_mk, AddHom.coe_mk, LinearMap.id_coe, id_eq]
      rw [map_smul_of_shift (gdim hA) (fun k x => by rw [gdim_shift, smul_eq_mul]), gdim_single,
        LaurentPolynomial.T_zero, smul_eq_mul, mul_one])
    (LinearMap.ext fun x => by
      have : ((LinearMap.toSpanSingleton (LaurentPolynomial ℤ) (K0 A)
          (of (GIdem.single 0))).toAddMonoidHom.comp (gdim hA)) = AddMonoidHom.id _ :=
        hom_ext fun P => by
          obtain ⟨m, t, h⟩ := GIdem.exists_free hA P
          rw [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe,
            LinearMap.toSpanSingleton_apply, gdim_of, gdimAux_eq_of_mvn hA h, AddMonoidHom.id_apply,
            of_eq h]
          show gdimAux t 1 • _ = _
          rw [gdimAux_one hA, Finset.sum_smul, of_free]
          simp only [T_smul_single]
      exact DFunLike.congr_fun this x)

theorem classify_of (P : GIdem A) : classify hA (of P) = gdimAux P.s P.e := gdim_of hA P

theorem classify_single (k : ℤ) :
    classify hA (of (GIdem.single k : GIdem A)) = LaurentPolynomial.T k := gdim_single hA k

theorem classify_symm_apply (p : LaurentPolynomial ℤ) :
    (classify hA).symm p = p • of (GIdem.single 0 : GIdem A) := rfl

/-- `K₀` of a connected graded ring is free of rank one over `ℤ[T;T⁻¹]` on `[R]`. -/
def basis : Basis (Fin 1) (LaurentPolynomial ℤ) (K0 A) :=
  (Basis.singleton (Fin 1) (LaurentPolynomial ℤ)).map (classify hA).symm

theorem basis_apply (i : Fin 1) : basis hA i = of (GIdem.single 0 : GIdem A) := by
  rw [basis, Basis.map_apply, Basis.singleton_apply, classify_symm_apply, one_smul]

end K0

end OddMath.Frontier.GradedK0
