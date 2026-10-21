/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.Realization.Generators

/-!
# The BE2 relations on a component of the twisted module

Brundan–Ellis, arXiv:1701.04133v2, (1.7)–(1.9) for the quiver Hecke supercategory of §11:
the operators of `Realization/Generators` satisfy each relation on the component of the
colour sequence of its source word. The operator identities of `Realization/Generators`
reduce each relation to an identity of coefficient operators on that component.
-/

noncomputable section
open scoped TensorProduct
namespace OddMath.QuiverHecke.Realization

universe u v
variable {I : Type u} {X : Type v} [AddCommGroup X] {k : Type*} [CommRing k]

/-! ## Operators on a single component -/

/-- Colour sequences are compared classically (they are functions on `ℕ`). -/
noncomputable instance (J : Type*) : DecidableEq (Seq J) := Classical.decEq _

section Single

variable {J : Type*}

/-- The vector `m` on the component `ν`. -/
abbrev sgl (ν : Seq J) (m : M k) : V k J := Pi.single ν m

theorem diag_single (F : Seq J → Module.End k (Coeff k)) (ν : Seq J) (m : M k) :
    diag F (sgl ν m) = sgl ν (Finsupp.mapRange.linearMap (F ν) m) := by
  ext1 ν'
  by_cases h : ν' = ν
  · subst h; simp
  · simp [h]

@[simp] theorem mapRange_one_apply (h : (1 : Module.End k (Coeff k)) 0 = 0) (m : M k) :
    Finsupp.mapRange (⇑(1 : Module.End k (Coeff k))) h m = m := by
  ext w; simp

theorem diag_smul (c : k) (F : Seq J → Module.End k (Coeff k)) :
    c • diag F = diag fun ν => c • F ν := by
  ext x ν w : 3
  simp [Finsupp.mapRange_apply]

theorem mulK_eq_diag (g : Seq J → K k) : mulK g = diag fun ν => scalar (g ν) := rfl

theorem oddAt_iff {par : J → ZMod 2} {ν : Seq J} {p : ℕ} {i : J} (h : ν p = some i) :
    oddAt par ν p ↔ par i = 1 := by
  constructor
  · rintro ⟨i', hi', hp⟩; rw [h] at hi'; cases hi'; exact hp
  · exact fun hp => ⟨i, h, hp⟩


/-- The vector `f · m` on the component `ν`, for a scalar `f`. -/
abbrev cv (ν : Seq J) (m : M k) (f : K k) : V k J :=
  sgl ν (Finsupp.mapRange.linearMap (scalar f) m)

theorem cv_add (ν : Seq J) (m : M k) (f g : K k) : cv ν m (f + g) = cv ν m f + cv ν m g := by
  ext ν' w
  by_cases h : ν' = ν
  · subst h; simp [scalar_add]
  · simp [h]

theorem cv_zero (ν : Seq J) (m : M k) : cv ν m 0 = 0 := by
  simp [cv]

theorem cv_neg (ν : Seq J) (m : M k) (f : K k) : cv ν m (-f) = -cv ν m f := by
  rw [eq_neg_iff_add_eq_zero, ← cv_add, neg_add_cancel, cv_zero]

theorem cv_sub (ν : Seq J) (m : M k) (f g : K k) : cv ν m (f - g) = cv ν m f - cv ν m g := by
  rw [sub_eq_add_neg, cv_add, cv_neg, ← sub_eq_add_neg]

theorem cv_smul (ν : Seq J) (m : M k) (c : k) (f : K k) :
    c • cv ν m f = cv ν m (algebraMap k (K k) c * f) := by
  ext ν' w
  by_cases h : ν' = ν
  · subst h; simp [scalar_mul, scalar_algebraMap]
  · simp [h]

theorem cv_sum {ι : Type*} (ν : Seq J) (m : M k) (S : Finset ι) (f : ι → K k) :
    ∑ x ∈ S, cv ν m (f x) = cv ν m (∑ x ∈ S, f x) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [cv_zero]
  | insert x S hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, ih, cv_add]

theorem cv_one (ν : Seq J) (m : M k) : cv ν m 1 = sgl ν m := by
  simp [cv]

theorem eL_eq_diag (par : J → ZMod 2) [DecidableEq J] (a : ℕ) :
    eL (k := k) par a =
      diag fun ν => scalar (eqv a ν) + cl par ν a * cl par ν (a + 1) * scalar (eqv a ν) := by
  rw [eL, mulK_eq_diag, clif_eq_diag, clif_eq_diag, ← diag_mul', ← diag_mul', ← diag_add]

theorem eR_eq_diag (par : J → ZMod 2) [DecidableEq J] (a : ℕ) :
    eR (k := k) par a =
      diag fun ν => -scalar (eqv a ν) + cl par ν a * cl par ν (a + 1) * scalar (eqv a ν) := by
  rw [eR, mulK_eq_diag, clif_eq_diag, clif_eq_diag, ← diag_mul', ← diag_mul', ← diag_neg,
    ← diag_add]

theorem eqv_of_ne [DecidableEq J] {a : ℕ} {ν : Seq J} (h : ν a ≠ ν (a + 1)) :
    eqv (k := k) a ν = 0 := by simp [eqv, h]

theorem eqv_of_eq [DecidableEq J] {a : ℕ} {ν : Seq J} (h : ν a = ν (a + 1)) :
    eqv (k := k) a ν = 1 := by simp [eqv, h]

end Single

/-! ## Two Clifford computations -/

theorem cliff_pair_sq {E : Type*} [Ring E] {ca cb : E} (ha : ca * ca = 1) (hb : cb * cb = 1)
    (hab : ca * cb = -(cb * ca)) : ca * cb * (ca * cb) = -1 := by
  have hba : cb * ca = -(ca * cb) := by rw [hab, neg_neg]
  calc ca * cb * (ca * cb) = ca * (cb * ca) * cb := by noncomm_ring
    _ = -((ca * ca) * (cb * cb)) := by rw [hba]; noncomm_ring
    _ = -1 := by rw [ha, hb, one_mul]

theorem cliff_pair_slideL {E : Type*} [Ring E] {ca cb : E} (ha : ca * ca = 1)
    (hb : cb * cb = 1) (hab : ca * cb = -(cb * ca)) : (ca * cb - 1) * (1 + ca * cb) = -2 := by
  have h := cliff_pair_sq ha hb hab
  calc (ca * cb - 1) * (1 + ca * cb) = ca * cb * (ca * cb) - 1 := by noncomm_ring
    _ = -2 := by rw [h]; norm_num

theorem cliff_pair_slideR {E : Type*} [Ring E] {ca cb : E} (ha : ca * ca = 1)
    (hb : cb * cb = 1) (hab : ca * cb = -(cb * ca)) : (1 + ca * cb) * (-1 + ca * cb) = -2 := by
  have h := cliff_pair_sq ha hb hab
  calc (1 + ca * cb) * (-1 + ca * cb) = ca * cb * (ca * cb) - 1 := by noncomm_ring
    _ = -2 := by rw [h]; norm_num

theorem cliff_diff_sq {E : Type*} [Ring E] {ca cb : E} (ha : ca * ca = 1) (hb : cb * cb = 1)
    (hab : ca * cb = -(cb * ca)) : -((ca - cb) * (ca - cb)) = -2 := by
  have : (ca - cb) * (ca - cb) = ca * ca + cb * cb - (ca * cb + cb * ca) := by noncomm_ring
  rw [this, ha, hb, hab, neg_add_cancel, sub_zero]; norm_num

theorem neg_two_mul_neg_half {E : Type*} [Ring E] [Algebra k E] (h2 : IsUnit (2 : k)) (q : E) :
    (-2 : E) * (algebraMap k E (-(half : k)) * q) = q := by
  have : (-2 : E) * algebraMap k E (-(half : k)) = 1 := by
    rw [map_neg, neg_mul_neg, ← map_ofNat (algebraMap k E) 2, ← map_mul, half,
      Ring.mul_inverse_cancel _ h2, map_one]
  rw [← mul_assoc, this, one_mul]

theorem neg_half_smul_neg_two {E : Type*} [Ring E] [Algebra k E] (h2 : IsUnit (2 : k)) :
    (-(half : k)) • (-2 : E) = 1 := by
  rw [neg_smul_neg, Algebra.smul_def, ← map_ofNat (algebraMap k E) 2, ← map_mul, half,
    Ring.inverse_mul_cancel _ h2, map_one]

/-! ## The dot–crossing relations (1.8) -/

section Slide

variable (D : SKM.Datum I X) (Sc : SKM.Scalars D k) [DecidableEq I] (a : ℕ)

theorem slideL_single {i j : I} {ν : Seq I} (hi : ν a = some i) (hj : ν (a + 1) = some j)
    (m : M k) :
    (crossOp D Sc i j a * dotOp D i a -
        SKM.zsign k (D.parity i * D.parity j) • (dotOp D i (a + 1) * crossOp D Sc i j a) :
          Module.End k (V k I)) (sgl ν m) = if i = j then sgl ν m else 0 := by
  rcases parity_cases (D.parity i) with hpi | hpi
  · rw [slideL_even D Sc a hpi, eL_eq_diag, diag_smul, diag_single]
    by_cases hij : i = j
    · subst hij
      have hν : ν a = ν (a + 1) := hi.trans hj.symm
      have ho : ¬ oddAt D.parity ν a := by rw [oddAt_iff hi, hpi]; decide
      simp [eqv_of_eq hν, cl, ho, gam, hpi]
    · have hν : ν a ≠ ν (a + 1) := by rw [hi, hj]; simpa using hij
      simp [eqv_of_ne hν, hij]
  · rcases parity_cases (D.parity j) with hpj | hpj
    · have hij : i ≠ j := fun h => by rw [h, hpj] at hpi; exact absurd hpi (by decide)
      have hν : ν a ≠ ν (a + 1) := by rw [hi, hj]; simpa using hij
      rw [slideL_odd_even D Sc a hpi hpj, eL_eq_diag, clif_eq_diag, ← diag_mul', diag_smul,
        diag_single]
      simp [eqv_of_ne hν, hij]
    · rw [slideL_odd_odd D Sc a hpi hpj, eL_eq_diag, clif_eq_diag, clif_eq_diag, mulK_eq_diag,
        ← diag_mul', ← diag_sub, ← diag_mul', diag_smul, diag_single]
      by_cases hij : i = j
      · subst hij
        have hν : ν a = ν (a + 1) := hi.trans hj.symm
        have h0 : oddAt D.parity ν a := (oddAt_iff hi).mpr hpi
        have h1 : oddAt D.parity ν (a + 1) := (oddAt_iff hj).mpr hpi
        have h := cliff_pair_slideL (E := Module.End k (Coeff k)) (cliff_mul_self a)
          (cliff_mul_self (a + 1)) (cliff_anticomm (show a ≠ a + 1 by omega))
        have key' : (-(half : k)) • ⇑((cliff (k := k) a * cliff (a + 1) - 1) *
            (1 + cliff (k := k) a * cliff (a + 1)) : Module.End k (Coeff k)) =
              ⇑(1 : Module.End k (Coeff k)) := by
          rw [← LinearMap.coe_smul, h]
          exact congrArg _ (neg_half_smul_neg_two (Sc.two_isUnit ⟨i, hpi⟩))
        simp [eqv_of_eq hν, cl, h0, h1, gam, hpi, key']
      · have hν : ν a ≠ ν (a + 1) := by rw [hi, hj]; simpa using hij
        simp [eqv_of_ne hν, hij]

theorem slideR_single {i j : I} {ν : Seq I} (hi : ν a = some i) (hj : ν (a + 1) = some j)
    (m : M k) :
    (dotOp D j a * crossOp D Sc i j a -
        SKM.zsign k (D.parity i * D.parity j) • (crossOp D Sc i j a * dotOp D j (a + 1)) :
          Module.End k (V k I)) (sgl ν m) = if i = j then sgl ν m else 0 := by
  rcases parity_cases (D.parity j) with hpj | hpj
  · rw [slideR_even D Sc a hpj, eR_eq_diag, ← diag_neg, diag_smul, diag_single]
    by_cases hij : i = j
    · subst hij
      have hν : ν a = ν (a + 1) := hi.trans hj.symm
      have ho : ¬ oddAt D.parity ν a := by rw [oddAt_iff hi, hpj]; decide
      simp [eqv_of_eq hν, cl, ho, gam, hpj]
    · have hν : ν a ≠ ν (a + 1) := by rw [hi, hj]; simpa using hij
      simp [eqv_of_ne hν, hij]
  · rcases parity_cases (D.parity i) with hpi | hpi
    · have hij : i ≠ j := fun h => by rw [h, hpj] at hpi; exact absurd hpi (by decide)
      have hν : ν a ≠ ν (a + 1) := by rw [hi, hj]; simpa using hij
      rw [slideR_even_odd D Sc a hpi hpj, eR_eq_diag, ← diag_neg, clif_eq_diag, ← diag_mul',
        diag_smul, diag_single]
      simp [eqv_of_ne hν, hij]
    · rw [slideR_odd_odd D Sc a hpi hpj, eR_eq_diag, clif_eq_diag, clif_eq_diag, mulK_eq_diag,
        ← diag_mul', ← diag_add, ← diag_mul', diag_smul, diag_single]
      by_cases hij : i = j
      · subst hij
        have hν : ν a = ν (a + 1) := hi.trans hj.symm
        have h0 : oddAt D.parity ν a := (oddAt_iff hi).mpr hpi
        have h1 : oddAt D.parity ν (a + 1) := (oddAt_iff hj).mpr hpi
        have h := cliff_pair_slideR (E := Module.End k (Coeff k)) (cliff_mul_self a)
          (cliff_mul_self (a + 1)) (cliff_anticomm (show a ≠ a + 1 by omega))
        have key' : (-(half : k)) • ⇑((1 + cliff (k := k) a * cliff (a + 1)) *
            (-1 + cliff (k := k) a * cliff (a + 1)) : Module.End k (Coeff k)) =
              ⇑(1 : Module.End k (Coeff k)) := by
          rw [← LinearMap.coe_smul, h]
          exact congrArg _ (neg_half_smul_neg_two (Sc.two_isUnit ⟨i, hpi⟩))
        simp [eqv_of_eq hν, cl, h0, h1, gam, hpi, key']
      · have hν : ν a ≠ ν (a + 1) := by rw [hi, hj]; simpa using hij
        simp [eqv_of_ne hν, hij]

theorem quad_single {i j : I} {ν : Seq I} (hi : ν a = some i) (hj : ν (a + 1) = some j)
    (m : M k) :
    (crossOp D Sc j i a * crossOp D Sc i j a : Module.End k (V k I)) (sgl ν m) =
      cv ν m (qL D Sc i j (y a) (y (a + 1))) := by
  rw [crossOp_mul_crossOp D Sc a i j]
  have hval : (qt D Sc).val a (a + 1) ν = algebraMap k (K k) (kap D i j) *
      qL D Sc i j (y a) (y (a + 1)) := by
    simp only [PairFn.val, hi, hj]; rfl
  by_cases hij : i = j
  · subst hij
    have h0 : qL D Sc i i (y (k := k) a) (y (a + 1)) = 0 := by simp [qL]
    rw [mulK_eq_diag, h0]
    unfold dsq
    split_ifs with h
    · rw [clif_eq_diag, clif_eq_diag, ← diag_sub, ← diag_mul', ← diag_neg, ← diag_mul',
        diag_smul, diag_single]
      simp [hval, h0, cv_zero]
    · rw [one_mul, diag_smul, diag_single]
      simp [hval, h0, cv_zero]
  · have hg : gam (k := k) D j i * gam D i j = 1 := by simp [gam, hij, Ne.symm hij]
    rw [hg, one_smul, mulK_eq_diag]
    unfold dsq
    split_ifs with h
    · rw [clif_eq_diag, clif_eq_diag, ← diag_sub, ← diag_mul', ← diag_neg, ← diag_mul',
        diag_single]
      have h0 : oddAt D.parity ν a := (oddAt_iff hi).mpr h.1
      have h1 : oddAt D.parity ν (a + 1) := (oddAt_iff hj).mpr h.2
      have hk : kap (k := k) D i j = -half := by simp [kap, hij, h.1, h.2]
      congr 2
      simp only [cl, h0, h1, ite_true, hval, hk]
      have hd := cliff_diff_sq (E := Module.End k (Coeff k)) (cliff_mul_self a)
        (cliff_mul_self (a + 1)) (cliff_anticomm (show a ≠ a + 1 by omega))
      rw [hd, scalar_mul, scalar_algebraMap, ← Algebra.algebraMap_eq_smul_one]
      exact congrArg _ (neg_two_mul_neg_half (E := Module.End k (Coeff k)) (Sc.two_isUnit ⟨i, h.1⟩)
        (scalar (qL D Sc i j (y a) (y (a + 1)))))
    · have hk : kap (k := k) D i j = 1 := by
        simp only [kap]; rw [ite_eq_right]; tauto
      rw [one_mul, diag_single, hval, hk, map_one, one_mul]

/-! ## Powers of dots on a component -/

omit [DecidableEq I] in
theorem diag_pow {J : Type*} (F : Seq J → Module.End k (Coeff k)) (n : ℕ) :
    diag F ^ n = diag fun ν => F ν ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ih, ← diag_mul']; simp only [pow_succ]

omit [DecidableEq I] in
theorem dotOp_eq_diag (i : I) (p : ℕ) :
    dotOp (k := k) D i p =
      diag fun ν => (if D.parity i = 1 then cl D.parity ν p else 1) * scalar (y p) := by
  unfold dotOp
  split_ifs
  · rw [clif_eq_diag, mulK_eq_diag, ← diag_mul']
  · rw [mulK_eq_diag]; simp only [one_mul]

theorem cliff_scalar_y_sq (p : ℕ) :
    (cliff p * scalar (y (k := k) p)) ^ 2 = scalar (-(y p ^ 2)) := by
  have hsc : scalar (y (k := k) p) * cliff p = cliff p * scalar (-y p) := by
    rw [cliff_scalar, map_neg, reflect_y_self, neg_neg]
  rw [sq, mul_assoc, ← mul_assoc (scalar (y p)), hsc, mul_assoc, ← mul_assoc (cliff p) (cliff p),
    cliff_mul_self, one_mul, ← scalar_mul]
  congr 1; ring

theorem scalar_pow (f : K k) (n : ℕ) : scalar (f ^ n) = scalar f ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, scalar_mul, ih, pow_succ]

theorem xpow_two_mul_odd (m : ℕ) (u : K k) :
    xpow (1 : ZMod 2) (2 * m) u = (-(u ^ 2)) ^ m := by
  simp only [xpow, ite_true, even_two_mul, Nat.mul_div_cancel_left m two_pos]
  ring

omit [DecidableEq I] in
theorem dotPow_single {i : I} {p n : ℕ} {ν : Seq I} (hp : ν p = some i)
    (h : D.parity i = 0 ∨ Even n) (m : M k) :
    (dotOp D i p ^ n : Module.End k (V k I)) (sgl ν m) =
      sgl ν (Finsupp.mapRange.linearMap (scalar (xpow (D.parity i) n (y p))) m) := by
  rw [dotOp_eq_diag, diag_pow, diag_single]
  congr 2
  rcases parity_cases (D.parity i) with hpi | hpi
  · simp [hpi, xpow, ← scalar_pow]
  · obtain ⟨r, rfl⟩ := h.resolve_left (by rw [hpi]; decide)
    have ho : oddAt D.parity ν p := (oddAt_iff hp).mpr hpi
    rw [← two_mul, hpi, xpow_two_mul_odd]
    simp only [cl, ho, ite_true, pow_mul, cliff_scalar_y_sq, ← scalar_pow]

theorem mapRange_scalar_scalar (f g : K k) (m : M k) :
    Finsupp.mapRange.linearMap (scalar f) (Finsupp.mapRange.linearMap (scalar g) m) =
      Finsupp.mapRange.linearMap (scalar (f * g)) m := by
  ext w; simp [scalar_mul]

omit [DecidableEq I] in
theorem dotPow_mul_single {i j : I} {p q : ℕ} {ν : Seq I} (hi : ν a = some i)
    (hj : ν (a + 1) = some j) (hp : D.parity i = 0 ∨ Even p) (hq : D.parity j = 0 ∨ Even q)
    (m : M k) :
    (dotOp D i a ^ p * dotOp D j (a + 1) ^ q : Module.End k (V k I)) (sgl ν m) =
      cv ν m (xpow (D.parity i) p (y a) * xpow (D.parity j) q (y (a + 1))) := by
  rw [Module.End.mul_apply, dotPow_single D hj hq, dotPow_single D hi hp, mapRange_scalar_scalar]

omit [DecidableEq I] in
theorem even_dn {i j : I} (hi : D.parity i = 1) (hij : i ≠ j) : Even (D.dn i j) := by
  have h := D.even_d_of_odd hi j
  rw [← D.dn_cast hij] at h
  exact Int.even_coe_nat _ |>.mp h

/-- BE2 (1.7) for `i = j`: the square of a crossing of equal colours vanishes. -/
theorem quadEq_single {i : I} {ν : Seq I} (hi : ν a = some i) (hj : ν (a + 1) = some i)
    (m : M k) : (crossOp D Sc i i a * crossOp D Sc i i a : Module.End k (V k I)) (sgl ν m) = 0 := by
  rw [quad_single D Sc a hi hj]
  simp [qL]

/-- BE2 (1.7) for `i ≠ j` with `d_{ij} = 0`. -/
theorem quadZero_single {i j : I} (hij : i ≠ j) (hd : D.d i j = 0) {ν : Seq I}
    (hi : ν a = some i) (hj : ν (a + 1) = some j) (m : M k) :
    (crossOp D Sc j i a * crossOp D Sc i j a - (Sc.t i j : k) • 1 : Module.End k (V k I))
      (sgl ν m) = 0 := by
  rw [LinearMap.sub_apply, quad_single D Sc a hi hj, LinearMap.smul_apply, Module.End.one_apply,
    ← cv_one ν m, cv_smul, mul_one, ← cv_sub]
  simp [qL, hij, hd, cv_zero]

/-- BE2 (1.7) for `i ≠ j` with `d_{ij} ≠ 0`. -/
theorem quadNe_single {i j : I} (hij : i ≠ j) (hd : D.d i j ≠ 0) {ν : Seq I}
    (hi : ν a = some i) (hj : ν (a + 1) = some j) (m : M k) :
    (crossOp D Sc j i a * crossOp D Sc i j a - (Sc.t i j : k) • dotOp D i a ^ D.dn i j -
        (Sc.t j i : k) • dotOp D j (a + 1) ^ D.dn j i -
        ∑ p ∈ Finset.Ioo 0 (D.dn i j), ∑ q ∈ Finset.Ioo 0 (D.dn j i),
          Sc.s i j p q • (dotOp D i a ^ p * dotOp D j (a + 1) ^ q) : Module.End k (V k I))
      (sgl ν m) = 0 := by
  have hpi : D.parity i = 0 ∨ Even (D.dn i j) := by
    rcases parity_cases (D.parity i) with h | h
    · exact Or.inl h
    · exact Or.inr (even_dn D h hij)
  have hpj : D.parity j = 0 ∨ Even (D.dn j i) := by
    rcases parity_cases (D.parity j) with h | h
    · exact Or.inl h
    · exact Or.inr (even_dn D h (Ne.symm hij))
  have hterm : ∀ p q, Sc.s i j p q • (dotOp D i a ^ p * dotOp D j (a + 1) ^ q :
      Module.End k (V k I)) (sgl ν m) = cv ν m (algebraMap k (K k) (Sc.s i j p q) *
        (xpow (D.parity i) p (y a) * xpow (D.parity j) q (y (a + 1)))) := by
    intro p q
    by_cases hs : Sc.s i j p q = 0
    · simp [hs, cv_zero]
    · have hp : D.parity i = 0 ∨ Even p := by
        rcases parity_cases (D.parity i) with h | h
        · exact Or.inl h
        · refine Or.inr (Nat.not_odd_iff_even.mp fun ho => hs (Sc.s_eq_zero i j p q ?_))
          rw [h, mul_one]; exact (ZMod.natCast_eq_one_iff_odd).mpr ho
      have hq : D.parity j = 0 ∨ Even q := by
        rcases parity_cases (D.parity j) with h | h
        · exact Or.inl h
        · refine Or.inr (Nat.not_odd_iff_even.mp fun ho => hs ?_)
          rw [Sc.s_symm]
          refine Sc.s_eq_zero j i q p ?_
          rw [h, mul_one]; exact (ZMod.natCast_eq_one_iff_odd).mpr ho
      rw [dotPow_mul_single D a hi hj hp hq, cv_smul]
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.sum_apply]
  rw [quad_single D Sc a hi hj, dotPow_single D hi hpi, dotPow_single D hj hpj]
  simp only [hterm, cv_sum]
  rw [cv_smul, cv_smul, ← cv_sub, ← cv_sub, ← cv_sub]
  convert cv_zero ν m using 2
  simp only [qL, hij, hd, ite_false]
  ring

end Slide

end OddMath.QuiverHecke.Realization
