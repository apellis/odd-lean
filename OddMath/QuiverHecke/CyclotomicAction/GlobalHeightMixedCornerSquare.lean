/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.GlobalHeightMixedQuadratic
import OddMath.QuiverHecke.CyclotomicAction.ParameterTransport
import OddMath.SKM.Calculus

/-!
# The distinct-colour quadratic relation on the two-colour composition corners

The corner half of the quadratic relations (1.7) of Brundan–Ellis, arXiv:1701.04133v2,
Definition 1.5, for distinct colours, at a fixed height of the extended tower. On the corner
`T_{ij} = C θ(1)`, `θ = φᵢ ∘ φⱼ`, write `x_out` for signed right multiplication by the new last
dot `y_i` and `x_in` for signed right multiplication by the appended dot `φᵢ(y_j)`
(`heightTwoColourRightMul`). An `m`-fold power of signed right multiplication by a dot of
parity `c` acts on an element of parity `p` by the sign `(-1)^{c(mp + ⌊m/2⌋)}`
(`heightTwoColourRightMul_pow_apply`). With the algebra identity
`heightLastCrossing_mul_mixed`, the composite of the two corner crossings is, in diagrammatic
order,

  `ψ_{ij} ψ_{ji} = t'_{ij} x_out^{d_{ij}} + t'_{ji} x_in^{d_{ji}}
      + ∑_{0<p<d_{ij}, 0<q<d_{ji}} s'^{pq}_{ij} x_in^q x_out^p`

(`heightCompositionCorner_square_ne`), and `ψ_{ij} ψ_{ji} = t'_{ij}` if `d_{ij} = 0`
(`heightCompositionCorner_square_zero`), where `t'`, `s'` are the parameters of
`parameterTwist`. The signs of the odd powers of the crossing parities and of the dots are
exactly the signs recorded by `parameterTwist`: every surviving monomial has `p|i|` and `q|j|`
even (`Sc.s_eq_zero`, `Datum.even_d_of_odd`).
-/

noncomputable section
open CategoryTheory StringDiagrams SuperBimodule Supercategory
namespace OddMath.QuiverHecke.CyclotomicAction
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]

/-! ### Sign bookkeeping -/

theorem parameterSignUnit_coe (p : ZMod 2) :
    ((parameterSignUnit (k := k) p : kˣ) : k) = SKM.zsign k p := by
  unfold parameterSignUnit SKM.zsign
  split_ifs <;> simp

private theorem zmod_two_eq_zero_or_one (p : ZMod 2) : p = 0 ∨ p = 1 := by
  revert p; decide

private theorem zmod_two_two : (2 : ZMod 2) = 0 := by decide

private theorem zmod_two_mul_self (p : ZMod 2) : p * p = p := by
  rcases zmod_two_eq_zero_or_one p with rfl | rfl <;> decide

omit [Fintype I] in
/-- The twisted distinct-colour leading parameter. -/
theorem parameterTwist_t_of_ne {i j : I} (hij : i ≠ j) :
    (((parameterTwist D Sc).t i j : kˣ) : k) =
      SKM.zsign k (parameterSignExponent D i j (D.dn i j) 0) * (Sc.t i j : k) := by
  simp [parameterTwist, hij, parameterSignUnit_coe]

omit [Fintype I] in
/-- The twisted mixed parameters. -/
theorem parameterTwist_s (i j : I) (p q : ℕ) :
    (parameterTwist D Sc).s i j p q =
      SKM.zsign k (parameterSignExponent D i j p q) * Sc.s i j p q := rfl

omit [Fintype I] in
/-- An odd colour has an even number of dots on every connected strand. -/
theorem dn_cast_mul_parity {i j : I} (hij : i ≠ j) :
    (D.dn i j : ZMod 2) * D.parity i = 0 := by
  rcases zmod_two_eq_zero_or_one (D.parity i) with h | h
  · rw [h, mul_zero]
  · rw [h, mul_one]
    have he : Even (D.dn i j : ℤ) := by
      rw [D.dn_cast hij]
      exact D.even_d_of_odd h j
    exact (ZMod.natCast_eq_zero_iff_even).2 (Int.even_coe_nat _ |>.1 he)

/-- The floor of half of a successor, modulo two. -/
private theorem half_succ_cast (m : ℕ) :
    (((m + 1) / 2 : ℕ) : ZMod 2) = (m : ZMod 2) + ((m / 2 : ℕ) : ZMod 2) := by
  have h : ((m + 1) / 2 : ℕ) + m / 2 = m := by omega
  have h' := congrArg (Nat.cast : ℕ → ZMod 2) h
  push_cast at h'
  linear_combination h' - ((m / 2 : ℕ) : ZMod 2) * zmod_two_two

/-! ### Powers of signed right multiplication -/

/-- Vertical powers of an endomorphism, `f^{m+1} = f^m ≫ f` (the recursion of
`SKM.rouquierPower`). -/
def endoPower {𝒞 : Type*} [Category 𝒞] {Y : 𝒞} (f : Y ⟶ Y) : ℕ → (Y ⟶ Y)
  | 0 => 𝟙 Y
  | m + 1 => endoPower f m ≫ f

@[simp] theorem endoPower_zero {𝒞 : Type*} [Category 𝒞] {Y : 𝒞} (f : Y ⟶ Y) :
    endoPower f 0 = 𝟙 Y := rfl

theorem endoPower_succ {𝒞 : Type*} [Category 𝒞] {Y : 𝒞} (f : Y ⟶ Y) (m : ℕ) :
    endoPower f (m + 1) = endoPower f m ≫ f := rfl

/-- The successor power, with the new factor applied first. -/
theorem endoPower_succ' {𝒞 : Type*} [Category 𝒞] {Y : 𝒞} (f : Y ⟶ Y) (m : ℕ) :
    endoPower f (m + 1) = f ≫ endoPower f m := by
  induction m with
  | zero => simp [endoPower]
  | succ m ih =>
    change endoPower f (m + 1) ≫ f = _
    conv_lhs => rw [ih]
    rw [Category.assoc]
    rfl

section Power
variable {i j c : I} {a : I → _root_.Polynomial k} {ha : CyclotomicPolynomialParity D a}
  {n : ℕ}

local notation "C" => heightAlgebra D Sc a (n + 1 + 1)
local notation "T" => heightCompositionCorner D Sc i j a ha n

/-- **Powers of signed right multiplication**: the `m`-th power of signed right multiplication
by `u` raises parity by `m|c|` and acts by `(-1)^{|c|(mp + ⌊m/2⌋)} x u^m`. -/
theorem heightTwoColourRightMul_pow_apply {u : C}
    (hu : TwoColourCornerMulData D Sc i j c a ha n u) (m : ℕ) {p : ZMod 2}
    (x : (T).toSVec) (hx : x ∈ (T).toSVec.part p) :
    (endoPower (heightTwoColourRightMul D Sc i j c a ha n hu) m).1 x ∈
        (T).toSVec.part (p + (m : ZMod 2) * D.parity c) ∧
      ((endoPower (heightTwoColourRightMul D Sc i j c a ha n hu) m).1 x).val =
        SKM.zsign k (D.parity c * ((m : ZMod 2) * p + ((m / 2 : ℕ) : ZMod 2))) •
          (x.val * u ^ m) := by
  induction m generalizing p x with
  | zero =>
    have h0 : (endoPower (heightTwoColourRightMul D Sc i j c a ha n hu) 0).1 x = x :=
      rfl
    rw [h0]
    refine ⟨by simpa using hx, ?_⟩
    simp [SKM.zsign]
  | succ m ih =>
    have h1 := SVec.apply_mem_part (heightTwoColourRightMulLinear_parity D Sc i j c a ha n hu) hx
    obtain ⟨hm, hv⟩ := ih ((heightTwoColourRightMul D Sc i j c a ha n hu).1 x) h1
    have hc : (endoPower (heightTwoColourRightMul D Sc i j c a ha n hu) (m + 1)).1 x =
        (endoPower (heightTwoColourRightMul D Sc i j c a ha n hu) m).1
          ((heightTwoColourRightMul D Sc i j c a ha n hu).1 x) := by
      rw [endoPower_succ']
      rfl
    rw [hc]
    refine ⟨?_, ?_⟩
    · convert hm using 2
      push_cast
      rw [add_mul, one_mul, add_assoc, add_comm ((m : ZMod 2) * _)]
    · rw [hv, heightTwoColourRightMul_apply D Sc i j c a ha n hu x hx,
        zsmul_koszulSign_eq_zsign_smul (k := k), smul_mul_assoc, smul_smul, mul_assoc,
        ← pow_succ']
      congr 1
      rw [← SKM.zsign_add]
      congr 1
      push_cast
      rw [half_succ_cast]
      linear_combination (D.parity c * (m : ZMod 2)) * zmod_two_mul_self (D.parity c) +
        (- (m : ZMod 2) * D.parity c) * zmod_two_two +
        (-(m : ZMod 2) * (D.parity c + 1)) * zmod_two_mul_self (D.parity c) +
        (D.parity c ^ 2 * (m : ZMod 2)) * zmod_two_two

end Power

/-! ### The corner square -/

section CornerSquare
variable {i j : I} (hij : i ≠ j) (a : I → _root_.Polynomial k)
  (ha : CyclotomicPolynomialParity D a) (n : ℕ)
include hij

local notation "T" => heightCompositionCorner D Sc i j a ha n
local notation "Cr" => heightCompositionSuperCrossing D Sc i j a ha n
local notation "Cr'" => heightCompositionSuperCrossing D Sc j i a ha n
local notation "Dr" => heightTwoColourRightMul D Sc i j i a ha n
  (twoColourCornerMulData_lastDot D Sc i j a ha n)
local notation "Dl" => heightTwoColourRightMul D Sc i j j a ha n
  (twoColourCornerMulData_appendDot D Sc i j a ha n)
local notation "A" => heightAppend D Sc a i (n + 1) (heightLastDot D Sc a j n)
local notation "B" => heightLastDot D Sc a i (n + 1)

/-- The composite of the two corner crossings on a homogeneous element. -/
private theorem corner_square_apply {p : ZMod 2} (z : (T).toSVec) (hz : z ∈ (T).toSVec.part p) :
    ((Cr ≫ Cr').1 z).val =
      SKM.zsign k (D.parity i * D.parity j) • (z.val * pairQuadPoly D Sc j i A B) := by
  have hz₂ : (Cr).1 z ∈ (heightCompositionCorner D Sc j i a ha n).toSVec.part
      (p + D.parity i * D.parity j) :=
    SVec.apply_mem_part (heightCompositionCrossingLinear_parity D Sc i j a ha n) hz
  change ((Cr').1 ((Cr).1 z)).val = _
  rw [heightCompositionSuperCrossing_apply D Sc j i a ha n _ hz₂,
    heightCompositionSuperCrossing_apply D Sc i j a ha n _ hz,
    zsmul_koszulSign_eq_zsign_smul (k := k), zsmul_koszulSign_eq_zsign_smul (k := k),
    smul_mul_assoc, smul_smul, mul_assoc, heightLastCrossing_mul_mixed D Sc a hij n,
    ← mul_assoc]
  congr 1
  swap
  · rw [← mul_assoc]
    congr 1
    exact z.2
  rw [← SKM.zsign_add]
  congr 1
  rcases zmod_two_eq_zero_or_one (D.parity i) with h | h <;>
    rcases zmod_two_eq_zero_or_one (D.parity j) with h' | h' <;>
    rcases zmod_two_eq_zero_or_one p with h'' | h'' <;>
    · rw [h, h', h'']; decide

/-- Evaluation of a corner endomorphism at a vector, as a linear map. -/
private def cornerEval (z : (T).toSVec) : (T ⟶ T) →ₗ[k] heightAlgebra D Sc a (n + 1 + 1) where
  toFun f := (f.1 z).val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit hij in
private theorem cornerEval_apply (z : (T).toSVec) (f : T ⟶ T) :
    cornerEval D Sc a ha n z f = (f.1 z).val := rfl

/-- **The distinct-colour quadratic relation on the corners**, `d_{ij} ≠ 0`, in diagrammatic
order and with the parameters of `parameterTwist`. -/
theorem heightCompositionCorner_square_ne (hd : D.d i j ≠ 0) :
    Cr ≫ Cr' =
      ((parameterTwist D Sc).t i j : k) • (endoPower Dr (D.dn i j)) +
        ((parameterTwist D Sc).t j i : k) • (endoPower Dl (D.dn j i)) +
        ∑ p ∈ Finset.Ioo 0 (D.dn i j), ∑ q ∈ Finset.Ioo 0 (D.dn j i),
          (parameterTwist D Sc).s i j p q • ((endoPower Dl q) ≫ (endoPower Dr p)) := by
  have hd' : D.d j i ≠ 0 := fun h => hd ((D.d_eq_zero_iff j i).mp h)
  apply SuperBimodule.hom_ext
  refine svec_hom_ext_homogeneous fun p₀ z hz => Subtype.ext ?_
  rw [← cornerEval_apply D Sc a ha n z, ← cornerEval_apply D Sc a ha n z]
  simp only [map_add, map_sum, map_smul, cornerEval_apply]
  have hpow (u : heightAlgebra D Sc a (n + 1 + 1)) (c : I)
      (hu : TwoColourCornerMulData D Sc i j c a ha n u) (m : ℕ) :=
    heightTwoColourRightMul_pow_apply D Sc hu m z hz
  have hmix (p q : ℕ) : (((endoPower Dl q) ≫ (endoPower Dr p)).1 z).val =
      (SKM.zsign k (D.parity j * ((q : ZMod 2) * p₀ + ((q / 2 : ℕ) : ZMod 2))) *
        SKM.zsign k (D.parity i * ((p : ZMod 2) * (p₀ + (q : ZMod 2) * D.parity j) +
          ((p / 2 : ℕ) : ZMod 2)))) • (z.val * (A ^ q * B ^ p)) := by
    obtain ⟨hm, hv⟩ := hpow _ _ (twoColourCornerMulData_appendDot D Sc i j a ha n) q
    change (((endoPower Dr p)).1 (((endoPower Dl q)).1 z)).val = _
    rw [(heightTwoColourRightMul_pow_apply D Sc
      (twoColourCornerMulData_lastDot D Sc i j a ha n) p _ hm).2, hv, smul_mul_assoc, smul_smul,
      mul_assoc, mul_comm (SKM.zsign k _)]
  rw [corner_square_apply D Sc hij a ha n z hz, (hpow _ _ _ (D.dn i j)).2,
    (hpow _ _ _ (D.dn j i)).2]
  simp only [hmix]
  simp only [pairQuadPoly, hd', ↓reduceIte, mul_add, Finset.mul_sum, mul_smul_comm, smul_add,
    Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm, add_comm (Finset.sum _ _), add_comm (_ • (_ * A ^ D.dn j i))]
  have hi := dn_cast_mul_parity D hij
  have hj := dn_cast_mul_parity D (Ne.symm hij)
  congr 1
  · congr 1
    · congr 1
      rw [parameterTwist_t_of_ne D Sc hij,
        show D.parity i * D.parity j = parameterSignExponent D i j (D.dn i j) 0 +
          (D.parity i * ((D.dn i j : ZMod 2) * p₀) + D.parity i * ((D.dn i j / 2 : ℕ) : ZMod 2))
          by unfold parameterSignExponent
             linear_combination (- D.parity i * ((D.dn i j / 2 : ℕ) : ZMod 2)) * zmod_two_two +
               (- p₀) * hi,
        SKM.zsign_add]
      ring
    · congr 1
      rw [parameterTwist_t_of_ne D Sc (Ne.symm hij),
        show D.parity i * D.parity j = parameterSignExponent D j i (D.dn j i) 0 +
          (D.parity j * ((D.dn j i : ZMod 2) * p₀) + D.parity j * ((D.dn j i / 2 : ℕ) : ZMod 2))
          by unfold parameterSignExponent
             linear_combination (- D.parity j * ((D.dn j i / 2 : ℕ) : ZMod 2)) * zmod_two_two +
               (- p₀) * hj,
        SKM.zsign_add]
      ring
  · refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    congr 1
    rw [Sc.s_symm j i q p]
    by_cases hs : Sc.s i j p q = 0
    · simp [parameterTwist, hs]
    have hp : (p : ZMod 2) * D.parity i = 0 := by
      rcases zmod_two_eq_zero_or_one ((p : ZMod 2) * D.parity i) with h | h
      · exact h
      · exact absurd (Sc.s_eq_zero i j p q h) hs
    have hq : (q : ZMod 2) * D.parity j = 0 := by
      rcases zmod_two_eq_zero_or_one ((q : ZMod 2) * D.parity j) with h | h
      · exact h
      · exact absurd (by rw [Sc.s_symm]; exact Sc.s_eq_zero j i q p h) hs
    rw [parameterTwist_s,
      show D.parity i * D.parity j = parameterSignExponent D i j p q +
        (D.parity j * ((q : ZMod 2) * p₀) + D.parity j * ((q / 2 : ℕ) : ZMod 2)) +
        (D.parity i * ((p : ZMod 2) * p₀) +
          D.parity i * ((p : ZMod 2) * ((q : ZMod 2) * D.parity j)) +
          D.parity i * ((p / 2 : ℕ) : ZMod 2))
        by unfold parameterSignExponent
           linear_combination
             (- D.parity i * ((p / 2 : ℕ) : ZMod 2) - D.parity j * ((q / 2 : ℕ) : ZMod 2)) *
               zmod_two_two + (- p₀ - (q : ZMod 2) * D.parity j) * hp + (- p₀) * hq,
      SKM.zsign_add, SKM.zsign_add]
    ring

/-- **The distinct-colour quadratic relation on the corners**, `d_{ij} = 0`. -/
theorem heightCompositionCorner_square_zero (hd : D.d i j = 0) :
    Cr ≫ Cr' = ((parameterTwist D Sc).t i j : k) • 𝟙 _ := by
  have hd' : D.d j i = 0 := (D.d_eq_zero_iff i j).mp hd
  apply SuperBimodule.hom_ext
  refine svec_hom_ext_homogeneous fun p₀ z hz => Subtype.ext ?_
  rw [← cornerEval_apply D Sc a ha n z, ← cornerEval_apply D Sc a ha n z]
  rw [map_smul, cornerEval_apply, cornerEval_apply, corner_square_apply D Sc hij a ha n z hz]
  simp only [pairQuadPoly, hd', ↓reduceIte, mul_smul_comm, mul_one, smul_smul]
  change _ = _ • z.val
  congr 1
  rw [← Sc.t_symm_of_d_eq_zero i j hd, parameterTwist_t_of_ne D Sc hij]
  congr 2
  unfold parameterSignExponent
  have h0 : D.dn i j = 0 := by simp [SKM.Datum.dn, hd]
  simp [h0]

end CornerSquare

end OddMath.QuiverHecke.CyclotomicAction
