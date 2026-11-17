import StringDiagrams.Super.PiTwo
import Mathlib.CategoryTheory.Adjunction.Mates
import OddMath.QuiverHecke.CyclotomicAction.ContentModule.ContentParity
import OddMath.QuiverHecke.CyclotomicAction.ParameterUntwist

/-!
# Content module

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # The original-parameter quadratic on common-content induction tensors

`DeformedActionAssembly.md` §6: the two actual induction crossings, over
`parameterTwist Sc`, compose to the ordered signed evaluation with the
specified `Sc`. The source is the actual two-word affine relation, with no
finite-colour assumption. This does not yet identify powers of the dotted
module operators with that ordered evaluation or assemble weight functors.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

theorem crossTwo_comp_pairQuad {i j : I} (hij : i ≠ j) :
    crossTwo D Sc i j ≫ crossTwo D Sc j i =
      pairQuadPoly D Sc i j (dotE D Sc [i,j] 0) (dotE D Sc [i,j] 1) := by
  unfold crossTwo
  rw [cl_comp]
  unfold pairQuadPoly
  split_ifs with hd
  · exact cross_cross_ne_zero D Sc [] [] hij hd _
  · exact cross_cross_ne D Sc [] [] hij hd _

/-- Actual two-word source quadratic, with the parameter involution cancelled. -/
theorem crossTwo_comp_parameterUntwist {i j : I} (hij : i ≠ j) :
    sign k (D.parity i * D.parity j) •
      (crossTwo D (parameterTwist D Sc) i j ≫ crossTwo D (parameterTwist D Sc) j i) =
      elvSignedPairQuadEval D Sc (R := End ((pres D (parameterTwist D Sc)).obj (ob D [i,j]))) i j
        (dotE D (parameterTwist D Sc) [i,j] 0) (dotE D (parameterTwist D Sc) [i,j] 1) := by
  rw [crossTwo_comp_pairQuad D _ hij, sign_eq_zsign]
  exact pairQuadPoly_parameterTwist_eval D Sc
    (R := End ((pres D (parameterTwist D Sc)).obj (ob D [i,j]))) hij _ _

@[simp] theorem contentAppendToComponent_smul {β γ : Multiset I} {σ τ : List I}
    (hσ : β + (σ : Multiset I) = γ) (hτ : β + (τ : Multiset I) = γ)
    (r : k) (a : (pres D Sc).obj (ob D σ) ⟶ (pres D Sc).obj (ob D τ))
    (v : ContentCategory D Sc cutoff N β) :
    contentAppendToComponent D Sc cutoff N hσ hτ (r • a) v =
      r • contentAppendToComponent D Sc cutoff N hσ hτ a v := by
  exact (contentAppendToLinear D Sc cutoff N hσ hτ v).map_smul r a

/-- Two crossed append maps on the same content endpoint, evaluated on an actual
balanced induction tensor. The resulting ordered polynomial has original Sc. -/
theorem contentInduction_quadratic_tensor (β : Multiset I) {i j : I} (hij : i ≠ j)
    (M : ContentModules D (parameterTwist D Sc) cutoff N β)
    (v : ContentCategory D (parameterTwist D Sc) cutoff N β)
    (w : ContentCategory D (parameterTwist D Sc) cutoff N (β + ([i,j] : Multiset I)))
    (h : (contentAppendTo D (parameterTwist D Sc) cutoff N β [i,j] _ rfl).obj v ⟶ w)
    (m : M.obj v) :
    BalancedInduction.transformLinear
      (contentAppendTo_supernatural D (parameterTwist D Sc) cutoff N rfl
        (content_pair_swap β i j) (contentCrossAffine_mem D (parameterTwist D Sc) i j)) M w
      (BalancedInduction.transformLinear
        (contentAppendTo_supernatural D (parameterTwist D Sc) cutoff N
          (content_pair_swap β i j) rfl (contentCrossAffine_mem D (parameterTwist D Sc) j i)) M w
        (BalancedInduction.tensor
          (contentAppendTo D (parameterTwist D Sc) cutoff N β [i,j] _ rfl) M.toFunctor v h m)) =
    BalancedInduction.tensor
      (contentAppendTo D (parameterTwist D Sc) cutoff N β [i,j] _ rfl) M.toFunctor v
      (contentAppendToComponent D (parameterTwist D Sc) cutoff N rfl rfl
        (elvSignedPairQuadEval D Sc (R := End ((pres D (parameterTwist D Sc)).obj (ob D [i,j]))) i j
          (dotE D (parameterTwist D Sc) [i,j] 0)
          (dotE D (parameterTwist D Sc) [i,j] 1)) v ≫ h) m := by
  let p := D.parity i * D.parity j
  have hp : D.parity j * D.parity i = p := mul_comm _ _
  have hpp : p + p = 0 := by
    rcases parity_eq_zero_or_one p with h | h <;> simp [h]
  have hsq : p * p = p := by
    rcases parity_eq_zero_or_one p with h | h <;> simp [h]
  rw [BalancedInduction.transformLinear_tensor, BalancedInduction.transformLinear_tensor,
    twist_comp]
  rw [twist_of_mem _ ((contentAppendTo_supernatural D (parameterTwist D Sc) cutoff N
    (content_pair_swap β i j) rfl (contentCrossAffine_mem D (parameterTwist D Sc) j i)).mem v)]
  rw [← twist_add, hp, hpp, twist_zero, hsq, Linear.smul_comp, Linear.comp_smul,
    ← Category.assoc,
    contentAppendToComponent_comp D (parameterTwist D Sc) cutoff N rfl
      (content_pair_swap β i j) rfl _ (contentCrossAffine_mem D (parameterTwist D Sc) j i),
    ← Linear.smul_comp, ← contentAppendToComponent_smul,
    contentCrossAffine_distinct D _ i j hij, contentCrossAffine_distinct D _ j i hij.symm,
    crossTwo_comp_parameterUntwist D Sc hij]

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Ordered polynomials in content induction operators

`DeformedActionAssembly.md` §5 (8) and §6 (9): powers of the induced dot
operators evaluate on balanced tensors with the total-parity twist. Each
interior coefficient of the specified parameter polynomial is identified
with its ordered source evaluation. The leading terms and the sum forming
the crossing square, and the corrected mixed braid, remain to be assembled.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV
universe u
namespace BalancedInduction
variable {k : Type u} [CommRing k]
variable {C B : Type u} [Category.{u} C] [Category.{u} B]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive B] [Linear k B] [Supercategory k B]
variable {J : C ⥤ B} [J.Additive] [J.Linear k] [IsSuperfunctor k J]

private theorem half_succ_parity (n : ℕ) :
    (((n + 1) / 2 : ℕ) : ZMod 2) = (n : ZMod 2) + (n / 2 : ℕ) := by
  have h : (n + 1) / 2 + n / 2 = n := by omega
  have he := congrArg (Nat.cast : ℕ → ZMod 2) h
  push_cast at he
  have hz : (2 : ZMod 2) = 0 := rfl
  linear_combination he - (n / 2 : ℕ) * hz

/-- Powers retain the twist of the entire kernel morphism, including odd coefficients. -/
theorem transformLinear_pow_tensor {p : ZMod 2} {a : ∀ v, End (J.obj v)}
    (ha : IsSupernatural k p a) (M : Superfunctor k C (SVec k))
    (w : B) (n : ℕ) (v : C) (h : J.obj v ⟶ w) (m : M.obj v) :
    (transformLinear ha M w ^ n) (tensor J M.toFunctor v h m) =
      sign k (p * (n / 2 : ℕ)) •
        tensor J M.toFunctor v ((a v ^ n) ≫ twist k ((n : ZMod 2) * p) h) m := by
  induction n generalizing h with
  | zero => simp [twist_zero, sign_zero]
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply, transformLinear_tensor, ih, twist_comp,
      twist_of_mem _ (ha.mem v), ← twist_add]
    simp only [Linear.smul_comp, Linear.comp_smul, tensor,
      ← TensorProduct.smul_tmul', map_smul, smul_smul]
    have hp : p * p = p := by
      rcases parity_eq_zero_or_one p with rfl | rfl <;> decide
    rw [← sign_add]
    have he : p * (n / 2 : ℕ) + (n : ZMod 2) * p * p =
        p * ((n + 1) / 2 : ℕ) := by
      rw [half_succ_parity, mul_add, mul_assoc, hp]
      ring
    rw [he]
    congr 2
    rw [pow_succ', End.mul_def, Category.assoc]
    congr 2
    push_cast
    ring
end BalancedInduction

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

/-- Append preserves powers without moving any coefficient across a dot. -/
theorem contentAppendToComponent_pow {β : Multiset I} {σ : List I} {p : ZMod 2}
    {a : End ((pres D Sc).obj (ob D σ))} (ha : a ∈ parity (R := k) _ _ p)
    (v : ContentCategory D Sc cutoff N β) (n : ℕ) :
    contentAppendToComponent D Sc cutoff N rfl rfl (a ^ n) v =
      ((show End ((contentAppendTo D Sc cutoff N β σ _ rfl).obj v) from
        contentAppendToComponent D Sc cutoff N rfl rfl a v) ^ n :
        End ((contentAppendTo D Sc cutoff N β σ _ rfl).obj v)) := by
  induction n with
  | zero => exact contentAppendToComponent_id D Sc cutoff N v
  | succ n ih =>
    rw [pow_succ', End.mul_def, ← contentAppendToComponent_comp D Sc cutoff N rfl rfl rfl _ ha,
      ih, pow_succ', End.mul_def]

/-- The polynomial powers are powers of the induced linear operator, not source-dot notation. -/
theorem contentInductionEndLinear_pow_tensor {β : Multiset I} {σ : List I} {p : ZMod 2}
    {a : End ((pres D Sc).obj (ob D σ))} (ha : a ∈ parity (R := k) _ _ p)
    (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N (β + (σ : Multiset I))) (n : ℕ)
    (v : ContentCategory D Sc cutoff N β)
    (h : (contentAppendTo D Sc cutoff N β σ _ rfl).obj v ⟶ w) (m : M.obj v) :
    (contentInductionEndLinear D Sc cutoff N ha M w ^ n)
        (BalancedInduction.tensor (contentAppendTo D Sc cutoff N β σ _ rfl) M.toFunctor v h m) =
      sign k (p * (n / 2 : ℕ)) •
        BalancedInduction.tensor (contentAppendTo D Sc cutoff N β σ _ rfl) M.toFunctor v
          (contentAppendToComponent D Sc cutoff N rfl rfl (a ^ n) v ≫
            twist k ((n : ZMod 2) * p) h) m := by
  rw [contentAppendToComponent_pow D Sc cutoff N ha]
  exact BalancedInduction.transformLinear_pow_tensor _ M w n v h m

theorem contentEnd_pow_parity {σ : List I} {p : ZMod 2}
    {a : End ((pres D Sc).obj (ob D σ))} (ha : a ∈ parity (R := k) _ _ p)
    (n : ℕ) : a ^ n ∈ parity (R := k) _ _ ((n : ZMod 2) * p) := by
  induction n with
  | zero => simpa using id_mem (R := k) ((pres D Sc).obj (ob D σ))
  | succ n ih =>
    rw [pow_succ', End.mul_def]
    simpa [add_mul] using comp_mem ih ha

/-- Ordered powers on admissible support; the second operator acts first. -/
theorem contentInductionEndLinear_ordered_tensor {β : Multiset I} {σ : List I}
    {p q : ZMod 2} {a b : End ((pres D Sc).obj (ob D σ))}
    (ha : a ∈ parity (R := k) _ _ p) (hb : b ∈ parity (R := k) _ _ q)
    (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N (β + (σ : Multiset I))) (r s : ℕ)
    (hr : (r : ZMod 2) * p = 0) (hs : (s : ZMod 2) * q = 0)
    (v : ContentCategory D Sc cutoff N β)
    (h : (contentAppendTo D Sc cutoff N β σ _ rfl).obj v ⟶ w) (m : M.obj v) :
    ((contentInductionEndLinear D Sc cutoff N ha M w ^ r) *
      (contentInductionEndLinear D Sc cutoff N hb M w ^ s))
        (BalancedInduction.tensor (contentAppendTo D Sc cutoff N β σ _ rfl) M.toFunctor v h m) =
      sign k (p * (r / 2 : ℕ) + q * (s / 2 : ℕ)) •
        BalancedInduction.tensor (contentAppendTo D Sc cutoff N β σ _ rfl) M.toFunctor v
          ((contentAppendToComponent D Sc cutoff N rfl rfl (a ^ r) v ≫
            contentAppendToComponent D Sc cutoff N rfl rfl (b ^ s) v) ≫ h) m := by
  rw [Module.End.mul_apply, contentInductionEndLinear_pow_tensor, map_smul,
    contentInductionEndLinear_pow_tensor, hr, hs, twist_zero, twist_zero,
    smul_smul, ← sign_add, add_comm (q * _) (p * _), Category.assoc]

/-- The second positioned dot on a two-colour block. -/
theorem contentPairDot_one_parity (i j : I) :
    dotE D Sc [i,j] 1 ∈ parity (R := k) _ _ (D.parity j) := by
  simpa using positionedDot_parity D Sc [i] [] j

/-- Each specified interior coefficient acts by the ordered powers of the two
induction dots. No support assumption is added: it follows from `Sc.s_eq_zero`. -/
theorem contentInduction_dot_monomial (β : Multiset I) (i j : I) (r s : ℕ)
    (M : ContentModules D (parameterTwist D Sc) cutoff N β)
    (w : ContentCategory D (parameterTwist D Sc) cutoff N (β + ([i,j] : Multiset I)))
    (v : ContentCategory D (parameterTwist D Sc) cutoff N β)
    (h : (contentAppendTo D (parameterTwist D Sc) cutoff N β [i,j] _ rfl).obj v ⟶ w)
    (m : M.obj v) :
    (Sc.s i j r s •
      ((contentInductionEndLinear D (parameterTwist D Sc) cutoff N
          (contentPairDot_one_parity D (parameterTwist D Sc) i j) M w ^ s) *
       (contentInductionEndLinear D (parameterTwist D Sc) cutoff N
          (firstDot_parity D (parameterTwist D Sc) i [j]) M w ^ r)))
      (BalancedInduction.tensor
        (contentAppendTo D (parameterTwist D Sc) cutoff N β [i,j] _ rfl) M.toFunctor v h m) =
    BalancedInduction.tensor
      (contentAppendTo D (parameterTwist D Sc) cutoff N β [i,j] _ rfl) M.toFunctor v
      (contentAppendToComponent D (parameterTwist D Sc) cutoff N rfl rfl
        ((SKM.zsign k (D.parity i * (r / 2 : ℕ) + D.parity j * (s / 2 : ℕ)) *
          Sc.s i j r s) •
          (dotE D (parameterTwist D Sc) [i,j] 0 ^ r *
           dotE D (parameterTwist D Sc) [i,j] 1 ^ s)) v ≫ h) m := by
  by_cases hc : Sc.s i j r s = 0
  · simp [hc, contentAppendToComponent_zero, BalancedInduction.tensor]
  · obtain ⟨hr, hs⟩ := elvParameter_support D Sc hc
    rw [LinearMap.smul_apply, contentInductionEndLinear_ordered_tensor D _ cutoff N _ _ M w s r hs hr,
      contentAppendToComponent_comp D _ cutoff N rfl rfl rfl _
        (contentEnd_pow_parity D _ (firstDot_parity D _ i [j]) r),
      contentAppendToComponent_smul, Linear.smul_comp]
    simp only [BalancedInduction.tensor, ← TensorProduct.smul_tmul', map_smul, smul_smul,
      ← End.mul_def, sign_eq_zsign]
    rw [add_comm (D.parity j * _) (D.parity i * _), mul_comm (Sc.s i j r s)]

end OddMath.QuiverHecke.ELV
end

end

section

/-! # The content induction quadratic polynomial

`DeformedActionAssembly.md` §6 (9): the normalized crossing square equals
the ordered polynomial in the two positioned induction dot operators. The
affine source uses `parameterTwist Sc`, while the operator polynomial has
exactly `Sc`. Its powers are reversed relative to End multiplication on the
affine source, without commuting any dots or coefficients.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

/-- Evaluation of an appended source endomorphism on a balanced generator. -/
def contentTensorEval {β : Multiset I} {σ : List I}
    (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N (β + (σ : Multiset I)))
    (v : ContentCategory D Sc cutoff N β)
    (h : (contentAppendTo D Sc cutoff N β σ _ rfl).obj v ⟶ w) (m : M.obj v) :
    End ((pres D Sc).obj (ob D σ)) →ₗ[k]
      BalancedInduction.Obj (contentAppendTo D Sc cutoff N β σ _ rfl) M.toFunctor w where
  toFun a := BalancedInduction.tensor (contentAppendTo D Sc cutoff N β σ _ rfl) M.toFunctor v
    (contentAppendToLinear D Sc cutoff N rfl rfl v a ≫ h) m
  map_add' a b := by
    simp only [map_add, Preadditive.add_comp, BalancedInduction.tensor, TensorProduct.add_tmul]
  map_smul' c a := by
    simp only [map_smul, Linear.smul_comp, BalancedInduction.tensor,
      ← TensorProduct.smul_tmul']
    rfl

/-- A supported dot power has no residual twist on the input coefficient. -/
theorem contentInductionEndLinear_supported_power {β : Multiset I} {σ : List I} {p : ZMod 2}
    {a : End ((pres D Sc).obj (ob D σ))} (ha : a ∈ parity (R := k) _ _ p)
    (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N (β + (σ : Multiset I)))
    (n : ℕ) (hn : (n : ZMod 2) * p = 0) (c : k)
    (v : ContentCategory D Sc cutoff N β)
    (h : (contentAppendTo D Sc cutoff N β σ _ rfl).obj v ⟶ w) (m : M.obj v) :
    (c • (contentInductionEndLinear D Sc cutoff N ha M w ^ n))
      (BalancedInduction.tensor (contentAppendTo D Sc cutoff N β σ _ rfl) M.toFunctor v h m) =
    contentTensorEval D Sc cutoff N M w v h m
      ((SKM.zsign k (p * (n / 2 : ℕ)) * c) • (a ^ n)) := by
  rw [LinearMap.smul_apply, contentInductionEndLinear_pow_tensor, hn, twist_zero,
    map_smul, smul_smul]
  change _ = _ • BalancedInduction.tensor _ M.toFunctor v
    (contentAppendToComponent D Sc cutoff N rfl rfl (a ^ n) v ≫ h) m
  rw [sign_eq_zsign, mul_comm c]

/-- Ordered polynomial: the first-position power acts before the second-position power. -/
def contentInductionPairPolynomial (β : Multiset I) (i j : I)
    (M : ContentModules D (parameterTwist D Sc) cutoff N β)
    (w : ContentCategory D (parameterTwist D Sc) cutoff N (β + ([i,j] : Multiset I))) :=
  let A := contentInductionEndLinear D (parameterTwist D Sc) cutoff N
    (firstDot_parity D (parameterTwist D Sc) i [j]) M w
  let B := contentInductionEndLinear D (parameterTwist D Sc) cutoff N
    (contentPairDot_one_parity D (parameterTwist D Sc) i j) M w
  if D.d i j = 0 then (Sc.t i j : k) • (1 : Module.End k _) else
    ∑ r ∈ Finset.range (D.dn i j), ∑ s ∈ Finset.range (D.dn j i),
      Sc.s i j r s • (B ^ s * A ^ r) +
    ((Sc.t i j : k) • A ^ D.dn i j + (Sc.t j i : k) • B ^ D.dn j i)

/-- The ordered polynomial in the induction dots evaluates to the specified source polynomial. -/
theorem contentInductionPairPolynomial_tensor (β : Multiset I) {i j : I} (hij : i ≠ j)
    (M : ContentModules D (parameterTwist D Sc) cutoff N β)
    (w : ContentCategory D (parameterTwist D Sc) cutoff N (β + ([i,j] : Multiset I)))
    (v : ContentCategory D (parameterTwist D Sc) cutoff N β)
    (h : (contentAppendTo D (parameterTwist D Sc) cutoff N β [i,j] _ rfl).obj v ⟶ w)
    (m : M.obj v) :
    contentInductionPairPolynomial D Sc cutoff N β i j M w
      (BalancedInduction.tensor (contentAppendTo D (parameterTwist D Sc) cutoff N β [i,j] _ rfl)
        M.toFunctor v h m) =
    contentTensorEval D (parameterTwist D Sc) cutoff N M w v h m
      (elvSignedPairQuadEval D Sc (R := End ((pres D (parameterTwist D Sc)).obj (ob D [i,j])))
        i j (dotE D (parameterTwist D Sc) [i,j] 0) (dotE D (parameterTwist D Sc) [i,j] 1)) := by
  unfold contentInductionPairPolynomial elvSignedPairQuadEval
  split_ifs with hd
  · simp [contentTensorEval, contentAppendToLinear_apply, contentAppendToComponent_id]
  · simp only [LinearMap.add_apply, LinearMap.sum_apply, map_add, map_sum]
    congr 1
    · apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro s _
      exact contentInduction_dot_monomial D Sc cutoff N β i j r s M w v h m
    · congr 1
      · exact contentInductionEndLinear_supported_power D _ cutoff N _ M w _
          (CyclotomicAction.dn_cast_mul_parity D hij) _ v h m
      · exact contentInductionEndLinear_supported_power D _ cutoff N _ M w _
          (CyclotomicAction.dn_cast_mul_parity D hij.symm) _ v h m

/-- The crossing square equals the ordered polynomial in the induction dot operators. -/
theorem contentInduction_quadratic_linear (β : Multiset I) {i j : I} (hij : i ≠ j)
    (M : ContentModules D (parameterTwist D Sc) cutoff N β)
    (w : ContentCategory D (parameterTwist D Sc) cutoff N (β + ([i,j] : Multiset I))) :
    (BalancedInduction.transformLinear
      (contentAppendTo_supernatural D (parameterTwist D Sc) cutoff N rfl
        (content_pair_swap β i j) (contentCrossAffine_mem D (parameterTwist D Sc) i j)) M w).comp
      (BalancedInduction.transformLinear
        (contentAppendTo_supernatural D (parameterTwist D Sc) cutoff N
          (content_pair_swap β i j) rfl (contentCrossAffine_mem D (parameterTwist D Sc) j i)) M w) =
      contentInductionPairPolynomial D Sc cutoff N β i j M w := by
  apply BalancedInduction.hom_ext
  intro v h m
  rw [LinearMap.comp_apply, contentInductionPairPolynomial_tensor D Sc cutoff N β hij M w v h m]
  exact contentInduction_quadratic_tensor D Sc cutoff N β hij M v w h m

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Single-letter content induction relations

Advances `DeformedActionAssembly.md` §5 by transporting the checked normalized
source crossing and positioned dots through the canonical even comparison.
`contentEPair_quadratic` is the original-Sc ordered polynomial relation on
successive single-letter induction, for every module. The second target content
is explicitly recast, not silently identified. `contentEPairCrossTransform`
is supernatural against odd module maps and `contentEPairCross_total` identifies
its evaluated map. No triple coherence, mixed braid, weight assembly or
nondegeneracy is asserted in this module.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

/-- Evaluation of a module isomorphism on the entire superspace. -/
def moduleIsoLinearEquiv {C : Type u} [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {M L : Superfunctor k C (SVec k)} (e : M ≅ L) (w : C) : M.obj w ≃ₗ[k] L.obj w where
  toLinearMap := e.hom.total w
  invFun := e.inv.total w
  left_inv x := by
    have h := congrArg (fun f : M ⟶ M => f.total w) e.hom_inv_id
    rw [Superfunctor.comp_total] at h
    simp only [SuperNatTrans.total, Superfunctor.id_app_zero,
      Superfunctor.id_app_one, add_zero] at h
    exact congrArg (fun f : M.obj w →ₗ[k] M.obj w => f x) h
  right_inv x := by
    have h := congrArg (fun f : L ⟶ L => f.total w) e.inv_hom_id
    rw [Superfunctor.comp_total] at h
    simp only [SuperNatTrans.total, Superfunctor.id_app_zero,
      Superfunctor.id_app_one, add_zero] at h
    exact congrArg (fun f : L.obj w →ₗ[k] L.obj w => f x) h

/-- The second single-letter induction has its target content explicitly transported. -/
abbrev contentEPairTo (β : Multiset I) (i j : I) (γ : Multiset I)
    (h : β + ([i,j] : Multiset I) = γ) :=
  contentE D Sc cutoff N β i ⋙
    contentInductionTo D Sc cutoff N (β + ([i] : Multiset I)) [j] γ
      (by rw [add_assoc]; exact h)

def contentEPairToComparison (β : Multiset I) (i j : I) (γ : Multiset I)
    (h : β + ([i,j] : Multiset I) = γ) :
    contentEPairTo D Sc cutoff N β i j γ h ≅ contentInductionTo D Sc cutoff N β [i,j] γ h :=
  contentInductionComp D Sc cutoff N β [i] [j] γ _ h

/-- The carrier of the actual evaluated pair functor. Keeping its SVec object
intact aligns all inherited module instances with independent whiskering maps. -/
abbrev ContentEPairSpace (β : Multiset I) (i j : I) (γ : Multiset I)
    (h : β + ([i,j] : Multiset I) = γ) (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N γ) : Type u :=
  (((contentEPairTo D Sc cutoff N β i j γ h).obj M).obj w).carrier

def contentEPairEquiv (β : Multiset I) (i j : I) (γ : Multiset I)
    (h : β + ([i,j] : Multiset I) = γ) (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N γ) :
    ((contentEPairTo D Sc cutoff N β i j γ h).obj M).obj w ≃ₗ[k]
      (((contentInductionTo D Sc cutoff N β [i,j] γ h).obj M).obj w).carrier :=
  moduleIsoLinearEquiv ((contentEPairToComparison D Sc cutoff N β i j γ h).app M) w

/-- Transport of a homogeneous transformation through even natural comparisons. -/
theorem evenComparison_supernatural
    {C B : Type*} [Category* C] [Category* B]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    {F G F' G' : C ⥤ B}
    [F.Additive] [F.Linear k] [G.Additive] [G.Linear k]
    [F'.Additive] [F'.Linear k] [G'.Additive] [G'.Linear k]
    (e : F' ≅ F) (f : G' ≅ G)
    (he : ∀ M, EvenComparisonAt (k := k) e M)
    (hf : ∀ M, EvenComparisonAt (k := k) f M)
    {p : ZMod 2} {x : ∀ M, F.obj M ⟶ G.obj M} (hx : IsSupernatural k p x) :
    IsSupernatural k p (fun M => (e.hom.app M ≫ x M) ≫ f.inv.app M) := by
  simpa only [zero_add, add_zero] using
    ((isSupernatural_of_natTrans e.hom (fun M => (he M).1)).comp hx).comp
      (isSupernatural_of_natTrans f.inv (fun M => (hf M).2))

private theorem homogeneous_total
    {C B : Type*} [Category* C] [Category* B]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    {F G : C ⥤ B} {p : ZMod 2} {x : ∀ M, F.obj M ⟶ G.obj M}
    (hx : IsSupernatural k p x) (M : C) : hx.toSuperNatTrans.total M = x M := by
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    simp [SuperNatTrans.total, IsSupernatural.toSuperNatTrans]

/-- Each positioned dot is transported by the same canonical even comparison. -/
def contentEPairDot (β : Multiset I) (i j : I)
    (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N (β + ([i,j] : Multiset I))) (a : Fin 2) :
    Module.End k (ContentEPairSpace D Sc cutoff N β i j _ rfl M w) :=
  (contentEPairEquiv D Sc cutoff N β i j _ rfl M w).symm.conjAlgEquiv k
    (if a = 0 then contentInductionEndLinear D Sc cutoff N (firstDot_parity D Sc i [j]) M w
      else contentInductionEndLinear D Sc cutoff N (contentPairDot_one_parity D Sc i j) M w)

/-- The polynomial retains the prescribed ordered dot powers and the specified Sc. -/
def contentEPairPolynomial (β : Multiset I) (i j : I)
    (M : ContentModules D (parameterTwist D Sc) cutoff N β)
    (w : ContentCategory D (parameterTwist D Sc) cutoff N (β + ([i,j] : Multiset I))) :
    Module.End k (ContentEPairSpace D (parameterTwist D Sc) cutoff N β i j _ rfl M w) :=
  let A := contentEPairDot D (parameterTwist D Sc) cutoff N β i j M w 0
  let B := contentEPairDot D (parameterTwist D Sc) cutoff N β i j M w 1
  if D.d i j = 0 then (Sc.t i j : k) • (1 : Module.End k _) else
    ∑ r ∈ Finset.range (D.dn i j), ∑ s ∈ Finset.range (D.dn j i),
      Sc.s i j r s • (B ^ s * A ^ r) +
    ((Sc.t i j : k) • A ^ D.dn i j + (Sc.t j i : k) • B ^ D.dn j i)

end OddMath.QuiverHecke.ELV
end

end
