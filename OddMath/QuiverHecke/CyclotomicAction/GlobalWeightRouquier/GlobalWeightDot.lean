import StringDiagrams.Super.TwoSCat
import StringDiagrams.Super.PiTwo
import StringDiagrams.Super.SCat
import OddMath.QuiverHecke.CyclotomicAction.GlobalHeight.GlobalHeightDot
import OddMath.QuiverHecke.CyclotomicAction.GlobalWeightRouquier.GlobalWeightCross

/-!
# Global weight rouquier

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-!
# The dot on weight-space induction

Ports `globalDot` of `Categorification/KLR/CyclotomicAction/Global.lean`. At
the successor of a block the dot is `globalContentDot`, transported along
`inductionComponent_blockSucc`; at a block without predecessor the induced
component is zero. The result is a supernatural endomorphism of `globalE`,
homogeneous of the colour parity `|i|`: odd colours carry the odd dot. This is
the `dot` field of `RouquierData` on weight spaces.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.CyclotomicAction
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
  (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a)

section Weight
variable (i : I) (Λ : X) {x y : X} (h : x + D.α i = y)

/-- The content dot between a block and its successor. -/
abbrev blockDot (β : WeightBlocks D Λ x) :=
  globalContentDot D Sc i a ha (blockSucc_val D Λ i h β).symm

/-- The dot component at a block with a chosen predecessor. -/
def globalWeightDotVia (p : ZMod 2) (M : WeightProduct D Sc a ha Λ x) (β : WeightBlocks D Λ x)
    (δ : WeightBlocks D Λ y) (hβ : blockSucc D Λ i h β = δ) :
    (inductionComponent D Sc a ha i Λ h δ).obj M ⟶ (inductionComponent D Sc a ha i Λ h δ).obj M := by
  subst hβ
  exact eqToHom (inductionComponent_obj_blockSucc D Sc a ha i Λ h β M) ≫
    (blockDot D Sc a ha i Λ h β).app p (M β) ≫
      eqToHom (inductionComponent_obj_blockSucc D Sc a ha i Λ h β M).symm

theorem globalWeightDotVia_eq (p : ZMod 2) (M : WeightProduct D Sc a ha Λ x)
    (β β' : WeightBlocks D Λ x) (δ : WeightBlocks D Λ y) (hβ : blockSucc D Λ i h β = δ)
    (hβ' : blockSucc D Λ i h β' = δ) :
    globalWeightDotVia D Sc a ha i Λ h p M β δ hβ =
      globalWeightDotVia D Sc a ha i Λ h p M β' δ hβ' := by
  obtain rfl := blockSucc_injective D Λ i h (hβ.trans hβ'.symm)
  subst hβ
  rfl

open scoped Classical in
/-- The dot component at a block: through the predecessor, or zero. -/
def globalWeightDotComponent (p : ZMod 2) (M : WeightProduct D Sc a ha Λ x)
    (δ : WeightBlocks D Λ y) :
    (inductionComponent D Sc a ha i Λ h δ).obj M ⟶ (inductionComponent D Sc a ha i Λ h δ).obj M :=
  if hδ : ∃ β, blockSucc D Λ i h β = δ then
    globalWeightDotVia D Sc a ha i Λ h p M hδ.choose δ hδ.choose_spec
  else 0

theorem globalWeightDotComponent_blockSucc (p : ZMod 2) (M : WeightProduct D Sc a ha Λ x)
    (β : WeightBlocks D Λ x) :
    globalWeightDotComponent D Sc a ha i Λ h p M (blockSucc D Λ i h β) =
      eqToHom (inductionComponent_obj_blockSucc D Sc a ha i Λ h β M) ≫
        (blockDot D Sc a ha i Λ h β).app p (M β) ≫
          eqToHom (inductionComponent_obj_blockSucc D Sc a ha i Λ h β M).symm := by
  unfold globalWeightDotComponent
  split
  · rename_i hc
    exact globalWeightDotVia_eq D Sc a ha i Λ h p M _ β _ hc.choose_spec rfl
  · rename_i hc
    exact absurd (⟨β, rfl⟩ : ∃ c, blockSucc D Λ i h c = blockSucc D Λ i h β) hc

theorem globalWeightDotComponent_mem (p : ZMod 2) (M : WeightProduct D Sc a ha Λ x)
    (δ : WeightBlocks D Λ y) :
    globalWeightDotComponent D Sc a ha i Λ h p M δ ∈ parity (R := k) _ _ p := by
  by_cases hδ : ∃ β, blockSucc D Λ i h β = δ
  · obtain ⟨β, rfl⟩ := hδ
    rw [globalWeightDotComponent_blockSucc]
    have hm := comp_mem (eqToHom_mem_parity_zero
        (inductionComponent_obj_blockSucc D Sc a ha i Λ h β M))
      (comp_mem ((blockDot D Sc a ha i Λ h β).app_mem p (M β))
        (eqToHom_mem_parity_zero (inductionComponent_obj_blockSucc D Sc a ha i Λ h β M).symm))
    simpa only [zero_add, add_zero] using hm
  · rw [(inductionComponent_isZero D Sc a ha i Λ h δ hδ M).eq_of_src
      (globalWeightDotComponent D Sc a ha i Λ h p M δ) 0]
    exact Submodule.zero_mem _

theorem globalWeightDotComponent_naturality (p : ZMod 2) (β : WeightBlocks D Λ x)
    {M M' : WeightProduct D Sc a ha Λ x} {q : ZMod 2} (f : M ⟶ M')
    (hf : f ∈ parity (R := k) M M' q) :
    (inductionComponent D Sc a ha i Λ h (blockSucc D Λ i h β)).map f ≫
        globalWeightDotComponent D Sc a ha i Λ h p M' (blockSucc D Λ i h β) =
      koszulSign p q • (globalWeightDotComponent D Sc a ha i Λ h p M (blockSucc D Λ i h β) ≫
        (inductionComponent D Sc a ha i Λ h (blockSucc D Λ i h β)).map f) := by
  rw [inductionComponent_map_blockSucc, globalWeightDotComponent_blockSucc,
    globalWeightDotComponent_blockSucc]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  have hn := (blockDot D Sc a ha i Λ h β).naturality p (f β) (hf β)
  rw [← Category.assoc ((blockInd D Sc a ha i Λ h β).map (f β)), Superfunctor.map, hn,
    Linear.smul_comp, Linear.comp_smul, Category.assoc]

/-- **The dot on weight-space induction.** -/
def globalWeightDot :
    SuperNatTrans k (globalEFunctor D Sc a ha i Λ h) (globalEFunctor D Sc a ha i Λ h) where
  app p M δ := globalWeightDotComponent D Sc a ha i Λ h p M δ
  app_mem p M δ := globalWeightDotComponent_mem D Sc a ha i Λ h p M δ
  naturality p M M' q f hf := by
    funext δ
    by_cases hδ : ∃ β, blockSucc D Λ i h β = δ
    · obtain ⟨β, rfl⟩ := hδ
      exact globalWeightDotComponent_naturality D Sc a ha i Λ h p β f hf
    · exact (inductionComponent_isZero D Sc a ha i Λ h δ hδ _).eq_of_src _ _

/-- The dot as a 2-endomorphism of weight-space induction in the action target. -/
def globalActionDot : globalActionE D Sc a ha i Λ h ⟶ globalActionE D Sc a ha i Λ h :=
  globalWeightDot D Sc a ha i Λ h

end Weight

end OddMath.QuiverHecke.CyclotomicAction
end

end

section

/-!
# The cyclotomic factor family on weight spaces, relative to local inversion

Assembles the fields of `SKM.RouquierFamily` for the cyclotomic weight spaces: weight-space
induction `E_i`, restriction `F_i`, the even adjunction `globalActionAdjunction`, the dot, the
signed crossing `-ψ` (`globalRouquierData`), square zero (`globalRouquierData_square`), the
same-colour braid (`globalRouquierData_braid`) and the two dot slides
(`globalActionSignedCross_slide_left/right`).

The remaining fields of `SKM.SuperRouquierLoc` are the two finite inverses of the Rouquier
mate (KKO I, arXiv:1206.5933v2, the local inversion of Theorem 8.5 / KK Theorem 5.2 in the
even case). They are not proved here: `GlobalLocalInversion` packages exactly these two
inverses at one pair of adjacent weight steps, and `globalRouquierFamily` takes a family of
them as an explicit hypothesis. No other field is assumed. The family also records the degree
hypothesis `CyclotomicDegreeMatch` (each `a i` monic of degree `⟨h_i, Λ⟩`), under which local
inversion is expected to hold; for arbitrary `a` it can fail.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.CyclotomicAction
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I] [DecidableEq I]
  (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a) (Λ : X)

/-- The two finite inverses of the Rouquier mate `F_i E_i ⟶ E_i F_i` at the weight steps
`x₀ → x₁ → x₂`, with the dotted counits (positive height `D.h i x₁`) and the dotted units
(negative height) as the extra columns: the `invPos`/`invNeg` fields of
`SKM.SuperRouquierLoc`. This is the local inversion statement, kept as data. -/
structure GlobalLocalInversion (i : I) {x₀ x₁ x₂ : X} (h₁ : x₀ + D.α i = x₁)
    (h₂ : x₁ + D.α i = x₂) where
  invPos : 0 ≤ D.h i x₁ → SKM.SuperSumInvTo (k := k)
    (SKM.rouquierMate (globalActionAdjunction D Sc a ha i Λ h₁)
      (globalActionAdjunction D Sc a ha i Λ h₂)
      (globalActionSignedCross D Sc a ha Λ i i h₁ h₂ h₁ h₂))
    (fun n => globalActionF D Sc a ha i Λ h₁ ◁
        SKM.rouquierPower (globalActionDot D Sc a ha i Λ h₁) n ≫
      (globalActionAdjunction D Sc a ha i Λ h₁).counit)
    (D.parity i) (fun n => n * D.parity i) (D.h i x₁).toNat
  invNeg : D.h i x₁ ≤ 0 → SKM.SuperSumInvFrom (k := k)
    (SKM.rouquierMate (globalActionAdjunction D Sc a ha i Λ h₁)
      (globalActionAdjunction D Sc a ha i Λ h₂)
      (globalActionSignedCross D Sc a ha Λ i i h₁ h₂ h₁ h₂))
    (fun n => (globalActionAdjunction D Sc a ha i Λ h₂).unit ≫
      SKM.rouquierPower (globalActionDot D Sc a ha i Λ h₂) n ▷ globalActionF D Sc a ha i Λ h₂)
    (D.parity i) (fun n => n * D.parity i) (-D.h i x₁).toNat

end OddMath.QuiverHecke.CyclotomicAction
end

end

section

/-!
# Dotted cup and cap kernels at one height

Write `A`, `B` for the deformed cyclotomic algebras at heights `n`, `n + 1` of the extended
tower, `φ : A → B` for the strand map of colour `i`, `e = φ(1)`, `P = B e`, `Q = e B` for the
induction and restriction corners of `GlobalHeightAdjunction`, `x ∈ B` for the last dot and
`p = |i|`. This file constructs the kernels of display (2)/(4) of
`docs/Nondegeneracy/DeformedMatrixComparison.md` without the normalizing signs `d_k`:

* the dotted cup `j_k : A ⟶ e B ⊗_B B e`, `a ↦ x^k φ(a) ⊗ e` (so `u_k = d_k j_k`);
* the dotted cap `κ_k : B e ⊗_A e B ⟶ B`, `y ⊗ z ↦ (-1)^{kp|y|} y x^k z`
  (so `c_k = d_k κ_k`).

In the Rouquier mate at the weight steps `x₀ → x₁ → x₂` the dotted cup is used for the
second step (at one height higher than the cap), so both kernels are stated at one level `n`.
Both are superbimodule morphisms of parity `k p`. The only input is the signed commutation
`φ(r) x = (-1)^{p|r|} x φ(r)` of the last dot (`heightLastDot_comm`), iterated in
`heightAppend_mul_heightLastDot_pow`.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
open SuperBimodule
namespace OddMath.QuiverHecke.CyclotomicAction
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]

/-- The last dot commutes with the strand map up to the iterated Koszul sign. -/
theorem heightAppend_mul_heightLastDot_pow (a : I → _root_.Polynomial k) (i : I)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) {q : ZMod 2}
    {r : heightAlgebra D Sc a n} (hr : r ∈ heightParity D Sc a ha n q) (m : ℕ) :
    heightAppend D Sc a i n r * heightLastDot D Sc a i n ^ m =
      koszulSign q ((m : ZMod 2) * D.parity i) •
        (heightLastDot D Sc a i n ^ m * heightAppend D Sc a i n r) := by
  induction m with
  | zero => simp [koszulSign]
  | succ m ih =>
    rw [pow_succ, ← mul_assoc, ih, smul_mul_assoc, mul_assoc,
      heightLastDot_comm D Sc a i ha n hr, mul_smul_comm, smul_smul, ← mul_assoc,
      ← koszulSign_add_right, Nat.cast_succ, add_mul, one_mul]

variable (i : I) (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a) (n : ℕ)
  (m : ℕ)

local notation "A₀" => heightAlgebra D Sc a n
local notation "B₁" => heightAlgebra D Sc a (n + 1)
local notation "GA" => heightParity D Sc a ha n
local notation "GB" => heightParity D Sc a ha (n + 1)
local notation "φ₁" => heightAppend D Sc a i n
local notation "x₁" => heightLastDot D Sc a i n
local notation "P₁" => heightInductionCorner D Sc i a ha n
local notation "Q₁" => heightRestrictionCorner D Sc i a ha n
local notation "p" => D.parity i
local notation "kp" => ((m : ZMod 2) * D.parity i)

/-! ### The dotted cup -/

/-! ### The dotted cap -/

/-- The bilinear dotted cap `x ⊗ y ↦ sgn_{m p}(x) x₁^m y`. -/
def rouquierCapKernelBi : (P₁).toSVec →ₗ[k] (Q₁).toSVec →ₗ[k] B₁ where
  toFun x :=
    { toFun := fun y => ((P₁).toSVec.sgn kp x).val * x₁ ^ m * y.val
      map_add' := fun y z => mul_add _ y.val z.val
      map_smul' := fun c y => mul_smul_comm c _ y.val }
  map_add' x y := by
    ext z
    change ((P₁).toSVec.sgn kp (x + y)).val * _ * _ = _
    rw [map_add]
    change (((P₁).toSVec.sgn kp x).val + ((P₁).toSVec.sgn kp y).val) * _ * _ = _
    rw [add_mul, add_mul]
    rfl
  map_smul' c x := by
    ext z
    change ((P₁).toSVec.sgn kp (c • x)).val * _ * _ = _
    rw [map_smul]
    change (c • ((P₁).toSVec.sgn kp x).val) * _ * _ = _
    rw [smul_mul_assoc, smul_mul_assoc]
    rfl

private theorem cap_sgn_action {q : ZMod 2} {f : (P₁).toSVec ⟶ (P₁).toSVec}
    (hf : f ∈ SVec.parityHom (P₁).toSVec (P₁).toSVec q) (x : (P₁).toSVec) :
    (P₁).toSVec.sgn kp (f x) = sign k (q * kp) • f ((P₁).toSVec.sgn kp x) :=
  LinearMap.congr_fun (SVec.sgn_comp_of_mem hf kp) x

theorem rouquierCapKernel_balance (x : (P₁).toSVec) (r : heightAlgebra D Sc a n)
    (y : (Q₁).toSVec) :
    rouquierCapKernelBi D Sc i a ha n m ((P₁).ract r x) y =
      rouquierCapKernelBi D Sc i a ha n m x ((Q₁).lact r y) := by
  induction r using SuperBimodule.alg_induction_on GA with
  | zero => simp
  | add r s hr hs =>
    rw [map_add, map_add, SVec.add_apply, SVec.add_apply, map_add, LinearMap.add_apply, map_add,
      hr, hs]
  | hom q r hr =>
    have h := cap_sgn_action D Sc i a ha n m ((P₁).ract_mem q r hr) x
    change ((P₁).toSVec.sgn kp ((P₁).ract r x)).val * x₁ ^ m * y.val =
      ((P₁).toSVec.sgn kp x).val * x₁ ^ m * (φ₁ r * y.val)
    rw [h]
    change (sign k (q * kp) • (((P₁).toSVec.sgn kp x).val * φ₁ r)) * x₁ ^ m * y.val = _
    rw [smul_mul_assoc, smul_mul_assoc, mul_assoc _ (φ₁ r),
      heightAppend_mul_heightLastDot_pow D Sc a i ha n hr m, mul_smul_comm, smul_mul_assoc,
      Supercategory.sign_mul, Int.cast_smul_eq_zsmul, koszulSign_smul_smul, mul_assoc, mul_assoc,
      mul_assoc]

/-- The linear dotted cap on the balanced tensor product. -/
def rouquierCapKernelLinear : (tensor P₁ Q₁).toSVec →ₗ[k] B₁ :=
  tensorLift (rouquierCapKernelBi D Sc i a ha n m) (rouquierCapKernel_balance D Sc i a ha n m)

@[simp] theorem rouquierCapKernelLinear_btmul (x : (P₁).toSVec) (y : (Q₁).toSVec) :
    rouquierCapKernelLinear D Sc i a ha n m (btmul P₁ Q₁ x y) =
      ((P₁).toSVec.sgn kp x).val * x₁ ^ m * y.val :=
  tensorLift_btmul _ _ x y

end OddMath.QuiverHecke.CyclotomicAction
end

end
