import StringDiagrams.Super.Functor
import StringDiagrams.Super.SCat
import StringDiagrams.Super.TwoSCat
import OddMath.QuiverHecke.CyclotomicAction.ModuleInduction.InductionComposition
import OddMath.SKM.RouquierData
import OddMath.QuiverHecke.CyclotomicAction.SuperQuotient

/-!
# Super adjunction

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-!
# The homogeneous crossing between composition corners

Ports the crossing construction of
`Categorification/KLR/CyclotomicAction/Induction.lean`, the intertwiner method of
`Categorification/KLR/CyclotomicAction/Slides.lean` and the corner comparison of
`Categorification/KLR/CyclotomicAction/Comparison.lean`.
The map from `compositionCorner i j` to `compositionCorner j i` is
`x ↦ (-1)^{|i||j||x|} x τᵢⱼ`. Here `τᵢⱼ` is the diagram from the word
ending in `[i,j]` to the word ending in `[j,i]`; right multiplication reverses
this direction on the left ideals. The sign gives signed left linearity and
ordinary right linearity in the superbimodule convention. No inverse is claimed.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
variable (i j : I) (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a) (n : ℕ)
local notation "P" => compositionCorner D Sc i j a ha n
local notation "Q" => compositionCorner D Sc j i a ha n
local notation "GC" => cyclotomicParity D Sc a ha (n + 1 + 1)
local notation "GA" => cyclotomicParity D Sc a ha n
local notation "c" => cyclotomicLastCrossing D Sc i j a n
local notation "d" => D.parity i * D.parity j

private theorem crossing_mul_mem (x : CyclotomicAlgebra D Sc a (n + 1 + 1))
    (_hx : x ∈ compositionCornerSubmodule D Sc i j a n) :
    x * c ∈ compositionCornerSubmodule D Sc j i a n := by
  change (x * c) * cyclotomicAppend D Sc j a (n + 1) (cyclotomicAppend D Sc i a n 1) = x * c
  rw [mul_assoc, (cyclotomicLastCrossing_corner D Sc i j a n).2]

/-- Parity sign followed by right multiplication by the concrete crossing. -/
def compositionCrossingLinear : (P).toSVec ⟶ (Q).toSVec :=
  SVec.ofHom ((P).toSVec.sgn d) ≫
    SVec.restrictHom ((SuperBimodule.regular GC).ract c) (crossing_mul_mem D Sc i j a n)

/-- The crossing map has parity `|i||j|`. -/
theorem compositionCrossingLinear_parity :
    compositionCrossingLinear D Sc i j a ha n ∈ SVec.parityHom (P).toSVec (Q).toSVec d := by
  change compositionCrossingLinear D Sc i j a ha n ∈ parity (R := k) (P).toSVec (Q).toSVec d
  unfold compositionCrossingLinear
  have hd := SVec.restrictHom_mem (hU := compositionCorner_odd_mem D Sc i j a ha n)
    (hU' := compositionCorner_odd_mem D Sc j i a ha n)
    ((SuperBimodule.regular GC).ract_mem d c
      (cyclotomicLastCrossing_parity D Sc i j a ha n)) (crossing_mul_mem D Sc i j a n)
  simpa only [compositionCorner, compositionCornerSpace, SuperBimodule.regular, zero_add] using
    Supercategory.comp_mem (SVec.sgn_mem (P).toSVec d) hd

private theorem crossing_sgn_action {p : ZMod 2} {f : (P).toSVec ⟶ (P).toSVec}
    (hf : f ∈ SVec.parityHom (P).toSVec (P).toSVec p) (x : (P).toSVec) :
    (P).toSVec.sgn d (f x) = sign k (p * d) • f ((P).toSVec.sgn d x) :=
  LinearMap.congr_fun (SVec.sgn_comp_of_mem hf d) x

/-- The two action laws follow from the proved signed crossing intertwiner. -/
theorem compositionCrossingLinear_isHom :
    SuperBimodule.IsHom P Q (compositionCrossingLinear D Sc i j a ha n) := by
  apply (SuperBimodule.isHom_iff_of_mem (compositionCrossingLinear_parity D Sc i j a ha n)).2
  constructor
  · intro p b hb
    apply SVec.hom_ext
    intro x
    have h := crossing_sgn_action D Sc i j a ha n ((P).lact_mem p b hb) x
    apply Subtype.ext
    change ((P).toSVec.sgn d ((P).lact b x)).val * c =
      sign k (p * d) • (b * (((P).toSVec.sgn d x).val * c))
    rw [h]
    change (sign k (p * d) • (b * ((P).toSVec.sgn d x).val)) * c = _
    rw [smul_mul_assoc, mul_assoc]
  · intro r
    induction r using SuperBimodule.alg_induction_on GA with
    | zero => simp
    | add r s hr hs => simp only [map_add, Preadditive.add_comp, Preadditive.comp_add, hr, hs]
    | hom p r hr =>
      apply SVec.hom_ext
      intro x
      have h := crossing_sgn_action D Sc i j a ha n ((P).ract_mem p r hr) x
      apply Subtype.ext
      change ((P).toSVec.sgn d ((P).ract r x)).val * c =
        (((P).toSVec.sgn d x).val * c) *
          cyclotomicAppend D Sc j a (n + 1) (cyclotomicAppend D Sc i a n r)
      rw [h]
      change (sign k (p * d) • (((P).toSVec.sgn d x).val *
        cyclotomicAppend D Sc i a (n + 1) (cyclotomicAppend D Sc j a n r))) * c = _
      rw [smul_mul_assoc, mul_assoc, cyclotomicLastCrossing_intertwines D Sc i j a ha n hr,
        mul_smul_comm, Supercategory.sign_mul, Int.cast_smul_eq_zsmul, koszulSign_smul_smul, mul_assoc]

/-- The homogeneous superbimodule map between the two composition corners. -/
def compositionSuperCrossing : P ⟶ Q :=
  ⟨compositionCrossingLinear D Sc i j a ha n, compositionCrossingLinear_isHom D Sc i j a ha n⟩

theorem compositionSuperCrossing_parity :
    compositionSuperCrossing D Sc i j a ha n ∈ parity (R := k) P Q d :=
  SuperBimodule.mem_parity_iff.2 (compositionCrossingLinear_parity D Sc i j a ha n)

end OddMath.QuiverHecke
end

end

section

/-!
# The crossing on composed cyclotomic superinduction

Ports the crossing of `Categorification/KLR/CyclotomicAction/Induction.lean`
through the even comparison of `CyclotomicAction/Comparison.lean`.
The transformation below is obtained from `compositionSuperCrossing`, not from
an assumed crossing operator. Only its parity and supernatural naturality are
asserted; no square, braid, inversion or KKO relations are asserted.
-/

noncomputable section
open CategoryTheory StringDiagrams SuperBimodule Supercategory
namespace OddMath.QuiverHecke
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
variable (i j : I) (a : I → _root_.Polynomial k)
  (ha : CyclotomicPolynomialParity D a) (n : ℕ)
local notation "P" => compositionCorner D Sc i j a ha n
local notation "Q" => compositionCorner D Sc j i a ha n
local notation "F" => cyclotomicSuperInduction D Sc j a ha n ⋙
  cyclotomicSuperInduction D Sc i a ha (n + 1)
local notation "G" => cyclotomicSuperInduction D Sc i a ha n ⋙
  cyclotomicSuperInduction D Sc j a ha (n + 1)
local notation "d" => D.parity i * D.parity j
local notation "e" => inductionFunctorComparison D Sc i j a ha n
local notation "e'" => inductionFunctorComparison D Sc j i a ha n

/-- Transport the corner crossing along the two even comparison isomorphisms. -/
def inductionCrossingApp (M : CyclotomicSupermodules D Sc a ha n) : (F).obj M ⟶ (G).obj M :=
  (e).hom.app M ≫ whiskerRight (compositionSuperCrossing D Sc i j a ha n) M ≫ (e').inv.app M

/-- The transported crossing has parity `|i||j|`. -/
theorem inductionCrossingApp_mem (M : CyclotomicSupermodules D Sc a ha n) :
    inductionCrossingApp D Sc i j a ha n M ∈ parity (R := k) _ _ d := by
  change ((inductionFunctorComparisonApp D Sc i j a ha n M).hom ≫
    whiskerRight (compositionSuperCrossing D Sc i j a ha n) M ≫
      (inductionFunctorComparisonApp D Sc j i a ha n M).inv) ∈
        parity (R := k) ((F).obj M) ((G).obj M) d
  simpa only [zero_add, add_zero] using comp_mem
    (inductionFunctorComparisonApp_hom_mem D Sc i j a ha n M)
    (comp_mem (whiskerRight_mem P (compositionSuperCrossing_parity D Sc i j a ha n) M)
      (inductionFunctorComparisonApp_inv_mem D Sc j i a ha n M))

/-- The comparison introduces no additional naturality sign. -/
theorem inductionCrossingApp_naturality
    {M N : CyclotomicSupermodules D Sc a ha n} {q : ZMod 2} (f : M ⟶ N)
    (hf : f ∈ parity (R := k) M N q) :
    (F).map f ≫ inductionCrossingApp D Sc i j a ha n N =
      koszulSign d q • (inductionCrossingApp D Sc i j a ha n M ≫ (G).map f) := by
  have hcross : whiskerLeft P f ≫ whiskerRight (compositionSuperCrossing D Sc i j a ha n) N =
      koszulSign d q • (whiskerRight (compositionSuperCrossing D Sc i j a ha n) M ≫
        whiskerLeft Q f) := by
    rw [super_interchange P f (compositionSuperCrossing_parity D Sc i j a ha n) hf,
      koszulSign_smul_smul]
  have he := (e).hom.naturality f
  have he' := (e').inv.naturality f
  change (F).map f ≫ (e).hom.app N = (e).hom.app M ≫ whiskerLeft P f at he
  change whiskerLeft Q f ≫ (e').inv.app N = (e').inv.app M ≫ (G).map f at he'
  unfold inductionCrossingApp
  rw [← Category.assoc, he, Category.assoc, ← Category.assoc (whiskerLeft P f),
    hcross, Linear.smul_comp, Linear.comp_smul, Category.assoc, he']
  simp only [Category.assoc]

/-- The homogeneous supernatural crossing between the composed induction superfunctors. -/
def cyclotomicSuperInductionCrossing : SuperNatTrans k F G where
  app p M := if p = d then inductionCrossingApp D Sc i j a ha n M else 0
  app_mem p M := by
    split_ifs with h
    · subst p
      exact inductionCrossingApp_mem D Sc i j a ha n M
    · exact Submodule.zero_mem _
  naturality p M N q f hf := by
    split_ifs with h
    · subst p
      exact inductionCrossingApp_naturality D Sc i j a ha n f hf
    · simp

/-- The component of parity `|i||j|` is precisely the transported corner crossing. -/
@[simp] theorem cyclotomicSuperInductionCrossing_app
    (M : CyclotomicSupermodules D Sc a ha n) :
    (cyclotomicSuperInductionCrossing D Sc i j a ha n).app d M =
      (e).hom.app M ≫ whiskerRight (compositionSuperCrossing D Sc i j a ha n) M ≫
        (e').inv.app M := by
  simp [cyclotomicSuperInductionCrossing, inductionCrossingApp]

end OddMath.QuiverHecke
end

end

section

/-!
# The unit of cyclotomic super induction and restriction

Ports the unit construction of
`Categorification/TwoRep/CyclotomicRouqAdjunction.lean` using genuine balanced
super tensor products. Both inserted colour idempotents are even.
-/

noncomputable section
open CategoryTheory StringDiagrams
open SuperBimodule
namespace OddMath.QuiverHecke
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
variable (i : I) (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a) (n : ℕ)

local notation "A" => CyclotomicAlgebra D Sc a n
local notation "B" => CyclotomicAlgebra D Sc a (n + 1)
local notation "φ" => cyclotomicAppend D Sc i a n
local notation "P" => inductionCorner D Sc i a ha n
local notation "Q" => restrictionCorner D Sc i a ha n
local notation "ep" => inductionCornerIdempotent D Sc i a ha n
local notation "eq" => restrictionCornerOf D Sc i a ha n 1

/-- The two even colour idempotents give the linear unit. -/
def superUnitLinear (M : CyclotomicSupermodules D Sc a ha n) :
    M.toSVec →ₗ[k] (tensor Q (tensor P M)).toSVec where
  toFun m := btmul Q (tensor P M) eq (btmul P M ep m)
  map_add' x y := by rw [btmul_add_right, btmul_add_right]
  map_smul' c x := by rw [btmul_smul_right, btmul_smul_right]; rfl

@[simp] theorem superUnitLinear_apply (M : CyclotomicSupermodules D Sc a ha n) (m : M.toSVec) :
    superUnitLinear D Sc i a ha n M m = btmul Q (tensor P M) eq (btmul P M ep m) := rfl

theorem restrictionCornerOf_one_mem : eq ∈ (Q).toSVec.part 0 :=
  (restrictionCorner_mem_part_iff D Sc i a ha n).mpr
    (cyclotomicAppend_parity D Sc i a ha n (SetLike.one_mem_graded _))

theorem superUnitLinear_mem (M : CyclotomicSupermodules D Sc a ha n) :
    SVec.ofHom (superUnitLinear D Sc i a ha n M) ∈
      SVec.parityHom M.toSVec (tensor Q (tensor P M)).toSVec 0 := by
  apply SVec.mem_parityHom_of_apply_mem
  intro p m hm
  change btmul Q (tensor P M) eq (btmul P M ep m) ∈
    (tensor Q (tensor P M)).toSVec.part (p + 0)
  simpa only [zero_add, add_zero] using
    btmul_mem_part Q (tensor P M) (restrictionCornerOf_one_mem D Sc i a ha n)
      (btmul_mem_part P M (inductionCornerIdempotent_mem D Sc i a ha n) hm)

theorem superUnitLinear_lact (M : CyclotomicSupermodules D Sc a ha n) (r : A) (m : M.toSVec) :
    superUnitLinear D Sc i a ha n M (M.lact r m) =
      (tensor Q (tensor P M)).lact r (superUnitLinear D Sc i a ha n M m) := by
  rw [superUnitLinear_apply, superUnitLinear_apply, lact_btmul, ← btmul_ract_lact]
  have he : (P).ract r ep = (P).lact (φ r) ep := by
    apply Subtype.ext
    change φ 1 * φ r = φ r * φ 1
    rw [← map_mul, ← map_mul, one_mul, mul_one]
  rw [he, ← lact_btmul, ← btmul_ract_lact]
  congr 1
  apply Subtype.ext
  change φ 1 * φ r = φ r * φ 1
  rw [← map_mul, ← map_mul, one_mul, mul_one]

/-- The even component of the induction-restriction unit. -/
def superUnitComponent (M : CyclotomicSupermodules D Sc a ha n) : M ⟶ tensor Q (tensor P M) :=
  ⟨SVec.ofHom (superUnitLinear D Sc i a ha n M), by
    apply (isHom_iff_of_mem (superUnitLinear_mem D Sc i a ha n M)).mpr
    constructor
    · intro p r _
      simp only [mul_zero, Supercategory.sign_zero, one_smul]
      apply SVec.hom_ext
      intro m
      exact superUnitLinear_lact D Sc i a ha n M r m
    · intro c
      apply SVec.hom_ext
      intro m
      rfl⟩

/-- Naturality includes homogeneous odd module maps. -/
theorem superUnitComponent_naturality_of_mem
    {M N : CyclotomicSupermodules D Sc a ha n} {p : ZMod 2} (f : M ⟶ N)
    (hf : f ∈ Supercategory.parity (R := k) M N p) :
    f ≫ superUnitComponent D Sc i a ha n N =
      superUnitComponent D Sc i a ha n M ≫ whiskerLeft Q (whiskerLeft P f) := by
  apply SuperBimodule.hom_ext
  apply SVec.hom_ext
  intro m
  change superUnitLinear D Sc i a ha n N (f.1 m) =
    (whiskerLeft Q (whiskerLeft P f)).1 (superUnitLinear D Sc i a ha n M m)
  rw [superUnitLinear_apply, superUnitLinear_apply,
    whiskerLeft_btmul Q _ (whiskerLeft_mem P f hf) (restrictionCornerOf_one_mem D Sc i a ha n),
    whiskerLeft_btmul P f hf (inductionCornerIdempotent_mem D Sc i a ha n)]
  simp only [zero_mul, Supercategory.sign_zero, one_smul]

/-- The actual even unit as a natural transformation between superfunctors. -/
def cyclotomicSuperUnit : 𝟭 (CyclotomicSupermodules D Sc a ha n) ⟶
    cyclotomicSuperInduction D Sc i a ha n ⋙ cyclotomicSuperRestriction D Sc i a ha n where
  app M := superUnitComponent D Sc i a ha n M
  naturality {M N} f := by
    change f ≫ superUnitComponent D Sc i a ha n N =
      superUnitComponent D Sc i a ha n M ≫ whiskerLeft Q (whiskerLeft P f)
    refine Supercategory.induction_on (R := k) f ?_ ?_ ?_
    · simp only [whiskerLeft_zero, Limits.zero_comp, Limits.comp_zero]
    · intro p g hg
      exact superUnitComponent_naturality_of_mem D Sc i a ha n g hg
    · intro f g hf hg
      simp only [whiskerLeft_add, Preadditive.add_comp, Preadditive.comp_add, hf, hg]

end OddMath.QuiverHecke
end

end

section

/-!
# The counit of cyclotomic super induction and restriction

Ports the counit construction of
`Categorification/TwoRep/CyclotomicRouqAdjunction.lean`. Evaluation is the
actual action `(x ⊗ (y ⊗ m)) ↦ (xy)m` on the balanced super tensor products.
-/

noncomputable section
open CategoryTheory StringDiagrams
open SuperBimodule
namespace OddMath.QuiverHecke
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
variable (i : I) (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a) (n : ℕ)
local notation "A" => CyclotomicAlgebra D Sc a n
local notation "B" => CyclotomicAlgebra D Sc a (n + 1)
local notation "φ" => cyclotomicAppend D Sc i a n
local notation "P" => inductionCorner D Sc i a ha n
local notation "Q" => restrictionCorner D Sc i a ha n
variable (M : CyclotomicSupermodules D Sc a ha (n + 1))

/-- The inner bilinear action of a fixed induction element. -/
def superCounitInnerBi (x : (P).toSVec) :
    (Q).toSVec →ₗ[k] M.toSVec →ₗ[k] M.toSVec :=
  M.lact.comp (cornerPairingBi D Sc i a ha n x)

theorem superCounitInner_balance (x : (P).toSVec) (y : (Q).toSVec) (b : B) (m : M.toSVec) :
    superCounitInnerBi D Sc i a ha n M x ((Q).ract b y) m =
      superCounitInnerBi D Sc i a ha n M x y (M.lact b m) := by
  change M.lact (x.1 * (y.1 * b)) m = M.lact (x.1 * y.1) (M.lact b m)
  rw [← mul_assoc, M.lact_mul]
  rfl

/-- Balanced evaluation in the inner tensor factor. -/
def superCounitInner (x : (P).toSVec) : (tensor Q M).toSVec →ₗ[k] M.toSVec :=
  tensorLift (superCounitInnerBi D Sc i a ha n M x) (superCounitInner_balance D Sc i a ha n M x)

@[simp] theorem superCounitInner_btmul (x : (P).toSVec) (y : (Q).toSVec) (m : M.toSVec) :
    superCounitInner D Sc i a ha n M x (btmul Q M y m) = M.lact (x.1 * y.1) m :=
  tensorLift_btmul _ _ y m

/-- The bilinear outer evaluation. -/
def superCounitBi : (P).toSVec →ₗ[k] (tensor Q M).toSVec →ₗ[k] M.toSVec where
  toFun := superCounitInner D Sc i a ha n M
  map_add' x y := by
    apply tensor_hom_ext Q M
    intro z m
    change M.lact ((x.1 + y.1) * z.1) m = M.lact (x.1 * z.1) m + M.lact (y.1 * z.1) m
    rw [add_mul, map_add]
    rfl
  map_smul' c x := by
    apply tensor_hom_ext Q M
    intro y m
    change M.lact ((c • x.1) * y.1) m = c • M.lact (x.1 * y.1) m
    rw [smul_mul_assoc, map_smul]
    rfl

theorem superCounit_balance (x : (P).toSVec) (r : A) (z : (tensor Q M).toSVec) :
    superCounitBi D Sc i a ha n M ((P).ract r x) z =
      superCounitBi D Sc i a ha n M x ((tensor Q M).lact r z) := by
  refine tensor_induction_on (M := Q) (N := M) («P» := fun z =>
    superCounitBi D Sc i a ha n M ((P).ract r x) z =
      superCounitBi D Sc i a ha n M x ((tensor Q M).lact r z)) z ?_ ?_ ?_
  · simp only [map_zero]
  · intro y m
    change superCounitInner D Sc i a ha n M ((P).ract r x) (btmul Q M y m) =
      superCounitInner D Sc i a ha n M x ((tensor Q M).lact r (btmul Q M y m))
    rw [lact_btmul, superCounitInner_btmul, superCounitInner_btmul]
    change M.lact ((x.1 * φ r) * y.1) m = M.lact (x.1 * (φ r * y.1)) m
    rw [mul_assoc]
  · intro z w hz hw
    simp only [map_add, hz, hw]

/-- The actual linear counit on the doubly balanced tensor. -/
def superCounitLinear : (tensor P (tensor Q M)).toSVec →ₗ[k] M.toSVec :=
  tensorLift (superCounitBi D Sc i a ha n M) (superCounit_balance D Sc i a ha n M)

@[simp] theorem superCounitLinear_btmul (x : (P).toSVec) (z : (tensor Q M).toSVec) :
    superCounitLinear D Sc i a ha n M (btmul P (tensor Q M) x z) =
      superCounitInner D Sc i a ha n M x z := tensorLift_btmul _ _ x z

@[simp] theorem superCounitLinear_btmul_btmul (x : (P).toSVec) (y : (Q).toSVec) (m : M.toSVec) :
    superCounitLinear D Sc i a ha n M (btmul P (tensor Q M) x (btmul Q M y m)) =
      M.lact (x.1 * y.1) m := by rw [superCounitLinear_btmul, superCounitInner_btmul]

theorem superCounitInner_mem {p : ZMod 2} {x : (P).toSVec} (hx : x ∈ (P).toSVec.part p) :
    SVec.ofHom (superCounitInner D Sc i a ha n M x) ∈
      SVec.parityHom (tensor Q M).toSVec M.toSVec p := by
  apply tensor_mem_parity_of_btmul
  intro q r y m hy hm
  change M.lact (x.1 * y.1) m ∈ M.toSVec.part (q + r + p)
  have hxy := SetLike.GradedMul.mul_mem
    ((inductionCorner_mem_part_iff D Sc i a ha n).mp hx)
    ((restrictionCorner_mem_part_iff D Sc i a ha n).mp hy)
  simpa only [add_comm, add_left_comm, add_assoc] using
    SVec.apply_mem_part (M.lact_mem (p + q) (x.1 * y.1) hxy) hm

theorem superCounitLinear_mem :
    SVec.ofHom (superCounitLinear D Sc i a ha n M) ∈
      SVec.parityHom (tensor P (tensor Q M)).toSVec M.toSVec 0 := by
  apply tensor_mem_parity_of_btmul
  intro p q x z hx hz
  change (SVec.ofHom (superCounitInner D Sc i a ha n M x)) z ∈ M.toSVec.part (p + q + 0)
  simpa only [add_zero, add_comm] using
    SVec.apply_mem_part (superCounitInner_mem D Sc i a ha n M hx) hz

theorem superCounitLinear_lact (b : B) (t : (tensor P (tensor Q M)).toSVec) :
    superCounitLinear D Sc i a ha n M ((tensor P (tensor Q M)).lact b t) =
      M.lact b (superCounitLinear D Sc i a ha n M t) := by
  refine tensor_induction_on (M := P) (N := tensor Q M) («P» := fun t =>
    superCounitLinear D Sc i a ha n M ((tensor P (tensor Q M)).lact b t) =
      M.lact b (superCounitLinear D Sc i a ha n M t)) t ?_ ?_ ?_
  · simp only [map_zero]
  · intro x z
    refine tensor_induction_on (M := Q) (N := M) («P» := fun z =>
      superCounitLinear D Sc i a ha n M ((tensor P (tensor Q M)).lact b (btmul P (tensor Q M) x z)) =
        M.lact b (superCounitLinear D Sc i a ha n M (btmul P (tensor Q M) x z))) z ?_ ?_ ?_
    · simp only [btmul_zero_right, map_zero]
    · intro y m
      rw [lact_btmul, superCounitLinear_btmul_btmul, superCounitLinear_btmul_btmul]
      change M.lact ((b * x.1) * y.1) m = M.lact b (M.lact (x.1 * y.1) m)
      rw [mul_assoc, M.lact_mul]
      rfl
    · intro z w hz hw
      simp only [btmul_add_right, map_add, hz, hw]
  · intro z w hz hw
    simp only [map_add, hz, hw]

theorem superCounitLinear_ract (c : k) (t : (tensor P (tensor Q M)).toSVec) :
    superCounitLinear D Sc i a ha n M ((tensor P (tensor Q M)).ract c t) =
      M.ract c (superCounitLinear D Sc i a ha n M t) := by
  refine tensor_induction_on (M := P) (N := tensor Q M) («P» := fun t =>
    superCounitLinear D Sc i a ha n M ((tensor P (tensor Q M)).ract c t) =
      M.ract c (superCounitLinear D Sc i a ha n M t)) t ?_ ?_ ?_
  · simp only [map_zero]
  · intro x z
    refine tensor_induction_on (M := Q) (N := M) («P» := fun z =>
      superCounitLinear D Sc i a ha n M ((tensor P (tensor Q M)).ract c (btmul P (tensor Q M) x z)) =
        M.ract c (superCounitLinear D Sc i a ha n M (btmul P (tensor Q M) x z))) z ?_ ?_ ?_
    · simp only [btmul_zero_right, map_zero]
    · intro y m
      rw [ract_btmul, ract_btmul, superCounitLinear_btmul_btmul, superCounitLinear_btmul_btmul]
      exact (congrArg (fun f : M.toSVec ⟶ M.toSVec => f m) (M.lact_ract (x.1 * y.1) c)).symm
    · intro z w hz hw
      simp only [btmul_add_right, map_add, hz, hw]
  · intro z w hz hw
    simp only [map_add, hz, hw]

/-- The even component of the restriction-induction counit. -/
def superCounitComponent : tensor P (tensor Q M) ⟶ M :=
  ⟨SVec.ofHom (superCounitLinear D Sc i a ha n M), by
    apply (isHom_iff_of_mem (superCounitLinear_mem D Sc i a ha n M)).mpr
    constructor
    · intro p b _
      simp only [mul_zero, Supercategory.sign_zero, one_smul]
      apply SVec.hom_ext
      intro t
      exact superCounitLinear_lact D Sc i a ha n M b t
    · intro c
      apply SVec.hom_ext
      intro t
      exact superCounitLinear_ract D Sc i a ha n M c t⟩

/-- Signed naturality of evaluation for a homogeneous module map. -/
theorem superCounitComponent_naturality_of_mem
    {M N : CyclotomicSupermodules D Sc a ha (n + 1)} {s : ZMod 2} (f : M ⟶ N)
    (hf : f ∈ Supercategory.parity (R := k) M N s) :
    whiskerLeft P (whiskerLeft Q f) ≫ superCounitComponent D Sc i a ha n N =
      superCounitComponent D Sc i a ha n M ≫ f := by
  apply SuperBimodule.hom_ext
  apply tensor_hom_ext_homogeneous P (tensor Q M)
  intro p _ x z hx _
  change superCounitLinear D Sc i a ha n N
    ((whiskerLeft P (whiskerLeft Q f)).1 (btmul P (tensor Q M) x z)) =
      f.1 (superCounitLinear D Sc i a ha n M (btmul P (tensor Q M) x z))
  refine tensor_induction_on_homogeneous (M := Q) (N := M) («P» := fun z =>
    superCounitLinear D Sc i a ha n N
      ((whiskerLeft P (whiskerLeft Q f)).1 (btmul P (tensor Q M) x z)) =
        f.1 (superCounitLinear D Sc i a ha n M (btmul P (tensor Q M) x z))) z ?_ ?_ ?_
  · simp only [btmul_zero_right, map_zero]
  · intro q r y m hy _
    rw [whiskerLeft_btmul P _ (whiskerLeft_mem Q f hf) hx,
      whiskerLeft_btmul Q f hf hy, btmul_smul_right, map_smul, map_smul,
      superCounitLinear_btmul_btmul, superCounitLinear_btmul_btmul]
    have hxy := SetLike.GradedMul.mul_mem
      ((inductionCorner_mem_part_iff D Sc i a ha n).mp hx)
      ((restrictionCorner_mem_part_iff D Sc i a ha n).mp hy)
    have h := congrArg (fun g : M.toSVec ⟶ N.toSVec => g m)
      (((isHom_iff_of_mem (mem_parity_iff.mp hf)).mp f.2).1 (p + q) (x.1 * y.1) hxy)
    change f.1 (M.lact (x.1 * y.1) m) =
      Supercategory.sign k ((p + q) * s) • N.lact (x.1 * y.1) (f.1 m) at h
    rw [h, smul_smul, ← Supercategory.sign_add, ← add_mul]
  · intro z w hz hw
    simp only [btmul_add_right, map_add, hz, hw]

/-- The actual even counit as a natural transformation between superfunctors. -/
def cyclotomicSuperCounit :
    cyclotomicSuperRestriction D Sc i a ha n ⋙ cyclotomicSuperInduction D Sc i a ha n ⟶
      𝟭 (CyclotomicSupermodules D Sc a ha (n + 1)) where
  app M := superCounitComponent D Sc i a ha n M
  naturality {M N} f := by
    change whiskerLeft P (whiskerLeft Q f) ≫ superCounitComponent D Sc i a ha n N =
      superCounitComponent D Sc i a ha n M ≫ f
    refine Supercategory.induction_on (R := k) f ?_ ?_ ?_
    · simp only [whiskerLeft_zero, Limits.zero_comp, Limits.comp_zero]
    · intro p g hg
      exact superCounitComponent_naturality_of_mem D Sc i a ha n g hg
    · intro f g hf hg
      simp only [whiskerLeft_add, Preadditive.add_comp, Preadditive.comp_add, hf, hg]

end OddMath.QuiverHecke
end

end
