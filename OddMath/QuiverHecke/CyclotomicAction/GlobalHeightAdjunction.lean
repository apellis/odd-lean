/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.GlobalWeightRestriction
import OddMath.QuiverHecke.CyclotomicAction.SuperAdjunction

/-!
# The induction-restriction adjunction at every height

Supports the adjunction `globalE ⊣ globalF` of
`Categorification/KLR/CyclotomicAction/Global.lean`. The corner pairing, the
even unit and counit, and the triangle identities of `CornerPairing`,
`SuperAdjunctionUnit`, `SuperAdjunctionCounit` and `SuperAdjunction` use only
that the strand map is a unital, even, multiplicative map of graded algebras.
They are restated here for the strand maps `heightAppend` of the extended
tower, which include `vacuumAppend` from the empty word to one strand. At
positive height the bimodules, and hence all constructions here, are
definitionally the original ones (`heightInductionCorner_succ`,
`heightRestrictionCorner_succ`).
-/

noncomputable section
open CategoryTheory StringDiagrams
open SuperBimodule
namespace OddMath.QuiverHecke.CyclotomicAction
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
variable (i : I) (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a) (n : ℕ)

local notation "A" => heightAlgebra D Sc a n
local notation "B" => heightAlgebra D Sc a (n + 1)
local notation "GA" => heightParity D Sc a ha n
local notation "GB" => heightParity D Sc a ha (n + 1)
local notation "φ" => heightAppend D Sc a i n
local notation "P" => heightInductionCorner D Sc i a ha n
local notation "Q" => heightRestrictionCorner D Sc i a ha n

/-! ### From `CornerPairing` -/

/-- Homogeneity in the induction corner is inherited from the algebra. -/
theorem heightInductionCorner_mem_part_iff {p : ZMod 2} {x : (P).toSVec} :
    x ∈ (P).toSVec.part p ↔ x.1 ∈ GB p := by
  change x ∈ (SVec.sub _ _ _).part p ↔ _
  rw [SVec.mem_sub_part_iff, mem_regularSVec_part_iff]

/-- Homogeneity in the restriction corner is inherited from the algebra. -/
theorem heightRestrictionCorner_mem_part_iff {p : ZMod 2} {x : (Q).toSVec} :
    x ∈ (Q).toSVec.part p ↔ x.1 ∈ GB p := by
  change x ∈ (SVec.sub _ _ _).part p ↔ _
  rw [SVec.mem_sub_part_iff, mem_regularSVec_part_iff]

/-- Multiplication of an induction element with a restriction element. -/
def heightCornerPairingBi : (P).toSVec →ₗ[k] (Q).toSVec →ₗ[k] B where
  toFun x :=
    { toFun := fun y => x.1 * y.1
      map_add' := fun y z => mul_add x.1 y.1 z.1
      map_smul' := fun c y => mul_smul_comm c x.1 y.1 }
  map_add' x y := by ext z; exact add_mul x.1 y.1 z.1
  map_smul' c x := by ext y; exact smul_mul_assoc c x.1 y.1

/-- The pairing descends through balancing over the lower cyclotomic algebra. -/
def heightCornerPairingLinear : (tensor P Q).toSVec →ₗ[k] B :=
  tensorLift (heightCornerPairingBi D Sc i a ha n) (fun x r y => mul_assoc x.1 (φ r) y.1)

@[simp] theorem heightCornerPairingLinear_btmul (x : (P).toSVec) (y : (Q).toSVec) :
    heightCornerPairingLinear D Sc i a ha n (btmul P Q x y) = x.1 * y.1 :=
  tensorLift_btmul _ _ x y

/-- Multiplication preserves total parity. -/
theorem heightCornerPairing_mem :
    SVec.ofHom (heightCornerPairingLinear D Sc i a ha n) ∈
      SVec.parityHom (tensor P Q).toSVec (regular GB).toSVec 0 := by
  apply tensor_mem_parity_of_btmul
  intro p q x y hx hy
  change heightCornerPairingLinear D Sc i a ha n (btmul P Q x y) ∈ (regularSVec GB).part (p + q + 0)
  rw [heightCornerPairingLinear_btmul, add_zero, mem_regularSVec_part_iff]
  exact SetLike.GradedMul.mul_mem
    ((heightInductionCorner_mem_part_iff D Sc i a ha n).mp hx)
    ((heightRestrictionCorner_mem_part_iff D Sc i a ha n).mp hy)

/-- The even evaluation `B e ⊗_A e B → B`. -/
def heightCornerEvaluation : tensor P Q ⟶ regular GB :=
  ⟨SVec.ofHom (heightCornerPairingLinear D Sc i a ha n), by
    apply (isHom_iff_of_mem (heightCornerPairing_mem D Sc i a ha n)).mpr
    constructor
    · intro p b _
      simp only [mul_zero, Supercategory.sign_zero, one_smul]
      apply tensor_hom_ext P Q
      intro x y
      change heightCornerPairingLinear D Sc i a ha n ((tensor P Q).lact b (btmul P Q x y)) =
        b * heightCornerPairingLinear D Sc i a ha n (btmul P Q x y)
      rw [lact_btmul, heightCornerPairingLinear_btmul, heightCornerPairingLinear_btmul]
      exact mul_assoc b x.1 y.1
    · intro b
      apply tensor_hom_ext P Q
      intro x y
      change heightCornerPairingLinear D Sc i a ha n ((tensor P Q).ract b (btmul P Q x y)) =
        heightCornerPairingLinear D Sc i a ha n (btmul P Q x y) * b
      rw [ract_btmul, heightCornerPairingLinear_btmul, heightCornerPairingLinear_btmul]
      exact (mul_assoc x.1 y.1 b).symm⟩

theorem heightCornerEvaluation_mem :
    heightCornerEvaluation D Sc i a ha n ∈ Supercategory.parity (R := k) _ _ 0 :=
  (mem_parity_iff).mpr (heightCornerPairing_mem D Sc i a ha n)

/-- The even colour-cut idempotent in the induction bimodule. -/
def heightInductionCornerIdempotent : (P).toSVec :=
  ⟨φ 1, by change φ 1 * φ 1 = φ 1; rw [← map_mul, mul_one]⟩

/-- The lower algebra maps into the restriction bimodule. -/
def heightRestrictionCornerOf : A →ₗ[k] (Q).toSVec where
  toFun r := ⟨φ r, by change φ 1 * φ r = φ r; rw [← map_mul, one_mul]⟩
  map_add' r s := Subtype.ext (map_add φ r s)
  map_smul' c r := Subtype.ext (map_smul φ c r)

theorem heightInductionCornerIdempotent_mem :
    heightInductionCornerIdempotent D Sc i a ha n ∈ (P).toSVec.part 0 :=
  (heightInductionCorner_mem_part_iff D Sc i a ha n).mpr
    (heightAppend_parity D Sc a ha i n (SetLike.one_mem_graded GA))

/-- The linear coevaluation `a ↦ φ(a) ⊗ e`. -/
def heightCornerUnitLinear : A →ₗ[k] (tensor Q P).toSVec where
  toFun r := btmul Q P (heightRestrictionCornerOf D Sc i a ha n r)
    (heightInductionCornerIdempotent D Sc i a ha n)
  map_add' r s := by rw [map_add, btmul_add_left]
  map_smul' c r := by rw [map_smul, btmul_smul_left]; rfl

@[simp] theorem heightCornerUnitLinear_apply (r : A) :
    heightCornerUnitLinear D Sc i a ha n r = btmul Q P (heightRestrictionCornerOf D Sc i a ha n r)
      (heightInductionCornerIdempotent D Sc i a ha n) := rfl

theorem heightCornerUnitLinear_lact (r s : A) :
    heightCornerUnitLinear D Sc i a ha n (r * s) =
      (tensor Q P).lact r (heightCornerUnitLinear D Sc i a ha n s) := by
  rw [heightCornerUnitLinear_apply, heightCornerUnitLinear_apply, lact_btmul]
  congr 1
  apply Subtype.ext
  exact map_mul φ r s

theorem heightCornerUnitLinear_ract (r s : A) :
    heightCornerUnitLinear D Sc i a ha n (r * s) =
      (tensor Q P).ract s (heightCornerUnitLinear D Sc i a ha n r) := by
  rw [heightCornerUnitLinear_apply, heightCornerUnitLinear_apply, ract_btmul]
  have hm : heightRestrictionCornerOf D Sc i a ha n (r * s) =
      (Q).ract (φ s) (heightRestrictionCornerOf D Sc i a ha n r) :=
    Subtype.ext (map_mul φ r s)
  rw [hm, btmul_ract_lact]
  congr 1
  apply Subtype.ext
  change φ s * φ 1 = φ 1 * φ s
  rw [← map_mul, ← map_mul, mul_one, one_mul]

theorem heightCornerUnit_mem :
    SVec.ofHom (heightCornerUnitLinear D Sc i a ha n) ∈
      SVec.parityHom (regular GA).toSVec (tensor Q P).toSVec 0 := by
  apply SVec.mem_parityHom_of_apply_mem
  intro p r hr
  apply btmul_mem_part
  · apply (heightRestrictionCorner_mem_part_iff D Sc i a ha n).mpr
    exact heightAppend_parity D Sc a ha i n ((mem_regularSVec_part_iff GA).mp hr)
  · exact heightInductionCornerIdempotent_mem D Sc i a ha n

/-- The even coevaluation `A → e B ⊗_B B e`. -/
def heightCornerCoevaluation : regular GA ⟶ tensor Q P :=
  ⟨SVec.ofHom (heightCornerUnitLinear D Sc i a ha n), by
    apply (isHom_iff_of_mem (heightCornerUnit_mem D Sc i a ha n)).mpr
    constructor
    · intro p r _
      simp only [mul_zero, Supercategory.sign_zero, one_smul]
      apply SVec.hom_ext
      intro s
      exact heightCornerUnitLinear_lact D Sc i a ha n r s
    · intro r
      apply SVec.hom_ext
      intro s
      exact heightCornerUnitLinear_ract D Sc i a ha n s r⟩

theorem heightCornerCoevaluation_mem :
    heightCornerCoevaluation D Sc i a ha n ∈ Supercategory.parity (R := k) _ _ 0 :=
  (mem_parity_iff).mpr (heightCornerUnit_mem D Sc i a ha n)

/-- The first elementary triangular identity for the corner pairing. -/
@[simp] theorem heightCornerPairing_right_unit (x : (P).toSVec) :
    heightCornerPairingLinear D Sc i a ha n
      (btmul P Q x (heightRestrictionCornerOf D Sc i a ha n 1)) = x.1 := by
  rw [heightCornerPairingLinear_btmul]
  exact x.2

/-- The second elementary triangular identity for the corner pairing. -/
@[simp] theorem heightCornerPairing_left_unit (y : (Q).toSVec) :
    heightCornerPairingLinear D Sc i a ha n
      (btmul P Q (heightInductionCornerIdempotent D Sc i a ha n) y) = y.1 := by
  rw [heightCornerPairingLinear_btmul]
  exact y.2


/-! ### From `SuperAdjunctionUnit` -/
local notation "ep" => heightInductionCornerIdempotent D Sc i a ha n
local notation "eq" => heightRestrictionCornerOf D Sc i a ha n 1
local notation "F" => heightSuperInduction D Sc i a ha n
local notation "E" => heightSuperRestriction D Sc i a ha n

/-- The two even colour idempotents give the linear unit. -/
def heightSuperUnitLinear (M : HeightModules D Sc a ha n) :
    M.toSVec →ₗ[k] (tensor Q (tensor P M)).toSVec where
  toFun m := btmul Q (tensor P M) eq (btmul P M ep m)
  map_add' x y := by rw [btmul_add_right, btmul_add_right]
  map_smul' c x := by rw [btmul_smul_right, btmul_smul_right]; rfl

@[simp] theorem heightSuperUnitLinear_apply (M : HeightModules D Sc a ha n) (m : M.toSVec) :
    heightSuperUnitLinear D Sc i a ha n M m = btmul Q (tensor P M) eq (btmul P M ep m) := rfl

theorem heightRestrictionCornerOf_one_mem : eq ∈ (Q).toSVec.part 0 :=
  (heightRestrictionCorner_mem_part_iff D Sc i a ha n).mpr
    (heightAppend_parity D Sc a ha i n (SetLike.one_mem_graded _))

theorem heightSuperUnitLinear_mem (M : HeightModules D Sc a ha n) :
    SVec.ofHom (heightSuperUnitLinear D Sc i a ha n M) ∈
      SVec.parityHom M.toSVec (tensor Q (tensor P M)).toSVec 0 := by
  apply SVec.mem_parityHom_of_apply_mem
  intro p m hm
  change btmul Q (tensor P M) eq (btmul P M ep m) ∈
    (tensor Q (tensor P M)).toSVec.part (p + 0)
  simpa only [zero_add, add_zero] using
    btmul_mem_part Q (tensor P M) (heightRestrictionCornerOf_one_mem D Sc i a ha n)
      (btmul_mem_part P M (heightInductionCornerIdempotent_mem D Sc i a ha n) hm)

theorem heightSuperUnitLinear_lact (M : HeightModules D Sc a ha n) (r : A) (m : M.toSVec) :
    heightSuperUnitLinear D Sc i a ha n M (M.lact r m) =
      (tensor Q (tensor P M)).lact r (heightSuperUnitLinear D Sc i a ha n M m) := by
  rw [heightSuperUnitLinear_apply, heightSuperUnitLinear_apply, lact_btmul, ← btmul_ract_lact]
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
def heightSuperUnitComponent (M : HeightModules D Sc a ha n) : M ⟶ tensor Q (tensor P M) :=
  ⟨SVec.ofHom (heightSuperUnitLinear D Sc i a ha n M), by
    apply (isHom_iff_of_mem (heightSuperUnitLinear_mem D Sc i a ha n M)).mpr
    constructor
    · intro p r _
      simp only [mul_zero, Supercategory.sign_zero, one_smul]
      apply SVec.hom_ext
      intro m
      exact heightSuperUnitLinear_lact D Sc i a ha n M r m
    · intro c
      apply SVec.hom_ext
      intro m
      rfl⟩

theorem heightSuperUnitComponent_mem (M : HeightModules D Sc a ha n) :
    heightSuperUnitComponent D Sc i a ha n M ∈ Supercategory.parity (R := k) _ _ 0 :=
  mem_parity_iff.mpr (heightSuperUnitLinear_mem D Sc i a ha n M)

/-- Naturality includes homogeneous odd module maps. -/
theorem heightSuperUnitComponent_naturality_of_mem
    {M N : HeightModules D Sc a ha n} {p : ZMod 2} (f : M ⟶ N)
    (hf : f ∈ Supercategory.parity (R := k) M N p) :
    f ≫ heightSuperUnitComponent D Sc i a ha n N =
      heightSuperUnitComponent D Sc i a ha n M ≫ whiskerLeft Q (whiskerLeft P f) := by
  apply SuperBimodule.hom_ext
  apply SVec.hom_ext
  intro m
  change heightSuperUnitLinear D Sc i a ha n N (f.1 m) =
    (whiskerLeft Q (whiskerLeft P f)).1 (heightSuperUnitLinear D Sc i a ha n M m)
  rw [heightSuperUnitLinear_apply, heightSuperUnitLinear_apply,
    whiskerLeft_btmul Q _ (whiskerLeft_mem P f hf) (heightRestrictionCornerOf_one_mem D Sc i a ha n),
    whiskerLeft_btmul P f hf (heightInductionCornerIdempotent_mem D Sc i a ha n)]
  simp only [zero_mul, Supercategory.sign_zero, one_smul]

/-- The actual even unit as a natural transformation between superfunctors. -/
def heightSuperUnit : 𝟭 (HeightModules D Sc a ha n) ⟶
    heightSuperInduction D Sc i a ha n ⋙ heightSuperRestriction D Sc i a ha n where
  app M := heightSuperUnitComponent D Sc i a ha n M
  naturality {M N} f := by
    change f ≫ heightSuperUnitComponent D Sc i a ha n N =
      heightSuperUnitComponent D Sc i a ha n M ≫ whiskerLeft Q (whiskerLeft P f)
    refine Supercategory.induction_on (R := k) f ?_ ?_ ?_
    · simp only [whiskerLeft_zero, Limits.zero_comp, Limits.comp_zero]
    · intro p g hg
      exact heightSuperUnitComponent_naturality_of_mem D Sc i a ha n g hg
    · intro f g hf hg
      simp only [whiskerLeft_add, Preadditive.add_comp, Preadditive.comp_add, hf, hg]


/-! ### From `SuperAdjunctionCounit` -/
section Counit
variable (M : HeightModules D Sc a ha (n + 1))

/-- The inner bilinear action of a fixed induction element. -/
def heightSuperCounitInnerBi (x : (P).toSVec) :
    (Q).toSVec →ₗ[k] M.toSVec →ₗ[k] M.toSVec :=
  M.lact.comp (heightCornerPairingBi D Sc i a ha n x)

theorem heightSuperCounitInner_balance (x : (P).toSVec) (y : (Q).toSVec) (b : B) (m : M.toSVec) :
    heightSuperCounitInnerBi D Sc i a ha n M x ((Q).ract b y) m =
      heightSuperCounitInnerBi D Sc i a ha n M x y (M.lact b m) := by
  change M.lact (x.1 * (y.1 * b)) m = M.lact (x.1 * y.1) (M.lact b m)
  rw [← mul_assoc, M.lact_mul]
  rfl

/-- Balanced evaluation in the inner tensor factor. -/
def heightSuperCounitInner (x : (P).toSVec) : (tensor Q M).toSVec →ₗ[k] M.toSVec :=
  tensorLift (heightSuperCounitInnerBi D Sc i a ha n M x) (heightSuperCounitInner_balance D Sc i a ha n M x)

@[simp] theorem heightSuperCounitInner_btmul (x : (P).toSVec) (y : (Q).toSVec) (m : M.toSVec) :
    heightSuperCounitInner D Sc i a ha n M x (btmul Q M y m) = M.lact (x.1 * y.1) m :=
  tensorLift_btmul _ _ y m

/-- The bilinear outer evaluation. -/
def heightSuperCounitBi : (P).toSVec →ₗ[k] (tensor Q M).toSVec →ₗ[k] M.toSVec where
  toFun := heightSuperCounitInner D Sc i a ha n M
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

theorem heightSuperCounit_balance (x : (P).toSVec) (r : A) (z : (tensor Q M).toSVec) :
    heightSuperCounitBi D Sc i a ha n M ((P).ract r x) z =
      heightSuperCounitBi D Sc i a ha n M x ((tensor Q M).lact r z) := by
  refine tensor_induction_on (M := Q) (N := M) («P» := fun z =>
    heightSuperCounitBi D Sc i a ha n M ((P).ract r x) z =
      heightSuperCounitBi D Sc i a ha n M x ((tensor Q M).lact r z)) z ?_ ?_ ?_
  · simp only [map_zero]
  · intro y m
    change heightSuperCounitInner D Sc i a ha n M ((P).ract r x) (btmul Q M y m) =
      heightSuperCounitInner D Sc i a ha n M x ((tensor Q M).lact r (btmul Q M y m))
    rw [lact_btmul, heightSuperCounitInner_btmul, heightSuperCounitInner_btmul]
    change M.lact ((x.1 * φ r) * y.1) m = M.lact (x.1 * (φ r * y.1)) m
    rw [mul_assoc]
  · intro z w hz hw
    simp only [map_add, hz, hw]

/-- The actual linear counit on the doubly balanced tensor. -/
def heightSuperCounitLinear : (tensor P (tensor Q M)).toSVec →ₗ[k] M.toSVec :=
  tensorLift (heightSuperCounitBi D Sc i a ha n M) (heightSuperCounit_balance D Sc i a ha n M)

@[simp] theorem heightSuperCounitLinear_btmul (x : (P).toSVec) (z : (tensor Q M).toSVec) :
    heightSuperCounitLinear D Sc i a ha n M (btmul P (tensor Q M) x z) =
      heightSuperCounitInner D Sc i a ha n M x z := tensorLift_btmul _ _ x z

@[simp] theorem heightSuperCounitLinear_btmul_btmul (x : (P).toSVec) (y : (Q).toSVec) (m : M.toSVec) :
    heightSuperCounitLinear D Sc i a ha n M (btmul P (tensor Q M) x (btmul Q M y m)) =
      M.lact (x.1 * y.1) m := by rw [heightSuperCounitLinear_btmul, heightSuperCounitInner_btmul]

theorem heightSuperCounitInner_mem {p : ZMod 2} {x : (P).toSVec} (hx : x ∈ (P).toSVec.part p) :
    SVec.ofHom (heightSuperCounitInner D Sc i a ha n M x) ∈
      SVec.parityHom (tensor Q M).toSVec M.toSVec p := by
  apply tensor_mem_parity_of_btmul
  intro q r y m hy hm
  change M.lact (x.1 * y.1) m ∈ M.toSVec.part (q + r + p)
  have hxy := SetLike.GradedMul.mul_mem
    ((heightInductionCorner_mem_part_iff D Sc i a ha n).mp hx)
    ((heightRestrictionCorner_mem_part_iff D Sc i a ha n).mp hy)
  simpa only [add_comm, add_left_comm, add_assoc] using
    SVec.apply_mem_part (M.lact_mem (p + q) (x.1 * y.1) hxy) hm

theorem heightSuperCounitLinear_mem :
    SVec.ofHom (heightSuperCounitLinear D Sc i a ha n M) ∈
      SVec.parityHom (tensor P (tensor Q M)).toSVec M.toSVec 0 := by
  apply tensor_mem_parity_of_btmul
  intro p q x z hx hz
  change (SVec.ofHom (heightSuperCounitInner D Sc i a ha n M x)) z ∈ M.toSVec.part (p + q + 0)
  simpa only [add_zero, add_comm] using
    SVec.apply_mem_part (heightSuperCounitInner_mem D Sc i a ha n M hx) hz

theorem heightSuperCounitLinear_lact (b : B) (t : (tensor P (tensor Q M)).toSVec) :
    heightSuperCounitLinear D Sc i a ha n M ((tensor P (tensor Q M)).lact b t) =
      M.lact b (heightSuperCounitLinear D Sc i a ha n M t) := by
  refine tensor_induction_on (M := P) (N := tensor Q M) («P» := fun t =>
    heightSuperCounitLinear D Sc i a ha n M ((tensor P (tensor Q M)).lact b t) =
      M.lact b (heightSuperCounitLinear D Sc i a ha n M t)) t ?_ ?_ ?_
  · simp only [map_zero]
  · intro x z
    refine tensor_induction_on (M := Q) (N := M) («P» := fun z =>
      heightSuperCounitLinear D Sc i a ha n M ((tensor P (tensor Q M)).lact b (btmul P (tensor Q M) x z)) =
        M.lact b (heightSuperCounitLinear D Sc i a ha n M (btmul P (tensor Q M) x z))) z ?_ ?_ ?_
    · simp only [btmul_zero_right, map_zero]
    · intro y m
      rw [lact_btmul, heightSuperCounitLinear_btmul_btmul, heightSuperCounitLinear_btmul_btmul]
      change M.lact ((b * x.1) * y.1) m = M.lact b (M.lact (x.1 * y.1) m)
      rw [mul_assoc, M.lact_mul]
      rfl
    · intro z w hz hw
      simp only [btmul_add_right, map_add, hz, hw]
  · intro z w hz hw
    simp only [map_add, hz, hw]

theorem heightSuperCounitLinear_ract (c : k) (t : (tensor P (tensor Q M)).toSVec) :
    heightSuperCounitLinear D Sc i a ha n M ((tensor P (tensor Q M)).ract c t) =
      M.ract c (heightSuperCounitLinear D Sc i a ha n M t) := by
  refine tensor_induction_on (M := P) (N := tensor Q M) («P» := fun t =>
    heightSuperCounitLinear D Sc i a ha n M ((tensor P (tensor Q M)).ract c t) =
      M.ract c (heightSuperCounitLinear D Sc i a ha n M t)) t ?_ ?_ ?_
  · simp only [map_zero]
  · intro x z
    refine tensor_induction_on (M := Q) (N := M) («P» := fun z =>
      heightSuperCounitLinear D Sc i a ha n M ((tensor P (tensor Q M)).ract c (btmul P (tensor Q M) x z)) =
        M.ract c (heightSuperCounitLinear D Sc i a ha n M (btmul P (tensor Q M) x z))) z ?_ ?_ ?_
    · simp only [btmul_zero_right, map_zero]
    · intro y m
      rw [ract_btmul, ract_btmul, heightSuperCounitLinear_btmul_btmul, heightSuperCounitLinear_btmul_btmul]
      exact (congrArg (fun f : M.toSVec ⟶ M.toSVec => f m) (M.lact_ract (x.1 * y.1) c)).symm
    · intro z w hz hw
      simp only [btmul_add_right, map_add, hz, hw]
  · intro z w hz hw
    simp only [map_add, hz, hw]

/-- The even component of the restriction-induction counit. -/
def heightSuperCounitComponent : tensor P (tensor Q M) ⟶ M :=
  ⟨SVec.ofHom (heightSuperCounitLinear D Sc i a ha n M), by
    apply (isHom_iff_of_mem (heightSuperCounitLinear_mem D Sc i a ha n M)).mpr
    constructor
    · intro p b _
      simp only [mul_zero, Supercategory.sign_zero, one_smul]
      apply SVec.hom_ext
      intro t
      exact heightSuperCounitLinear_lact D Sc i a ha n M b t
    · intro c
      apply SVec.hom_ext
      intro t
      exact heightSuperCounitLinear_ract D Sc i a ha n M c t⟩

theorem heightSuperCounitComponent_mem :
    heightSuperCounitComponent D Sc i a ha n M ∈ Supercategory.parity (R := k) _ _ 0 :=
  mem_parity_iff.mpr (heightSuperCounitLinear_mem D Sc i a ha n M)

/-- Signed naturality of evaluation for a homogeneous module map. -/
theorem heightSuperCounitComponent_naturality_of_mem
    {M N : HeightModules D Sc a ha (n + 1)} {s : ZMod 2} (f : M ⟶ N)
    (hf : f ∈ Supercategory.parity (R := k) M N s) :
    whiskerLeft P (whiskerLeft Q f) ≫ heightSuperCounitComponent D Sc i a ha n N =
      heightSuperCounitComponent D Sc i a ha n M ≫ f := by
  apply SuperBimodule.hom_ext
  apply tensor_hom_ext_homogeneous P (tensor Q M)
  intro p _ x z hx _
  change heightSuperCounitLinear D Sc i a ha n N
    ((whiskerLeft P (whiskerLeft Q f)).1 (btmul P (tensor Q M) x z)) =
      f.1 (heightSuperCounitLinear D Sc i a ha n M (btmul P (tensor Q M) x z))
  refine tensor_induction_on_homogeneous (M := Q) (N := M) («P» := fun z =>
    heightSuperCounitLinear D Sc i a ha n N
      ((whiskerLeft P (whiskerLeft Q f)).1 (btmul P (tensor Q M) x z)) =
        f.1 (heightSuperCounitLinear D Sc i a ha n M (btmul P (tensor Q M) x z))) z ?_ ?_ ?_
  · simp only [btmul_zero_right, map_zero]
  · intro q r y m hy _
    rw [whiskerLeft_btmul P _ (whiskerLeft_mem Q f hf) hx,
      whiskerLeft_btmul Q f hf hy, btmul_smul_right, map_smul, map_smul,
      heightSuperCounitLinear_btmul_btmul, heightSuperCounitLinear_btmul_btmul]
    have hxy := SetLike.GradedMul.mul_mem
      ((heightInductionCorner_mem_part_iff D Sc i a ha n).mp hx)
      ((heightRestrictionCorner_mem_part_iff D Sc i a ha n).mp hy)
    have h := congrArg (fun g : M.toSVec ⟶ N.toSVec => g m)
      (((isHom_iff_of_mem (mem_parity_iff.mp hf)).mp f.2).1 (p + q) (x.1 * y.1) hxy)
    change f.1 (M.lact (x.1 * y.1) m) =
      Supercategory.sign k ((p + q) * s) • N.lact (x.1 * y.1) (f.1 m) at h
    rw [h, smul_smul, ← Supercategory.sign_add, ← add_mul]
  · intro z w hz hw
    simp only [btmul_add_right, map_add, hz, hw]

/-- The actual even counit as a natural transformation between superfunctors. -/
def heightSuperCounit :
    heightSuperRestriction D Sc i a ha n ⋙ heightSuperInduction D Sc i a ha n ⟶
      𝟭 (HeightModules D Sc a ha (n + 1)) where
  app M := heightSuperCounitComponent D Sc i a ha n M
  naturality {M N} f := by
    change whiskerLeft P (whiskerLeft Q f) ≫ heightSuperCounitComponent D Sc i a ha n N =
      heightSuperCounitComponent D Sc i a ha n M ≫ f
    refine Supercategory.induction_on (R := k) f ?_ ?_ ?_
    · simp only [whiskerLeft_zero, Limits.zero_comp, Limits.comp_zero]
    · intro p g hg
      exact heightSuperCounitComponent_naturality_of_mem D Sc i a ha n g hg
    · intro f g hf hg
      simp only [whiskerLeft_add, Preadditive.add_comp, Preadditive.comp_add, hf, hg]

end Counit


/-! ### From `SuperAdjunction` -/

theorem heightSuperInduction_triangle (M : HeightModules D Sc a ha n) :
    (F).map ((heightSuperUnit D Sc i a ha n).app M) ≫
      (heightSuperCounit D Sc i a ha n).app ((F).obj M) = 𝟙 ((F).obj M) := by
  apply SuperBimodule.hom_ext
  apply tensor_hom_ext P M
  intro x m
  change heightSuperCounitLinear D Sc i a ha n (tensor P M)
    ((whiskerLeft P (heightSuperUnitComponent D Sc i a ha n M)).1 (btmul P M x m)) = btmul P M x m
  rw [whiskerLeft_btmul_even P _ (heightSuperUnitComponent_mem D Sc i a ha n M)]
  change heightSuperCounitLinear D Sc i a ha n (tensor P M)
    (btmul P (tensor Q (tensor P M)) x
      (btmul Q (tensor P M) (heightRestrictionCornerOf D Sc i a ha n 1)
        (btmul P M (heightInductionCornerIdempotent D Sc i a ha n) m))) = btmul P M x m
  rw [heightSuperCounitLinear_btmul_btmul, lact_btmul]
  congr 1
  apply Subtype.ext
  change (x.1 * φ 1) * φ 1 = x.1
  rw [x.2, x.2]

theorem heightSuperRestriction_triangle (M : HeightModules D Sc a ha (n + 1)) :
    (heightSuperUnit D Sc i a ha n).app ((E).obj M) ≫
      (E).map ((heightSuperCounit D Sc i a ha n).app M) = 𝟙 ((E).obj M) := by
  apply SuperBimodule.hom_ext
  apply tensor_hom_ext Q M
  intro y m
  change (whiskerLeft Q (heightSuperCounitComponent D Sc i a ha n M)).1
    (heightSuperUnitLinear D Sc i a ha n (tensor Q M) (btmul Q M y m)) = btmul Q M y m
  rw [heightSuperUnitLinear_apply,
    whiskerLeft_btmul_even Q _ (heightSuperCounitComponent_mem D Sc i a ha n M)]
  change btmul Q M (heightRestrictionCornerOf D Sc i a ha n 1)
    (heightSuperCounitLinear D Sc i a ha n M
      (btmul P (tensor Q M) (heightInductionCornerIdempotent D Sc i a ha n) (btmul Q M y m))) =
    btmul Q M y m
  rw [heightSuperCounitLinear_btmul_btmul]
  change btmul Q M (heightRestrictionCornerOf D Sc i a ha n 1) (M.lact (φ 1 * y.1) m) = btmul Q M y m
  rw [y.2, ← btmul_ract_lact]
  congr 1
  apply Subtype.ext
  exact y.2

/-- Induction is left adjoint to restriction on the actual supermodule categories. -/
def heightSuperIndResAdjunction : F ⊣ E where
  unit := heightSuperUnit D Sc i a ha n
  counit := heightSuperCounit D Sc i a ha n
  left_triangle_components := heightSuperInduction_triangle D Sc i a ha n
  right_triangle_components := heightSuperRestriction_triangle D Sc i a ha n

/-- The adjunction bijection preserves the parity of a homogeneous morphism. -/
theorem heightSuperAdjunction_homEquiv_mem
    {M : HeightModules D Sc a ha n}
    {N : HeightModules D Sc a ha (n + 1)} {p : ZMod 2}
    {f : (F).obj M ⟶ N} (hf : f ∈ Supercategory.parity (R := k) _ _ p) :
    (heightSuperIndResAdjunction D Sc i a ha n).homEquiv M N f ∈
      Supercategory.parity (R := k) _ _ p := by
  rw [Adjunction.homEquiv_unit]
  change heightSuperUnitComponent D Sc i a ha n M ≫ whiskerLeft Q f ∈
    Supercategory.parity (R := k) _ _ p
  simpa only [zero_add] using Supercategory.comp_mem
    (heightSuperUnitComponent_mem D Sc i a ha n M) (whiskerLeft_mem Q f hf)

/-- The inverse adjunction bijection also preserves parity. -/
theorem heightSuperAdjunction_homEquiv_symm_mem
    {M : HeightModules D Sc a ha n}
    {N : HeightModules D Sc a ha (n + 1)} {p : ZMod 2}
    {f : M ⟶ (E).obj N} (hf : f ∈ Supercategory.parity (R := k) _ _ p) :
    ((heightSuperIndResAdjunction D Sc i a ha n).homEquiv M N).symm f ∈
      Supercategory.parity (R := k) _ _ p := by
  rw [Adjunction.homEquiv_counit]
  change whiskerLeft P f ≫ heightSuperCounitComponent D Sc i a ha n N ∈
    Supercategory.parity (R := k) _ _ p
  simpa only [add_zero] using Supercategory.comp_mem
    (whiskerLeft_mem P f hf) (heightSuperCounitComponent_mem D Sc i a ha n N)

/-! ### Content blocks at every height -/

section Content
variable (β : Multiset I) (hβ : β.card = n)

/-- The even unit at every height, restricted to content blocks. -/
def heightContentUnit : 𝟭 (ObjectProperty.FullSubcategory (heightContentSupported D Sc a ha n β)) ⟶
    (heightContentInduction D Sc i a ha n β).toFunctor ⋙
      (heightContentRestriction D Sc i a ha n β hβ).toFunctor where
  app M := ⟨(heightSuperUnit D Sc i a ha n).app M.obj⟩
  naturality _ _ f := InducedCategory.hom_ext ((heightSuperUnit D Sc i a ha n).naturality f.hom)

/-- The even counit at every height, restricted to content blocks. -/
def heightContentCounit : (heightContentRestriction D Sc i a ha n β hβ).toFunctor ⋙
    (heightContentInduction D Sc i a ha n β).toFunctor ⟶
      𝟭 (ObjectProperty.FullSubcategory
        (heightContentSupported D Sc a ha (n + 1) (({i} : Multiset I) + β))) where
  app M := ⟨(heightSuperCounit D Sc i a ha n).app M.obj⟩
  naturality _ _ f :=
    InducedCategory.hom_ext ((heightSuperCounit D Sc i a ha n).naturality f.hom)

/-- Induction is left adjoint to restriction on content blocks at every height, including
from the empty word to one strand. -/
def heightContentAdjunction :
    (heightContentInduction D Sc i a ha n β).toFunctor ⊣
      (heightContentRestriction D Sc i a ha n β hβ).toFunctor where
  unit := heightContentUnit D Sc i a ha n β hβ
  counit := heightContentCounit D Sc i a ha n β hβ
  left_triangle_components M :=
    InducedCategory.hom_ext (heightSuperInduction_triangle D Sc i a ha n M.obj)
  right_triangle_components M :=
    InducedCategory.hom_ext (heightSuperRestriction_triangle D Sc i a ha n M.obj)

theorem heightContentUnit_mem
    (M : ObjectProperty.FullSubcategory (heightContentSupported D Sc a ha n β)) :
    (heightContentUnit D Sc i a ha n β hβ).app M ∈ Supercategory.parity (R := k) _ _ 0 :=
  heightSuperUnitComponent_mem D Sc i a ha n M.obj

theorem heightContentCounit_mem (M : ObjectProperty.FullSubcategory
    (heightContentSupported D Sc a ha (n + 1) (({i} : Multiset I) + β))) :
    (heightContentCounit D Sc i a ha n β hβ).app M ∈ Supercategory.parity (R := k) _ _ 0 :=
  heightSuperCounitComponent_mem D Sc i a ha n M.obj

end Content

/-- The identity transports along equal heights and contents are mutually adjoint. -/
def heightContentCastAdjunction {m m' : ℕ} {γ γ' : Multiset I} (hm : m = m') (hγ : γ = γ') :
    (heightContentCast D Sc a ha hm hγ).toFunctor ⊣
      (heightContentCast D Sc a ha hm.symm hγ.symm).toFunctor := by
  subst hm
  subst hγ
  exact Adjunction.id

/-- **Induction is left adjoint to restriction** between global content categories,
`δ = {i} + β`, including from the empty content. -/
def globalContentAdjunction {β δ : Multiset I} (h : {i} + β = δ) :
    (globalContentInduction D Sc i a ha h).toFunctor ⊣
      (globalContentRestriction D Sc i a ha h).toFunctor :=
  (heightContentAdjunction D Sc i a ha β.card β rfl).comp
    (heightContentCastAdjunction D Sc a ha (card_of_add i h) h)

end OddMath.QuiverHecke.CyclotomicAction
