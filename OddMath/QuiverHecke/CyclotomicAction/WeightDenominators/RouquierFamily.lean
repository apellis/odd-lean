import StringDiagrams.Super.PiTwo
import OddMath.QuiverHecke.CyclotomicAction.WeightTripleBraid.WeightAbsentCapInverse
import OddMath.QuiverHecke.SwappedAssembly.Generators.CrossCoeffExpansion
import OddMath.QuiverHecke.SwappedAssembly.ProductDenominatorUnits
import OddMath.QuiverHecke.SwappedAssembly.Sigma.TransposeNorms
import OddMath.SKM.AugmentedInverseEvaluation
import OddMath.SKM.RouquierHomDistinctSourceUnits

/-!
# Weight denominators

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # The ELV Rouquier family on the original weight group

Brundan–Ellis Definition 1.5, (1.8)–(1.14): assemble the prescribed
induction, restriction, dots, same-colour crossings and constructed local
inverses. The cutoff matches the highest weight. The separate multicolour
relations are still required for an action of the complete presentation.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELV
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (Λ : X) (hcutoff : ∀ i, (cutoff i : ℤ) = D.h i Λ)

/-- The chosen weight functors and their constructed local inverses.
There is no local-inverse or factor-family premise. -/
def elvRouquierFamily :
    SKM.RouquierFamily (k := k) (B := PiSCat.{u,u,u + 1} k) D where
  toRouquierData := elvRouquierData D Sc cutoff bound Λ
  F i _ _ h := elvF D Sc cutoff bound i Λ h
  adj i _ _ h := elvActionAdjunction D Sc cutoff bound i Λ h
  square i _ _ _ h₁ h₂ := elvRouquierData_square D Sc cutoff bound i Λ h₁ h₂
  braid i _ _ _ _ h₁ h₂ h₃ := elvRouquierData_braid D Sc cutoff bound i Λ h₁ h₂ h₃
  loc i _ _ _ h₁ h₂ := Classical.choice
    (elvWeightRouquierLocal_nonempty D Sc cutoff bound i Λ h₁ h₂ (hcutoff i))

/-- Restriction is the prescribed right adjoint at each original weight. -/
theorem elvRouquierFamily_F (i : I) {x y : X} (h : x + D.α i = y) :
    (elvRouquierFamily D Sc cutoff bound Λ hcutoff).F i h =
      elvF D Sc cutoff bound i Λ h := rfl

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Coordinates of the chosen reservoir principal inverses

The reservoir closure uses the principal inverse selected by the actual
Rouquier family. Its finite forward matrix determines this principal,
independently of the choices used to construct the local record.
These coordinates attach that chosen inverse to the represented matrices
used in the integer-degree calculation of ReservoirClosureDegree.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELV
open CyclotomicAction BalancedInduction CyclotomicCrossingTensor
universe u
section Detection
variable {k : Type u} [CommRing k] {C : Type*} [Category C]
  [Preadditive C] [Linear k C] [Supercategory k C]
  {A B Z : C} {p : ZMod 2} {q : ℕ → ZMod 2} {n : ℕ}
private theorem column_principal_eq {f : B ⟶ A} {g : ℕ → (Z ⟶ A)}
    (K : SKM.SuperSumInvFrom (k := k) f g p q n) (s : A ⟶ B)
    (hs : f ≫ s = 𝟙 B) (hg : ∀ r, r < n → g r ≫ s = 0) : s = K.f' := by
  apply K.hom_ext
  · exact hs.trans K.ff.symm
  · intro r hr
    exact (hg r hr).trans (K.gf r hr).symm
private theorem row_principal_square {A' B' : C} {f : A ⟶ B} {g : ℕ → (A ⟶ Z)}
    {f' : A' ⟶ B'} {g' : ℕ → (A' ⟶ Z)}
    (K : SKM.SuperSumInvTo (k := k) f' g' p q n) (s : B ⟶ A)
    (a : A ⟶ A') (b : B ⟶ B') (hf : a ≫ f' = f ≫ b)
    (hg : ∀ r, r < n → a ≫ g' r = g r)
    (hs : s ≫ f = 𝟙 B) (hsg : ∀ r, r < n → s ≫ g r = 0) :
    s ≫ a = b ≫ K.f' := by
  apply K.hom_ext
  · rw [Category.assoc, hf, ← Category.assoc, hs, Category.id_comp,
      Category.assoc, K.ff, Category.comp_id]
  · intro r hr
    rw [Category.assoc, hg r hr, hsg r hr, Category.assoc, K.fg r hr, Limits.comp_zero]

private theorem column_principal_square {A' B' : C} {f : B ⟶ A} {g : ℕ → (Z ⟶ A)}
    {f' : B' ⟶ A'} {g' : ℕ → (Z ⟶ A')}
    (K : SKM.SuperSumInvFrom (k := k) f' g' p q n) (s : A ⟶ B)
    (a : A ≅ A') (b : B ≅ B') (hf : f ≫ a.hom = b.hom ≫ f')
    (hg : ∀ r, r < n → g r ≫ a.hom = g' r)
    (hs : f ≫ s = 𝟙 B) (hgs : ∀ r, r < n → g r ≫ s = 0) :
    s ≫ b.hom = a.hom ≫ K.f' := by
  apply (cancel_epi a.inv).mp
  rw [← Category.assoc a.inv a.hom, a.inv_hom_id, Category.id_comp]
  apply column_principal_eq K
  · have he : f' ≫ a.inv = b.inv ≫ f := by
      apply (cancel_mono a.hom).mp
      simp only [Category.assoc, a.inv_hom_id, Category.comp_id]
      rw [hf, ← Category.assoc, b.inv_hom_id, Category.id_comp]
    rw [← Category.assoc f' a.inv, he, Category.assoc b.inv f,
      ← Category.assoc f s, hs, Category.id_comp, b.inv_hom_id]
  · intro r hr
    rw [← hg r hr, Category.assoc, a.hom_inv_id_assoc,
      ← Category.assoc, hgs r hr, Limits.zero_comp]

end Detection

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (Λ : X) (hcutoff : ∀ i, (cutoff i : ℤ) = D.h i Λ)
  (i : I) {x₀ x₁ x₂ : X} (h₁ : x₀ + D.α i = x₁) (h₂ : x₁ + D.α i = x₂)
  (M : ELVWeightProduct D Sc cutoff N Λ x₁) (δ : WeightBlocks D Λ x₁)
local notation "W" => elvRouquierFamily D Sc cutoff N Λ hcutoff

/-- The literal chosen principal at an input family and output block. -/
def elvChosenCapPrincipal (hh : 0 ≤ D.h i x₁) :=
  ((((elvRouquierFamily D Sc cutoff N Λ hcutoff).loc i h₁ h₂).invPos hh).f').total M δ

/-- The literal chosen negative principal at an input family and output block. -/
def elvChosenUnitPrincipal (hh : D.h i x₁ ≤ 0) :=
  ((((elvRouquierFamily D Sc cutoff N Λ hcutoff).loc i h₁ h₂).invNeg hh).f').total M δ

variable (β : WeightBlocks D Λ x₀)
local notation "δ₁" => blockSucc D Λ i h₁ β
local notation "δ₂" => blockSucc D Λ i h₂ (blockSucc D Λ i h₁ β)
local notation "hS" => elvWeightMixedSource_obj D Sc cutoff N i i Λ h₁ h₁ β M
local notation "hT" => elvWeightMixedTarget_obj D Sc cutoff N i i Λ h₁ h₂ h₁ h₂ β M

/-- The constructed canonical content cap inverse at this supported weight block. -/
def elvContentCapInverseAtWeight (hh : 0 ≤ D.h i x₁) :=
  Classical.choice (contentTargetsLocalInverseTo_nonempty D Sc cutoff N β.1 i δ₁.1 δ₂.1
    (elvBlockSucc_content_eq D i Λ h₁ β) (elvBlockSucc_content_eq D i Λ h₂ δ₁) (M δ₁) (by
      rw [contentCrossingHeight_eq_neg_weight D cutoff i Λ x₁ (hcutoff i) δ₁]
      exact neg_nonpos.mpr hh))

/-- The constructed canonical content unit inverse at this supported weight block. -/
def elvContentUnitInverseAtWeight (hh : D.h i x₁ ≤ 0) :=
  Classical.choice (contentTargetsLocalInverseFrom_nonempty D Sc cutoff N β.1 i δ₁.1 δ₂.1
    (elvBlockSucc_content_eq D i Λ h₁ β) (elvBlockSucc_content_eq D i Λ h₂ δ₁) (M δ₁) (by
      rw [contentCrossingHeight_eq_neg_weight D cutoff i Λ x₁ (hcutoff i) δ₁]
      exact neg_nonneg.mpr hh))

local notation "φ" => SKM.rouquierMate
  (elvActionAdjunction D Sc cutoff N i Λ h₁)
  (elvActionAdjunction D Sc cutoff N i Λ h₂)
  (elvActionCross D Sc cutoff N i i Λ h₁ h₂ h₁ h₂)
local notation "CapField" r => elvF D Sc cutoff N i Λ h₁ ◁
  SKM.rouquierPower (elvActionDot D Sc cutoff N i Λ h₁) r ≫
    elvActionCounit D Sc cutoff N i Λ h₁
local notation "UnitField" r => elvActionUnit D Sc cutoff N i Λ h₂ ≫
  SKM.rouquierPower (elvActionDot D Sc cutoff N i Λ h₂) r ▷
    elvF D Sc cutoff N i Λ h₂

/-- Any cap inverse of the prescribed forward matrix has these coordinates. -/
theorem elvCapPrincipal_coordinates (hh : 0 ≤ D.h i x₁)
    (L : SKM.SuperSumInvTo (k := k) (φ) (fun r => CapField r)
      (D.parity i) (fun r => (r : ZMod 2) * D.parity i) (D.h i x₁).toNat) :
    L.f'.total M δ₁ ≫ eqToHom hS =
      eqToHom hT ≫ (elvContentCapInverseAtWeight D Sc cutoff N Λ hcutoff i h₁ h₂ M β hh).f' := by
  let J := L.at M
  let K := elvContentCapInverseAtWeight D Sc cutoff N Λ hcutoff i h₁ h₂ M β hh
  apply row_principal_square K (L.f'.total M δ₁) (eqToHom hS) (eqToHom hT)
  · exact (elvWeightRouquierGridMate_comparison D Sc cutoff N i Λ h₁ h₂ β M).symm
  · intro r _
    exact (elvWeightCapPower_localCoordinates D Sc cutoff N i Λ h₁ β M r).symm
  · have hj := congrFun J.ff δ₁
    dsimp only [J] at hj
    simpa only [SKM.SuperSumInvTo.at_f', CategoryTheory.Pi.comp_apply,
      CategoryTheory.Pi.id_apply, Categorification.TwoRep.pi_zero_apply] using hj
  · intro r hr
    have hcount := contentCapCount_weightBlock D cutoff i Λ x₁ (hcutoff i) δ₁
    have hr' : r < (D.h i x₁).toNat := by simpa only [hcount] using hr
    have hj := (CategoryTheory.Pi.eval _ δ₁).congr_map (J.fg r hr')
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_zero] at hj
    dsimp only [J, CategoryTheory.Pi.eval] at hj
    simpa only [SKM.SuperSumInvTo.at_f'] using hj

/-- Any unit inverse of the prescribed forward matrix has these coordinates. -/
theorem elvUnitPrincipal_coordinates (hh : D.h i x₁ ≤ 0)
    (L : SKM.SuperSumInvFrom (k := k) (φ) (fun r => UnitField r)
      (D.parity i) (fun r => (r : ZMod 2) * D.parity i) (-D.h i x₁).toNat) :
    L.f'.total M δ₁ ≫ eqToHom hS =
      eqToHom hT ≫ (elvContentUnitInverseAtWeight D Sc cutoff N Λ hcutoff i h₁ h₂ M β hh).f' := by
  let J := L.at M
  let K := elvContentUnitInverseAtWeight D Sc cutoff N Λ hcutoff i h₁ h₂ M β hh
  apply column_principal_square K (L.f'.total M δ₁) (eqToIso hT) (eqToIso hS)
  · exact elvWeightRouquierGridMate_comparison D Sc cutoff N i Λ h₁ h₂ β M
  · intro r _
    exact elvWeightUnitPower_localCoordinates D Sc cutoff N i Λ h₁ h₂ β M r
  · have hj := congrFun J.ff δ₁
    dsimp only [J] at hj
    simpa only [SKM.SuperSumInvFrom.at_f', CategoryTheory.Pi.comp_apply,
      CategoryTheory.Pi.id_apply, Categorification.TwoRep.pi_zero_apply] using hj
  · intro r hr
    have hcount := contentUnitCount_weightBlock D cutoff i Λ x₁ (hcutoff i) δ₁
    have hr' : r < (-D.h i x₁).toNat := by simpa only [hcount] using hr
    have hj := (CategoryTheory.Pi.eval _ δ₁).congr_map (J.gf r hr')
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_zero] at hj
    dsimp only [J, CategoryTheory.Pi.eval] at hj
    simpa only [SKM.SuperSumInvFrom.at_f'] using hj

/-- The chosen positive principal has the canonical content inverse square. -/
theorem elvChosenCapPrincipal_coordinates (hh : 0 ≤ D.h i x₁) :
    elvChosenCapPrincipal D Sc cutoff N Λ hcutoff i h₁ h₂ M δ₁ hh ≫ eqToHom hS =
      eqToHom hT ≫ (elvContentCapInverseAtWeight D Sc cutoff N Λ hcutoff i h₁ h₂ M β hh).f' :=
  elvCapPrincipal_coordinates D Sc cutoff N Λ hcutoff i h₁ h₂ M β hh
    (((elvRouquierFamily D Sc cutoff N Λ hcutoff).loc i h₁ h₂).invPos hh)

/-- The chosen negative principal has the canonical content inverse square. -/
theorem elvChosenUnitPrincipal_coordinates (hh : D.h i x₁ ≤ 0) :
    elvChosenUnitPrincipal D Sc cutoff N Λ hcutoff i h₁ h₂ M δ₁ hh ≫ eqToHom hS =
      eqToHom hT ≫ (elvContentUnitInverseAtWeight D Sc cutoff N Λ hcutoff i h₁ h₂ M β hh).f' :=
  elvUnitPrincipal_coordinates D Sc cutoff N Λ hcutoff i h₁ h₂ M β hh
    (((elvRouquierFamily D Sc cutoff N Λ hcutoff).loc i h₁ h₂).invNeg hh)

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Module-uniform bounds at each actual weight-content block

The exponent varies with the target content block, while one exponent at a
fixed block works for every input module. This is the form needed before
transposing the actual dot through the actual induction/restriction adjunction.
No exponent over an entire original-weight fibre is asserted.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV
open OddMath.QuiverHecke.CyclotomicAction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (i : I) (Λ : X) {x y : X} (h : x + D.α i = y)

/-- A fixed source-content bound is uniform in the arbitrary input module. -/
theorem elvContentDotTo_pow_zero [Finite I]
    (hdot : TruncatedAppendDotNilpotent D Sc cutoff bound) (β γ : Multiset I)
    (hγ : β + ([i] : Multiset I) = γ) :
    ∃ e : ℕ, 0 < e ∧ ∀ M : ContentModules D Sc cutoff bound β,
      (show End ((contentInductionTo D Sc cutoff bound β [i] γ hγ).obj M) from
        (elvContentDotTo D Sc cutoff bound i β γ hγ).app (D.parity i) M) ^ e = 0 := by
  classical
  subst γ
  have hp := contentInductionDot_module_pow_zero D Sc cutoff bound hdot β.toList i
  rw [Multiset.coe_toList] at hp
  exact hp

theorem elvBlockDot_pow_zero [Finite I]
    (hdot : TruncatedAppendDotNilpotent D Sc cutoff bound) (β : WeightBlocks D Λ x) :
    ∃ e : ℕ, 0 < e ∧ ∀ M : ContentModules D Sc cutoff bound β.1,
      (show End ((elvBlockInd D Sc cutoff bound i Λ h β).obj M) from
        (elvBlockDot D Sc cutoff bound i Λ h β).app (D.parity i) M) ^ e = 0 :=
  elvContentDotTo_pow_zero D Sc cutoff bound i hdot β.1
    (blockSucc D Λ i h β).1 (by rw [blockSucc_val, add_comm]; rfl)

private theorem end_eqToHom_conj_pow
    {C : Type*} [Category C] [Preadditive C]
    {M N : C} (e : M = N) (d : End N) (n : ℕ) :
    (show End M from eqToHom e ≫ d ≫ eqToHom e.symm) ^ n =
      eqToHom e ≫ (d ^ n) ≫ eqToHom e.symm := by
  subst e
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

/-- Each actual target-weight block has one exponent for every input module.
The exponent may depend on the target block. -/
theorem elvWeightDotComponent_pow_zero [Finite I]
    (hdot : TruncatedAppendDotNilpotent D Sc cutoff bound) (δ : WeightBlocks D Λ y) :
    ∃ e : ℕ, 0 < e ∧ ∀ M : ELVWeightProduct D Sc cutoff bound Λ x,
      (show End ((elvInductionComponent D Sc cutoff bound i Λ h δ).obj M) from
        elvWeightDotComponent D Sc cutoff bound i Λ h (D.parity i) M δ) ^ e = 0 := by
  classical
  by_cases hδ : ∃ β, blockSucc D Λ i h β = δ
  · obtain ⟨β, rfl⟩ := hδ
    obtain ⟨e, he, hp⟩ := elvBlockDot_pow_zero D Sc cutoff bound i Λ h hdot β
    refine ⟨e, he, fun M => ?_⟩
    rw [elvWeightDotComponent_blockSucc, end_eqToHom_conj_pow, hp (M β)]
    simp
  · refine ⟨1, by decide, fun M => ?_⟩
    simpa only [pow_one] using
      (elvInductionComponent_isZero D Sc cutoff bound i Λ h δ hδ M).eq_of_src
        (elvWeightDotComponent D Sc cutoff bound i Λ h (D.parity i) M δ) 0

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Actual full-ELV denominator inverses from contentwise dot bounds

An arbitrary source superfunctor is followed by the actual weight induction.
The reservoir dot is the whiskering of the chosen normalized full-ELV dot.
Denominator inverses use fixed-content nilpotence, assembled as even natural
transformations. Neither the source objects nor target blocks are assumed
finite, and no global reservoir-dot exponent is used.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV
open OddMath.QuiverHecke.CyclotomicAction OddMath.QuiverHecke.SwappedAssembly
universe u v w
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (hdot : TruncatedAppendDotNilpotent D Sc cutoff bound)
  (i : I) (Λ : X) {x y : X} (h : x + D.α i = y)
  {C : Type v} [Category.{w} C] [Preadditive C] [Linear k C] [Supercategory k C]
  (F : Superfunctor k C (ELVWeightProduct D Sc cutoff bound Λ x))

abbrev elvPostInduction := F.comp (elvE D Sc cutoff bound i Λ h)
abbrev elvPostDot : End (elvPostInduction D Sc cutoff bound i Λ h F) :=
  Superfunctor.whiskerLeft F (elvActionDot D Sc cutoff bound i Λ h)

/-- A typed endomorphism component of the actual postinduction functor. -/
abbrev elvPostEndComponent
    (g : End (elvPostInduction D Sc cutoff bound i Λ h F)) (p : ZMod 2)
    (M : C) (δ : WeightBlocks D Λ y) :
    End (((elvPostInduction D Sc cutoff bound i Λ h F).obj M) δ) := g.app p M δ

theorem elvPostDot_mem :
    elvPostDot D Sc cutoff bound i Λ h F ∈ parity (R := k) _ _ (D.parity i) :=
  Superfunctor.whiskerLeft_mem F (elvActionDot_mem D Sc cutoff bound i Λ h)

include hdot in
theorem elvPostDot_component_isNilpotent [Finite I] (M : C) (δ : WeightBlocks D Λ y) :
    IsNilpotent (elvPostEndComponent D Sc cutoff bound i Λ h F (elvPostDot D Sc cutoff bound i Λ h F) (D.parity i) M δ) :=
  elvWeightDotComponent_isNilpotent D Sc cutoff bound i Λ h hdot (F.obj M) δ

include hdot in
theorem elvPostDot_difference_isUnit [Finite I] (hi : D.parity i = 0)
    (X : End (elvPostInduction D Sc cutoff bound i Λ h F))
    (hx : X ∈ parity (R := k) _ _ 0)
    (hu : IsUnit X)
    (hcomm : ∀ M δ, Commute
      (elvPostEndComponent D Sc cutoff bound i Λ h F (elvPostDot D Sc cutoff bound i Λ h F) 0 M δ) (elvPostEndComponent D Sc cutoff bound i Λ h F X 0 M δ)) :
    IsUnit (elvPostDot D Sc cutoff bound i Λ h F - X) := by
  apply superfunctorEnd_isUnit
  · exact Submodule.sub_mem _
      (hi ▸ elvPostDot_mem D Sc cutoff bound i Λ h F) hx
  · intro M
    change IsUnit (show End ((elvPostInduction D Sc cutoff bound i Λ h F).obj M) from
      (elvPostDot D Sc cutoff bound i Λ h F).app 0 M - X.app 0 M)
    apply product_difference_isUnit
      (fun δ : WeightBlocks D Λ y => ContentModules D Sc cutoff bound δ.1)
    · exact fun δ => superfunctorProductEnd_component_isUnit _ _ X hu 0 hx M δ
    · intro δ
      simpa only [hi] using
        elvPostDot_component_isNilpotent D Sc cutoff bound hdot i Λ h F M δ
    · exact hcomm M

include hdot in
theorem elvPostDot_square_difference_isUnit [Finite I] (hi : D.parity i = 1)
    (X : End (elvPostInduction D Sc cutoff bound i Λ h F))
    (hx : X ∈ parity (R := k) _ _ 1)
    (hu : IsUnit X)
    (hanti : ∀ M δ,
      elvPostEndComponent D Sc cutoff bound i Λ h F (elvPostDot D Sc cutoff bound i Λ h F) 1 M δ * elvPostEndComponent D Sc cutoff bound i Λ h F X 1 M δ =
        -(elvPostEndComponent D Sc cutoff bound i Λ h F X 1 M δ * elvPostEndComponent D Sc cutoff bound i Λ h F (elvPostDot D Sc cutoff bound i Λ h F) 1 M δ)) :
    IsUnit (X ^ 2 - elvPostDot D Sc cutoff bound i Λ h F ^ 2) := by
  have hy : elvPostDot D Sc cutoff bound i Λ h F ∈ parity (R := k) _ _ 1 :=
    hi ▸ elvPostDot_mem D Sc cutoff bound i Λ h F
  apply superfunctorEnd_isUnit
  · simpa only [pow_two, End.mul_def, SuperNatTrans.zmod2_one_add_one] using
      Submodule.sub_mem _ (comp_mem hx hx) (comp_mem hy hy)
  · intro M
    change IsUnit (
      (show End ((elvPostInduction D Sc cutoff bound i Λ h F).obj M) from (X ^ 2).app 0 M) -
      (show End ((elvPostInduction D Sc cutoff bound i Λ h F).obj M) from
        (elvPostDot D Sc cutoff bound i Λ h F ^ 2).app 0 M))
    rw [superfunctor_odd_square_app_zero _ X hx M,
      superfunctor_odd_square_app_zero _ (elvPostDot D Sc cutoff bound i Λ h F) hy M]
    exact product_square_difference_isUnit
      (fun δ : WeightBlocks D Λ y => ContentModules D Sc cutoff bound δ.1)
      ((elvPostInduction D Sc cutoff bound i Λ h F).obj M)
      (show End ((elvPostInduction D Sc cutoff bound i Λ h F).obj M) from X.app 1 M)
      (show End ((elvPostInduction D Sc cutoff bound i Λ h F).obj M) from
        (elvPostDot D Sc cutoff bound i Λ h F).app 1 M)
      (fun δ => superfunctorProductEnd_component_isUnit _ _ X hu 1 hx M δ)
      (fun δ => by
        simpa only [hi] using
          elvPostDot_component_isNilpotent D Sc cutoff bound hdot i Λ h F M δ)
      (hanti M)

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Coefficient expansions at the chosen ELV output component

`SwappedHomInversion.md` §3 (3) and §4: evaluate at the actual reservoir
output block and supply its constructed nilpotence bound. The bound may
vary with the block; no full-weight support bound is imposed.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV
open SwappedAssembly CyclotomicAction
universe u v w
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (i : I) (Λ : X) {x y : X} (h : x + D.α i = y)
  {C : Type v} [Category.{w} C] [Preadditive C] [Linear k C] [Supercategory k C]
  (F : Superfunctor k C (ELVWeightProduct D Sc cutoff bound Λ x))
local notation "G" => elvPostInduction D Sc cutoff bound i Λ h F
local notation "Y" => elvPostDot D Sc cutoff bound i Λ h F

/-- Total supernatural evaluation followed by the literal output projection. -/
def elvPostEndEvaluation (M : C) (δ : WeightBlocks D Λ y) :
    End G →ₐ[k] End (((G).obj M) δ) :=
  (piEndEvaluation ((G).obj M) δ).comp (supernaturalEndEvaluation G M)

/-- Evaluation retains the prescribed component of a homogeneous endomorphism. -/
theorem elvPostEndEvaluation_of_mem (M : C) (δ : WeightBlocks D Λ y)
    (f : End G) {p : ZMod 2} (hf : f ∈ parity (R := k) _ _ p) :
    elvPostEndEvaluation D Sc cutoff bound i Λ h F M δ f = f.app p M δ := by
  change f.total M δ = f.app p M δ
  exact congrArg (fun a : End ((G).obj M) => a δ) (OddMath.HomogeneousSuperfunctorIso.total_eq_app f hf M)

/-- The evaluated chosen postdot has its already constructed component bound. -/
theorem elvPostEndEvaluation_dot_isNilpotent [Finite I]
    (hdot : TruncatedAppendDotNilpotent D Sc cutoff bound)
    (M : C) (δ : WeightBlocks D Λ y) :
    IsNilpotent (elvPostEndEvaluation D Sc cutoff bound i Λ h F M δ Y) := by
  rw [elvPostEndEvaluation_of_mem D Sc cutoff bound i Λ h F M δ Y
    (elvPostDot_mem D Sc cutoff bound i Λ h F)]
  exact elvPostDot_component_isNilpotent D Sc cutoff bound hdot i Λ h F M δ

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Denominator units on the actual content-shifted Hom summand

Use the same canonical homPiLeft structure as the existing swapped Hom
construction. The chosen normalized postdot is mapped through the actual
homParityShift functor, exactly as in homContentPostDot. Every unit is
transported through this functor; no alternative action or dot gauge is used.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELV
open OddMath.QuiverHecke.CyclotomicAction
universe u

local instance piSCatHomPi {k : Type u} [CommRing k]
    (A B : PiSCat.{u, u, u + 1} k) : PiSupercategory k (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (i : I) (Λ : X) {x y : X} (h : x + D.α i = y)
  {A : PiSCat.{u, u, u + 1} k} (F : A ⟶ elvWeightSpace D Sc cutoff bound Λ x)

/-- The literal postcomposition image of the probe-precomposition dot. -/
abbrev elvPostProbeDot (α : End F) : End (elvPostInduction D Sc cutoff bound i Λ h F) :=
  Superfunctor.whiskerRight α (elvE D Sc cutoff bound i Λ h)

theorem elvPostProbeDot_isUnit (α : End F) (hu : IsUnit α) :
    IsUnit (elvPostProbeDot D Sc cutoff bound i Λ h F α) :=
  hu.map ((SKM.homPost (k := k) (a := A) (elvE D Sc cutoff bound i Λ h)).mapEnd F)

theorem elvPostProbeDot_mem {p : ZMod 2} (α : End F)
    (hα : α ∈ parity (R := k) _ _ p) :
    elvPostProbeDot D Sc cutoff bound i Λ h F α ∈ parity (R := k) _ _ p :=
  Superfunctor.whiskerRight_mem hα (elvE D Sc cutoff bound i Λ h)

private theorem elvPostProbe_even_comm (α : End F) (M : A) (δ : WeightBlocks D Λ y) :
    Commute
      (elvPostEndComponent D Sc cutoff bound i Λ h F
        (elvPostDot D Sc cutoff bound i Λ h F) 0 M δ)
      (elvPostEndComponent D Sc cutoff bound i Λ h F
        (elvPostProbeDot D Sc cutoff bound i Λ h F α) 0 M δ) := by
  change
    ((elvE D Sc cutoff bound i Λ h).map (α.app 0 M)) δ ≫
        (elvActionDot D Sc cutoff bound i Λ h).app 0 (F.obj M) δ =
      (elvActionDot D Sc cutoff bound i Λ h).app 0 (F.obj M) δ ≫
        ((elvE D Sc cutoff bound i Λ h).map (α.app 0 M)) δ
  have hh := (elvActionDot D Sc cutoff bound i Λ h).naturality
    0 (α.app 0 M) (α.app_mem 0 M)
  simp only [koszulSign_zero_left, one_smul] at hh
  exact congrArg (fun f => f δ) hh

private theorem elvPostProbe_odd_anticomm (α : End F) (M : A) (δ : WeightBlocks D Λ y) :
    elvPostEndComponent D Sc cutoff bound i Λ h F
        (elvPostDot D Sc cutoff bound i Λ h F) 1 M δ *
      elvPostEndComponent D Sc cutoff bound i Λ h F
        (elvPostProbeDot D Sc cutoff bound i Λ h F α) 1 M δ =
    -(elvPostEndComponent D Sc cutoff bound i Λ h F
        (elvPostProbeDot D Sc cutoff bound i Λ h F α) 1 M δ *
      elvPostEndComponent D Sc cutoff bound i Λ h F
        (elvPostDot D Sc cutoff bound i Λ h F) 1 M δ) := by
  change
    ((elvE D Sc cutoff bound i Λ h).map (α.app 1 M)) δ ≫
        (elvActionDot D Sc cutoff bound i Λ h).app 1 (F.obj M) δ =
      -((elvActionDot D Sc cutoff bound i Λ h).app 1 (F.obj M) δ ≫
        ((elvE D Sc cutoff bound i Λ h).map (α.app 1 M)) δ)
  have hh := (elvActionDot D Sc cutoff bound i Λ h).naturality
    1 (α.app 1 M) (α.app_mem 1 M)
  have hs : koszulSign (1 : ZMod 2) 1 = -1 := by simp [koszulSign]
  rw [hs, neg_one_zsmul] at hh
  exact congrArg (fun f => f δ) hh

theorem elvPostProbe_difference_isUnit [Finite I]
    (hdot : TruncatedAppendDotNilpotent D Sc cutoff bound) (hi : D.parity i = 0)
    (α : End F) (hα : α ∈ parity (R := k) _ _ 0) (hu : IsUnit α) :
    IsUnit (elvPostDot D Sc cutoff bound i Λ h F -
      elvPostProbeDot D Sc cutoff bound i Λ h F α) :=
  elvPostDot_difference_isUnit D Sc cutoff bound hdot i Λ h F hi _
    (elvPostProbeDot_mem D Sc cutoff bound i Λ h F α hα)
    (elvPostProbeDot_isUnit D Sc cutoff bound i Λ h F α hu)
    (elvPostProbe_even_comm D Sc cutoff bound i Λ h F α)

theorem elvPostProbe_square_difference_isUnit [Finite I]
    (hdot : TruncatedAppendDotNilpotent D Sc cutoff bound) (hi : D.parity i = 1)
    (α : End F) (hα : α ∈ parity (R := k) _ _ 1) (hu : IsUnit α) :
    IsUnit (elvPostProbeDot D Sc cutoff bound i Λ h F α ^ 2 -
      elvPostDot D Sc cutoff bound i Λ h F ^ 2) :=
  elvPostDot_square_difference_isUnit D Sc cutoff bound hdot i Λ h F hi _
    (elvPostProbeDot_mem D Sc cutoff bound i Λ h F α hα)
    (elvPostProbeDot_isUnit D Sc cutoff bound i Λ h F α hu)
    (elvPostProbe_odd_anticomm D Sc cutoff bound i Λ h F α)

private theorem functor_map_end_pow {C C' : Type*} [Category C] [Category C']
    (G : C ⥤ C') (M : C) (f : End M) (n : ℕ) :
    G.map (f ^ n) = (show End (G.obj M) from G.map f) ^ n :=
  (G.mapEnd M).map_pow f n

abbrev elvShiftedPostInduction (κ : ZMod 2) :
    A ⟶ elvWeightSpace D Sc cutoff bound Λ y :=
  (SKM.homParityShift (k := k) (C := A ⟶ elvWeightSpace D Sc cutoff bound Λ y) κ).obj
    (elvPostInduction D Sc cutoff bound i Λ h F)

abbrev elvShiftedPostEnd
    (g : End (elvPostInduction D Sc cutoff bound i Λ h F)) (κ : ZMod 2) :
    End (elvShiftedPostInduction D Sc cutoff bound i Λ h F κ) :=
  (SKM.homParityShift (k := k) (C := A ⟶ elvWeightSpace D Sc cutoff bound Λ y) κ).map g

/-- This is the literal homContentPostDot formula for the chosen full-ELV dot. -/
abbrev elvShiftedPostDot (κ : ZMod 2) :
    End (elvShiftedPostInduction D Sc cutoff bound i Λ h F κ) :=
  elvShiftedPostEnd D Sc cutoff bound i Λ h F (elvPostDot D Sc cutoff bound i Λ h F) κ

theorem elvShiftedPostProbe_difference_isUnit [Finite I]
    (hdot : TruncatedAppendDotNilpotent D Sc cutoff bound) (κ : ZMod 2)
    (hi : D.parity i = 0) (α : End F)
    (hα : α ∈ parity (R := k) _ _ 0) (hu : IsUnit α) :
    IsUnit (elvShiftedPostDot D Sc cutoff bound i Λ h F κ -
      elvShiftedPostEnd D Sc cutoff bound i Λ h F
        (elvPostProbeDot D Sc cutoff bound i Λ h F α) κ) := by
  let S := SKM.homParityShift (k := k)
    (C := A ⟶ elvWeightSpace D Sc cutoff bound Λ y) κ
  have hh := (elvPostProbe_difference_isUnit D Sc cutoff bound i Λ h F hdot hi α hα hu).map
    (S.mapEnd (elvPostInduction D Sc cutoff bound i Λ h F))
  change IsUnit (show End (S.obj (elvPostInduction D Sc cutoff bound i Λ h F)) from
    S.map (elvPostDot D Sc cutoff bound i Λ h F -
      elvPostProbeDot D Sc cutoff bound i Λ h F α)) at hh
  rw [Functor.map_sub] at hh
  exact hh

theorem elvShiftedPostProbe_square_difference_isUnit [Finite I]
    (hdot : TruncatedAppendDotNilpotent D Sc cutoff bound) (κ : ZMod 2)
    (hi : D.parity i = 1) (α : End F)
    (hα : α ∈ parity (R := k) _ _ 1) (hu : IsUnit α) :
    IsUnit (elvShiftedPostEnd D Sc cutoff bound i Λ h F
        (elvPostProbeDot D Sc cutoff bound i Λ h F α) κ ^ 2 -
      elvShiftedPostDot D Sc cutoff bound i Λ h F κ ^ 2) := by
  let S := SKM.homParityShift (k := k)
    (C := A ⟶ elvWeightSpace D Sc cutoff bound Λ y) κ
  have hh := (elvPostProbe_square_difference_isUnit D Sc cutoff bound i Λ h F hdot hi α hα hu).map
    (S.mapEnd (elvPostInduction D Sc cutoff bound i Λ h F))
  change IsUnit (show End (S.obj (elvPostInduction D Sc cutoff bound i Λ h F)) from
    S.map (elvPostProbeDot D Sc cutoff bound i Λ h F α ^ 2 -
      elvPostDot D Sc cutoff bound i Λ h F ^ 2)) at hh
  rw [Functor.map_sub, functor_map_end_pow, functor_map_end_pow] at hh
  exact hh

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Output bounds in the prescribed shifted ELV summand

`SwappedHomInversion.md` §3 (2)–(3): evaluate the actual content-shifted
postdot at an input and reservoir block. The nilpotence exponent belongs
to that component, without a common bound on the whole weight fibre.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELV
open CyclotomicAction
universe u

private def productPiEndComponent {k J : Type u} [CommRing k]
    (C : J → Type (u + 1)) [∀ j, Category.{u} (C j)] [∀ j, Preadditive (C j)]
    [∀ j, Linear k (C j)] [∀ j, Supercategory k (C j)] [∀ j, PiSupercategory k (C j)]
    (M : ∀ j, C j) (j : J) :
    letI := productPiSupercategory (k := k) C
    End (M j) →+* End ((PiSupercategory.pi (R := k) (C := ∀ j, C j)).obj M j) := by
  letI := productPiSupercategory (k := k) C
  let e : ((PiSupercategory.pi (R := k) (C := ∀ j, C j)).obj M j) ≅ M j :=
    { hom := (PiSupercategory.ζ (R := k) M).hom j
      inv := (PiSupercategory.ζ (R := k) M).inv j
      hom_inv_id := congrArg (fun f => f j) (PiSupercategory.ζ (R := k) M).hom_inv_id
      inv_hom_id := congrArg (fun f => f j) (PiSupercategory.ζ (R := k) M).inv_hom_id }
  exact
    { toFun := fun f => e.hom ≫ twist k 1 f ≫ e.inv
      map_zero' := by
        change e.hom ≫ twist k 1 (0 : End (M j)) ≫ e.inv = 0
        rw [map_zero, Limits.zero_comp, Limits.comp_zero]
      map_one' := by
        change e.hom ≫ twist k 1 (𝟙 (M j)) ≫ e.inv = 𝟙 _
        rw [twist_id, Category.id_comp, Iso.hom_inv_id]
      map_add' := by
        intro f g
        change e.hom ≫ twist k 1 (f + g) ≫ e.inv =
          (e.hom ≫ twist k 1 f ≫ e.inv) + (e.hom ≫ twist k 1 g ≫ e.inv)
        rw [map_add, Preadditive.add_comp, Preadditive.comp_add]
      map_mul' := by
        intro f g
        change e.hom ≫ twist k 1 (g ≫ f) ≫ e.inv =
          (e.hom ≫ twist k 1 g ≫ e.inv) ≫ (e.hom ≫ twist k 1 f ≫ e.inv)
        simp only [twist_comp, Category.assoc, Iso.inv_hom_id_assoc] }

private theorem productPi_map_component {k J : Type u} [CommRing k]
    (C : J → Type (u + 1)) [∀ j, Category.{u} (C j)] [∀ j, Preadditive (C j)]
    [∀ j, Linear k (C j)] [∀ j, Supercategory k (C j)] [∀ j, PiSupercategory k (C j)]
    (M : ∀ j, C j) (f : End M) (j : J) :
    letI := productPiSupercategory (k := k) C
    ((PiSupercategory.pi (R := k) (C := ∀ j, C j)).map f) j =
      productPiEndComponent (k := k) C M j (f j) := by
  let _ := productPiSupercategory (k := k) C
  rw [PiSupercategory.pi_map_eq]
  change (PiSupercategory.ζ (R := k) M).hom j ≫ (twist k 1 f) j ≫
      (PiSupercategory.ζ (R := k) M).inv j =
    (PiSupercategory.ζ (R := k) M).hom j ≫ twist k 1 (f j) ≫
      (PiSupercategory.ζ (R := k) M).inv j
  have ht : (twist k 1 f) j = twist k 1 (f j) :=
    map_twist (R := k) (Pi.eval C j) 1 f
  rw [ht]

local instance shiftedCoefficientHomPi {k : Type u} [CommRing k]
    (A B : PiSCat.{u, u, u + 1} k) : PiSupercategory k (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (i : I) (Λ : X) {x y : X} (h : x + D.α i = y)
  {A : PiSCat.{u,u,u + 1} k} (F : A ⟶ elvWeightSpace D Sc cutoff bound Λ x)
local notation "G" => elvPostInduction D Sc cutoff bound i Λ h F
local notation "Gs" κ => elvShiftedPostInduction D Sc cutoff bound i Λ h F κ
local notation "Ys" κ => elvShiftedPostDot D Sc cutoff bound i Λ h F κ

/-- Total evaluation on the shifted functor followed by the actual reservoir block. -/
def elvShiftedPostEndEvaluation (κ : ZMod 2) (M : A) (δ : WeightBlocks D Λ y) :
    End (Gs κ) →ₐ[k] End (((Gs κ).obj M) δ) :=
  (piEndEvaluation ((Gs κ).obj M) δ).comp (supernaturalEndEvaluation (Gs κ) M)

/-- With no shift the evaluation is the original literal component projection. -/
theorem elvShiftedPostEndEvaluation_zero (M : A) (δ : WeightBlocks D Λ y) (f : End G) :
    elvShiftedPostEndEvaluation D Sc cutoff bound i Λ h F 0 M δ
      (elvShiftedPostEnd D Sc cutoff bound i Λ h F f 0) =
    elvPostEndEvaluation D Sc cutoff bound i Λ h F M δ f := by
  rfl

/-- The odd shift acts by the actual product parity chart at this output block. -/
theorem elvShiftedPostEndEvaluation_one (M : A) (δ : WeightBlocks D Λ y) (f : End G) :
    elvShiftedPostEndEvaluation D Sc cutoff bound i Λ h F 1 M δ
      (elvShiftedPostEnd D Sc cutoff bound i Λ h F f 1) =
    productPiEndComponent (k := k) (fun β : WeightBlocks D Λ y => ContentModules D Sc cutoff bound β.1)
      ((G).obj M) δ (elvPostEndEvaluation D Sc cutoff bound i Λ h F M δ f) := by
  let _ := elvWeightPi D Sc cutoff bound Λ y
  change (((PiSupercategory.pi (R := k) (C := ELVWeightProduct D Sc cutoff bound Λ y)).map
    (f.app 0 M)) δ +
    ((PiSupercategory.pi (R := k) (C := ELVWeightProduct D Sc cutoff bound Λ y)).map
      (f.app 1 M)) δ) = _
  rw [productPi_map_component, productPi_map_component]
  exact (map_add (productPiEndComponent (k := k)
    (fun β : WeightBlocks D Λ y => ContentModules D Sc cutoff bound β.1) ((G).obj M) δ)
    (f.app 0 M δ) (f.app 1 M δ)).symm

/-- The chosen content shift preserves the already proved local reservoir-dot bound. -/
theorem elvShiftedPostEndEvaluation_dot_isNilpotent [Finite I]
    (hdot : TruncatedAppendDotNilpotent D Sc cutoff bound)
    (κ : ZMod 2) (M : A) (δ : WeightBlocks D Λ y) :
    IsNilpotent (elvShiftedPostEndEvaluation D Sc cutoff bound i Λ h F κ M δ (Ys κ)) := by
  rcases parity_eq_zero_or_one κ with rfl | rfl
  · rw [elvShiftedPostDot, elvShiftedPostEndEvaluation_zero]
    exact elvPostEndEvaluation_dot_isNilpotent D Sc cutoff bound i Λ h F hdot M δ
  · rw [elvShiftedPostDot, elvShiftedPostEndEvaluation_one]
    exact (elvPostEndEvaluation_dot_isNilpotent D Sc cutoff bound i Λ h F hdot M δ).map
      (productPiEndComponent (k := k) (fun β : WeightBlocks D Λ y => ContentModules D Sc cutoff bound β.1)
        ((G).obj M) δ)

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Fixed-content nilpotence of the actual full-ELV dot transpose

The induction-dot bound at blockSucc β is uniform in the input module.
The actual right transpose uses only that block when evaluated at β.
The reversal sign is retained and cancelled as a unit; no exponent on a whole
weight fibre or additional grading is assumed.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELV
open OddMath.QuiverHecke.CyclotomicAction
universe u v w t
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (i : I) (Λ : X) {x y : X} (h : x + D.α i = y)

private theorem total_whiskerLeft
    {A B C : PiSCat.{u, u, u + 1} k} (F : A ⟶ B)
    {G H : B ⟶ C} (f : G ⟶ H) (M : A) :
    (F ◁ f).total M = f.total (F.obj M) := rfl

private theorem total_whiskerRight
    {A B C : PiSCat.{u, u, u + 1} k} {F G : A ⟶ B}
    (f : F ⟶ G) (H : B ⟶ C) (M : A) :
    (f ▷ H).total M = H.map (f.total M) := by
  change H.map (f.app 0 M) + H.map (f.app 1 M) =
    H.map (f.app 0 M + f.app 1 M)
  exact H.toFunctor.map_add.symm

private def totalEndRingHom
    {A B : PiSCat.{u, u, u + 1} k} (F : A ⟶ B) (M : A) :
    End F →+* End (F.obj M) where
  toFun f := f.total M
  map_zero' := by
    change (0 : End (F.obj M)) + 0 = 0
    exact add_zero 0
  map_one' := by
    change (𝟙 (F.obj M) : End (F.obj M)) + 0 = (1 : End (F.obj M))
    exact add_zero _
  map_add' f g := by
    change (f.app 0 M + g.app 0 M) + (f.app 1 M + g.app 1 M) =
      (f.app 0 M + f.app 1 M) + (g.app 0 M + g.app 1 M)
    abel
  map_mul' f g := Superfunctor.comp_total g f M

private def componentEndRingHom {J : Type v} (C : J → Type w)
    [∀ a, Category.{t} (C a)] [∀ a, Preadditive (C a)]
    (M : ∀ a, C a) (a : J) : End M →+* End (M a) where
  toFun f := f a
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

private theorem end_total_id {A B : PiSCat.{u, u, u + 1} k}
    (F : A ⟶ B) (M : A) :
    (𝟙 F : End F).total M = 𝟙 (F.obj M) := by
  change (𝟙 (F.obj M) : End (F.obj M)) + 0 = 𝟙 _
  exact add_zero _

private theorem end_total_eq_app
    {A B : PiSCat.{u, u, u + 1} k} {F G : A ⟶ B}
    (f : F ⟶ G) (p : ZMod 2) (hf : f ∈ parity (R := k) F G p) (M : A) :
    f.total M = f.app p M := by
  rcases parity_eq_zero_or_one p with rfl | rfl
  · simp only [SuperNatTrans.total,
      Superfunctor.app_eq_zero_of_mem hf (by decide : (1 : ZMod 2) ≠ 0), add_zero]
  · simp only [SuperNatTrans.total,
      Superfunctor.app_eq_zero_of_mem hf (by decide : (0 : ZMod 2) ≠ 1), zero_add]

private theorem cupMapCap_total
    {A B : PiSCat.{u, u, u + 1} k} {E : A ⟶ B} {F : B ⟶ A}
    (η : 𝟙 A ⟶ E ≫ F) (ε : F ≫ E ⟶ 𝟙 B) (f : End E) (N : B) :
    ((rightUnitor F).inv ≫ F ◁ η ≫ (associator F E F).inv ≫
      (F ◁ f ≫ ε) ▷ F ≫ (leftUnitor F).hom).total N =
      η.total (F.obj N) ≫ F.map (f.total (F.obj N) ≫ ε.total N) := by
  erw [Superfunctor.comp_total, Superfunctor.comp_total,
    Superfunctor.comp_total, Superfunctor.comp_total]
  simp only [PiSCat.rightUnitor_inv, PiSCat.associator_inv, PiSCat.leftUnitor_hom]
  erw [end_total_id, end_total_id]
  let a : F.obj N ⟶ F.obj (E.obj (F.obj N)) := (F ◁ η).total N
  let b : F.obj (E.obj (F.obj N)) ⟶ F.obj N := ((F ◁ f ≫ ε) ▷ F).total N
  change 𝟙 (F.obj N) ≫ a ≫ 𝟙 (F.obj (E.obj (F.obj N))) ≫ b ≫ 𝟙 (F.obj N) = _
  simp only [Category.id_comp, Category.comp_id]
  change (F ◁ η).total N ≫ ((F ◁ f ≫ ε) ▷ F).total N = _
  erw [total_whiskerLeft, total_whiskerRight, Superfunctor.comp_total]
  rfl

private theorem adjointTranspose_total
    {A B : PiSCat.{u, u, u + 1} k} {E : A ⟶ B} {F : B ⟶ A}
    (adj : SKM.SuperAdjunction (k := k) E F) (f : End E) (N : B) :
    (SKM.SuperAdjunction.rightTranspose adj adj f).total N =
      adj.unit.total (F.obj N) ≫ F.map (f.total (F.obj N) ≫ adj.counit.total N) := by
  rw [SKM.SuperAdjunction.rightTranspose_apply]
  exact cupMapCap_total adj.unit adj.counit f N

private theorem ringHom_zsmul_pow {R S : Type*} [Ring R] [Ring S]
    (φ : R →+* S) (s : ℤ) (x : R) (n : ℕ) :
    φ (s • x ^ n) = s • (φ x) ^ n := by
  rw [map_zsmul, map_pow]

private theorem transpose_power_zero
    {A B : PiSCat.{u, u, u + 1} k} {E : A ⟶ B} {F : B ⟶ A}
    (adj : SKM.SuperAdjunction (k := k) E F) (d : End E)
    (p : ZMod 2) (hd : d ∈ parity (R := k) _ _ p)
    {S : Type*} [Ring S] (evt : End F →+* S) (n : ℕ)
    (hz : evt (SKM.SuperAdjunction.rightTranspose adj adj (d ^ n)) = 0) :
    (evt (SKM.SuperAdjunction.rightTranspose adj adj d)) ^ n = 0 := by
  have hs := SKM.SuperAdjunction.rightTranspose_power adj hd n
  rw [SKM.rouquierPower_eq_pow, SKM.rouquierPower_eq_pow] at hs
  let s : ℤ := koszulSign p p ^ (n.choose 2)
  have hh : evt (SKM.SuperAdjunction.rightTranspose adj adj (d ^ n)) =
      s • (evt (SKM.SuperAdjunction.rightTranspose adj adj d)) ^ n := by
    calc
      _ = evt (s • (show End F from SKM.SuperAdjunction.rightTranspose adj adj d) ^ n) :=
        congrArg evt hs
      _ = _ := ringHom_zsmul_pow evt s _ n
  rw [hz] at hh
  have hss : s * s = 1 := by
    dsimp [s]
    rw [← mul_pow, koszulSign_mul_self, one_pow]
  calc
    _ = s • (s • ((evt (SKM.SuperAdjunction.rightTranspose adj adj d)) ^ n)) := by
      rw [smul_smul, hss, one_smul]
    _ = 0 := by rw [← hh]; simp

/-- The actual dot transpose through the actual induction/restriction adjunction. -/
abbrev elvActionDotTranspose : End (elvF D Sc cutoff bound i Λ h) :=
  SKM.SuperAdjunction.rightTranspose (elvActionAdjunction D Sc cutoff bound i Λ h)
    (elvActionAdjunction D Sc cutoff bound i Λ h) (elvActionDot D Sc cutoff bound i Λ h)

theorem elvActionDotTranspose_mem :
    elvActionDotTranspose D Sc cutoff bound i Λ h ∈ parity (R := k) _ _ (D.parity i) :=
  SKM.SuperAdjunction.rightTranspose_mem _ _ (elvActionDot_mem D Sc cutoff bound i Λ h)

private theorem elvTranspose_total_component_zero
    (f : End (elvE D Sc cutoff bound i Λ h))
    (N : ELVWeightProduct D Sc cutoff bound Λ y) (β : WeightBlocks D Λ x)
    (hf : f.total ((elvF D Sc cutoff bound i Λ h).obj N)
      (blockSucc D Λ i h β) = 0) :
    (SKM.SuperAdjunction.rightTranspose (elvActionAdjunction D Sc cutoff bound i Λ h)
      (elvActionAdjunction D Sc cutoff bound i Λ h) f).total N β = 0 := by
  rw [adjointTranspose_total]
  change
    (elvActionUnit D Sc cutoff bound i Λ h).total
        ((elvF D Sc cutoff bound i Λ h).obj N) β ≫
      (elvBlockRes D Sc cutoff bound i Λ h β).map
        (f.total ((elvF D Sc cutoff bound i Λ h).obj N) (blockSucc D Λ i h β) ≫
          (elvActionCounit D Sc cutoff bound i Λ h).total N (blockSucc D Λ i h β)) = 0
  rw [hf, Limits.zero_comp]
  simp [Superfunctor.map]

private theorem elvDot_total_power_zero
    (M : ELVWeightProduct D Sc cutoff bound Λ x) (δ : WeightBlocks D Λ y) (n : ℕ)
    (hn : (show End (((elvE D Sc cutoff bound i Λ h).obj M) δ) from
      elvWeightDotComponent D Sc cutoff bound i Λ h (D.parity i) M δ) ^ n = 0) :
    ((show End (elvE D Sc cutoff bound i Λ h) from
      elvActionDot D Sc cutoff bound i Λ h) ^ n).total M δ = 0 := by
  let d : End (elvE D Sc cutoff bound i Λ h) := elvActionDot D Sc cutoff bound i Λ h
  let evd : End (elvE D Sc cutoff bound i Λ h) →+*
      End (((elvE D Sc cutoff bound i Λ h).obj M) δ) :=
    (componentEndRingHom
      (fun γ : WeightBlocks D Λ y => ContentModules D Sc cutoff bound γ.1)
      ((elvE D Sc cutoff bound i Λ h).obj M) δ).comp
      (totalEndRingHom (elvE D Sc cutoff bound i Λ h) M)
  change evd (d ^ n) = 0
  rw [map_pow]
  have hv : evd d =
      (show End (((elvE D Sc cutoff bound i Λ h).obj M) δ) from
        elvWeightDotComponent D Sc cutoff bound i Λ h (D.parity i) M δ) := by
    change d.total M δ = _
    rw [end_total_eq_app d (D.parity i) (elvActionDot_mem D Sc cutoff bound i Λ h)]
    rfl
  rw [hv]
  exact hn

private theorem elvTranspose_total_power_zero
    (d : End (elvE D Sc cutoff bound i Λ h)) (p : ZMod 2)
    (hd : d ∈ parity (R := k) _ _ p) (n : ℕ)
    (N : ELVWeightProduct D Sc cutoff bound Λ y) (β : WeightBlocks D Λ x)
    (hz : (d ^ n).total ((elvF D Sc cutoff bound i Λ h).obj N) (blockSucc D Λ i h β) = 0) :
    (show End (((elvF D Sc cutoff bound i Λ h).obj N) β) from
      (SKM.SuperAdjunction.rightTranspose
        (elvActionAdjunction D Sc cutoff bound i Λ h)
        (elvActionAdjunction D Sc cutoff bound i Λ h) d).total N β) ^ n = 0 := by
  let A := elvActionAdjunction D Sc cutoff bound i Λ h
  let evt : End (elvF D Sc cutoff bound i Λ h) →+*
      End (((elvF D Sc cutoff bound i Λ h).obj N) β) :=
    (componentEndRingHom
      (fun γ : WeightBlocks D Λ x => ContentModules D Sc cutoff bound γ.1)
      ((elvF D Sc cutoff bound i Λ h).obj N) β).comp
      (totalEndRingHom (elvF D Sc cutoff bound i Λ h) N)
  have htr := elvTranspose_total_component_zero D Sc cutoff bound i Λ h (d ^ n) N β hz
  change (SKM.SuperAdjunction.rightTranspose A A (d ^ n)).total N β = 0 at htr
  generalize htn : SKM.SuperAdjunction.rightTranspose A A (d ^ n) = tn at htr
  change evt tn = 0 at htr
  rw [← htn] at htr
  have hnil := transpose_power_zero A d p hd evt n htr
  generalize SKM.SuperAdjunction.rightTranspose A A d = t at hnil ⊢
  change (show End (((elvF D Sc cutoff bound i Λ h).obj N) β) from t.total N β) ^ n = 0 at hnil
  exact hnil

/-- One exponent at each source-content block works for every target module
after transposing the chosen dot, with its odd reversal sign retained. -/
theorem elvActionDotTranspose_component_pow_zero [Finite I]
    (hdot : TruncatedAppendDotNilpotent D Sc cutoff bound) (β : WeightBlocks D Λ x) :
    ∃ e : ℕ, 0 < e ∧ ∀ N : ELVWeightProduct D Sc cutoff bound Λ y,
      (show End (((elvF D Sc cutoff bound i Λ h).obj N) β) from
        (elvActionDotTranspose D Sc cutoff bound i Λ h).app (D.parity i) N β) ^ e = 0 := by
  obtain ⟨e, he, hp⟩ := elvWeightDotComponent_pow_zero D Sc cutoff bound i Λ h
    (hdot)
    (blockSucc D Λ i h β)
  refine ⟨e, he, fun N => ?_⟩
  have hz := elvDot_total_power_zero D Sc cutoff bound i Λ h
    ((elvF D Sc cutoff bound i Λ h).obj N) (blockSucc D Λ i h β) e
    (hp ((elvF D Sc cutoff bound i Λ h).obj N))
  have ht := elvTranspose_total_power_zero D Sc cutoff bound i Λ h
    (elvActionDot D Sc cutoff bound i Λ h) (D.parity i)
    (elvActionDot_mem D Sc cutoff bound i Λ h) e N β hz
  let t : End (elvF D Sc cutoff bound i Λ h) := elvActionDotTranspose D Sc cutoff bound i Λ h
  have hmem : t ∈ parity (R := k) _ _ (D.parity i) :=
    elvActionDotTranspose_mem D Sc cutoff bound i Λ h
  change (show End (((elvF D Sc cutoff bound i Λ h).obj N) β) from t.total N β) ^ e = 0 at ht
  simpa only [end_total_eq_app t (D.parity i) hmem] using ht

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Denominator inverses for the right-transposed ELV dot

The source-content exponent is uniform over input modules but may vary with
the source block. These bounds construct natural denominator inverses on
postrestriction. The postdot is literally the right transpose of the chosen
normalized full-ELV induction dot.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV
open OddMath.QuiverHecke.CyclotomicAction OddMath.QuiverHecke.SwappedAssembly
universe u v w
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (hdot : TruncatedAppendDotNilpotent D Sc cutoff bound)
  (i : I) (Λ : X) {x y : X} (h : x + D.α i = y)
  {C : Type v} [Category.{w} C] [Preadditive C] [Linear k C] [Supercategory k C]
  (F : Superfunctor k C (ELVWeightProduct D Sc cutoff bound Λ y))

abbrev elvPostRestriction := F.comp (elvF D Sc cutoff bound i Λ h)
def elvPostTransposeDot : End (elvPostRestriction D Sc cutoff bound i Λ h F) :=
  Superfunctor.whiskerLeft F (elvActionDotTranspose D Sc cutoff bound i Λ h)

theorem elvPostTransposeDot_eq :
    elvPostTransposeDot D Sc cutoff bound i Λ h F =
      Superfunctor.whiskerLeft F (elvActionDotTranspose D Sc cutoff bound i Λ h) := rfl

/-- A typed endomorphism component of the postrestriction functor. -/
abbrev elvRestrictionEndComponent
    (g : End (elvPostRestriction D Sc cutoff bound i Λ h F)) (p : ZMod 2)
    (M : C) (δ : WeightBlocks D Λ x) :
    End (((elvPostRestriction D Sc cutoff bound i Λ h F).obj M) δ) := g.app p M δ

theorem elvPostTransposeDot_mem :
    elvPostTransposeDot D Sc cutoff bound i Λ h F ∈ parity (R := k) _ _ (D.parity i) :=
  Superfunctor.whiskerLeft_mem F (elvActionDotTranspose_mem D Sc cutoff bound i Λ h)

include hdot in
theorem elvPostTransposeDot_component_isNilpotent [Finite I] (M : C) (δ : WeightBlocks D Λ x) :
    IsNilpotent (elvRestrictionEndComponent D Sc cutoff bound i Λ h F (elvPostTransposeDot D Sc cutoff bound i Λ h F) (D.parity i) M δ) := by
  obtain ⟨e, _, he⟩ := elvActionDotTranspose_component_pow_zero D Sc cutoff bound i Λ h hdot δ
  exact ⟨e, he (F.obj M)⟩

include hdot in
theorem elvPostTransposeDot_difference_isUnit [Finite I] (hi : D.parity i = 0)
    (X : End (elvPostRestriction D Sc cutoff bound i Λ h F))
    (hx : X ∈ parity (R := k) _ _ 0)
    (hu : IsUnit X)
    (hcomm : ∀ M δ, Commute
      (elvRestrictionEndComponent D Sc cutoff bound i Λ h F (elvPostTransposeDot D Sc cutoff bound i Λ h F) 0 M δ) (elvRestrictionEndComponent D Sc cutoff bound i Λ h F X 0 M δ)) :
    IsUnit (elvPostTransposeDot D Sc cutoff bound i Λ h F - X) := by
  apply superfunctorEnd_isUnit
  · exact Submodule.sub_mem _
      (hi ▸ elvPostTransposeDot_mem D Sc cutoff bound i Λ h F) hx
  · intro M
    change IsUnit (show End ((elvPostRestriction D Sc cutoff bound i Λ h F).obj M) from
      (elvPostTransposeDot D Sc cutoff bound i Λ h F).app 0 M - X.app 0 M)
    apply product_difference_isUnit
      (fun δ : WeightBlocks D Λ x => ContentModules D Sc cutoff bound δ.1)
    · exact fun δ => superfunctorProductEnd_component_isUnit _ _ X hu 0 hx M δ
    · intro δ
      simpa only [hi] using
        elvPostTransposeDot_component_isNilpotent D Sc cutoff bound hdot i Λ h F M δ
    · exact hcomm M

section Probe
variable {A : PiSCat.{u, u, u + 1} k}
  (G : A ⟶ elvWeightSpace D Sc cutoff bound Λ y)

/-- The literal postcomposition image of the probe-precomposition dot. -/
def elvRestrictionProbeDot (α : End G) : End (elvPostRestriction D Sc cutoff bound i Λ h G) :=
  Superfunctor.whiskerRight α (elvF D Sc cutoff bound i Λ h)

theorem elvRestrictionProbeDot_isUnit (α : End G) (hu : IsUnit α) :
    IsUnit (elvRestrictionProbeDot D Sc cutoff bound i Λ h G α) :=
  hu.map ((SKM.homPost (k := k) (a := A) (elvF D Sc cutoff bound i Λ h)).mapEnd G)

theorem elvRestrictionProbeDot_mem {p : ZMod 2} (α : End G)
    (hα : α ∈ parity (R := k) _ _ p) :
    elvRestrictionProbeDot D Sc cutoff bound i Λ h G α ∈ parity (R := k) _ _ p :=
  Superfunctor.whiskerRight_mem hα (elvF D Sc cutoff bound i Λ h)

private theorem elvRestrictionProbe_even_comm (t : End (elvF D Sc cutoff bound i Λ h)) (α : End G) (M : A) (δ : WeightBlocks D Λ x) :
    Commute
      (elvRestrictionEndComponent D Sc cutoff bound i Λ h G
        (Superfunctor.whiskerLeft G t) 0 M δ)
      (elvRestrictionEndComponent D Sc cutoff bound i Λ h G
        (elvRestrictionProbeDot D Sc cutoff bound i Λ h G α) 0 M δ) := by
  change
    ((elvF D Sc cutoff bound i Λ h).map (α.app 0 M)) δ ≫
        t.app 0 (G.obj M) δ =
      t.app 0 (G.obj M) δ ≫
        ((elvF D Sc cutoff bound i Λ h).map (α.app 0 M)) δ
  have hh := t.naturality
    0 (α.app 0 M) (α.app_mem 0 M)
  simp only [koszulSign_zero_left, one_smul] at hh
  exact congrArg (fun f => f δ) hh

theorem elvRestrictionProbe_difference_isUnit [Finite I]
    (hdot : TruncatedAppendDotNilpotent D Sc cutoff bound) (hi : D.parity i = 0)
    (α : End G) (hα : α ∈ parity (R := k) _ _ 0) (hu : IsUnit α) :
    IsUnit (elvPostTransposeDot D Sc cutoff bound i Λ h G -
      elvRestrictionProbeDot D Sc cutoff bound i Λ h G α) := by
  apply elvPostTransposeDot_difference_isUnit D Sc cutoff bound hdot i Λ h G hi
    (elvRestrictionProbeDot D Sc cutoff bound i Λ h G α)
  · exact elvRestrictionProbeDot_mem D Sc cutoff bound i Λ h G α hα
  · exact elvRestrictionProbeDot_isUnit D Sc cutoff bound i Λ h G α hu
  · rw [elvPostTransposeDot_eq]
    generalize elvActionDotTranspose D Sc cutoff bound i Λ h = t
    intro M δ
    exact elvRestrictionProbe_even_comm D Sc cutoff bound i Λ h G
      t α M δ

end Probe
end OddMath.QuiverHecke.ELV
end

end

section

/-! # Literal full-ELV source operators and even mixed-mate norm

Precompose the actual reservoir restriction by E followed by the prescribed
content parity shift of H. The probe and transposed dots are exactly the
mixedPostSourcePreDot and mixedPostSourcePostDot operators, using strict
Π-SCat whiskering. No complete factor family is assumed or replaced.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELV
universe u

local instance elvSourceHomPi {k : Type u} [CommRing k]
    (A B : PiSCat.{u, u, u + 1} k) : PiSupercategory k (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B

private theorem sourcePostDot_assoc {k : Type u} [CommRing k]
    {A B C D : PiSCat.{u, u, u + 1} k} (E : A ⟶ B) (K : B ⟶ C)
    (F : C ⟶ D) (t : End F) :
    Superfunctor.whiskerLeft (E ≫ K) t =
      Superfunctor.whiskerLeft E (Superfunctor.whiskerLeft K t) := rfl

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (i : I) (Λ : X) {x y : X} (h : x + D.α i = y)
  {A B : PiSCat.{u, u, u + 1} k} (E : A ⟶ B) (κ : ZMod 2)
  (H : B ⟶ elvWeightSpace D Sc cutoff bound Λ y)

/-- The twice-whiskered probe dot is the literal source pre dot. -/
theorem elvMixedSourceProbeDot_eq (xDot : End E) :
    elvRestrictionProbeDot D Sc cutoff bound i Λ h
        (E ≫ (SKM.homParityShift (k := k) (C := B ⟶ elvWeightSpace D Sc cutoff bound Λ y) κ).obj H)
        (xDot ▷ (SKM.homParityShift (k := k) (C := B ⟶ elvWeightSpace D Sc cutoff bound Λ y) κ).obj H) =
      SKM.mixedPostSourcePreDot (k := k) E κ H
        (F' := elvF D Sc cutoff bound i Λ h) xDot := rfl

/-- The precomposed chosen transpose is the literal source post dot. -/
theorem elvMixedSourceTransposeDot_eq :
    elvPostTransposeDot D Sc cutoff bound i Λ h
        (E ≫ (SKM.homParityShift (k := k) (C := B ⟶ elvWeightSpace D Sc cutoff bound Λ y) κ).obj H) =
      SKM.mixedPostSourcePostDot (k := k) E κ H
        (elvActionAdjunction D Sc cutoff bound i Λ h)
        (elvActionDot D Sc cutoff bound i Λ h) := by
  unfold elvPostTransposeDot SKM.mixedPostSourcePostDot elvActionDotTranspose
  exact sourcePostDot_assoc E
    ((SKM.homParityShift (k := k) (C := B ⟶ elvWeightSpace D Sc cutoff bound Λ y) κ).obj H)
    (elvF D Sc cutoff bound i Λ h)
    (SKM.SuperAdjunction.rightTranspose
      (elvActionAdjunction D Sc cutoff bound i Λ h)
      (elvActionAdjunction D Sc cutoff bound i Λ h)
      (elvActionDot D Sc cutoff bound i Λ h))

/-- The even source difference is a unit at every original weight. -/
theorem elvMixedSource_difference_isUnit [Finite I]
    (hdot : TruncatedAppendDotNilpotent D Sc cutoff bound) (hi : D.parity i = 0)
    (xDot : End E) (hx : xDot ∈ parity (R := k) _ _ 0) (hu : IsUnit xDot) :
    IsUnit (SKM.mixedPostSourcePreDot (k := k) E κ H
        (F' := elvF D Sc cutoff bound i Λ h) xDot -
      SKM.mixedPostSourcePostDot (k := k) E κ H
        (elvActionAdjunction D Sc cutoff bound i Λ h)
        (elvActionDot D Sc cutoff bound i Λ h)) := by
  have hx' := Superfunctor.whiskerRight_mem hx ((SKM.homParityShift (k := k) (C := B ⟶ elvWeightSpace D Sc cutoff bound Λ y) κ).obj H)
  have hu' : IsUnit (show End (E ≫ (SKM.homParityShift (k := k) (C := B ⟶ elvWeightSpace D Sc cutoff bound Λ y) κ).obj H) from
      xDot ▷ (SKM.homParityShift (k := k) (C := B ⟶ elvWeightSpace D Sc cutoff bound Λ y) κ).obj H) :=
    hu.map ((SKM.homPost (k := k) ((SKM.homParityShift (k := k) (C := B ⟶ elvWeightSpace D Sc cutoff bound Λ y) κ).obj H)).mapEnd E)
  have hh := elvRestrictionProbe_difference_isUnit D Sc cutoff bound i Λ h
    (E ≫ (SKM.homParityShift (k := k) (C := B ⟶ elvWeightSpace D Sc cutoff bound Λ y) κ).obj H) hdot hi
    (xDot ▷ (SKM.homParityShift (k := k) (C := B ⟶ elvWeightSpace D Sc cutoff bound Λ y) κ).obj H) hx' hu'
  rw [elvMixedSourceTransposeDot_eq D Sc cutoff bound i Λ h E κ H,
    elvMixedSourceProbeDot_eq D Sc cutoff bound i Λ h E κ H xDot] at hh
  simpa only [neg_sub] using hh.neg

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Odd mixed-source norms on the literal parenthesization

Work on E followed by (ΠH followed by actual restriction). Componentwise
nilpotence of the chosen transpose gives both source norm units without
transporting a norm through an equality of functor parenthesizations.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELV
open OddMath.QuiverHecke.SwappedAssembly OddMath.QuiverHecke.CyclotomicAction
universe u v w v' w'
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (Λ x : X)

/-- Use the bicategory's original Hom data rather than the strict-category Quiver path. -/
local instance elvOddPiQuiver : Quiver.{u + 1} (PiSCat.{u, u, u + 1} k) :=
  (PiSCat.instBicategoryStruct (R := k)).toCategoryStruct.toQuiver

local instance elvOddPiCategoryStruct :
    CategoryStruct.{u + 1} (PiSCat.{u, u, u + 1} k) :=
  (PiSCat.instBicategoryStruct (R := k)).toCategoryStruct

/-- Fix the bundled Hom category before inserting actual coend endomorphisms. -/
local instance elvOddHomCategory (A B : PiSCat.{u, u, u + 1} k) :
    Category.{u + 1} (A ⟶ B) :=
  BicategoryStruct.homCategory A B

section Norms
variable {A B : PiSCat.{u, u, u + 1} k}

private theorem oddEndNorms
    (U : A ⟶ elvWeightSpace D Sc cutoff bound Λ x)
    (X Y : End U) (hx : X ∈ parity (R := k) _ _ 1)
    (hy : Y ∈ parity (R := k) _ _ 1) (hu : IsUnit X)
    (hn : ∀ (M : A.carrier) (δ : WeightBlocks D Λ x), IsNilpotent
      (show End ((U.obj M) δ) from Y.app 1 M δ))
    (ha : ∀ (M : A.carrier) (δ : WeightBlocks D Λ x),
      (show End ((U.obj M) δ) from Y.app 1 M δ) *
        (show End ((U.obj M) δ) from X.app 1 M δ) =
        -((show End ((U.obj M) δ) from X.app 1 M δ) *
          (show End ((U.obj M) δ) from Y.app 1 M δ))) :
    IsUnit (X ^ 2 - Y ^ 2) ∧ IsUnit (X ^ 2 + Y ^ 2) := by
  constructor
  · apply superfunctorEnd_isUnit
    · simpa only [pow_two, End.mul_def, SuperNatTrans.zmod2_one_add_one] using
        Submodule.sub_mem _ (comp_mem hx hx) (comp_mem hy hy)
    · intro M
      change IsUnit ((show End (U.obj M) from (X ^ 2).app 0 M) -
        (show End (U.obj M) from (Y ^ 2).app 0 M))
      rw [superfunctor_odd_square_app_zero _ X hx M,
        superfunctor_odd_square_app_zero _ Y hy M]
      exact product_square_difference_isUnit
        (fun δ : WeightBlocks D Λ x => ContentModules D Sc cutoff bound δ.1)
        (U.obj M) (show End (U.obj M) from X.app 1 M)
        (show End (U.obj M) from Y.app 1 M)
        (fun δ => superfunctorProductEnd_component_isUnit _ _ X hu 1 hx M δ)
        (hn M) (ha M)
  · apply superfunctorEnd_isUnit
    · simpa only [pow_two, End.mul_def, SuperNatTrans.zmod2_one_add_one] using
        Submodule.add_mem _ (comp_mem hx hx) (comp_mem hy hy)
    · intro M
      change IsUnit ((show End (U.obj M) from (X ^ 2).app 0 M) +
        (show End (U.obj M) from (Y ^ 2).app 0 M))
      rw [superfunctor_odd_square_app_zero _ X hx M,
        superfunctor_odd_square_app_zero _ Y hy M]
      exact product_square_sum_isUnit
        (fun δ : WeightBlocks D Λ x => ContentModules D Sc cutoff bound δ.1)
        (U.obj M) (show End (U.obj M) from X.app 1 M)
        (show End (U.obj M) from Y.app 1 M)
        (fun δ => superfunctorProductEnd_component_isUnit _ _ X hu 1 hx M δ)
        (hn M) (ha M)

/-- Odd composition norms from the componentwise bounds of an arbitrary module-valued functor. -/
theorem mixedOddNorms (E : A ⟶ B)
    (K : B ⟶ elvWeightSpace D Sc cutoff bound Λ x)
    (a : End E) (t : End K) (ht : t ∈ parity (R := k) _ _ 1)
    (ha : a ∈ parity (R := k) _ _ 1) (hu : IsUnit a)
    (hn : ∀ (M : B.carrier) (δ : WeightBlocks D Λ x), IsNilpotent (show End ((K.obj M) δ) from t.app 1 M δ)) :
    IsUnit ((show End (E ≫ K) from a ▷ K) ^ 2 -
      (show End (E ≫ K) from E ◁ t) ^ 2) ∧
    IsUnit ((show End (E ≫ K) from a ▷ K) ^ 2 +
      (show End (E ≫ K) from E ◁ t) ^ 2) := by
  apply oddEndNorms (A := A) D Sc cutoff bound Λ x (E ≫ K)
    (a ▷ K) (E ◁ t)
    (Superfunctor.whiskerRight_mem ha K) (Superfunctor.whiskerLeft_mem E ht)
    (hu.map ((SKM.homPost (k := k) (B := PiSCat.{u, u, u + 1} k)
      (a := A) (b := B) (c := elvWeightSpace D Sc cutoff bound Λ x) K).mapEnd E))
  · intro M δ
    exact hn (E.obj M) δ
  · intro M δ
    change K.map (a.app 1 M) δ ≫ t.app 1 (E.obj M) δ =
      -(t.app 1 (E.obj M) δ ≫ K.map (a.app 1 M) δ)
    have h := t.naturality 1 (a.app 1 M) (a.app_mem 1 M)
    have hs : koszulSign (1 : ZMod 2) 1 = -1 := by simp [koszulSign]
    rw [hs, neg_one_zsmul] at h
    exact congrArg (fun f => f δ) h

end Norms

local instance elvOddSourceHomPi (A B : PiSCat.{u, u, u + 1} k) :
    PiSupercategory k (A ⟶ B) := PiTwoSupercategory.homPiLeft A B

variable (i : I) {y : X} (h : x + D.α i = y)
  {A B : PiSCat.{u, u, u + 1} k} (E : A ⟶ B) (κ : ZMod 2)
  (H : B ⟶ elvWeightSpace D Sc cutoff bound Λ y)

private theorem elvMixedSource_oddNorms [Finite I]
    (hdot : TruncatedAppendDotNilpotent D Sc cutoff bound) (hi : D.parity i = 1)
    (a : End E) (ha : a ∈ parity (R := k) _ _ 1) (hu : IsUnit a) :
    IsUnit (SKM.mixedPostSourcePreDot (k := k) E κ H
        (F' := elvF D Sc cutoff bound i Λ h) a ^ 2 -
      SKM.mixedPostSourcePostDot (k := k) E κ H
        (elvActionAdjunction D Sc cutoff bound i Λ h)
        (elvActionDot D Sc cutoff bound i Λ h) ^ 2) ∧
    IsUnit (SKM.mixedPostSourcePreDot (k := k) E κ H
        (F' := elvF D Sc cutoff bound i Λ h) a ^ 2 +
      SKM.mixedPostSourcePostDot (k := k) E κ H
        (elvActionAdjunction D Sc cutoff bound i Λ h)
        (elvActionDot D Sc cutoff bound i Λ h) ^ 2) := by
  let K : B ⟶ elvWeightSpace D Sc cutoff bound Λ y := (SKM.homParityShift (k := k)
    (C := B ⟶ elvWeightSpace D Sc cutoff bound Λ y) κ).obj H
  let F : B ⟶ elvWeightSpace D Sc cutoff bound Λ x := K ≫ elvF D Sc cutoff bound i Λ h
  let t : End F := K ◁ elvActionDotTranspose D Sc cutoff bound i Λ h
  have ht : t ∈ parity (R := k) _ _ 1 :=
    Superfunctor.whiskerLeft_mem K (hi ▸ elvActionDotTranspose_mem D Sc cutoff bound i Λ h)
  have hn : ∀ (M : B.carrier) (δ : WeightBlocks D Λ x), IsNilpotent (show End ((F.obj M) δ) from t.app 1 M δ) := by
    intro M δ
    obtain ⟨n, _, hn⟩ :=
      elvActionDotTranspose_component_pow_zero D Sc cutoff bound i Λ h hdot δ
    refine ⟨n, ?_⟩
    change (show End (((elvF D Sc cutoff bound i Λ h).obj (K.obj M)) δ) from
      (elvActionDotTranspose D Sc cutoff bound i Λ h).app 1 (K.obj M) δ) ^ n = 0
    simpa only [hi] using hn (K.obj M)
  have hh := mixedOddNorms (A := A) (B := B) D Sc cutoff bound Λ x E F a t ht ha hu hn
  set_option backward.dsimp.instances true in
    dsimp only [K, F, t] at hh
  delta elvOddPiQuiver elvOddPiCategoryStruct elvOddHomCategory
    SKM.mixedPostSourcePreDot SKM.mixedPostSourcePostDot elvActionDotTranspose at hh ⊢
  exact hh

/-- The literal odd source square difference is a unit without a whole-fibre exponent. -/
theorem elvMixedSource_square_difference_isUnit [Finite I]
    (hdot : TruncatedAppendDotNilpotent D Sc cutoff bound) (hi : D.parity i = 1)
    (a : End E) (ha : a ∈ parity (R := k) _ _ 1) (hu : IsUnit a) :
    IsUnit (SKM.mixedPostSourcePreDot (k := k) E κ H
        (F' := elvF D Sc cutoff bound i Λ h) a ^ 2 -
      SKM.mixedPostSourcePostDot (k := k) E κ H
        (elvActionAdjunction D Sc cutoff bound i Λ h)
        (elvActionDot D Sc cutoff bound i Λ h) ^ 2) := by
  have hh := elvMixedSource_oddNorms D Sc cutoff bound Λ x i h E κ H hdot hi a ha hu
  exact hh.1

/-- The literal odd source square sum is a unit without a whole-fibre exponent. -/
theorem elvMixedSource_square_sum_isUnit [Finite I]
    (hdot : TruncatedAppendDotNilpotent D Sc cutoff bound) (hi : D.parity i = 1)
    (a : End E) (ha : a ∈ parity (R := k) _ _ 1) (hu : IsUnit a) :
    IsUnit (SKM.mixedPostSourcePreDot (k := k) E κ H
        (F' := elvF D Sc cutoff bound i Λ h) a ^ 2 +
      SKM.mixedPostSourcePostDot (k := k) E κ H
        (elvActionAdjunction D Sc cutoff bound i Λ h)
        (elvActionDot D Sc cutoff bound i Λ h) ^ 2) := by
  have hh := elvMixedSource_oddNorms D Sc cutoff bound Λ x i h E κ H hdot hi a ha hu
  exact hh.2

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Contentwise units of ELV mixed-source polynomials

SwappedDistinctMixedMates (13)–(15): source polynomials with a positive
reservoir-dot remainder are units. Their inverses are assembled at each
input and output content; a common nilpotence exponent is not required.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELV
open SwappedAssembly CyclotomicAction
universe u v w r

section Product
variable {k : Type r} [CommRing k]
  {J : Type u} {C : J → Type v} [∀ j, Category.{w} (C j)]
  [∀ j, Preadditive (C j)] [∀ j, Linear k (C j)] [∀ j, Supercategory k (C j)]
  {A : Type*} [Category* A] [Preadditive A] [Linear k A] [Supercategory k A]

private theorem even_end_pow {F : Superfunctor k A (∀ j, C j)} {f : End F}
    (hf : f ∈ parity (R := k) F F 0) (n : ℕ) :
    f ^ n ∈ parity (R := k) F F 0 := by
  induction n with
  | zero => exact id_mem F
  | succ n ih =>
    simpa only [pow_succ, End.mul_def, add_zero] using comp_mem hf ih

private theorem admissible_even {F : Superfunctor k A (∀ j, C j)} {a b : End F}
    (ha : a ∈ parity (R := k) F F 0) (hb : b ∈ parity (R := k) F F 0)
    {N : End F} (hN : N ∈ SKM.admissibleMonomials (k := k) a b
      (fun _ => True) (fun _ => True) 1) : N ∈ parity (R := k) F F 0 := by
  apply Submodule.span_le.mpr ?_ hN
  rintro _ ⟨p, q, _, _, _, rfl⟩
  change a ^ p * b ^ q ∈ parity (R := k) F F 0
  simpa only [End.mul_def, add_zero] using comp_mem (even_end_pow hb q) (even_end_pow ha p)

private theorem admissible_map {R S : Type*} [Ring R] [Ring S]
    [Algebra k R] [Algebra k S] (φ : R →ₐ[k] S) {a b N : R}
    (hN : N ∈ SKM.admissibleMonomials (k := k) a b
      (fun _ => True) (fun _ => True) 1) :
    φ N ∈ SKM.admissibleMonomials (k := k) (φ a) (φ b)
      (fun _ => True) (fun _ => True) 1 := by
  induction hN using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨p, q, hp, hq, hn, rfl⟩ := hz
    rw [map_mul, map_pow, map_pow]
    exact Submodule.subset_span ⟨p, q, hp, hq, hn, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ r hx

/-- Componentwise nilpotence supplies every even source polynomial unit,
including arbitrary linear combinations of positive post-dot monomials. -/
theorem product_source_polynomial_isUnit
    (F : Superfunctor k A (∀ j, C j)) (a b : End F)
    (ha : a ∈ parity (R := k) F F 0) (hb : b ∈ parity (R := k) F F 0)
    (hu : IsUnit a) (hab : Commute a b)
    (hn : ∀ M j, IsNilpotent (show End (F.obj M j) from b.app 0 M j))
    (c : kˣ) (n : ℕ) {N : End F}
    (hN : N ∈ SKM.admissibleMonomials (k := k) a b
      (fun _ => True) (fun _ => True) 1) : IsUnit ((c : k) • a ^ n + N) := by
  have hN0 := admissible_even ha hb hN
  have hpoly : (c : k) • a ^ n + N ∈ parity (R := k) F F 0 :=
    Submodule.add_mem _ (Submodule.smul_mem _ _ (even_end_pow ha n)) hN0
  apply superfunctorProductEnd_isUnit C F _ hpoly
  intro M j
  let φ : End F →ₐ[k] End (F.obj M j) :=
    (piEndEvaluation (F.obj M) j).comp (supernaturalEndEvaluation F M)
  have heval (f : End F) (hf : f ∈ parity (R := k) F F 0) : φ f = f.app 0 M j := by
    exact congrArg (fun z : End (F.obj M) => z j)
      (OddMath.HomogeneousSuperfunctorIso.total_eq_app f hf M)
  have hnil : IsNilpotent (φ b) := by rw [heval b hb]; exact hn M j
  have hh := SKM.isUnit_smul_pow_add_of_mem_admissibleMonomials (k := k)
    (Pa := fun _ => True) (Pb := fun _ => True)
    (fun _ _ _ _ => trivial) (fun _ _ _ _ => trivial)
    (fun p q _ _ => (hab.map φ.toRingHom).pow_pow p q)
    hnil (hu.map φ.toRingHom) c (d := n) trivial (admissible_map φ hN)
  change IsUnit ((c : k) • (φ a) ^ n + φ N) at hh
  have hφ : φ ((c : k) • a ^ n + N) = (c : k) • (φ a) ^ n + φ N := by
    rw [map_add, map_smul, map_pow]
  rw [← hφ, heval _ hpoly] at hh
  exact hh

end Product

local instance elvPolynomialHomPi {k : Type u} [CommRing k]
    (A B : PiSCat.{u,u,u + 1} k) : PiSupercategory k (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B

attribute [local irreducible] SKM.mixedPostSourcePreDot SKM.mixedPostSourcePostDot

private theorem source_post_even {k : Type u} [CommRing k]
    {A B C T : PiSCat.{u,u,u + 1} k}
    (E : A ⟶ B) {E' : C ⟶ T} {F' : T ⟶ C}
    (adj : SKM.SuperAdjunction (k := k) E' F') (κ : ZMod 2) (H : B ⟶ T)
    (y : End E') (hy : y ∈ parity (R := k) E' E' 0) :
    SKM.mixedPostSourcePostDot (k := k) E κ H adj y ∈
      parity (R := k)
        (E ≫ ((SKM.homParityShift (k := k) (C := B ⟶ T) κ).obj H ≫ F'))
        (E ≫ ((SKM.homParityShift (k := k) (C := B ⟶ T) κ).obj H ≫ F')) 0 := by
  delta SKM.mixedPostSourcePostDot
  exact Superfunctor.whiskerLeft_mem E
    (Superfunctor.whiskerLeft_mem _ (SKM.SuperAdjunction.rightTranspose_mem adj adj hy))

private theorem source_post_app {k : Type u} [CommRing k]
    {A B C T : PiSCat.{u,u,u + 1} k}
    (E : A ⟶ B) {E' : C ⟶ T} {F' : T ⟶ C}
    (adj : SKM.SuperAdjunction (k := k) E' F') (κ : ZMod 2) (H : B ⟶ T)
    (y : End E') (p : ZMod 2) (M : A) :
    (SKM.mixedPostSourcePostDot (k := k) E κ H adj y).app p M =
      (SKM.SuperAdjunction.rightTranspose adj adj y).app p
        (((SKM.homParityShift (k := k) (C := B ⟶ T) κ).obj H).obj (E.obj M)) := by
  delta SKM.mixedPostSourcePostDot
  rfl

section ELV
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (i : I) (Λ : X) {x y : X} (h : x + D.α i = y)

private theorem transpose_power_component_isNilpotent [Finite I]
    (hdot : TruncatedAppendDotNilpotent D Sc cutoff bound) (n : ℕ) (hn : 0 < n)
    (M : ELVWeightProduct D Sc cutoff bound Λ y) (δ : WeightBlocks D Λ x) :
    IsNilpotent (show End (((elvF D Sc cutoff bound i Λ h).obj M) δ) from
      (SKM.SuperAdjunction.rightTranspose (elvActionAdjunction D Sc cutoff bound i Λ h)
        (elvActionAdjunction D Sc cutoff bound i Λ h)
        (SKM.rouquierPower (elvActionDot D Sc cutoff bound i Λ h) n)).total M δ) := by
  let φ := (piEndEvaluation ((elvF D Sc cutoff bound i Λ h).obj M) δ).comp
    (supernaturalEndEvaluation (elvF D Sc cutoff bound i Λ h) M)
  have ht : IsNilpotent (φ (elvActionDotTranspose D Sc cutoff bound i Λ h)) := by
    obtain ⟨e, _, he⟩ := elvActionDotTranspose_component_pow_zero D Sc cutoff bound i Λ h hdot δ
    refine ⟨e, ?_⟩
    change (show End (((elvF D Sc cutoff bound i Λ h).obj M) δ) from
      (elvActionDotTranspose D Sc cutoff bound i Λ h).total M δ) ^ e = 0
    rw [OddMath.HomogeneousSuperfunctorIso.total_eq_app _
      (elvActionDotTranspose_mem D Sc cutoff bound i Λ h) M]
    exact he M
  have hp := SKM.SuperAdjunction.rightTranspose_power
    (elvActionAdjunction D Sc cutoff bound i Λ h)
    (elvActionDot_mem D Sc cutoff bound i Λ h) n
  simp only [SKM.rouquierPower_eq_pow] at hp
  change IsNilpotent (φ _)
  rw [SKM.rouquierPower_eq_pow, hp, map_zsmul, map_pow]
  exact (ht.pow_of_pos (Nat.ne_of_gt hn)).smul _

attribute [local irreducible] elvF elvActionAdjunction elvActionDot

/-- Every admissible source polynomial built from an even probe unit and a
positive even reservoir dot power is a unit on the entire input Hom functor. -/
theorem elvMixedSource_polynomialUnits [Finite I]
    (hdot : TruncatedAppendDotNilpotent D Sc cutoff bound)
    {A B : PiSCat.{u,u,u + 1} k} (E : A ⟶ B) (κ : ZMod 2)
    (H : B ⟶ elvWeightSpace D Sc cutoff bound Λ y)
    (a : End E) (ha : a ∈ parity (R := k) E E 0) (hu : IsUnit a)
    (n : ℕ) (hn : 0 < n) (heven : (n : ZMod 2) * D.parity i = 0) :
    SKM.MixedPostSourceUnits E (elvActionAdjunction D Sc cutoff bound i Λ h) κ H a
      (SKM.rouquierPower (elvActionDot D Sc cutoff bound i Λ h) n) := by
  let K := (SKM.homParityShift (k := k)
    (C := B ⟶ elvWeightSpace D Sc cutoff bound Λ y) κ).obj H
  let F : A ⟶ elvWeightSpace D Sc cutoff bound Λ x :=
    E ≫ (K ≫ elvF D Sc cutoff bound i Λ h)
  let b := SKM.rouquierPower (elvActionDot D Sc cutoff bound i Λ h) n
  have hb : b ∈ parity (R := k) _ _ 0 := by
    simpa only [heven] using SKM.rouquierPower_mem (elvActionDot_mem D Sc cutoff bound i Λ h) n
  let t : End (elvF D Sc cutoff bound i Λ h) :=
    SKM.SuperAdjunction.rightTranspose (elvActionAdjunction D Sc cutoff bound i Λ h)
      (elvActionAdjunction D Sc cutoff bound i Λ h) b
  have htb : t ∈ parity (R := k) _ _ 0 := SKM.SuperAdjunction.rightTranspose_mem
    (elvActionAdjunction D Sc cutoff bound i Λ h)
    (elvActionAdjunction D Sc cutoff bound i Λ h) hb
  let pre : End F := SKM.mixedPostSourcePreDot (k := k) E κ H
    (F' := elvF D Sc cutoff bound i Λ h) a
  let post : End F := SKM.mixedPostSourcePostDot (k := k) E κ H
    (elvActionAdjunction D Sc cutoff bound i Λ h) b
  have hpre : pre ∈ parity (R := k) F F 0 := by
    dsimp only [pre]
    delta SKM.mixedPostSourcePreDot
    exact TwoSupercategory.whiskerRight_mem (R := k) (K ≫ elvF D Sc cutoff bound i Λ h) ha
  have hpost : post ∈ parity (R := k) F F 0 :=
    source_post_even E (elvActionAdjunction D Sc cutoff bound i Λ h) κ H b hb
  have hpreu : IsUnit pre := SKM.mixedPostSourcePreDot_isUnit E κ H hu
  have hcomm : Commute pre post := SKM.commute_mixedPostSource E
    (elvActionAdjunction D Sc cutoff bound i Λ h) κ H ha (y := b)
  have hnil : ∀ M δ, IsNilpotent (show End (F.obj M δ) from post.app 0 M δ) := by
    intro M δ
    dsimp only [post]
    rw [source_post_app E (elvActionAdjunction D Sc cutoff bound i Λ h) κ H b 0 M]
    rw [← OddMath.HomogeneousSuperfunctorIso.total_eq_app t htb (K.obj (E.obj M))]
    exact transpose_power_component_isNilpotent D Sc cutoff bound i Λ h hdot n hn _ δ
  intro c e N hN
  exact product_source_polynomial_isUnit F pre post hpre hpost hpreu hcomm hnil c e hN

end ELV
end OddMath.QuiverHecke.ELV
end

end
