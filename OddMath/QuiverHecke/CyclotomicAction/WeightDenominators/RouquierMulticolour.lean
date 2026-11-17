import StringDiagrams.Super.PiTwo
import OddMath.QuiverHecke.CyclotomicAction.ContentTriple.ContentPrincipalInverseCoordinates
import OddMath.QuiverHecke.CyclotomicAction.WeightDenominators.RouquierFamily
import OddMath.QuiverHecke.CyclotomicAction.WeightTripleComparison.WeightTriplePolynomialComparison

/-!
# Weight denominators

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # The multicolour relations of the selected original-weight family

Brundan--Ellis Definition 1.5, (1.7)–(1.9), (1.12). Assemble all seven
multicolour fields from the prescribed induction/restriction, adjunction,
dots and crossings. The acting scalar family is parameterTwist Sc while
the presentation parameters remain Sc.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELV
universe u v w r
section Field
variable {k : Type u} [CommRing k] {B : Type v} [BicategoryStruct.{w,r} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)]
  {I X : Type u} [AddCommGroup X] (D : SKM.Datum I X) (Sc : SKM.Scalars D k)
  (T : SKM.RouquierFamily (k := k) (B := B) D)

/-- Decode the named dotted equation while the family is abstract; the
closed chosen action is substituted only after this conversion. -/
private theorem braidEq_field
    (h : ∀ (i j : I), i ≠ j → ∀ {a b c d e f : X}
      (hab : a + D.α i = b) (haf : a + D.α j = f) (hbc : b + D.α j = c)
      (hbe : b + D.α i = e) (hfc : f + D.α i = c) (hcd : c + D.α i = d)
      (hed : e + D.α j = d),
      rouquierMixedBraidEquation D Sc T.toRouquierData i j hab haf hbc hbe hfc hcd hed)
: ∀ (i j : I), i ≠ j → ∀ {a b c d e f : X}
    (hab : a + D.α i = b) (haf : a + D.α j = f) (hbc : b + D.α j = c)
    (hbe : b + D.α i = e) (hfc : f + D.α i = c) (hcd : c + D.α i = d)
    (hed : e + D.α j = d),
    T.E i hab ◁ T.cross i j hbc hcd hbe hed ≫
        (associator (T.E i hab) (T.E i hbe) (T.E j hed)).inv ≫
        T.cross i i hab hbe hab hbe ▷ T.E j hed ≫
        (associator (T.E i hab) (T.E i hbe) (T.E j hed)).hom ≫
        T.E i hab ◁ T.cross j i hbe hed hbc hcd -
      ((associator (T.E i hab) (T.E j hbc) (T.E i hcd)).inv ≫
        T.cross j i hab hbc haf hfc ▷ T.E i hcd ≫
        (associator (T.E j haf) (T.E i hfc) (T.E i hcd)).hom ≫
        T.E j haf ◁ T.cross i i hfc hcd hfc hcd ≫
        (associator (T.E j haf) (T.E i hfc) (T.E i hcd)).inv ≫
        T.cross i j haf hfc hab hbc ▷ T.E i hcd ≫
        (associator (T.E i hab) (T.E j hbc) (T.E i hcd)).hom) =
      ∑ s ∈ Finset.range (D.dn i j),
        (SKM.zsign k (D.parity i * (D.parity j + s)) * (Sc.t i j : k)) •
          (SKM.rouquierPower (T.dot i hab) s ▷ (T.E j hbc ≫ T.E i hcd) ≫
            T.E i hab ◁ T.E j hbc ◁ SKM.rouquierPower (T.dot i hcd) (D.dn i j - 1 - s)) +
      ∑ p ∈ Finset.range (D.dn i j), ∑ q ∈ Finset.range (D.dn j i), ∑ s ∈ Finset.range p,
        (SKM.zsign k (D.parity i * (D.parity j + s)) * Sc.s i j p q) •
          (SKM.rouquierPower (T.dot i hab) s ▷ (T.E j hbc ≫ T.E i hcd) ≫
            T.E i hab ◁ (SKM.rouquierPower (T.dot j hbc) q ▷ T.E i hcd) ≫
            T.E i hab ◁ T.E j hbc ◁ SKM.rouquierPower (T.dot i hcd) (p - 1 - s)) := by
  intro i j hij a b c d e f hab haf hbc hbe hfc hcd hed
  exact h i j hij hab haf hbc hbe hfc hcd hed
end Field

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (Λ : X) (hcutoff : ∀ i, (cutoff i : ℤ) = D.h i Λ)
local notation "Sc'" => parameterTwist D Sc

/-- The chosen weight family satisfies every multicolour relation of the
original-Sc presentation. The cutoff is the stated highest-weight pairing. No factor-action,
local-inverse or generator-compatibility premise is required. -/
theorem elvRouquierMulticolour :
    SKM.RouquierMulticolour
      (elvRouquierFamily D Sc' cutoff bound Λ hcutoff) Sc := by
  refine {
    quadZero := ?_
    quadNe := ?_
    slideLeft := ?_
    slideRight := ?_
    braid := ?_
    braidEq := ?_
    invNe := ?_ }
  · intro i j hij hd a b c d h₁ h₂ h₃ h₄
    exact elvActionCross_quadZero D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄ hij hd
  · intro i j hij hd a b c d h₁ h₂ h₃ h₄
    exact elvActionCross_quadNe D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄ hij hd
  · intro i j hij a b c d h₁ h₂ h₃ h₄
    exact elvActionCross_slideLeft_distinct D Sc' cutoff bound i j Λ h₁ h₂ h₃ h₄ hij
  · intro i j hij a b c d h₁ h₂ h₃ h₄
    exact elvActionCross_slideRight_distinct D Sc' cutoff bound i j Λ h₁ h₂ h₃ h₄ hij
  · intro i j l hb a bl bj bi clj cli cji d hal haj hai hlj hli hjl hji hil hij hd₁ hd₂ hd₃
    change rouquierMulticolourBraidEquation D (elvRouquierData D Sc' cutoff bound Λ)
      i j l hal haj hai hlj hli hjl hji hil hij hd₁ hd₂ hd₃
    exact elvRouquierData_multicolour_braid D Sc' cutoff bound i j l Λ
      hal haj hai hlj hli hjl hji hil hij hd₁ hd₂ hd₃ hb
  · apply braidEq_field D Sc (elvRouquierFamily D Sc' cutoff bound Λ hcutoff)
    intro i j hij a b c d e f hab haf hbc hbe hfc hcd hed
    exact elvRouquierData_braidEq D Sc cutoff bound i j Λ hab haf hbc hbe hfc hcd hed hij
  · intro i j hij a b c d h₁ h₂ h₃ h₄
    exact elvActionCrossMate_isIso D Sc' cutoff bound i j Λ h₁ h₂ h₃ h₄ hij

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Exact-content evaluation of coefficient actions

SwappedHomInversion §4, condition (J): evaluating the post-whiskering
coefficient action at an output content gives the action of the restricted
coefficient. This identifies the whole-weight closure action with the
content coefficient ideal without a uniform bound on the weight fibre.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELV.WeightCentreBlocks
open CyclotomicAction SwappedAssembly
universe u
private theorem postCoeff_eq_whiskerLeft {k : Type u} [CommRing k]
    {A B : PiSCat.{u,u,u + 1} k} (Z : A ⟶ B) (η : End (𝟙 B)) :
    ProbeWindow.postCoeff Z η = Superfunctor.whiskerLeft Z η := by
  unfold ProbeWindow.postCoeff
  simp only [PiSCat.rightUnitor_inv, PiSCat.rightUnitor_hom]
  erw [Category.id_comp, Category.comp_id]
  rfl

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (Λ : X) {x : X} (β : WeightBlocks D Λ x) (T : PiSCat.{u,u,u + 1} k)

/-- Output projection preserves the action of a whole-weight central coefficient. -/
theorem postCoeff_evaluate (Z : T ⟶ elvWeightSpace D Sc cutoff N Λ x)
    (η : End (Superfunctor.id k (ELVWeightProduct D Sc cutoff N Λ x))) :
    Superfunctor.whiskerRight (ProbeWindow.postCoeff Z η)
      (elvBlockEval D Sc cutoff N Λ β) =
        ProbeWindow.postCoeff (B := PiSCat.{u,u,u + 1} k)
          (a := T) (b := contentModuleTarget D Sc cutoff N β.1)
          (Z.comp (elvBlockEval D Sc cutoff N Λ β))
          (restrict D Sc cutoff N Λ β η) := by
  rw [postCoeff_eq_whiskerLeft, postCoeff_eq_whiskerLeft]
  apply Superfunctor.hom_ext
  intro p M
  change η.app p (Z.obj M) β = (restrict D Sc cutoff N Λ β η).app p (Z.obj M β)
  exact (restrict_app D Sc cutoff N Λ β η p (Z.obj M)).symm

end OddMath.QuiverHecke.ELV.WeightCentreBlocks
end

end

section

/-! # Coordinates of the chosen reservoir finite inverse windows

For SwappedHomInversion §4 (7), every finite chosen `g'` is forced by
its forward matrix. These equations retain the supported weight-to-content
charts in both orientations, without a new inverse comparison premise.
-/
noncomputable section
set_option backward.dsimp.instances true
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELV
open CyclotomicAction BalancedInduction CyclotomicCrossingTensor
universe u
private theorem identity_obj {k : Type u} [CommRing k]
    (A : PiSCat.{u, u, u + 1} k) (V : A) :
    (𝟙 A : Superfunctor k A A).obj V = V := rfl

section Detection
variable {k : Type u} [CommRing k] {C : Type*} [Category C]
  [Preadditive C] [Linear k C] [Supercategory k C]
  {A B Z : C} {p : ZMod 2} {q : ℕ → ZMod 2} {n : ℕ}
private theorem row_window_square {A' B' : C} {f : A ⟶ B} {g : ℕ → (A ⟶ Z)}
    {f' : A' ⟶ B'} {g' : ℕ → (A' ⟶ Z)}
    (K : SKM.SuperSumInvTo (k := k) f' g' p q n) (j : ℕ) (hj : j < n) (s : Z ⟶ A)
    (a : A ⟶ A') (b : B ⟶ B') (hf : a ≫ f' = f ≫ b)
    (hg : ∀ r, r < n → a ≫ g' r = g r)
    (hs : s ≫ f = 0) (hsg : ∀ r, r < n → s ≫ g r = if j = r then 𝟙 Z else 0) :
    s ≫ a = K.g' j := by
  apply K.hom_ext
  · rw [Category.assoc, hf, ← Category.assoc, hs, Limits.zero_comp, K.gf j hj]
  · intro r hr
    rw [Category.assoc, hg r hr, hsg r hr, K.gg j r hj hr]

private theorem column_window_square {A' B' : C} {f : B ⟶ A} {g : ℕ → (Z ⟶ A)}
    {f' : B' ⟶ A'} {g' : ℕ → (Z ⟶ A')}
    (K : SKM.SuperSumInvFrom (k := k) f' g' p q n) (j : ℕ) (hj : j < n) (s : A ⟶ Z)
    (a : A ≅ A') (b : B ≅ B') (hf : f ≫ a.hom = b.hom ≫ f')
    (hg : ∀ r, r < n → g r ≫ a.hom = g' r)
    (hs : f ≫ s = 0) (hgs : ∀ r, r < n → g r ≫ s = if r = j then 𝟙 Z else 0) :
    s = a.hom ≫ K.g' j := by
  apply (cancel_epi a.inv).mp
  rw [← Category.assoc a.inv a.hom, a.inv_hom_id, Category.id_comp]
  apply K.hom_ext
  · have he : f' ≫ a.inv = b.inv ≫ f := by
      apply (cancel_mono a.hom).mp
      simp only [Category.assoc, a.inv_hom_id, Category.comp_id]
      rw [hf, ← Category.assoc, b.inv_hom_id, Category.id_comp]
    rw [← Category.assoc f' a.inv, he, Category.assoc b.inv f,
      hs, Limits.comp_zero, K.fg j hj]
  · intro r hr
    rw [← hg r hr, Category.assoc, a.hom_inv_id_assoc,
      hgs r hr, hg r hr, K.gg r j hr hj]
end Detection

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (Λ : X) (hcutoff : ∀ i, (cutoff i : ℤ) = D.h i Λ)
  (i : I) {x₀ x₁ x₂ : X} (h₁ : x₀ + D.α i = x₁) (h₂ : x₁ + D.α i = x₂)
  (M : ELVWeightProduct D Sc cutoff N Λ x₁) (δ : WeightBlocks D Λ x₁)
local notation "W" => elvRouquierFamily D Sc cutoff N Λ hcutoff

/-- The chosen positive-weight finite cap inverse column on an output block. -/
def elvChosenCapWindow (hh : 0 ≤ D.h i x₁) (j : ℕ) :=
  ((((W).loc i h₁ h₂).invPos hh).g' j).total M δ

/-- The chosen negative-weight finite unit inverse row on an output block. -/
def elvChosenUnitWindow (hh : D.h i x₁ ≤ 0) (j : ℕ) :=
  ((((W).loc i h₁ h₂).invNeg hh).g' j).total M δ

variable (β : WeightBlocks D Λ x₀)
local notation "δ₁" => blockSucc D Λ i h₁ β
local notation "δ₂" => blockSucc D Λ i h₂ (blockSucc D Λ i h₁ β)
local notation "hS" => elvWeightMixedSource_obj D Sc cutoff N i i Λ h₁ h₁ β M
local notation "hT" => elvWeightMixedTarget_obj D Sc cutoff N i i Λ h₁ h₂ h₁ h₂ β M

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

/-- Every finite weight cap inverse column has the prescribed content coordinate. -/
theorem elvCapWindow_coordinates (hh : 0 ≤ D.h i x₁)
    (L : SKM.SuperSumInvTo (k := k) (φ) (fun r => CapField r)
      (D.parity i) (fun r => (r : ZMod 2) * D.parity i) (D.h i x₁).toNat)
    (j : ℕ) (hj : j < (D.h i x₁).toNat) :
    (L.g' j).total M δ₁ ≫ eqToHom hS =
      (elvContentCapInverseAtWeight D Sc cutoff N Λ hcutoff i h₁ h₂ M β hh).g' j := by
  let J := L.at M
  let K := elvContentCapInverseAtWeight D Sc cutoff N Λ hcutoff i h₁ h₂ M β hh
  have hcount := contentCapCount_weightBlock D cutoff i Λ x₁ (hcutoff i) δ₁
  have hj' : j < contentCapCount D cutoff i δ₁.1 := by simpa only [hcount] using hj
  apply row_window_square K j hj' ((L.g' j).total M δ₁) (eqToHom hS) (eqToHom hT)
  · exact (elvWeightRouquierGridMate_comparison D Sc cutoff N i Λ h₁ h₂ β M).symm
  · intro r _
    exact (elvWeightCapPower_localCoordinates D Sc cutoff N i Λ h₁ β M r).symm
  · have he := (CategoryTheory.Pi.eval _ δ₁).congr_map (J.gf j hj)
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_zero] at he
    dsimp only [J, CategoryTheory.Pi.eval] at he
    simpa only [SKM.SuperSumInvTo.at_g', Superfunctor.id, Functor.id_obj] using he
  · intro r hr
    have hr' : r < (D.h i x₁).toNat := by simpa only [hcount] using hr
    have he := (CategoryTheory.Pi.eval _ δ₁).congr_map (J.gg j r hj hr')
    split_ifs at he ⊢
    · rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] at he
      dsimp only [J, CategoryTheory.Pi.eval] at he
      simp only [identity_obj] at he
      simpa only [SKM.SuperSumInvTo.at_g', Superfunctor.id, Functor.id_obj] using he
    · rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_zero] at he
      dsimp only [J, CategoryTheory.Pi.eval] at he
      simp only [identity_obj] at he
      simpa only [SKM.SuperSumInvTo.at_g', Superfunctor.id, Functor.id_obj] using he

/-- Every finite weight unit inverse row has the prescribed content coordinate. -/
theorem elvUnitWindow_coordinates (hh : D.h i x₁ ≤ 0)
    (L : SKM.SuperSumInvFrom (k := k) (φ) (fun r => UnitField r)
      (D.parity i) (fun r => (r : ZMod 2) * D.parity i) (-D.h i x₁).toNat)
    (j : ℕ) (hj : j < (-D.h i x₁).toNat) :
    (L.g' j).total M δ₁ =
      eqToHom hT ≫ (elvContentUnitInverseAtWeight D Sc cutoff N Λ hcutoff i h₁ h₂ M β hh).g' j := by
  let J := L.at M
  let K := elvContentUnitInverseAtWeight D Sc cutoff N Λ hcutoff i h₁ h₂ M β hh
  have hcount := contentUnitCount_weightBlock D cutoff i Λ x₁ (hcutoff i) δ₁
  have hj' : j < contentUnitCount D cutoff i δ₁.1 := by simpa only [hcount] using hj
  apply column_window_square K j hj' ((L.g' j).total M δ₁) (eqToIso hT) (eqToIso hS)
  · exact elvWeightRouquierGridMate_comparison D Sc cutoff N i Λ h₁ h₂ β M
  · intro r _
    exact elvWeightUnitPower_localCoordinates D Sc cutoff N i Λ h₁ h₂ β M r
  · have he := (CategoryTheory.Pi.eval _ δ₁).congr_map (J.fg j hj)
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_zero] at he
    dsimp only [J, CategoryTheory.Pi.eval] at he
    simpa only [SKM.SuperSumInvFrom.at_g', Superfunctor.id, Functor.id_obj] using he
  · intro r hr
    have hr' : r < (-D.h i x₁).toNat := by simpa only [hcount] using hr
    have he := (CategoryTheory.Pi.eval _ δ₁).congr_map (J.gg r j hr' hj)
    split_ifs at he ⊢
    · rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] at he
      dsimp only [J, CategoryTheory.Pi.eval] at he
      simp only [identity_obj] at he
      simpa only [SKM.SuperSumInvFrom.at_g', Superfunctor.id, Functor.id_obj] using he
    · rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_zero] at he
      dsimp only [J, CategoryTheory.Pi.eval] at he
      simp only [identity_obj] at he
      simpa only [SKM.SuperSumInvFrom.at_g', Superfunctor.id, Functor.id_obj] using he

/-- The literal chosen positive finite inverse column retains the content chart. -/
theorem elvChosenCapWindow_coordinates (hh : 0 ≤ D.h i x₁)
    (j : ℕ) (hj : j < (D.h i x₁).toNat) :
    elvChosenCapWindow D Sc cutoff N Λ hcutoff i h₁ h₂ M δ₁ hh j ≫ eqToHom hS =
      (elvContentCapInverseAtWeight D Sc cutoff N Λ hcutoff i h₁ h₂ M β hh).g' j :=
  elvCapWindow_coordinates D Sc cutoff N Λ hcutoff i h₁ h₂ M β hh
    (((W).loc i h₁ h₂).invPos hh) j hj

/-- The literal chosen negative finite inverse row retains the content chart. -/
theorem elvChosenUnitWindow_coordinates (hh : D.h i x₁ ≤ 0)
    (j : ℕ) (hj : j < (-D.h i x₁).toNat) :
    elvChosenUnitWindow D Sc cutoff N Λ hcutoff i h₁ h₂ M δ₁ hh j =
      eqToHom hT ≫ (elvContentUnitInverseAtWeight D Sc cutoff N Λ hcutoff i h₁ h₂ M β hh).g' j :=
  elvUnitWindow_coordinates D Sc cutoff N Λ hcutoff i h₁ h₂ M β hh
    (((W).loc i h₁ h₂).invNeg hh) j hj

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Finite unit inverse windows at absent predecessors

SwappedHomInversion §4 (7): absent lower induction kills principal closures,
but need not kill unit-window boundary coefficients. The chosen finite unit
inverse rows retain the weighted content inverse at every absent block.
-/
noncomputable section
set_option backward.dsimp.instances true
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELV
open CyclotomicAction BalancedInduction CyclotomicCrossingTensor
universe u
private theorem identity_obj_2 {k : Type u} [CommRing k]
    (A : PiSCat.{u, u, u + 1} k) (V : A) :
    (𝟙 A : Superfunctor k A A).obj V = V := rfl

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

section Content
variable (β : Multiset I) (i : I)
local notation "γ" => β + ([i] : Multiset I)
local notation "hK" => contentBlockCanonicalSum β [i]
local notation "K" => contentAppendTo D Sc cutoff N β [i] γ hK
local notation "hDot" => contentBlockMatrixDot_supernatural D Sc cutoff N β i
variable (M : ContentModules D Sc cutoff N β)
local notation "P" => induced (contentInclusion D Sc cutoff N β) M
local notation "Target" => contentPrincipalTargetIso D Sc cutoff N β γ i hK M
local notation "Value" => contentExtensionUnitIso D Sc cutoff N β M
local notation "Q" => contentInclusion D Sc cutoff N β
local notation "T" => truncatedAppend D Sc cutoff N [i]

/-- Every finite row of a zero-principal content inverse is the chosen weighted row. -/
theorem contentAbsentUnitInverse_window
    (L : SKM.SuperSumInvFrom (k := k)
      (0 : elvZeroModule D Sc cutoff N β ⟶ (restriction K).obj (induced K M))
      (unitDotColumn K hDot M) (D.parity i) (fun n => n • D.parity i)
      (contentUnitCount D cutoff i β))
    (hh : 0 ≤ contentCrossingHeight D cutoff i β)
    (j : ℕ) (hj : j < contentUnitCount D cutoff i β) :
    L.g' j = (Target).hom ≫ (weightedContentLocalInverseFrom D Sc cutoff N i P β hh).g' j ≫
      (Value).inv := by
  classical
  let B := weightedContentLocalInverseFrom D Sc cutoff N i P β hh
  symm
  apply L.hom_ext
  · rw [Limits.zero_comp, L.fg j hj]
  · intro r hr
    have hs := contentUnitDotColumn_square D Sc cutoff N β i M r
    change unitDotColumn K hDot M r ≫ (Target).hom =
      (Value).hom ≫ (restriction Q).map
        (unitDotColumn T (truncatedDot_supernatural D Sc cutoff N i) P r) at hs
    calc
      unitDotColumn K hDot M r ≫ ((Target).hom ≫ B.g' j ≫ (Value).inv) =
          (Value).hom ≫ ((restriction Q).map
            (unitDotColumn T (truncatedDot_supernatural D Sc cutoff N i) P r) ≫ B.g' j) ≫
              (Value).inv := by rw [← Category.assoc, hs]; simp only [Category.assoc]
      _ = unitDotColumn K hDot M r ≫ L.g' j := by
        rw [B.gg r j hr hj, L.gg r j hr hj]
        split_ifs <;> simp
end Content

private theorem absentSingletonDot_mem (i : I) :
    dotE D Sc [i] 0 ∈ parity (R := k) _ _ (D.parity i) := by
  simpa only [pow_one, one_nsmul] using firstDot_pow_parity D Sc i [] 1

/-- Stored successor contents retain the same absent finite unit row. -/
theorem contentAbsentUnitTargetInverse_window (β γ : Multiset I) (i : I)
    (hγ : β + ([i] : Multiset I) = γ) (M : ContentModules D Sc cutoff N β)
    (L : SKM.SuperSumInvFrom (k := k)
      (0 : elvZeroModule D Sc cutoff N β ⟶
        (restriction (contentAppendTo D Sc cutoff N β [i] γ hγ)).obj
          (induced (contentAppendTo D Sc cutoff N β [i] γ hγ) M))
      (unitDotColumn (contentAppendTo D Sc cutoff N β [i] γ hγ)
        (contentAppendTo_supernatural D Sc cutoff N hγ hγ (absentSingletonDot_mem D Sc i)) M)
      (D.parity i) (fun n => n • D.parity i) (contentUnitCount D cutoff i β))
    (hh : 0 ≤ contentCrossingHeight D cutoff i β)
    (j : ℕ) (hj : j < contentUnitCount D cutoff i β) :
    L.g' j = (contentPrincipalTargetIso D Sc cutoff N β γ i hγ M).hom ≫
      (weightedContentLocalInverseFrom D Sc cutoff N i
        (induced (contentInclusion D Sc cutoff N β) M) β hh).g' j ≫
          (contentExtensionUnitIso D Sc cutoff N β M).inv := by
  subst γ
  exact contentAbsentUnitInverse_window D Sc cutoff N β i M L hh j hj

variable (Λ : X) (hcutoff : ∀ i, (cutoff i : ℤ) = D.h i Λ)
  (i : I) {x₀ x₁ x₂ : X} (h₁ : x₀ + D.α i = x₁) (h₂ : x₁ + D.α i = x₂)
  (M : ELVWeightProduct D Sc cutoff N Λ x₁) (δ : WeightBlocks D Λ x₁)
local notation "K" => elvBlockAppend D Sc cutoff N i Λ h₂ δ
local notation "ResU" => elvBlockRes D Sc cutoff N i Λ h₂ δ
local notation "ε" => blockSucc D Λ i h₂ δ
local notation "φ" => SKM.rouquierMate
  (elvActionAdjunction D Sc cutoff N i Λ h₁)
  (elvActionAdjunction D Sc cutoff N i Λ h₂)
  (elvActionCross D Sc cutoff N i i Λ h₁ h₂ h₁ h₂)
local notation "UnitField" r => elvActionUnit D Sc cutoff N i Λ h₂ ≫
  SKM.rouquierPower (elvActionDot D Sc cutoff N i Λ h₂) r ▷ elvF D Sc cutoff N i Λ h₂

/-- The prescribed absent-content inverse at the actual stored upper successor. -/
def elvContentAbsentUnitInverseAtWeight
    (hδ : ¬ ∃ β, blockSucc D Λ i h₁ β = δ) :=
  Classical.choice (contentAbsentUnitTargetInverse_nonempty D Sc cutoff N δ.1 ε.1 i
    (elvBlockSucc_content_eq D i Λ h₂ δ)
    (fun hi => hδ ((exists_blockSucc_iff D Λ i h₁ δ).mpr hi)) (M δ))

/-- The following upper-loop chart retains all ordinary weight unit columns. -/
theorem elvWeightUnitPower_following_coordinates (r : ℕ) :
    (UnitField r).total M δ ≫ eqToHom (elvWeightFollowing_obj D Sc cutoff N i Λ h₂ δ M) =
      unitDotColumn K (elvBlockGridDot_supernatural D Sc cutoff N i Λ h₂ δ) (M δ) r := by
  have ha : eqToHom (elvWeightFollowing_obj D Sc cutoff N i Λ h₂ δ M) =
      (ResU).map (eqToHom (elvInductionComponent_obj_blockSucc D Sc cutoff N i Λ h₂ δ M)) :=
    (eqToHom_map (ResU).toFunctor
      (elvInductionComponent_obj_blockSucc D Sc cutoff N i Λ h₂ δ M)).symm
  rw [ha]
  exact elvWeightUnit_gridColumn_comparison D Sc cutoff N i Λ h₂ δ M r

include hcutoff in
/-- Any finite weight unit inverse row has the prescribed absent content coordinate. -/
theorem elvAbsentUnitWindow_coordinates
    (hδ : ¬ ∃ β, blockSucc D Λ i h₁ β = δ)
    (L : SKM.SuperSumInvFrom (k := k) (φ) (fun r => UnitField r)
      (D.parity i) (fun r => (r : ZMod 2) * D.parity i) (-D.h i x₁).toNat)
    (j : ℕ) (hj : j < (-D.h i x₁).toNat) :
    (L.g' j).total M δ =
      eqToHom (elvWeightFollowing_obj D Sc cutoff N i Λ h₂ δ M) ≫
        (elvContentAbsentUnitInverseAtWeight D Sc cutoff N Λ i h₁ h₂ M δ hδ).g' j := by
  let J := L.at M
  let B := elvContentAbsentUnitInverseAtWeight D Sc cutoff N Λ i h₁ h₂ M δ hδ
  let a := eqToIso (elvWeightFollowing_obj D Sc cutoff N i Λ h₂ δ M)
  change (L.g' j).total M δ = a.hom ≫ B.g' j
  have hcount := contentUnitCount_weightBlock D cutoff i Λ x₁ (hcutoff i) δ
  have hj' : j < contentUnitCount D cutoff i δ.1 := by simpa only [hcount] using hj
  apply (cancel_epi a.inv).mp
  rw [← Category.assoc a.inv a.hom, a.inv_hom_id, Category.id_comp]
  apply B.hom_ext
  · rw [Limits.zero_comp, B.fg j hj']
  · intro r hr
    have hs := elvWeightUnitPower_following_coordinates D Sc cutoff N Λ i h₂ M δ r
    change (UnitField r).total M δ ≫ a.hom = _ at hs
    rw [← hs, Category.assoc, a.hom_inv_id_assoc, hs, B.gg r j hr hj']
    have hr' : r < (-D.h i x₁).toNat := by simpa only [hcount] using hr
    have he := (CategoryTheory.Pi.eval _ δ).congr_map (J.gg r j hr' hj)
    split_ifs at he ⊢
    · rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] at he
      dsimp only [J, CategoryTheory.Pi.eval] at he
      simp only [identity_obj_2] at he
      simpa only [SKM.SuperSumInvFrom.at_g'] using he
    · rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_zero] at he
      dsimp only [J, CategoryTheory.Pi.eval] at he
      simp only [identity_obj_2] at he
      simpa only [SKM.SuperSumInvFrom.at_g'] using he

/-- The literal chosen absent unit row is retained; absence does not set it to zero. -/
theorem elvChosenAbsentUnitWindow_coordinates
    (hδ : ¬ ∃ β, blockSucc D Λ i h₁ β = δ) (hh : D.h i x₁ ≤ 0)
    (j : ℕ) (hj : j < (-D.h i x₁).toNat) :
    elvChosenUnitWindow D Sc cutoff N Λ hcutoff i h₁ h₂ M δ hh j =
      eqToHom (elvWeightFollowing_obj D Sc cutoff N i Λ h₂ δ M) ≫
        (elvContentAbsentUnitInverseAtWeight D Sc cutoff N Λ i h₁ h₂ M δ hδ).g' j :=
  elvAbsentUnitWindow_coordinates D Sc cutoff N Λ hcutoff i h₁ h₂ M δ hδ
    (((elvRouquierFamily D Sc cutoff N Λ hcutoff).loc i h₁ h₂).invNeg hh) j hj

end OddMath.QuiverHecke.ELV
end

end
