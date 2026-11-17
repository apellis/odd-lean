import OddMath.QuiverHecke.CyclotomicAction.ContentBlockMatrix.ContentWeightedCapInverse
import OddMath.QuiverHecke.CyclotomicAction.WeightTripleBraid.WeightAbsentUnitInverse

/-!
# Weight triple braid

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # Prescribed cap inversion at absent zero-height blocks

BE (1.13): an absent predecessor block in the nonnegative categorical
height range has height zero. The already constructed empty-window unit
inverse supplies the same principal inverse for the cap presentation.
Both pointwise and input-natural fields retain the prescribed maps.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELV
universe u
private def emptyFromTo
    {k C : Type*} [CommRing k] [Category C] [Preadditive C]
    [Linear k C] [Supercategory k C] {A B Z : C}
    {f : B ⟶ A} {u : ℕ → (Z ⟶ A)} {p : ZMod 2} {q : ℕ → ZMod 2} {m : ℕ}
    (J : SKM.SuperSumInvFrom (k := k) f u p q m) (hm : m = 0)
    (g : ℕ → (B ⟶ Z)) (hg : ∀ n, g n ∈ parity (R := k) _ _ (q n)) :
    SKM.SuperSumInvTo (k := k) f g p q 0 := by
  subst m
  exact {
    f' := J.f'
    g' := fun _ => 0
    f_mem := J.f_mem
    g_mem := hg
    f'_mem := J.f'_mem
    g'_mem := fun _ => Submodule.zero_mem _
    total := by simpa only [Finset.range_zero, Finset.sum_empty, add_zero] using J.ff
    ff := by simpa only [Finset.range_zero, Finset.sum_empty, add_zero] using J.total
    fg := fun n hn => (Nat.not_lt_zero n hn).elim
    gf := fun n hn => (Nat.not_lt_zero n hn).elim
    gg := fun n _ hn _ => (Nat.not_lt_zero n hn).elim }

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (i : I) (Λ : X) {x₀ x₁ x₂ : X}
  (h₁ : x₀ + D.α i = x₁) (h₂ : x₁ + D.α i = x₂)
  (δ : WeightBlocks D Λ x₁)
local notation "E₁" => elvE D Sc cutoff N i Λ h₁
local notation "F₁" => elvF D Sc cutoff N i Λ h₁
local notation "E₂" => elvE D Sc cutoff N i Λ h₂
local notation "F₂" => elvF D Sc cutoff N i Λ h₂
local notation "φ" => SKM.rouquierMate
  (elvActionAdjunction D Sc cutoff N i Λ h₁)
  (elvActionAdjunction D Sc cutoff N i Λ h₂)
  (elvActionCross D Sc cutoff N i i Λ h₁ h₂ h₁ h₂)
local notation "ρ" n => F₁ ◁ SKM.rouquierPower (elvActionDot D Sc cutoff N i Λ h₁) n ≫
  elvActionCounit D Sc cutoff N i Λ h₁

/-- The constructed empty-window unit inverse is also the prescribed cap
inverse at every absent block in the nonnegative-height range. -/
theorem elvWeightAbsentCapInverse_nonempty
    (hcutoff : (cutoff i : ℤ) = D.h i Λ)
    (hδ : ¬ ∃ β, blockSucc D Λ i h₁ β = δ) (hpos : 0 ≤ D.h i x₁)
    (M : ELVWeightProduct D Sc cutoff N Λ x₁) :
    Nonempty (SKM.SuperSumInvTo (k := k) ((φ).app (D.parity i) M δ)
      (fun n => (ρ n).total M δ) (D.parity i) (fun n => n • D.parity i)
      (D.h i x₁).toNat) := by
  have hz : D.h i x₁ = 0 := le_antisymm
    (elvWeightHeight_nonpos_of_absent D cutoff i Λ h₁ hcutoff δ hδ) hpos
  let J := Classical.choice (elvWeightAbsentUnitInverse_nonempty D Sc cutoff N i Λ h₁ h₂ δ hcutoff hδ M)
  have hm : (-D.h i x₁).toNat = 0 := by simp only [hz, neg_zero, Int.toNat_zero]
  have H := emptyFromTo J hm (fun n => (ρ n).total M δ)
    (fun n => (elvWeightCapPower_block_supernatural D Sc cutoff N i Λ h₁ δ n).mem M)
  exact ⟨by simpa only [hz, Int.toNat_zero] using H⟩

  ContentModules D Sc cutoff N (Subtype.val ε)) δ
  (Superfunctor.id k (ELVWeightProduct D Sc cutoff N Λ x₁)) (Superfunctor.mk Ev)

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Prescribed local inverses on entire weight fibres

BE (1.13)–(1.14): supported and absent block inverses assemble on every
output content of the categorical weight. The inverse families are then
bundled in the whole input weight module, retaining the exact native
principal, unit/power and cap/power maps of the Rouquier presentation.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELV
universe u
section Recovery
universe u₀ v₀ w₀
variable {k : Type w₀} {C A : Type u₀} [CommRing k]
  [Category.{v₀} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{v₀} A] [Preadditive A] [Linear k A] [Supercategory k A]
  {F G H : Superfunctor k C A} {p : ZMod 2} {q : ℕ → ZMod 2} {m : ℕ}

private theorem total_supernatural (f : F ⟶ G) (hf : f ∈ parity (R := k) F G p) :
    IsSupernatural k p (F := F.toFunctor) (G := G.toFunctor) (fun X => f.total X) := by
  simpa only [OddMath.HomogeneousSuperfunctorIso.total_eq_app f hf] using f.isSupernatural p

private theorem recover_component (f : F ⟶ G) (hf : f ∈ parity (R := k) F G p) :
    Superfunctor.homMk (F := F) (G := G) (f.isSupernatural p).toSuperNatTrans = f := by
  apply OddMath.HomogeneousSuperfunctorIso.total_ext
  intro X
  exact (OddMath.HomogeneousSuperfunctorIso.homogeneous_total (f.isSupernatural p) X).trans
    (OddMath.HomogeneousSuperfunctorIso.total_eq_app f hf X).symm

private theorem recover_total (f : F ⟶ G) (hf : f ∈ parity (R := k) F G p) :
    Superfunctor.homMk (F := F) (G := G) (total_supernatural f hf).toSuperNatTrans = f := by
  apply OddMath.HomogeneousSuperfunctorIso.total_ext
  intro X
  exact OddMath.HomogeneousSuperfunctorIso.homogeneous_total (total_supernatural f hf) X

private def exactFromFamily (f : G ⟶ F) (g : ℕ → (H ⟶ F))
    (hf : f ∈ parity (R := k) G F p) (hg : ∀ n, g n ∈ parity (R := k) H F (q n))
    (J : ∀ X, SKM.SuperSumInvFrom (k := k) (f.app p X) (fun n => (g n).total X) p q m) :
    SKM.SuperSumInvFrom (k := k) f g p q m := by
  have K := SKM.SuperSumInvFrom.ofSupernaturalComponents (k := k) (F := F) (G := G) (H := H) J (f.isSupernatural p)
    (fun n => total_supernatural (g n) (hg n))
  have heF := recover_component f hf
  have heG := funext (fun n => recover_total (g n) (hg n))
  dsimp only [Superfunctor.homMk] at K heF heG
  rw [heF, heG] at K
  exact K

private def exactToFamily (f : F ⟶ G) (g : ℕ → (F ⟶ H))
    (hf : f ∈ parity (R := k) F G p) (hg : ∀ n, g n ∈ parity (R := k) F H (q n))
    (J : ∀ X, SKM.SuperSumInvTo (k := k) (f.app p X) (fun n => (g n).total X) p q m) :
    SKM.SuperSumInvTo (k := k) f g p q m := by
  have K := SKM.SuperSumInvTo.ofSupernaturalComponents (k := k) (F := F) (G := G) (H := H) J (f.isSupernatural p)
    (fun n => total_supernatural (g n) (hg n))
  have heF := recover_component f hf
  have heG := funext (fun n => recover_total (g n) (hg n))
  dsimp only [Superfunctor.homMk] at K heF heG
  rw [heF, heG] at K
  exact K
end Recovery

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (i : I) (Λ : X) {x₀ x₁ x₂ : X}
  (h₁ : x₀ + D.α i = x₁) (h₂ : x₁ + D.α i = x₂)
local notation "E₁" => elvE D Sc cutoff N i Λ h₁
local notation "F₁" => elvF D Sc cutoff N i Λ h₁
local notation "E₂" => elvE D Sc cutoff N i Λ h₂
local notation "F₂" => elvF D Sc cutoff N i Λ h₂
local notation "φ" => SKM.rouquierMate
  (elvActionAdjunction D Sc cutoff N i Λ h₁)
  (elvActionAdjunction D Sc cutoff N i Λ h₂)
  (elvActionCross D Sc cutoff N i i Λ h₁ h₂ h₁ h₂)
local notation "U" n => elvActionUnit D Sc cutoff N i Λ h₂ ≫
  SKM.rouquierPower (elvActionDot D Sc cutoff N i Λ h₂) n ▷ F₂
local notation "CapField" n => F₁ ◁ SKM.rouquierPower (elvActionDot D Sc cutoff N i Λ h₁) n ≫
  elvActionCounit D Sc cutoff N i Λ h₁

/-- The actual given unit inverse exists on the entire weight fibre. -/
theorem elvWeightLocalUnitInverse_nonempty
    (M : ELVWeightProduct D Sc cutoff N Λ x₁)
    (hcutoff : (cutoff i : ℤ) = D.h i Λ) (hh : D.h i x₁ ≤ 0) :
    Nonempty (SKM.SuperSumInvFrom (k := k) ((φ).app (D.parity i) M)
      (fun n => (U n).total M) (D.parity i) (fun n => n • D.parity i) (-D.h i x₁).toNat) := by
  classical
  have h (δ : WeightBlocks D Λ x₁) :
      Nonempty (SKM.SuperSumInvFrom (k := k) ((φ).app (D.parity i) M δ)
        (fun n => (U n).total M δ) (D.parity i) (fun n => n • D.parity i) (-D.h i x₁).toNat) := by
    by_cases hδ : ∃ β, blockSucc D Λ i h₁ β = δ
    · rcases hδ with ⟨β, rfl⟩
      exact elvWeightSupportedUnitInverse_nonempty D Sc cutoff N i Λ h₁ h₂ β M hcutoff hh
    · exact elvWeightAbsentUnitInverse_nonempty D Sc cutoff N i Λ h₁ h₂ δ hcutoff hδ M
  exact ⟨SKM.SuperSumInvFrom.pi (fun δ => Classical.choice (h δ))⟩

/-- The given cap inverse also includes the derived absent zero-height case. -/
theorem elvWeightLocalCapInverse_nonempty
    (M : ELVWeightProduct D Sc cutoff N Λ x₁)
    (hcutoff : (cutoff i : ℤ) = D.h i Λ) (hh : 0 ≤ D.h i x₁) :
    Nonempty (SKM.SuperSumInvTo (k := k) ((φ).app (D.parity i) M)
      (fun n => (CapField n).total M) (D.parity i) (fun n => n • D.parity i) (D.h i x₁).toNat) := by
  classical
  have h (δ : WeightBlocks D Λ x₁) :
      Nonempty (SKM.SuperSumInvTo (k := k) ((φ).app (D.parity i) M δ)
        (fun n => (CapField n).total M δ) (D.parity i) (fun n => n • D.parity i) (D.h i x₁).toNat) := by
    by_cases hδ : ∃ β, blockSucc D Λ i h₁ β = δ
    · rcases hδ with ⟨β, rfl⟩
      exact elvWeightSupportedCapInverse_nonempty D Sc cutoff N i Λ h₁ h₂ β M hcutoff hh
    · exact elvWeightAbsentCapInverse_nonempty D Sc cutoff N i Λ h₁ h₂ δ hcutoff hδ hh M
  exact ⟨SKM.SuperSumInvTo.pi (fun δ => Classical.choice (h δ))⟩

/-- Literal upper unit/power fields have the whole Rouquier shift profile. -/
theorem elvWeightUnitPower_mem (n : ℕ) :
    (U n) ∈ parity (R := k) _ _ (n • D.parity i) := by
  have hu : elvActionUnit D Sc cutoff N i Λ h₂ ∈ parity (R := k) _ _ 0 :=
    (elvActionAdjunction D Sc cutoff N i Λ h₂).unit_mem
  have hd := SKM.rouquierPower_mem (elvActionDot_mem D Sc cutoff N i Λ h₂) n
  simpa only [zero_add, nsmul_eq_mul] using comp_mem hu (TwoSupercategory.whiskerRight_mem F₂ hd)

/-- The whole input-natural unit inverse retains the exact selected native fields. -/
theorem elvWeightLocalUnitFamily_nonempty
    (hcutoff : (cutoff i : ℤ) = D.h i Λ) (hh : D.h i x₁ ≤ 0) :
    Nonempty (SKM.SuperSumInvFrom (k := k) (φ) (fun n => U n)
      (D.parity i) (fun n => (n : ZMod 2) * D.parity i) (-D.h i x₁).toNat) := by
  exact ⟨(exactFromFamily (φ) (fun n => U n)
    (elvWeightRouquierMate_mem D Sc cutoff N i Λ h₁ h₂)
    (elvWeightUnitPower_mem D Sc cutoff N i Λ h₂)
    (fun M => Classical.choice
      (elvWeightLocalUnitInverse_nonempty D Sc cutoff N i Λ h₁ h₂ M hcutoff hh))).mulProfile⟩

/-- The whole input-natural cap inverse retains the exact selected native fields. -/
theorem elvWeightLocalCapFamily_nonempty
    (hcutoff : (cutoff i : ℤ) = D.h i Λ) (hh : 0 ≤ D.h i x₁) :
    Nonempty (SKM.SuperSumInvTo (k := k) (φ) (fun n => CapField n)
      (D.parity i) (fun n => (n : ZMod 2) * D.parity i) (D.h i x₁).toNat) := by
  exact ⟨(exactToFamily (φ) (fun n => CapField n)
    (elvWeightRouquierMate_mem D Sc cutoff N i Λ h₁ h₂)
    (elvWeightCapPower_mem D Sc cutoff N i Λ h₁)
    (fun M => Classical.choice
      (elvWeightLocalCapInverse_nonempty D Sc cutoff N i Λ h₁ h₂ M hcutoff hh))).mulProfile⟩

end OddMath.QuiverHecke.ELV
end

end

section

/-! # The prescribed local Rouquier action on weight products

BE (1.13)–(1.14): combine the selected weight adjunctions, dots, crossing,
signed slides and constructed local inverse families. No factor-action
or local-inverse existence assumption is supplied.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELV
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (i : I) (Λ : X) {x₀ x₁ x₂ : X}
  (h₁ : x₀ + D.α i = x₁) (h₂ : x₁ + D.α i = x₂)

/-- The selected weight fields form the local Rouquier data with their
actual categorical height and both constructed inverse presentations. -/
theorem elvWeightRouquierLocal_nonempty
    (hcutoff : (cutoff i : ℤ) = D.h i Λ) :
    Nonempty (SKM.SuperRouquierLoc
      (elvActionAdjunction D Sc cutoff N i Λ h₁)
      (elvActionAdjunction D Sc cutoff N i Λ h₂)
      (elvActionDot D Sc cutoff N i Λ h₁)
      (elvActionDot D Sc cutoff N i Λ h₂)
      (elvActionCross D Sc cutoff N i i Λ h₁ h₂ h₁ h₂)
      (D.parity i) (D.h i x₁)) := by
  refine ⟨{
    dot₁_mem := elvActionDot_mem D Sc cutoff N i Λ h₁
    dot₂_mem := elvActionDot_mem D Sc cutoff N i Λ h₂
    cross_mem := ?_
    slide_left := elvActionCross_slideLeft D Sc cutoff N i Λ h₁ h₂
    slide_right := elvActionCross_slideRight D Sc cutoff N i Λ h₁ h₂
    invPos := fun hh => Classical.choice
      (elvWeightLocalCapFamily_nonempty D Sc cutoff N i Λ h₁ h₂ hcutoff hh)
    invNeg := fun hh => Classical.choice
      (elvWeightLocalUnitFamily_nonempty D Sc cutoff N i Λ h₁ h₂ hcutoff hh) }⟩
  simpa only [SKM.zmod2_mul_self] using
    elvActionCross_mem D Sc cutoff N i i Λ h₁ h₂ h₁ h₂

end OddMath.QuiverHecke.ELV
end

end

section

/-! # The prescribed same-colour braid on the weight action

Brundan--Ellis (1.9), the same-colour braid field of `SKM.RouquierFamily`.
Both given crossing whiskerings intertwine through the same selected
triple chart; the direct normalized content braid therefore transports.
Absent predecessor sectors are handled by the actual zero-module support
statement. No crossing-compatibility or invertibility premise is added.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELV
universe u
private theorem intertwine_product
    {C : Type*} [Category* C] {X Y : C} (e : X ⟶ Y)
    (l r : End X) (a b : End Y)
    (hl : l ≫ e = e ≫ a) (hr : r ≫ e = e ≫ b) :
    (l ≫ r) ≫ e = e ≫ (a ≫ b) := by
  rw [Category.assoc, hr, ← Category.assoc, hl, Category.assoc]
private theorem braid_of_comparison
    {C : Type*} [Category* C] {X Y : C} (e : X ≅ Y)
    (l r : End X) (a b : End Y)
    (hl : l ≫ e.hom = e.hom ≫ a) (hr : r ≫ e.hom = e.hom ≫ b)
    (hb : b ≫ a ≫ b = a ≫ b ≫ a) :
    r ≫ l ≫ r = l ≫ r ≫ l := by
  have hleft := intertwine_product e.hom r (l ≫ r) b (a ≫ b) hr
    (intertwine_product e.hom l r a b hl hr)
  have hright := intertwine_product e.hom l (r ≫ l) a (b ≫ a) hl
    (intertwine_product e.hom r l b a hr hl)
  exact (cancel_mono e.hom).1
    (hleft.trans ((congrArg (fun z => e.hom ≫ z) hb).trans hright.symm))
private theorem braid_total_three
    {k : Type u} [CommRing k] {A B : PiSCat.{u, u, u + 1} k}
    (F : A ⟶ B) (f g h : End F) (M : A) :
    (f ≫ g ≫ h).total M = f.total M ≫ g.total M ≫ h.total M := by
  rw [Superfunctor.comp_total, Superfunctor.comp_total]

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (i : I) (Λ : X) {x₀ x₁ x₂ x₃ : X}
  (h₁ : x₀ + D.α i = x₁) (h₂ : x₁ + D.α i = x₂) (h₃ : x₂ + D.α i = x₃)
local notation "E₁" => elvE D Sc cutoff bound i Λ h₁
local notation "E₂" => elvE D Sc cutoff bound i Λ h₂
local notation "E₃" => elvE D Sc cutoff bound i Λ h₃
local notation "t₁" => elvWeightBraidPrefix D Sc cutoff bound i Λ h₁ h₂ h₃
local notation "t₂" => elvWeightBraidSuffix D Sc cutoff bound i Λ h₁ h₂ h₃

/-- The literal given same-colour weight crossings satisfy the braid,
on all product modules and all output blocks, including absent sectors. -/
theorem elvActionCross_braid : t₂ ≫ t₁ ≫ t₂ = t₁ ≫ t₂ ≫ t₁ := by
  apply supernatural_hom_ext_total
  intro M
  funext ε
  have hL := congrFun (braid_total_three (E₁ ≫ E₂ ≫ E₃) t₂ t₁ t₂ M) ε
  have hR := congrFun (braid_total_three (E₁ ≫ E₂ ≫ E₃) t₁ t₂ t₁ M) ε
  by_cases hs : ∃ β, elvBlockSucc₃ D i i i Λ h₁ h₂ h₃ β = ε
  · obtain ⟨β, rfl⟩ := hs
    have hb := contentInduction_sameColour_braid D Sc cutoff bound β.1 i _
      (elvBlockTriple_content_eq D i i i Λ h₁ h₂ h₃ β) (M β)
    have hm := braid_of_comparison
      ((elvWeightTripleComparison D Sc cutoff bound i i i Λ h₁ h₂ h₃ β _ rfl).app M)
      ((t₁).total M (elvBlockSucc₃ D i i i Λ h₁ h₂ h₃ β))
      ((t₂).total M (elvBlockSucc₃ D i i i Λ h₁ h₂ h₃ β))
      ((contentInductionTransform D Sc cutoff bound
        (elvBlockTriple_content_eq D i i i Λ h₁ h₂ h₃ β)
        (elvBlockTriple_content_eq D i i i Λ h₁ h₂ h₃ β)
        (contentNormalizedLeft_mem D Sc i i i)).app (D.parity i * D.parity i) (M β))
      ((contentInductionTransform D Sc cutoff bound
        (elvBlockTriple_content_eq D i i i Λ h₁ h₂ h₃ β)
        (elvBlockTriple_content_eq D i i i Λ h₁ h₂ h₃ β)
        (contentNormalizedRight_mem D Sc i i i)).app (D.parity i * D.parity i) (M β))
      (elvWeightBraidPrefix_comparison D Sc cutoff bound i Λ h₁ h₂ h₃ β M)
      (elvWeightBraidSuffix_comparison D Sc cutoff bound i Λ h₁ h₂ h₃ β M) hb
    exact hL.trans (hm.trans hR.symm)
  · have hz := elvEFunctor_comp₃_isZero D Sc cutoff bound i i i Λ h₁ h₂ h₃ ε hs M
    exact hL.trans ((hz.eq_of_src _ _).trans hR.symm)

/-- This is exactly the same-colour braid field for the independently
chosen `elvRouquierData`, with its prescribed associators and crossings. -/
theorem elvRouquierData_braid :
    let R := elvRouquierData D Sc cutoff bound Λ
    let a := (associator (R.E i h₁) (R.E i h₂) (R.E i h₃)).inv ≫
      R.cross i i h₁ h₂ h₁ h₂ ▷ R.E i h₃ ≫
      (associator (R.E i h₁) (R.E i h₂) (R.E i h₃)).hom
    let b := R.E i h₁ ◁ R.cross i i h₂ h₃ h₂ h₃
    b ≫ a ≫ b = a ≫ b ≫ a :=
  elvActionCross_braid D Sc cutoff bound i Λ h₁ h₂ h₃

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Distinct-colour signed slides in the original-weight action

Brundan--Ellis (1.8), DeformedActionAssembly §6. The two selected pair
charts retain the given crossing and the independently defined dots.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELV
universe u
section Coordinates
variable {k C : Type u} [CommRing k] [Category.{u} C]
  [Preadditive C] [Linear k C] [Supercategory k C]

def ModuleCrossSlide {A B : Superfunctor k C (SVec k)}
    (c : A ⟶ B) (x : A ⟶ A) (y : B ⟶ B) (w : C) (s : k) : Prop :=
  (c.total w).comp (x.total w) = s • (y.total w).comp (c.total w)

def ModuleCrossCoordinateSquare {A B E F : Superfunctor k C (SVec k)}
    (e : A ≅ E) (f : B ≅ F) (c : A ⟶ B) (w : C)
    (c' : E.obj w →ₗ[k] F.obj w) : Prop :=
  (f.hom.total w).comp (c.total w) = c'.comp (e.hom.total w)

private theorem crossSquare_of_total {A B E F : Superfunctor k C (SVec k)}
    (e : A ≅ E) (f : B ≅ F) (c : A ⟶ B) (w : C)
    (c' : E.obj w →ₗ[k] F.obj w)
    (h : c.total w = (moduleIsoLinearEquiv f w).symm.toLinearMap.comp
      (c'.comp (moduleIsoLinearEquiv e w).toLinearMap)) :
    ModuleCrossCoordinateSquare e f c w c' := by
  apply LinearMap.ext
  intro v
  change (moduleIsoLinearEquiv f w) (c.total w v) = c' ((moduleIsoLinearEquiv e w) v)
  rw [h]
  exact (moduleIsoLinearEquiv f w).apply_symm_apply _

private theorem crossSlide_of_squares {A B E F : Superfunctor k C (SVec k)}
    (e : A ≅ E) (f : B ≅ F) (c : A ⟶ B) (x : A ⟶ A) (y : B ⟶ B)
    (w : C) (s : k) (c' : E.obj w →ₗ[k] F.obj w)
    (x' : Module.End k (E.obj w)) (y' : Module.End k (F.obj w))
    (hc : ModuleCrossCoordinateSquare e f c w c')
    (hx : ModuleCoordinateSquare e x w x') (hy : ModuleCoordinateSquare f y w y')
    (h : c'.comp x' = s • y'.comp c') : ModuleCrossSlide c x y w s := by
  apply LinearMap.ext
  intro v
  apply (moduleIsoLinearEquiv f w).injective
  have hc' (z : A.obj w) : (f.hom.total w) (c.total w z) = c' ((e.hom.total w) z) :=
    LinearMap.congr_fun hc z
  have hx' (z : A.obj w) := ModuleCoordinateSquare_apply hx z
  have hy' (z : B.obj w) := ModuleCoordinateSquare_apply hy z
  change (f.hom.total w) (c.total w (x.total w v)) =
    (f.hom.total w) (s • y.total w (c.total w v))
  rw [map_smul, hc', hx', hy', hc']
  exact LinearMap.congr_fun h ((e.hom.total w) v)
private theorem crossSlide_of_isZero {A B : Superfunctor k C (SVec k)}
    (hA : Limits.IsZero A) (c : A ⟶ B) (x : A ⟶ A) (y : B ⟶ B) (w : C) (s : k) :
    ModuleCrossSlide c x y w s := by
  let := moduleValue_subsingleton_of_isZero hA w
  apply LinearMap.ext
  intro v
  have hv : v = 0 := Subsingleton.elim _ _
  change c.total w (x.total w v) = s • y.total w (c.total w v)
  simp only [hv, map_zero, smul_zero]
end Coordinates

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (i j : I) (Λ : X) {x₀ x₁ x₃ : X}
  (h₁ : x₀ + D.α j = x₁) (h₂ : x₁ + D.α i = x₃)

private theorem pair_inner_square_to (β : WeightBlocks D Λ x₀)
    (ε : WeightBlocks D Λ x₃) (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε)
    (M : ELVWeightProduct D Sc cutoff bound Λ x₀) (w : ContentCategory D Sc cutoff bound ε.1) :
    ModuleCoordinateSquare
      ((elvWeightPairComparison D Sc cutoff bound i j Λ h₁ h₂ β ε hε).app M)
      ((elvActionDot D Sc cutoff bound j Λ h₁ ▷ elvE D Sc cutoff bound i Λ h₂).app
        (D.parity j) M ε) w
      (BalancedInduction.transformLinear
        (contentAppendTo_supernatural D Sc cutoff bound
          (elvWeightPair_content_eq D i j Λ h₁ h₂ β ε hε)
          (elvWeightPair_content_eq D i j Λ h₁ h₂ β ε hε)
          (firstDot_parity D Sc j [i])) (M β) w) := by
  cases hε
  have h := elvWeightPairComparison_inner_total D Sc cutoff bound i j Λ h₁ h₂ β M w
  rw [contentInduction_inner_positioned] at h
  exact h

private theorem pair_outer_square_to (β : WeightBlocks D Λ x₀)
    (ε : WeightBlocks D Λ x₃) (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε)
    (M : ELVWeightProduct D Sc cutoff bound Λ x₀) (w : ContentCategory D Sc cutoff bound ε.1) :
    ModuleCoordinateSquare
      ((elvWeightPairComparison D Sc cutoff bound i j Λ h₁ h₂ β ε hε).app M)
      ((elvE D Sc cutoff bound j Λ h₁ ◁ elvActionDot D Sc cutoff bound i Λ h₂).app
        (D.parity i) M ε) w
      (BalancedInduction.transformLinear
        (contentAppendTo_supernatural D Sc cutoff bound
          (elvWeightPair_content_eq D i j Λ h₁ h₂ β ε hε)
          (elvWeightPair_content_eq D i j Λ h₁ h₂ β ε hε)
          (contentPairDot_one_parity D Sc j i)) (M β) w) := by
  cases hε
  have h := elvWeightPairComparison_outer_total D Sc cutoff bound i j Λ h₁ h₂ β M w
  rw [contentInduction_outer_positioned] at h
  exact h
variable {x₂ : X} (h₃ : x₀ + D.α i = x₂) (h₄ : x₂ + D.α j = x₃)

theorem elvWeightDistinct_slideLeft_supported (hij : i ≠ j)
    (β : WeightBlocks D Λ x₀) (M : ELVWeightProduct D Sc cutoff bound Λ x₀)
    (w : ContentCategory D Sc cutoff bound (blockSucc₂ D i j Λ h₁ h₂ β).1) :
    let ε := blockSucc₂ D i j Λ h₁ h₂ β
    ModuleCrossSlide
      ((elvActionCross D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄).app
        (D.parity i * D.parity j) M ε)
      ((elvE D Sc cutoff bound j Λ h₁ ◁ elvActionDot D Sc cutoff bound i Λ h₂).app
        (D.parity i) M ε)
      ((elvActionDot D Sc cutoff bound i Λ h₃ ▷ elvE D Sc cutoff bound j Λ h₄).app
        (D.parity i) M ε) w (sign k (D.parity i * D.parity j)) := by
  dsimp only
  let ε := blockSucc₂ D i j Λ h₁ h₂ β
  let he := blockSucc₂_swap D i j Λ h₁ h₂ h₃ h₄ (β := β) (ε := ε) rfl
  let hs := elvWeightPair_content_eq D i j Λ h₁ h₂ β ε rfl
  let ht := elvWeightPair_content_eq D j i Λ h₃ h₄ β ε he
  let e := (elvWeightPairComparison D Sc cutoff bound i j Λ h₁ h₂ β ε rfl).app M
  let f := (elvWeightPairComparison D Sc cutoff bound j i Λ h₃ h₄ β ε he).app M
  let C := BalancedInduction.transformLinear
    (contentAppendTo_supernatural D Sc cutoff bound ht hs (contentCrossAffine_mem D Sc i j)) (M β) w
  let X := BalancedInduction.transformLinear
    (contentAppendTo_supernatural D Sc cutoff bound hs hs (contentPairDot_one_parity D Sc j i)) (M β) w
  let Y := BalancedInduction.transformLinear
    (contentAppendTo_supernatural D Sc cutoff bound ht ht (firstDot_parity D Sc i [j])) (M β) w
  have hc : ModuleCrossCoordinateSquare e f
      ((elvActionCross D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄).app
        (D.parity i * D.parity j) M ε) w C := by
    apply crossSquare_of_total
    change (elvWeightCrossComponent D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄
      (D.parity i * D.parity j) M ε).total w =
      (moduleIsoLinearEquiv f w).symm.toLinearMap.comp
        (C.comp (moduleIsoLinearEquiv e w).toLinearMap)
    rw [elvWeightCrossComponent_total D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄ β ε rfl M w,
      contentInductionTransform_total]
  apply crossSlide_of_squares e f _ _ _ w _ C X Y
  · exact hc
  · exact pair_outer_square_to D Sc cutoff bound i j Λ h₁ h₂ β ε rfl M w
  · exact pair_inner_square_to D Sc cutoff bound j i Λ h₃ h₄ β ε he M w
  · have h := contentInduction_distinct_slide_left_linear D Sc cutoff bound β.1 hij ε.1 ht hs (M β) w
    have hh := congrArg (fun z => sign k (D.parity i * D.parity j) • z) h
    simpa only [smul_smul, Supercategory.sign_mul_self, one_smul] using hh.symm
theorem elvWeightDistinct_slideRight_supported (hij : i ≠ j)
    (β : WeightBlocks D Λ x₀) (M : ELVWeightProduct D Sc cutoff bound Λ x₀)
    (w : ContentCategory D Sc cutoff bound (blockSucc₂ D i j Λ h₁ h₂ β).1) :
    let ε := blockSucc₂ D i j Λ h₁ h₂ β
    ModuleCrossSlide
      ((elvActionCross D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄).app
        (D.parity i * D.parity j) M ε)
      ((elvActionDot D Sc cutoff bound j Λ h₁ ▷ elvE D Sc cutoff bound i Λ h₂).app
        (D.parity j) M ε)
      ((elvE D Sc cutoff bound i Λ h₃ ◁ elvActionDot D Sc cutoff bound j Λ h₄).app
        (D.parity j) M ε) w (sign k (D.parity i * D.parity j)) := by
  dsimp only
  let ε := blockSucc₂ D i j Λ h₁ h₂ β
  let he := blockSucc₂_swap D i j Λ h₁ h₂ h₃ h₄ (β := β) (ε := ε) rfl
  let hs := elvWeightPair_content_eq D i j Λ h₁ h₂ β ε rfl
  let ht := elvWeightPair_content_eq D j i Λ h₃ h₄ β ε he
  let e := (elvWeightPairComparison D Sc cutoff bound i j Λ h₁ h₂ β ε rfl).app M
  let f := (elvWeightPairComparison D Sc cutoff bound j i Λ h₃ h₄ β ε he).app M
  let C := BalancedInduction.transformLinear
    (contentAppendTo_supernatural D Sc cutoff bound ht hs (contentCrossAffine_mem D Sc i j)) (M β) w
  let X := BalancedInduction.transformLinear
    (contentAppendTo_supernatural D Sc cutoff bound hs hs (firstDot_parity D Sc j [i])) (M β) w
  let Y := BalancedInduction.transformLinear
    (contentAppendTo_supernatural D Sc cutoff bound ht ht (contentPairDot_one_parity D Sc i j)) (M β) w
  have hc : ModuleCrossCoordinateSquare e f
      ((elvActionCross D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄).app
        (D.parity i * D.parity j) M ε) w C := by
    apply crossSquare_of_total
    change (elvWeightCrossComponent D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄
      (D.parity i * D.parity j) M ε).total w =
      (moduleIsoLinearEquiv f w).symm.toLinearMap.comp
        (C.comp (moduleIsoLinearEquiv e w).toLinearMap)
    rw [elvWeightCrossComponent_total D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄ β ε rfl M w,
      contentInductionTransform_total]
  apply crossSlide_of_squares e f _ _ _ w _ C X Y
  · exact hc
  · exact pair_inner_square_to D Sc cutoff bound i j Λ h₁ h₂ β ε rfl M w
  · exact pair_outer_square_to D Sc cutoff bound j i Λ h₃ h₄ β ε he M w
  · exact contentInduction_distinct_slide_right_linear D Sc cutoff bound β.1 hij ε.1 ht hs (M β) w

theorem elvWeightDistinct_slideLeft_component (hij : i ≠ j)
    (M : ELVWeightProduct D Sc cutoff bound Λ x₀) (ε : WeightBlocks D Λ x₃)
    (w : ContentCategory D Sc cutoff bound ε.1) :
    ModuleCrossSlide
      ((elvActionCross D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄).app
        (D.parity i * D.parity j) M ε)
      ((elvE D Sc cutoff bound j Λ h₁ ◁ elvActionDot D Sc cutoff bound i Λ h₂).app
        (D.parity i) M ε)
      ((elvActionDot D Sc cutoff bound i Λ h₃ ▷ elvE D Sc cutoff bound j Λ h₄).app
        (D.parity i) M ε) w (sign k (D.parity i * D.parity j)) := by
  by_cases hε : ∃ β, blockSucc₂ D i j Λ h₁ h₂ β = ε
  · obtain ⟨β, rfl⟩ := hε
    exact elvWeightDistinct_slideLeft_supported D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄ hij β M w
  · exact crossSlide_of_isZero
      (elvEFunctor_comp₂_isZero D Sc cutoff bound i j Λ h₁ h₂ ε hε M) _ _ _ w _

theorem elvWeightDistinct_slideRight_component (hij : i ≠ j)
    (M : ELVWeightProduct D Sc cutoff bound Λ x₀) (ε : WeightBlocks D Λ x₃)
    (w : ContentCategory D Sc cutoff bound ε.1) :
    ModuleCrossSlide
      ((elvActionCross D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄).app
        (D.parity i * D.parity j) M ε)
      ((elvActionDot D Sc cutoff bound j Λ h₁ ▷ elvE D Sc cutoff bound i Λ h₂).app
        (D.parity j) M ε)
      ((elvE D Sc cutoff bound i Λ h₃ ◁ elvActionDot D Sc cutoff bound j Λ h₄).app
        (D.parity j) M ε) w (sign k (D.parity i * D.parity j)) := by
  by_cases hε : ∃ β, blockSucc₂ D i j Λ h₁ h₂ β = ε
  · obtain ⟨β, rfl⟩ := hε
    exact elvWeightDistinct_slideRight_supported D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄ hij β M w
  · exact crossSlide_of_isZero
      (elvEFunctor_comp₂_isZero D Sc cutoff bound i j Λ h₁ h₂ ε hε M) _ _ _ w _

end OddMath.QuiverHecke.ELV
end

end
