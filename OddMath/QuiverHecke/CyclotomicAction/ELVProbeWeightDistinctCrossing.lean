import OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightPairInduction
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeEvaluatedDistinctCrossing

/-! # Positive distinct crossings on OLD probe weight spaces

Brundan–Ellis Definition 1.5, (1.7)–(1.9): construct the positive
distinct crossing on the actual weight-product induction functors. The
four append functors retain their canonical stored contents and common
upper target. Absent double predecessors contribute the actual zero map.
The distinct mate inverse is a separate transport obligation.
-/
noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
open ELVOld ELVOld.BalancedInduction ELVOld.CyclotomicCrossingTensor CyclotomicAction
universe u v w t z

private def distinctTransport
    {k : Type u} [CommRing k] {C : Type v} [Category.{w} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {A : Type t} [Category.{z} A] [Preadditive A] [Linear k A] [Supercategory k A]
    {F G F' G' : C ⥤ A} (hs : F = F') (ht : G = G')
    (f : SuperNatTrans k F' G') : SuperNatTrans k F G := by
  cases hs
  cases ht
  exact f

private theorem distinctTransport_homogeneous
    {k : Type u} [CommRing k] {C : Type v} [Category.{w} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {A : Type t} [Category.{z} A] [Preadditive A] [Linear k A] [Supercategory k A]
    {F G F' G' : C ⥤ A} (hs : F = F') (ht : G = G')
    (f : SuperNatTrans k F' G') {p : ZMod 2} (hf : f.IsHomogeneous p) :
    (distinctTransport hs ht f).IsHomogeneous p := by
  cases hs
  cases ht
  exact hf

private theorem distinctTransport_component
    {k : Type u} [CommRing k] {C : Type v} [Category.{w} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {A : Type t} [Category.{z} A] [Preadditive A] [Linear k A] [Supercategory k A]
    {F G F' G' : C ⥤ A} (hs : F = F') (ht : G = G')
    (f : SuperNatTrans k F' G') (p : ZMod 2) (N : C) :
    (distinctTransport hs ht f).app p N =
      eqToHom (congrArg (fun H : C ⥤ A => H.obj N) hs) ≫ f.app p N ≫
        eqToHom (congrArg (fun H : C ⥤ A => H.obj N) ht).symm := by
  cases hs
  cases ht
  simp only [distinctTransport, eqToHom_refl, Category.id_comp, Category.comp_id]

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)

section Pair
variable (i j : I) (Λ : X) {x₀ x₁ xu : X}
  (h₁ : x₀ + D.α j = x₁) (h₂ : x₁ + D.α i = xu)

/-- The common upper stored list carries the actual two-successor content. -/
theorem probeOldPairUpper_perm (β : WeightBlocks D Λ x₀) (ε : WeightBlocks D Λ xu)
    (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε) :
    (i :: (blockSucc D Λ j h₁ β).1.toList).Perm ε.1.toList := by
  apply Multiset.coe_eq_coe.mp
  rw [Multiset.coe_toList]
  change {i} + ((blockSucc D Λ j h₁ β).1.toList : Multiset I) = ε.1
  rw [Multiset.coe_toList]
  exact congrArg Subtype.val hε

/-- The second OLD append retains the specified common upper target. -/
abbrev probeOldPairUpperAppend (β : WeightBlocks D Λ x₀) (ε : WeightBlocks D Λ xu)
    (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε) :=
  oldContentAppendTo D Sc (probeCutoff D m) (blockSucc D Λ j h₁ β).1.toList i ε.1.toList
    (probeOldPairUpper_perm D i j Λ h₁ h₂ β ε hε)

/-- Both actual block inductions with their prescribed common upper list. -/
abbrev probeOldBlockPairIndTo (β : WeightBlocks D Λ x₀) (ε : WeightBlocks D Λ xu)
    (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε) :=
  (probeOldBlockInd D Sc m j Λ h₁ β).comp
    (⟨probeEvaluatedAppendTo D Sc m (blockSucc D Λ j h₁ β).1.toList i ε.1.toList
      (probeOldPairUpper_perm D i j Λ h₁ h₂ β ε hε)⟩ :
      Superfunctor k (ProbeCanonicalModules D Sc m (blockSucc D Λ j h₁ β).1)
        (ProbeCanonicalModules D Sc m ε.1))

/-- The global coordinate equals the specified stored-target block pair. -/
theorem probeOldEFunctor_comp₂_to (β : WeightBlocks D Λ x₀) (ε : WeightBlocks D Λ xu)
    (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε) :
    probeOldEFunctor D Sc m j Λ h₁ ⋙
        (probeOldInductionComponent D Sc m i Λ h₂ ε).toFunctor =
      (probeOldBlockEval D Sc m Λ β).toFunctor ⋙
        (probeOldBlockPairIndTo D Sc m i j Λ h₁ h₂ β ε hε).toFunctor := by
  subst ε
  exact probeOldEFunctor_comp₂_blockSucc D Sc m i j Λ h₁ h₂ β
end Pair

section Crossing
variable (i j : I) (Λ : X) {x₀ xj xi xu : X}
  (h₁ : x₀ + D.α j = xj) (h₂ : xj + D.α i = xu)
  (h₃ : x₀ + D.α i = xi) (h₄ : xi + D.α j = xu)
local notation "sw" => blockSucc₂_swap D i j Λ h₁ h₂ h₃ h₄
local notation "J" => probeOldBlockAppend D Sc m i Λ h₃
local notation "K" => probeOldBlockAppend D Sc m j Λ h₁
local notation "L" => (fun β ε hε => probeOldPairUpperAppend D Sc m j i Λ h₃ h₄ β ε (sw hε))
local notation "U" => probeOldPairUpperAppend D Sc m i j Λ h₁ h₂

/-- The same positive OLD crossing, at all four canonical stored contents. -/
def probeOldBlockDistinctCrossArrow (β : WeightBlocks D Λ x₀) (ε : WeightBlocks D Λ xu)
    (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε)
    (s : OldContentCategory D Sc (probeCutoff D m) β.1.toList) :
    ((J β) ⋙ (L β ε hε)).obj s ⟶ ((K β) ⋙ (U β ε hε)).obj s :=
  Distinct.crossComponent D Sc (probeCutoff D m) j i s.obj

theorem probeOldBlockDistinctCrossArrow_supernatural (β : WeightBlocks D Λ x₀)
    (ε : WeightBlocks D Λ xu) (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε) :
    IsSupernatural k (D.parity i * D.parity j)
      (probeOldBlockDistinctCrossArrow D Sc m i j Λ h₁ h₂ h₃ h₄ β ε hε) := by
  have h : IsSupernatural k (D.parity j * D.parity i)
      (probeOldBlockDistinctCrossArrow D Sc m i j Λ h₁ h₂ h₃ h₄ β ε hε) := {
    mem := fun s => (Distinct.cross_supernatural D Sc (probeCutoff D m) j i).mem s.obj
    naturality := fun hf =>
      (Distinct.cross_supernatural D Sc (probeCutoff D m) j i).naturality hf }
  simpa only [mul_comm] using h
local notation "hc" =>
  probeOldBlockDistinctCrossArrow_supernatural D Sc m i j Λ h₁ h₂ h₃ h₄

private theorem blockDistinctSource_closed (β : WeightBlocks D Λ x₀) (ε : WeightBlocks D Λ xu)
    (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε)
    (N : Superfunctor k (OldContentCategory D Sc (probeCutoff D m) β.1.toList) (SVec k))
    (hN : ProbeEvaluatesCoefficients D m Sc β.1.toList N) :
    ProbeEvaluatesCoefficients D m Sc ε.1.toList
      ((induction (K β) ⋙ induction (U β ε hε)).obj N) :=
  ((probeOldBlockPairIndTo D Sc m i j Λ h₁ h₂ β ε hε).obj ⟨N, hN⟩).property

private theorem blockDistinctTarget_closed (β : WeightBlocks D Λ x₀) (ε : WeightBlocks D Λ xu)
    (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε)
    (N : Superfunctor k (OldContentCategory D Sc (probeCutoff D m) β.1.toList) (SVec k))
    (hN : ProbeEvaluatesCoefficients D m Sc β.1.toList N) :
    ProbeEvaluatesCoefficients D m Sc ε.1.toList
      ((induction (J β) ⋙ induction (L β ε hε)).obj N) :=
  ((probeOldBlockPairIndTo D Sc m j i Λ h₃ h₄ β ε (sw hε)).obj ⟨N, hN⟩).property

/-- The selected positive crossing of the two stored-target block pairs. -/
def probeOldBlockDistinctCross (β : WeightBlocks D Λ x₀) (ε : WeightBlocks D Λ xu)
    (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε) :
    probeOldBlockPairIndTo D Sc m i j Λ h₁ h₂ β ε hε ⟶
      probeOldBlockPairIndTo D Sc m j i Λ h₃ h₄ β ε (sw hε) :=
  fullLiftTrans (ProbeEvaluatesCoefficients D m Sc β.1.toList)
    (ProbeEvaluatesCoefficients D m Sc ε.1.toList)
    (blockDistinctSource_closed D Sc m i j Λ h₁ h₂ β ε hε)
    (blockDistinctTarget_closed D Sc m i j Λ h₁ h₂ h₃ h₄ β ε hε)
    (rectangularCrossComponent_supernatural (J β) (K β) (L β ε hε) (U β ε hε)
      (hc β ε hε)).toSuperNatTrans

theorem probeOldBlockDistinctCross_mem (β : WeightBlocks D Λ x₀) (ε : WeightBlocks D Λ xu)
    (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε) :
    probeOldBlockDistinctCross D Sc m i j Λ h₁ h₂ h₃ h₄ β ε hε ∈
      parity (R := k) _ _ (D.parity i * D.parity j) :=
  Superfunctor.mem_parity_iff_isHomogeneous.mpr
    (fullLiftTrans_homogeneous (ProbeEvaluatesCoefficients D m Sc β.1.toList)
      (ProbeEvaluatesCoefficients D m Sc ε.1.toList)
      (blockDistinctSource_closed D Sc m i j Λ h₁ h₂ β ε hε)
      (blockDistinctTarget_closed D Sc m i j Λ h₁ h₂ h₃ h₄ β ε hε) _
      (rectangularCrossComponent_supernatural (J β) (K β) (L β ε hε) (U β ε hε)
        (hc β ε hε)).toSuperNatTrans_isHomogeneous)

/-- Each parity component retains the literal OLD positive rectangular crossing. -/
theorem probeOldBlockDistinctCross_native_app (β : WeightBlocks D Λ x₀)
    (ε : WeightBlocks D Λ xu) (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε)
    (p : ZMod 2) (N : ProbeCanonicalModules D Sc m β.1) :
    ((probeOldBlockDistinctCross D Sc m i j Λ h₁ h₂ h₃ h₄ β ε hε).app p N).hom =
      (rectangularCrossComponent_supernatural (J β) (K β) (L β ε hε) (U β ε hε)
        (hc β ε hε)).toSuperNatTrans.app p N.obj := rfl

local notation "Fs" => (fun ε => probeOldEFunctor D Sc m j Λ h₁ ⋙
  Superfunctor.toFunctor (probeOldInductionComponent D Sc m i Λ h₂ ε))
local notation "Ft" => (fun ε => probeOldEFunctor D Sc m i Λ h₃ ⋙
  Superfunctor.toFunctor (probeOldInductionComponent D Sc m j Λ h₄ ε))

/-- Transport the constructed block crossing through both actual product coordinates. -/
def probeOldWeightDistinctCrossVia (β : WeightBlocks D Λ x₀) (ε : WeightBlocks D Λ xu)
    (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε) : SuperNatTrans k (Fs ε) (Ft ε) :=
  distinctTransport (probeOldEFunctor_comp₂_to D Sc m i j Λ h₁ h₂ β ε hε)
    (probeOldEFunctor_comp₂_to D Sc m j i Λ h₃ h₄ β ε (sw hε))
    (Superfunctor.whiskerLeft (probeOldBlockEval D Sc m Λ β)
      (probeOldBlockDistinctCross D Sc m i j Λ h₁ h₂ h₃ h₄ β ε hε))

theorem probeOldWeightDistinctCrossVia_homogeneous (β : WeightBlocks D Λ x₀)
    (ε : WeightBlocks D Λ xu) (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε) :
    (probeOldWeightDistinctCrossVia D Sc m i j Λ h₁ h₂ h₃ h₄ β ε hε).IsHomogeneous
      (D.parity i * D.parity j) :=
  distinctTransport_homogeneous _ _ _
    (Superfunctor.mem_parity_iff_isHomogeneous.mp
      (Superfunctor.whiskerLeft_mem (probeOldBlockEval D Sc m Λ β)
        (probeOldBlockDistinctCross_mem D Sc m i j Λ h₁ h₂ h₃ h₄ β ε hε)))

/-- The supported component uses precisely the two selected product-coordinate equalities. -/
theorem probeOldWeightDistinctCrossVia_component (β : WeightBlocks D Λ x₀)
    (ε : WeightBlocks D Λ xu) (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε)
    (p : ZMod 2) (N : ProbeOldWeightProduct D Sc m Λ x₀) :
    (probeOldWeightDistinctCrossVia D Sc m i j Λ h₁ h₂ h₃ h₄ β ε hε).app p N =
      eqToHom (Functor.congr_obj (probeOldEFunctor_comp₂_to D Sc m i j Λ h₁ h₂ β ε hε) N) ≫
        (probeOldBlockDistinctCross D Sc m i j Λ h₁ h₂ h₃ h₄ β ε hε).app p (N β) ≫
      eqToHom (Functor.congr_obj
        (probeOldEFunctor_comp₂_to D Sc m j i Λ h₃ h₄ β ε (sw hε)) N).symm :=
  distinctTransport_component _ _ _ p N

theorem probeOldWeightDistinctCrossVia_eq (β β' : WeightBlocks D Λ x₀)
    (ε : WeightBlocks D Λ xu) (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε)
    (hε' : blockSucc₂ D i j Λ h₁ h₂ β' = ε) :
    probeOldWeightDistinctCrossVia D Sc m i j Λ h₁ h₂ h₃ h₄ β ε hε =
      probeOldWeightDistinctCrossVia D Sc m i j Λ h₁ h₂ h₃ h₄ β' ε hε' := by
  obtain rfl := blockSucc₂_injective D i j Λ h₁ h₂ (hε.trans hε'.symm)
  rfl

/-- The actual weight-product crossing component, zero at absent predecessors. -/
def probeOldWeightDistinctCrossComponent (p : ZMod 2)
    (N : ProbeOldWeightProduct D Sc m Λ x₀) (ε : WeightBlocks D Λ xu) :
    (Fs ε).obj N ⟶ (Ft ε).obj N :=
  if hε : ∃ β, blockSucc₂ D i j Λ h₁ h₂ β = ε then
    (probeOldWeightDistinctCrossVia D Sc m i j Λ h₁ h₂ h₃ h₄ hε.choose ε hε.choose_spec).app p N
  else 0

theorem probeOldWeightDistinctCrossComponent_of (p : ZMod 2)
    (N : ProbeOldWeightProduct D Sc m Λ x₀) (β : WeightBlocks D Λ x₀)
    (ε : WeightBlocks D Λ xu) (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε) :
    probeOldWeightDistinctCrossComponent D Sc m i j Λ h₁ h₂ h₃ h₄ p N ε =
      (probeOldWeightDistinctCrossVia D Sc m i j Λ h₁ h₂ h₃ h₄ β ε hε).app p N := by
  unfold probeOldWeightDistinctCrossComponent
  split
  · rename_i hchoice
    rw [probeOldWeightDistinctCrossVia_eq D Sc m i j Λ h₁ h₂ h₃ h₄ hchoice.choose β ε hchoice.choose_spec hε]
  · rename_i hn
    exact absurd (⟨β, hε⟩ : ∃ β, blockSucc₂ D i j Λ h₁ h₂ β = ε) hn

theorem probeOldWeightDistinctCrossComponent_mem (p : ZMod 2)
    (N : ProbeOldWeightProduct D Sc m Λ x₀) (ε : WeightBlocks D Λ xu) :
    probeOldWeightDistinctCrossComponent D Sc m i j Λ h₁ h₂ h₃ h₄ p N ε ∈
      parity (R := k) _ _ p := by
  unfold probeOldWeightDistinctCrossComponent
  split
  · exact SuperNatTrans.app_mem _ p N
  · exact Submodule.zero_mem _

theorem probeOldWeightDistinctCrossComponent_naturality (p : ZMod 2) (ε : WeightBlocks D Λ xu)
    {N N' : ProbeOldWeightProduct D Sc m Λ x₀} {q : ZMod 2} (f : N ⟶ N')
    (hf : f ∈ parity (R := k) _ _ q) :
    (Fs ε).map f ≫ probeOldWeightDistinctCrossComponent D Sc m i j Λ h₁ h₂ h₃ h₄ p N' ε =
      koszulSign p q • (probeOldWeightDistinctCrossComponent D Sc m i j Λ h₁ h₂ h₃ h₄ p N ε ≫
        (Ft ε).map f) := by
  by_cases hε : ∃ β, blockSucc₂ D i j Λ h₁ h₂ β = ε
  · obtain ⟨β, hβ⟩ := hε
    rw [probeOldWeightDistinctCrossComponent_of D Sc m i j Λ h₁ h₂ h₃ h₄ p N β ε hβ,
      probeOldWeightDistinctCrossComponent_of D Sc m i j Λ h₁ h₂ h₃ h₄ p N' β ε hβ]
    exact (probeOldWeightDistinctCrossVia D Sc m i j Λ h₁ h₂ h₃ h₄ β ε hβ).naturality p f hf
  · exact (probeOldEFunctor_comp₂_isZero D Sc m i j Λ h₁ h₂ ε hε N).eq_of_src _ _

/-- The positive distinct crossing on the whole original-weight product. -/
def probeOldWeightDistinctCross : SuperNatTrans k
    (probeOldEFunctor D Sc m j Λ h₁ ⋙ probeOldEFunctor D Sc m i Λ h₂)
    (probeOldEFunctor D Sc m i Λ h₃ ⋙ probeOldEFunctor D Sc m j Λ h₄) where
  app p N ε := probeOldWeightDistinctCrossComponent D Sc m i j Λ h₁ h₂ h₃ h₄ p N ε
  app_mem p N ε := probeOldWeightDistinctCrossComponent_mem D Sc m i j Λ h₁ h₂ h₃ h₄ p N ε
  naturality p _ _ _ f hf := funext fun ε =>
    probeOldWeightDistinctCrossComponent_naturality D Sc m i j Λ h₁ h₂ h₃ h₄ p ε f hf

theorem probeOldWeightDistinctCross_homogeneous :
    (probeOldWeightDistinctCross D Sc m i j Λ h₁ h₂ h₃ h₄).IsHomogeneous
      (D.parity i * D.parity j) := by
  intro q hq
  funext N ε
  change probeOldWeightDistinctCrossComponent D Sc m i j Λ h₁ h₂ h₃ h₄ q N ε = 0
  by_cases hε : ∃ β, blockSucc₂ D i j Λ h₁ h₂ β = ε
  · obtain ⟨β, hβ⟩ := hε
    rw [probeOldWeightDistinctCrossComponent_of D Sc m i j Λ h₁ h₂ h₃ h₄ q N β ε hβ]
    exact congrFun (probeOldWeightDistinctCrossVia_homogeneous D Sc m i j Λ h₁ h₂ h₃ h₄ β ε hβ q hq) N
  · simp only [probeOldWeightDistinctCrossComponent, dite_eq_right hε]

/-- The prescribed crossing as a homogeneous two-morphism in the action target. -/
def probeOldActionDistinctCross :
    probeOldE D Sc m j Λ h₁ ≫ probeOldE D Sc m i Λ h₂ ⟶
      probeOldE D Sc m i Λ h₃ ≫ probeOldE D Sc m j Λ h₄ :=
  probeOldWeightDistinctCross D Sc m i j Λ h₁ h₂ h₃ h₄

theorem probeOldActionDistinctCross_mem :
    probeOldActionDistinctCross D Sc m i j Λ h₁ h₂ h₃ h₄ ∈ parity (R := k) _ _
      (D.parity i * D.parity j) :=
  Superfunctor.mem_parity_iff_isHomogeneous.mpr
    (probeOldWeightDistinctCross_homogeneous D Sc m i j Λ h₁ h₂ h₃ h₄)
end Crossing
end OddMath.QuiverHecke
