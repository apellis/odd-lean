import OddMath.QuiverHecke.CyclotomicAction.WeightMixed
import OddMath.QuiverHecke.CyclotomicAction.ContentAppend
import OddMath.QuiverHecke.CyclotomicAction.AppendMackey
import OddMath.QuiverHecke.CyclotomicAction.ContentModule
import OddMath.QuiverHecke.CyclotomicAction.InductionMixed
import OddMath.QuiverHecke.CyclotomicAction.DistinctCrossing
import OddMath.Algebra.HomogeneousSuperfunctorIso
import OddMath.QuiverHecke.CyclotomicAction.ContentMatrix
import OddMath.QuiverHecke.CyclotomicAction.InductionGridMatrix
import OddMath.QuiverHecke.CyclotomicAction.ProbeVacuumCharts
import OddMath.QuiverHecke.CyclotomicAction.EvenInputMatrix
import OddMath.QuiverHecke.CyclotomicAction.InductionGridRouquier

/-!
# Content hom

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # Exact-content Hom functors inside the original weight products

The formal support input F4 and (A1) of `SwappedActionAssembly.md`.
Projection at the chosen probe block and zero extension at the chosen
reservoir block realize arbitrary functors on those exact content categories.
No assertion that all whole-weight Hom functors have this support is made.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped Classical
namespace OddMath.QuiverHecke.ELVOld.ContentHomSupport
open CyclotomicAction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (cutoff : I → ℕ) (bound : ℕ) {ΛP ΛR x y : X}
  (β : WeightBlocks D ΛP x) (γ : WeightBlocks D ΛR y)

/-- The exact-content Hom category prescribed in (A1). -/
abbrev Hom := Superfunctor k (ProbeCanonicalModules D Sc m β.1)
  (ContentModules D Sc cutoff bound γ.1)

/-- Input projection and one output component of zero extension. -/
def component (G : Hom D Sc m cutoff bound β γ) (δ : WeightBlocks D ΛR y) :
    Superfunctor k (ProbeOldWeightProduct D Sc m ΛP x)
      (ContentModules D Sc cutoff bound δ.1) :=
  if h : δ = γ then by
    subst δ
    exact (probeOldBlockEval D Sc m ΛP β).comp G
  else ⟨elvZeroFunctor D Sc cutoff bound δ.1⟩

def functor (G : Hom D Sc m cutoff bound β γ) :
    ProbeOldWeightProduct D Sc m ΛP x ⥤ ELVWeightProduct D Sc cutoff bound ΛR y :=
  Functor.pi' fun δ => (component D Sc m cutoff bound β γ G δ).toFunctor

instance (G : Hom D Sc m cutoff bound β γ) :
    (functor D Sc m cutoff bound β γ G).Additive where
  map_add := funext fun δ => (component D Sc m cutoff bound β γ G δ).toFunctor.map_add
instance (G : Hom D Sc m cutoff bound β γ) :
    (functor D Sc m cutoff bound β γ G).Linear k where
  map_smul f r := funext fun δ => (component D Sc m cutoff bound β γ G δ).toFunctor.map_smul r f
instance (G : Hom D Sc m cutoff bound β γ) :
    IsSuperfunctor k (functor D Sc m cutoff bound β γ G) where
  map_mem hf δ := IsSuperfunctor.map_mem
    (F := (component D Sc m cutoff bound β γ G δ).toFunctor) hf

/-- The full original-weight realization retains every other block as zero. -/
def realization (G : Hom D Sc m cutoff bound β γ) :
    probeOldWeightSpace D Sc m ΛP x ⟶ elvWeightSpace D Sc cutoff bound ΛR y :=
  ⟨functor D Sc m cutoff bound β γ G⟩

theorem component_selected (G : Hom D Sc m cutoff bound β γ) :
    component D Sc m cutoff bound β γ G γ = (probeOldBlockEval D Sc m ΛP β).comp G := by
  simp [component]

theorem obj_selected (G : Hom D Sc m cutoff bound β γ)
    (M : ProbeOldWeightProduct D Sc m ΛP x) :
    ((realization D Sc m cutoff bound β γ G).obj M) γ = G.obj (M β) := by
  change (component D Sc m cutoff bound β γ G γ).obj M = _
  rw [component_selected]
  rfl

theorem obj_off_isZero (G : Hom D Sc m cutoff bound β γ)
    (M : ProbeOldWeightProduct D Sc m ΛP x) (δ : WeightBlocks D ΛR y) (hδ : δ ≠ γ) :
    Limits.IsZero (((realization D Sc m cutoff bound β γ G).obj M) δ) := by
  change Limits.IsZero ((component D Sc m cutoff bound β γ G δ).obj M)
  simp only [component, dite_eq_right hδ, Superfunctor.obj]
  exact elvZeroModule_isZero D Sc cutoff bound δ.1

private theorem map_isZero {C C' : Type*} [Category C] [Category C']
    [Preadditive C] [Preadditive C'] (F : C ⥤ C') [F.Additive]
    (M : C) (hM : Limits.IsZero M) : Limits.IsZero (F.obj M) := by
  apply (Limits.IsZero.iff_id_eq_zero _).mpr
  rw [← F.map_id, (Limits.IsZero.iff_id_eq_zero _).mp hM, F.map_zero]

/-- Vanishing of the selected input block kills every output block. -/
theorem obj_isZero_of_input (G : Hom D Sc m cutoff bound β γ)
    (M : ProbeOldWeightProduct D Sc m ΛP x) (hM : Limits.IsZero (M β))
    (δ : WeightBlocks D ΛR y) :
    Limits.IsZero (((realization D Sc m cutoff bound β γ G).obj M) δ) := by
  by_cases hδ : δ = γ
  · subst δ
    rw [obj_selected]
    exact map_isZero G.toFunctor _ hM
  · exact obj_off_isZero D Sc m cutoff bound β γ G M δ hδ

/-- Reservoir induction preserves exact output support, including all collisions. -/
theorem postE_off_isZero (i : I) {y' : X} (h : y + D.α i = y')
    (G : Hom D Sc m cutoff bound β γ) (M : ProbeOldWeightProduct D Sc m ΛP x)
    (δ : WeightBlocks D ΛR y') (hδ : δ ≠ blockSucc D ΛR i h γ) :
    Limits.IsZero (((elvE D Sc cutoff bound i ΛR h).obj
      ((realization D Sc m cutoff bound β γ G).obj M)) δ) := by
  change Limits.IsZero ((elvInductionComponent D Sc cutoff bound i ΛR h δ).obj _)
  by_cases hp : ∃ ε, blockSucc D ΛR i h ε = δ
  · obtain ⟨ε, rfl⟩ := hp
    rw [elvInductionComponent_obj_blockSucc]
    apply map_isZero
    exact obj_off_isZero D Sc m cutoff bound β γ G M ε
      (fun he => hδ (congrArg (blockSucc D ΛR i h) he))
  · exact elvInductionComponent_isZero D Sc cutoff bound i ΛR h δ hp _

/-- Reservoir restriction preserves exact predecessor support. -/
theorem postF_off_isZero (i : I) {y' : X} (h : y + D.α i = y')
    (G : Hom D Sc m cutoff bound β (blockSucc D ΛR i h γ))
    (M : ProbeOldWeightProduct D Sc m ΛP x) (δ : WeightBlocks D ΛR y) (hδ : δ ≠ γ) :
    Limits.IsZero (((elvF D Sc cutoff bound i ΛR h).obj
      ((realization D Sc m cutoff bound β (blockSucc D ΛR i h γ) G).obj M)) δ) := by
  change Limits.IsZero ((elvBlockRes D Sc cutoff bound i ΛR h δ).obj
    (((realization D Sc m cutoff bound β (blockSucc D ΛR i h γ) G).obj M)
      (blockSucc D ΛR i h δ)))
  apply map_isZero
  exact obj_off_isZero D Sc m cutoff bound β (blockSucc D ΛR i h γ) G M _
    (fun he => hδ (blockSucc_injective D ΛR i h he))

/-- A reservoir output missing i has zero restriction on every retained block. -/
theorem postF_absent_isZero (i : I) {y₀ : X} (h : y₀ + D.α i = y)
    (G : Hom D Sc m cutoff bound β γ) (hi : i ∉ γ.1)
    (M : ProbeOldWeightProduct D Sc m ΛP x) (δ : WeightBlocks D ΛR y₀) :
    Limits.IsZero (((elvF D Sc cutoff bound i ΛR h).obj
      ((realization D Sc m cutoff bound β γ G).obj M)) δ) := by
  change Limits.IsZero ((elvBlockRes D Sc cutoff bound i ΛR h δ).obj
    (((realization D Sc m cutoff bound β γ G).obj M) (blockSucc D ΛR i h δ)))
  apply map_isZero
  exact obj_off_isZero D Sc m cutoff bound β γ G M _
    (fun he => hi ((exists_blockSucc_iff D ΛR i h γ).mp ⟨δ, he⟩))

/-- A probe input block missing i kills precomposition by induction on
all output blocks; no original-weight injectivity is used. -/
theorem preE_absent_isZero (i : I) {x₀ : X} (h : x₀ + D.α i = x)
    (G : Hom D Sc m cutoff bound β γ) (hi : i ∉ β.1)
    (M : ProbeOldWeightProduct D Sc m ΛP x₀) (δ : WeightBlocks D ΛR y) :
    Limits.IsZero (((realization D Sc m cutoff bound β γ G).obj
      ((probeOldE D Sc m i ΛP h).obj M)) δ) := by
  apply obj_isZero_of_input
  exact probeOldInductionComponent_isZero D Sc m i ΛP h β
    (fun ⟨ε, he⟩ => hi ((exists_blockSucc_iff D ΛP i h β).mp ⟨ε, he⟩)) M

/-- The selected post-induction component equality holds on all maps. -/
theorem postE_component (i : I) {y' : X} (h : y + D.α i = y')
    (G : Hom D Sc m cutoff bound β γ) :
    ((realization D Sc m cutoff bound β γ G).comp (elvE D Sc cutoff bound i ΛR h)).comp
      (elvBlockEval D Sc cutoff bound ΛR (blockSucc D ΛR i h γ)) =
    ((probeOldBlockEval D Sc m ΛP β).comp G).comp
      (elvBlockInd D Sc cutoff bound i ΛR h γ) := by
  change (realization D Sc m cutoff bound β γ G).comp
    (elvInductionComponent D Sc cutoff bound i ΛR h (blockSucc D ΛR i h γ)) = _
  rw [elvInductionComponent_blockSucc]
  change (component D Sc m cutoff bound β γ G γ).comp
    (elvBlockInd D Sc cutoff bound i ΛR h γ) = _
  rw [component_selected]

/-- The selected post-restriction component equality holds on all maps. -/
theorem postF_component (i : I) {y' : X} (h : y + D.α i = y')
    (G : Hom D Sc m cutoff bound β (blockSucc D ΛR i h γ)) :
    ((realization D Sc m cutoff bound β (blockSucc D ΛR i h γ) G).comp
      (elvF D Sc cutoff bound i ΛR h)).comp (elvBlockEval D Sc cutoff bound ΛR γ) =
    ((probeOldBlockEval D Sc m ΛP β).comp G).comp
      (elvBlockRes D Sc cutoff bound i ΛR h γ) := by
  change (component D Sc m cutoff bound β (blockSucc D ΛR i h γ) G
    (blockSucc D ΛR i h γ)).comp (elvBlockRes D Sc cutoff bound i ΛR h γ) = _
  rw [component_selected]

/-- The selected pre-induction component equality holds on all maps. -/
theorem preE_component (i : I) {x₀ : X} (h : x₀ + D.α i = x)
    (β₀ : WeightBlocks D ΛP x₀) (G : Hom D Sc m cutoff bound (blockSucc D ΛP i h β₀) γ) :
    ((probeOldE D Sc m i ΛP h).comp
      (realization D Sc m cutoff bound (blockSucc D ΛP i h β₀) γ G)).comp
        (elvBlockEval D Sc cutoff bound ΛR γ) =
    ((probeOldBlockEval D Sc m ΛP β₀).comp (probeOldBlockInd D Sc m i ΛP h β₀)).comp G := by
  change (probeOldE D Sc m i ΛP h).comp
    (component D Sc m cutoff bound (blockSucc D ΛP i h β₀) γ G γ) = _
  rw [component_selected]
  change (probeOldInductionComponent D Sc m i ΛP h (blockSucc D ΛP i h β₀)).comp G = _
  rw [probeOldInductionComponent_blockSucc]

/-- The selected pre-restriction component equality holds on all maps. -/
theorem preF_component (i : I) {x' : X} (h : x + D.α i = x')
    (G : Hom D Sc m cutoff bound β γ) :
    ((probeOldF D Sc m i ΛP h).comp (realization D Sc m cutoff bound β γ G)).comp
      (elvBlockEval D Sc cutoff bound ΛR γ) =
    ((probeOldBlockEval D Sc m ΛP (blockSucc D ΛP i h β)).comp
      (probeOldBlockRes D Sc m i ΛP h β)).comp G := by
  change (probeOldF D Sc m i ΛP h).comp (component D Sc m cutoff bound β γ G γ) = _
  rw [component_selected]
  rfl

section Shift
local instance : PiSupercategory k (ELVWeightProduct D Sc cutoff bound ΛR y) :=
  elvWeightPi D Sc cutoff bound ΛR y
local instance (δ : WeightBlocks D ΛR y) : PiSupercategory k (ContentModules D Sc cutoff bound δ.1) :=
  contentModulesPi D Sc cutoff bound δ.1

/-- The prescribed parity shift acts componentwise on the full weight product. -/
theorem shift_component (p : ZMod 2) (N : ELVWeightProduct D Sc cutoff bound ΛR y)
    (δ : WeightBlocks D ΛR y) :
    ((SKM.homParityShift (k := k) p).obj N) δ =
      (SKM.homParityShift (k := k) p).obj (N δ) := by
  unfold SKM.homParityShift
  split <;> rfl

/-- Parity shifts preserve the exact output support. -/
theorem shift_off_isZero (p : ZMod 2) (G : Hom D Sc m cutoff bound β γ)
    (M : ProbeOldWeightProduct D Sc m ΛP x) (δ : WeightBlocks D ΛR y) (hδ : δ ≠ γ) :
    Limits.IsZero (((SKM.homParityShift (k := k) p).obj
      ((realization D Sc m cutoff bound β γ G).obj M)) δ) := by
  rw [shift_component]
  exact map_isZero (SKM.homParityShift (k := k) p) _
    (obj_off_isZero D Sc m cutoff bound β γ G M δ hδ)

end Shift

end OddMath.QuiverHecke.ELVOld.ContentHomSupport
end

end

section

/-! # Replete exact-content Hom categories

The formal support requirement F4 and (A1) of `SwappedActionAssembly.md`.
The full subcategory retains every arrow between objects isomorphic to an
exact-content realization. Absent primitive composites vanish as whole
functors, on every input and every retained original-weight block.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped Classical
namespace OddMath.QuiverHecke.ELVOld.ContentHomSupport
open CyclotomicAction
universe u
private theorem superfunctor_isZero {k : Type*} [CommRing k]
    {C C' : Type*} [CategoryTheory.Category C] [Preadditive C] [Linear k C] [Supercategory k C]
    [CategoryTheory.Category C'] [Preadditive C'] [Linear k C'] [Supercategory k C']
    (F : Superfunctor k C C') (h : ∀ M, Limits.IsZero (F.obj M)) : Limits.IsZero F := by
  apply (Limits.IsZero.iff_id_eq_zero _).mpr
  apply Superfunctor.hom_ext_parity
  · intro M
    exact (h M).eq_of_src _ _
  · intro M
    exact (h M).eq_of_src _ _

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (cutoff : I → ℕ) (bound : ℕ) {ΛP ΛR x y : X}
  (β : WeightBlocks D ΛP x) (γ : WeightBlocks D ΛR y)

/-- Replete exact support, with every natural arrow retained. -/
def Supported : ObjectProperty
    (probeOldWeightSpace D Sc m ΛP x ⟶ elvWeightSpace D Sc cutoff bound ΛR y) :=
  fun F => ∃ G : Hom D Sc m cutoff bound β γ,
    Nonempty (F ≅ realization D Sc m cutoff bound β γ G)

/-- The full supported Hom category prescribed by (A1), in whole-weight coordinates. -/
abbrev SupportedHom := (Supported D Sc m cutoff bound β γ).FullSubcategory

theorem realization_supported (G : Hom D Sc m cutoff bound β γ) :
    Supported D Sc m cutoff bound β γ (realization D Sc m cutoff bound β γ G) :=
  ⟨G, ⟨Iso.refl _⟩⟩

theorem supported_of_iso
    {F F' : probeOldWeightSpace D Sc m ΛP x ⟶ elvWeightSpace D Sc cutoff bound ΛR y}
    (e : F ≅ F') (h : Supported D Sc m cutoff bound β γ F') :
    Supported D Sc m cutoff bound β γ F := by
  obtain ⟨G, ⟨a⟩⟩ := h
  exact ⟨G, ⟨e ≪≫ a⟩⟩

private theorem functor_isZero
    (F : probeOldWeightSpace D Sc m ΛP x ⟶ elvWeightSpace D Sc cutoff bound ΛR y)
    (h : ∀ M δ, Limits.IsZero ((F.obj M) δ)) : Limits.IsZero F := by
  apply (Limits.IsZero.iff_id_eq_zero _).mpr
  apply Superfunctor.hom_ext_parity
  · intro M
    funext δ
    exact (h M δ).eq_of_src _ _
  · intro M
    funext δ
    exact (h M δ).eq_of_src _ _

/-- A missing exact probe predecessor kills the whole pre-induction
functor, including every collision block and every module input. -/
theorem preE_absent_functor_isZero (i : I) {x₀ : X} (h : x₀ + D.α i = x)
    (G : Hom D Sc m cutoff bound β γ) (hi : i ∉ β.1) :
    Limits.IsZero ((probeOldE D Sc m i ΛP h).comp
      (realization D Sc m cutoff bound β γ G)) := by
  apply functor_isZero
  intro M δ
  exact preE_absent_isZero D Sc m cutoff bound β γ i h G hi M δ

/-- A missing exact reservoir predecessor kills the whole post-restriction
functor; no assertion about unrelated whole-Hom objects is used. -/
theorem postF_absent_functor_isZero (i : I) {y₀ : X} (h : y₀ + D.α i = y)
    (G : Hom D Sc m cutoff bound β γ) (hi : i ∉ γ.1) :
    Limits.IsZero ((realization D Sc m cutoff bound β γ G).comp
      (elvF D Sc cutoff bound i ΛR h)) := by
  apply functor_isZero
  intro M δ
  exact postF_absent_isZero D Sc m cutoff bound β γ i h G hi M δ

private def productIso
    (F F' : probeOldWeightSpace D Sc m ΛP x ⟶ elvWeightSpace D Sc cutoff bound ΛR y)
    (e : ∀ δ, F.comp (elvBlockEval D Sc cutoff bound ΛR δ) ≅
      F'.comp (elvBlockEval D Sc cutoff bound ΛR δ)) : F ≅ F' where
  hom :=
    { app := fun p M δ => (e δ).hom.app p M
      app_mem := fun p M δ => (e δ).hom.app_mem p M
      naturality := by
        intro p M N q f hf
        funext δ
        exact (e δ).hom.naturality p f hf }
  inv :=
    { app := fun p M δ => (e δ).inv.app p M
      app_mem := fun p M δ => (e δ).inv.app_mem p M
      naturality := by
        intro p M N q f hf
        funext δ
        exact (e δ).inv.naturality p f hf }
  hom_inv_id := by
    apply Superfunctor.hom_ext_parity
    · intro M
      funext δ
      exact congrArg (fun f => f.app 0 M) (e δ).hom_inv_id
    · intro M
      funext δ
      exact congrArg (fun f => f.app 1 M) (e δ).hom_inv_id
  inv_hom_id := by
    apply Superfunctor.hom_ext_parity
    · intro M
      funext δ
      exact congrArg (fun f => f.app 0 M) (e δ).inv_hom_id
    · intro M
      funext δ
      exact congrArg (fun f => f.app 1 M) (e δ).inv_hom_id

private def comparisonComponent
    (F F' : probeOldWeightSpace D Sc m ΛP x ⟶ elvWeightSpace D Sc cutoff bound ΛR y)
    (q : F.comp (elvBlockEval D Sc cutoff bound ΛR γ) =
      F'.comp (elvBlockEval D Sc cutoff bound ΛR γ))
    (hF : ∀ M δ, δ ≠ γ → Limits.IsZero ((F.obj M) δ))
    (hF' : ∀ M δ, δ ≠ γ → Limits.IsZero ((F'.obj M) δ)) (δ : WeightBlocks D ΛR y) :
    F.comp (elvBlockEval D Sc cutoff bound ΛR δ) ≅
      F'.comp (elvBlockEval D Sc cutoff bound ΛR δ) :=
  if hδ : δ = γ then by subst δ; exact eqToIso q
  else (superfunctor_isZero _ (fun M => hF M δ hδ)).iso
    (superfunctor_isZero _ (fun M => hF' M δ hδ))

private def comparisonIso
    (F F' : probeOldWeightSpace D Sc m ΛP x ⟶ elvWeightSpace D Sc cutoff bound ΛR y)
    (q : F.comp (elvBlockEval D Sc cutoff bound ΛR γ) =
      F'.comp (elvBlockEval D Sc cutoff bound ΛR γ))
    (hF : ∀ M δ, δ ≠ γ → Limits.IsZero ((F.obj M) δ))
    (hF' : ∀ M δ, δ ≠ γ → Limits.IsZero ((F'.obj M) δ)) : F ≅ F' :=
  productIso D Sc m cutoff bound F F'
    (comparisonComponent D Sc m cutoff bound γ F F' q hF hF')

/-- Selected-block factorization and actual zero components place a whole
functor in the replete exact-content category. -/
theorem supported_of_selected
    (F : probeOldWeightSpace D Sc m ΛP x ⟶ elvWeightSpace D Sc cutoff bound ΛR y)
    (G : Hom D Sc m cutoff bound β γ)
    (h : F.comp (elvBlockEval D Sc cutoff bound ΛR γ) =
      (probeOldBlockEval D Sc m ΛP β).comp G)
    (hz : ∀ M δ, δ ≠ γ → Limits.IsZero ((F.obj M) δ)) :
    Supported D Sc m cutoff bound β γ F := by
  refine ⟨G, ⟨comparisonIso D Sc m cutoff bound γ F _ ?_ hz ?_⟩⟩
  · exact h.trans (component_selected D Sc m cutoff bound β γ G).symm
  · exact fun M δ hδ => obj_off_isZero D Sc m cutoff bound β γ G M δ hδ

/-- Post-induction preserves exact-content realization by the chosen block induction. -/
def postEIso (i : I) {y' : X} (h : y + D.α i = y')
    (G : Hom D Sc m cutoff bound β γ) :
    (realization D Sc m cutoff bound β γ G).comp (elvE D Sc cutoff bound i ΛR h) ≅
      realization D Sc m cutoff bound β (blockSucc D ΛR i h γ)
        (G.comp (elvBlockInd D Sc cutoff bound i ΛR h γ)) :=
  comparisonIso D Sc m cutoff bound (blockSucc D ΛR i h γ) _ _
    (by rw [postE_component]; exact (component_selected D Sc m cutoff bound β
      (blockSucc D ΛR i h γ) (G.comp (elvBlockInd D Sc cutoff bound i ΛR h γ))).symm)
    (fun M δ hδ => postE_off_isZero D Sc m cutoff bound β γ i h G M δ hδ)
    (fun M δ hδ => obj_off_isZero D Sc m cutoff bound β (blockSucc D ΛR i h γ) _ M δ hδ)

/-- Post-restriction preserves exact-content realization at its predecessor. -/
def postFIso (i : I) {y' : X} (h : y + D.α i = y')
    (G : Hom D Sc m cutoff bound β (blockSucc D ΛR i h γ)) :
    (realization D Sc m cutoff bound β (blockSucc D ΛR i h γ) G).comp
      (elvF D Sc cutoff bound i ΛR h) ≅
    realization D Sc m cutoff bound β γ (G.comp (elvBlockRes D Sc cutoff bound i ΛR h γ)) :=
  comparisonIso D Sc m cutoff bound γ _ _
    (by rw [postF_component]; exact (component_selected D Sc m cutoff bound β γ
      (G.comp (elvBlockRes D Sc cutoff bound i ΛR h γ))).symm)
    (fun M δ hδ => postF_off_isZero D Sc m cutoff bound β γ i h G M δ hδ)
    (fun M δ hδ => obj_off_isZero D Sc m cutoff bound β γ _ M δ hδ)

/-- Pre-induction preserves exact-content realization at a present predecessor. -/
def preEIso (i : I) {x₀ : X} (h : x₀ + D.α i = x)
    (β₀ : WeightBlocks D ΛP x₀) (G : Hom D Sc m cutoff bound (blockSucc D ΛP i h β₀) γ) :
    (probeOldE D Sc m i ΛP h).comp
      (realization D Sc m cutoff bound (blockSucc D ΛP i h β₀) γ G) ≅
    realization D Sc m cutoff bound β₀ γ ((probeOldBlockInd D Sc m i ΛP h β₀).comp G) :=
  comparisonIso D Sc m cutoff bound γ _ _
    (by rw [preE_component]; exact (component_selected D Sc m cutoff bound β₀ γ
      ((probeOldBlockInd D Sc m i ΛP h β₀).comp G)).symm)
    (fun M δ hδ => obj_off_isZero D Sc m cutoff bound (blockSucc D ΛP i h β₀) γ G
      ((probeOldE D Sc m i ΛP h).obj M) δ hδ)
    (fun M δ hδ => obj_off_isZero D Sc m cutoff bound β₀ γ _ M δ hδ)

/-- Pre-restriction preserves exact-content realization at the selected successor. -/
def preFIso (i : I) {x' : X} (h : x + D.α i = x')
    (G : Hom D Sc m cutoff bound β γ) :
    (probeOldF D Sc m i ΛP h).comp (realization D Sc m cutoff bound β γ G) ≅
    realization D Sc m cutoff bound (blockSucc D ΛP i h β) γ
      ((probeOldBlockRes D Sc m i ΛP h β).comp G) :=
  comparisonIso D Sc m cutoff bound γ _ _
    (by rw [preF_component]; exact (component_selected D Sc m cutoff bound
      (blockSucc D ΛP i h β) γ ((probeOldBlockRes D Sc m i ΛP h β).comp G)).symm)
    (fun M δ hδ => obj_off_isZero D Sc m cutoff bound β γ G
      ((probeOldF D Sc m i ΛP h).obj M) δ hδ)
    (fun M δ hδ => obj_off_isZero D Sc m cutoff bound (blockSucc D ΛP i h β) γ _ M δ hδ)

/-- Post-induction is closed on the replete exact-content Hom categories. -/
theorem postE_supported (i : I) {y' : X} (h : y + D.α i = y')
    {F : probeOldWeightSpace D Sc m ΛP x ⟶ elvWeightSpace D Sc cutoff bound ΛR y}
    (hF : Supported D Sc m cutoff bound β γ F) :
    Supported D Sc m cutoff bound β (blockSucc D ΛR i h γ)
      (F.comp (elvE D Sc cutoff bound i ΛR h)) := by
  obtain ⟨G, ⟨e⟩⟩ := hF
  exact ⟨G.comp (elvBlockInd D Sc cutoff bound i ΛR h γ),
    ⟨(SKM.homPost (k := k) (elvE D Sc cutoff bound i ΛR h)).mapIso e ≪≫
      postEIso D Sc m cutoff bound β γ i h G⟩⟩

/-- Post-restriction is closed on the replete predecessor category. -/
theorem postF_supported (i : I) {y' : X} (h : y + D.α i = y')
    {F : probeOldWeightSpace D Sc m ΛP x ⟶ elvWeightSpace D Sc cutoff bound ΛR y'}
    (hF : Supported D Sc m cutoff bound β (blockSucc D ΛR i h γ) F) :
    Supported D Sc m cutoff bound β γ (F.comp (elvF D Sc cutoff bound i ΛR h)) := by
  obtain ⟨G, ⟨e⟩⟩ := hF
  exact ⟨G.comp (elvBlockRes D Sc cutoff bound i ΛR h γ),
    ⟨(SKM.homPost (k := k) (elvF D Sc cutoff bound i ΛR h)).mapIso e ≪≫
      postFIso D Sc m cutoff bound β γ i h G⟩⟩

/-- Pre-induction is closed on the replete predecessor category. -/
theorem preE_supported (i : I) {x₀ : X} (h : x₀ + D.α i = x)
    (β₀ : WeightBlocks D ΛP x₀)
    {F : probeOldWeightSpace D Sc m ΛP x ⟶ elvWeightSpace D Sc cutoff bound ΛR y}
    (hF : Supported D Sc m cutoff bound (blockSucc D ΛP i h β₀) γ F) :
    Supported D Sc m cutoff bound β₀ γ ((probeOldE D Sc m i ΛP h).comp F) := by
  obtain ⟨G, ⟨e⟩⟩ := hF
  exact ⟨(probeOldBlockInd D Sc m i ΛP h β₀).comp G,
    ⟨(SKM.homPre (k := k) (probeOldE D Sc m i ΛP h)).mapIso e ≪≫
      preEIso D Sc m cutoff bound γ i h β₀ G⟩⟩

/-- Pre-restriction is closed on the replete successor category. -/
theorem preF_supported (i : I) {x' : X} (h : x + D.α i = x')
    {F : probeOldWeightSpace D Sc m ΛP x ⟶ elvWeightSpace D Sc cutoff bound ΛR y}
    (hF : Supported D Sc m cutoff bound β γ F) :
    Supported D Sc m cutoff bound (blockSucc D ΛP i h β) γ ((probeOldF D Sc m i ΛP h).comp F) := by
  obtain ⟨G, ⟨e⟩⟩ := hF
  exact ⟨(probeOldBlockRes D Sc m i ΛP h β).comp G,
    ⟨(SKM.homPre (k := k) (probeOldF D Sc m i ΛP h)).mapIso e ≪≫
      preFIso D Sc m cutoff bound β γ i h G⟩⟩

/-- The missing probe predecessor vanishes for every replete-supported object. -/
theorem preE_supported_absent_isZero (i : I) {x₀ : X} (h : x₀ + D.α i = x)
    {F : probeOldWeightSpace D Sc m ΛP x ⟶ elvWeightSpace D Sc cutoff bound ΛR y}
    (hF : Supported D Sc m cutoff bound β γ F) (hi : i ∉ β.1) :
    Limits.IsZero ((probeOldE D Sc m i ΛP h).comp F) := by
  obtain ⟨G, ⟨e⟩⟩ := hF
  exact (preE_absent_functor_isZero D Sc m cutoff bound β γ i h G hi).of_iso
    ((SKM.homPre (k := k) (probeOldE D Sc m i ΛP h)).mapIso e)

/-- The missing reservoir predecessor vanishes for every replete-supported object. -/
theorem postF_supported_absent_isZero (i : I) {y₀ : X} (h : y₀ + D.α i = y)
    {F : probeOldWeightSpace D Sc m ΛP x ⟶ elvWeightSpace D Sc cutoff bound ΛR y}
    (hF : Supported D Sc m cutoff bound β γ F) (hi : i ∉ γ.1) :
    Limits.IsZero (F.comp (elvF D Sc cutoff bound i ΛR h)) := by
  obtain ⟨G, ⟨e⟩⟩ := hF
  exact (postF_absent_functor_isZero D Sc m cutoff bound β γ i h G hi).of_iso
    ((SKM.homPost (k := k) (elvF D Sc cutoff bound i ΛR h)).mapIso e)

section Shift
local instance : PiSupercategory k (ELVWeightProduct D Sc cutoff bound ΛR y) :=
  elvWeightPi D Sc cutoff bound ΛR y
local instance (δ : WeightBlocks D ΛR y) : PiSupercategory k (ContentModules D Sc cutoff bound δ.1) :=
  contentModulesPi D Sc cutoff bound δ.1
local instance : PiSupercategory k
    (probeOldWeightSpace D Sc m ΛP x ⟶ elvWeightSpace D Sc cutoff bound ΛR y) :=
  PiTwoSupercategory.homPiLeft _ _

private theorem shift_eval (p : ZMod 2) (δ : WeightBlocks D ΛR y) :
    (show Superfunctor k (ELVWeightProduct D Sc cutoff bound ΛR y)
      (ELVWeightProduct D Sc cutoff bound ΛR y) from ⟨SKM.homParityShift (k := k) p⟩).comp
      (elvBlockEval D Sc cutoff bound ΛR δ) =
    (elvBlockEval D Sc cutoff bound ΛR δ).comp
      (show Superfunctor k (ContentModules D Sc cutoff bound δ.1)
        (ContentModules D Sc cutoff bound δ.1) from ⟨SKM.homParityShift (k := k) p⟩) := by
  unfold SKM.homParityShift
  split
  · rfl
  · apply Superfunctor.ext
    apply CategoryTheory.Functor.ext
    case h_obj => intro N; rfl
    case h_map =>
      intro N N' f
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
      change ((PiSupercategory.pi (R := k) (C := ELVWeightProduct D Sc cutoff bound ΛR y)).map f) δ =
        (PiSupercategory.pi (R := k) (C := ContentModules D Sc cutoff bound δ.1)).map (f δ)
      rw [PiSupercategory.pi_map_eq, PiSupercategory.pi_map_eq]
      change (PiSupercategory.ζ (R := k) (N δ)).hom ≫ ((twist k 1) f) δ ≫
        (PiSupercategory.ζ (R := k) (N' δ)).inv = _
      rw [show ((twist k 1) f) δ = (twist k 1) (f δ) from
        map_twist (elvBlockEval D Sc cutoff bound ΛR δ).toFunctor 1 f]

/-- Parity shift preserves the realization by shifting its exact output category. -/
def postShiftIso (p : ZMod 2) (G : Hom D Sc m cutoff bound β γ) :
    (realization D Sc m cutoff bound β γ G).comp
      (show Superfunctor k (ELVWeightProduct D Sc cutoff bound ΛR y)
        (ELVWeightProduct D Sc cutoff bound ΛR y) from ⟨SKM.homParityShift (k := k) p⟩) ≅
    realization D Sc m cutoff bound β γ
      (G.comp (show Superfunctor k (ContentModules D Sc cutoff bound γ.1)
        (ContentModules D Sc cutoff bound γ.1) from ⟨SKM.homParityShift (k := k) p⟩)) :=
  comparisonIso D Sc m cutoff bound γ _ _
    (by
      change (realization D Sc m cutoff bound β γ G).comp
        ((show Superfunctor k (ELVWeightProduct D Sc cutoff bound ΛR y)
          (ELVWeightProduct D Sc cutoff bound ΛR y) from ⟨SKM.homParityShift (k := k) p⟩).comp
          (elvBlockEval D Sc cutoff bound ΛR γ)) = _
      rw [shift_eval]
      change (component D Sc m cutoff bound β γ G γ).comp
        (show Superfunctor k (ContentModules D Sc cutoff bound γ.1)
          (ContentModules D Sc cutoff bound γ.1) from ⟨SKM.homParityShift (k := k) p⟩) =
        component D Sc m cutoff bound β γ _ γ
      rw [component_selected, component_selected]
      rfl)
    (fun M δ hδ => shift_off_isZero D Sc m cutoff bound β γ p G M δ hδ)
    (fun M δ hδ => obj_off_isZero D Sc m cutoff bound β γ _ M δ hδ)

/-- The replete category is closed under parity shift on the Hom supercategory. -/
theorem shift_supported (p : ZMod 2)
    {F : probeOldWeightSpace D Sc m ΛP x ⟶ elvWeightSpace D Sc cutoff bound ΛR y}
    (hF : Supported D Sc m cutoff bound β γ F) :
    Supported D Sc m cutoff bound β γ ((SKM.homParityShift (k := k) p).obj F) := by
  obtain ⟨G, ⟨e⟩⟩ := hF
  have he : (SKM.homParityShift (k := k) p).obj F ≅
      (SKM.homParityShift (k := k) p).obj (realization D Sc m cutoff bound β γ G) :=
    (SKM.homParityShift (k := k) p).mapIso e
  apply supported_of_iso D Sc m cutoff bound β γ he
  refine ⟨G.comp (show Superfunctor k (ContentModules D Sc cutoff bound γ.1)
    (ContentModules D Sc cutoff bound γ.1) from ⟨SKM.homParityShift (k := k) p⟩), ⟨?_⟩⟩
  have hi := postShiftIso D Sc m cutoff bound β γ p G
  by_cases hp : p = 0
  · subst p
    exact hi
  · rw [SKM.homParityShift, ite_eq_right hp]
    change (realization D Sc m cutoff bound β γ G).comp
      (show Superfunctor k (ELVWeightProduct D Sc cutoff bound ΛR y)
        (ELVWeightProduct D Sc cutoff bound ΛR y) from ⟨PiSupercategory.pi (R := k)⟩) ≅ _
    simpa only [SKM.homParityShift, ite_eq_right hp] using hi

/-- The replete supported full subcategory inherits the prescribed parity completion. -/
@[instance_reducible]
def supportedPi : PiSupercategory k (SupportedHom D Sc m cutoff bound β γ) :=
  fullPiSupercategory (Supported D Sc m cutoff bound β γ)
    (fun _ hF => shift_supported D Sc m cutoff bound β γ 1 hF)

end Shift

end OddMath.QuiverHecke.ELVOld.ContentHomSupport
end

end

section

/-! # The selected tensor vacuum has exact formal support

The initial object of F4/(A1) in `SwappedActionAssembly.md` is the already
chosen whole-weight `WeightTensorVacuum.selectedHom`, on every input and
all collision blocks. Its support is proved from its construction.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.ContentHomSupport
open CyclotomicAction SwappedAssembly
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) [Fintype I] (m : I → ℕ)
  (cutoff : I → ℕ) (ΛP ΛR : X) (L : I × ℕ → ℕ)

private def forgetEmptyFunctor (ν : List I) (h : ν = []) :
    ProbeEvaluatedModules D Sc m ν ⥤
      Superfunctor k (OldContentCategory D Sc (probeCutoff D m) []) (SVec k) := by
  subst ν
  exact ObjectProperty.ι _
private instance (ν : List I) (h : ν = []) : (forgetEmptyFunctor D Sc m ν h).Additive := by
  subst ν
  exact ⟨by intros; rfl⟩
private instance (ν : List I) (h : ν = []) : (forgetEmptyFunctor D Sc m ν h).Linear k := by
  subst ν
  exact ⟨fun _ _ => rfl⟩
private instance (ν : List I) (h : ν = []) : IsSuperfunctor k (forgetEmptyFunctor D Sc m ν h) := by
  subst ν
  exact ⟨fun hf => hf⟩

/-- Formal reservoir content zero at its literal chosen weight. -/
def reservoirVacuumBlock : WeightBlocks D ΛR (ReservoirWord.weight D ΛR 0) :=
  ⟨0, by simp [blockWeight, ReservoirWord.weight]⟩

/-- The exact-content tensor functor whose whole-weight realization is the selected vacuum. -/
def vacuumHom : Hom D Sc m cutoff (PowerWordContent.powerBound D cutoff L)
    (WeightTensorVacuum.emptyBlock D ΛP) (reservoirVacuumBlock D ΛR) :=
  (show Superfunctor k (ProbeCanonicalModules D Sc m (0 : Multiset I))
    (Superfunctor k (OldContentCategory D Sc (probeCutoff D m) []) (SVec k)) from
      ⟨forgetEmptyFunctor D Sc m _ Multiset.toList_zero⟩).comp
    (VacuumTensor.superfunctor
      ((ReservoirWordValue.initialValue D ΛR Sc cutoff L) (reservoirVacuumBlock D ΛR))
      (probeOldVacuumObject D Sc m))

/-- The selected component equality holds as a whole Superfunctor, on all maps. -/
theorem selectedVacuum_component :
    (WeightTensorVacuum.selectedHom D Sc m cutoff ΛP ΛR L).comp
      (elvBlockEval D Sc cutoff (PowerWordContent.powerBound D cutoff L) ΛR
        (reservoirVacuumBlock D ΛR)) =
    (probeOldBlockEval D Sc m ΛP (WeightTensorVacuum.emptyBlock D ΛP)).comp
      (vacuumHom D Sc m cutoff ΛP ΛR L) := by
  rfl

private theorem tensor_isZero {C : Type u} [Category.{u} C] [Preadditive C]
    [Linear k C] [Supercategory k C] (W : Superfunctor k C (SVec k))
    (hW : Limits.IsZero W) (V : SVec k) : Limits.IsZero (VacuumTensor.object W V) := by
  apply (Limits.IsZero.iff_id_eq_zero _).mpr
  have he := (Limits.IsZero.iff_id_eq_zero W).mp hW
  apply Superfunctor.hom_ext_parity
  · intro c
    have hc : (𝟙 (W.obj c) : End (W.obj c)) = 0 := congrArg (fun f : End W => f.app 0 c) he
    change (𝟙 (SVec.tensorObj (W.obj c) V) : End _) = 0
    rw [← SVec.whiskerRight_id, hc, SVec.whiskerRight_zero]
  · intro c
    rfl

/-- Every nonzero-content output of the literal selected Hom is zero,
for every input, including other blocks of the same original weight. -/
theorem selectedVacuum_off_isZero
    (M : ProbeOldWeightProduct D Sc m ΛP (-ΛP))
    (δ : WeightBlocks D ΛR (ReservoirWord.weight D ΛR 0))
    (hδ : δ ≠ reservoirVacuumBlock D ΛR) :
    Limits.IsZero (((WeightTensorVacuum.selectedHom D Sc m cutoff ΛP ΛR L).obj M) δ) := by
  have hd : δ.1 ≠ (0 : Multiset I) := fun he => hδ (Subtype.ext he)
  change Limits.IsZero (VacuumTensor.object
    ((ReservoirWordValue.initialValue D ΛR Sc cutoff L) δ)
    (((WeightTensorVacuum.emptyProbe D Sc m ΛP).obj M).obj (probeOldVacuumObject D Sc m)))
  apply tensor_isZero
  exact PowerWordWeight.wordAt_isZero D Sc cutoff L [] δ.1 hd

/-- The actual selected Hom belongs to the replete exact-content category,
without an assumed comparison or a regular-input-only support assertion. -/
theorem selectedVacuum_supported :
    Supported D Sc m cutoff (PowerWordContent.powerBound D cutoff L)
      (WeightTensorVacuum.emptyBlock D ΛP) (reservoirVacuumBlock D ΛR)
      (WeightTensorVacuum.selectedHom D Sc m cutoff ΛP ΛR L) :=
  supported_of_selected D Sc m cutoff (PowerWordContent.powerBound D cutoff L)
    (WeightTensorVacuum.emptyBlock D ΛP) (reservoirVacuumBlock D ΛR)
    (WeightTensorVacuum.selectedHom D Sc m cutoff ΛP ΛR L)
    (vacuumHom D Sc m cutoff ΛP ΛR L)
    (selectedVacuum_component D Sc m cutoff ΛP ΛR L)
    (fun M δ hδ => selectedVacuum_off_isZero D Sc m cutoff ΛP ΛR L M δ hδ)

end OddMath.QuiverHecke.ELVOld.ContentHomSupport
end

end

section

/-! # Affine relations in the untruncated old content quotient

The local action of BE (1.13)–(1.14) requires the literal positive old equal crossing to be square-zero
and to satisfy both signed dot slides. All relations descend directly
from affine relations through the full-coefficient old quotient. The
stored content targets are cons lists, while underlying words append
on the right. These are the coefficient inputs for the probe local action.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
namespace OddMath.QuiverHecke.ELVOld
open CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

private theorem oldDot_affine (i : I) (s : OldCategory D Sc cutoff) :
    oldAppendDotComponent D Sc cutoff i s =
      (ideal D Sc cutoff _ _).mkQ (affineUnit D Sc cutoff _ _
        (dotE D Sc (s.word ++ [i]) s.word.length)) := by
  rw [oldAppendDotComponent_eq, appendMovingPower, pow_one]

private theorem oldLowerDot_affine (i : I) (s : OldCategory D Sc cutoff) :
    (append D Sc cutoff i).map (oldAppendDotComponent D Sc cutoff i s) =
      (ideal D Sc cutoff _ _).mkQ (affineUnit D Sc cutoff _ _
        (dotE D Sc (s.word ++ [i] ++ [i]) s.word.length)) := by
  rw [oldDot_affine]
  change (ideal D Sc cutoff (s.word ++ [i] ++ [i]) (s.word ++ [i] ++ [i])).mkQ
    (rightContext D Sc cutoff [i] (s.word ++ [i]) (s.word ++ [i])
      (affineUnit D Sc cutoff (s.word ++ [i]) (s.word ++ [i])
        (dotE D Sc (s.word ++ [i]) s.word.length))) = _
  rw [rightContext_affineUnit]
  change (ideal D Sc cutoff (s.word ++ [i] ++ [i]) (s.word ++ [i] ++ [i])).mkQ
    (affineUnit D Sc cutoff (s.word ++ [i] ++ [i]) (s.word ++ [i] ++ [i])
      (dotE D Sc (s.word ++ [i]) s.word.length ▷ (pres D Sc).obj (ob D [i]))) = _
  rw [dotE_whiskerRight D Sc (s.word ++ [i]) [i] s.word.length (by simp)]

private theorem oldUpperDot_affine (i : I) (s : OldCategory D Sc cutoff) :
    oldAppendDotComponent D Sc cutoff i ((append D Sc cutoff i).obj s) =
      (ideal D Sc cutoff _ _).mkQ (affineUnit D Sc cutoff _ _
        (dotE D Sc (s.word ++ [i] ++ [i]) (s.word.length + 1))) := by
  simpa only [append, List.length_append, List.length_singleton] using
    oldDot_affine D Sc cutoff i ((append D Sc cutoff i).obj s)

private theorem affineCrossLast_square (v : List I) (i : I) :
    crossLast D Sc v i i ≫ crossLast D Sc v i i = 0 := by
  have he := crossE_mul_crossE D Sc (w := v ++ [i] ++ [i]) v [] i
    (j := v.length) rfl (by simp [List.append_assoc])
  have hc : crossE D Sc (v ++ [i] ++ [i]) v.length = crossLast D Sc v i i := by
    unfold crossE
    rw [genE_eq D Sc (by simpa using sChain_crossAt v [] i i)]
    rfl
  simpa only [hc, End.mul_def] using he

private theorem oldCross_square (i : I) (s : OldCategory D Sc cutoff) :
    equalCrossComponent D Sc cutoff i s ≫ equalCrossComponent D Sc cutoff i s = 0 := by
  change oldComp D Sc cutoff _ _ _ ((ideal D Sc cutoff _ _).mkQ _)
    ((ideal D Sc cutoff _ _).mkQ _) = 0
  rw [oldComp_mk, ← affineUnit_comp, affineCrossLast_square, map_zero, map_zero]

private theorem affine_slideLeft (v : List I) (i : I) :
    affineUnit D Sc cutoff _ _ (dotE D Sc (v ++ [i] ++ [i]) v.length) ≫
        affineUnit D Sc cutoff _ _ (crossLast D Sc v i i) -
      sign k (D.parity i * D.parity i) •
        (affineUnit D Sc cutoff _ _ (crossLast D Sc v i i) ≫
          affineUnit D Sc cutoff _ _ (dotE D Sc (v ++ [i] ++ [i]) (v.length + 1))) = 𝟙 _ := by
  have h := congrArg (affineUnit D Sc cutoff _ _) (dotE_comp_crossLast_self D Sc (i := i) v)
  rw [map_add, map_smul, affineUnit_comp, affineUnit_comp, affineUnit_id,
    ← sign_eq_zsign] at h
  exact sub_eq_iff_eq_add.mpr (h.trans (add_comm _ _))

private theorem affine_slideRight (v : List I) (i : I) :
    affineUnit D Sc cutoff _ _ (crossLast D Sc v i i) ≫
        affineUnit D Sc cutoff _ _ (dotE D Sc (v ++ [i] ++ [i]) v.length) -
      sign k (D.parity i * D.parity i) •
        (affineUnit D Sc cutoff _ _ (dotE D Sc (v ++ [i] ++ [i]) (v.length + 1)) ≫
          affineUnit D Sc cutoff _ _ (crossLast D Sc v i i)) = 𝟙 _ := by
  have h := congrArg (affineUnit D Sc cutoff _ _) (crossLast_comp_dotE_self D Sc (i := i) v)
  rw [map_add, map_smul, affineUnit_comp, affineUnit_comp, affineUnit_id,
    ← sign_eq_zsign] at h
  exact sub_eq_iff_eq_add.mpr (h.trans (add_comm _ _))

private theorem oldCross_slideLeft (i : I) (s : OldCategory D Sc cutoff) :
    (show End (((append D Sc cutoff i) ⋙ (append D Sc cutoff i)).obj s) from
      (append D Sc cutoff i).map (oldAppendDotComponent D Sc cutoff i s)) ≫
        equalCrossComponent D Sc cutoff i s -
      sign k (D.parity i * D.parity i) •
        (equalCrossComponent D Sc cutoff i s ≫
          (show End (((append D Sc cutoff i) ⋙ (append D Sc cutoff i)).obj s) from
            oldAppendDotComponent D Sc cutoff i ((append D Sc cutoff i).obj s))) = 𝟙 _ := by
  rw [oldLowerDot_affine, oldUpperDot_affine]
  change oldComp D Sc cutoff _ _ _ ((ideal D Sc cutoff _ _).mkQ _)
      ((ideal D Sc cutoff _ _).mkQ _) - sign k (D.parity i * D.parity i) •
    oldComp D Sc cutoff _ _ _ ((ideal D Sc cutoff _ _).mkQ _)
      ((ideal D Sc cutoff _ _).mkQ _) = (ideal D Sc cutoff _ _).mkQ (𝟙 _)
  rw [oldComp_mk, oldComp_mk, ← map_smul, ← map_sub]
  exact congrArg (ideal D Sc cutoff _ _).mkQ (affine_slideLeft D Sc cutoff s.word i)

private theorem oldCross_slideRight (i : I) (s : OldCategory D Sc cutoff) :
    equalCrossComponent D Sc cutoff i s ≫
        (show End (((append D Sc cutoff i) ⋙ (append D Sc cutoff i)).obj s) from
          (append D Sc cutoff i).map (oldAppendDotComponent D Sc cutoff i s)) -
      sign k (D.parity i * D.parity i) •
        ((show End (((append D Sc cutoff i) ⋙ (append D Sc cutoff i)).obj s) from
          oldAppendDotComponent D Sc cutoff i ((append D Sc cutoff i).obj s)) ≫
          equalCrossComponent D Sc cutoff i s) = 𝟙 _ := by
  rw [oldLowerDot_affine, oldUpperDot_affine]
  change oldComp D Sc cutoff _ _ _ ((ideal D Sc cutoff _ _).mkQ _)
      ((ideal D Sc cutoff _ _).mkQ _) - sign k (D.parity i * D.parity i) •
    oldComp D Sc cutoff _ _ _ ((ideal D Sc cutoff _ _).mkQ _)
      ((ideal D Sc cutoff _ _).mkQ _) = (ideal D Sc cutoff _ _).mkQ (𝟙 _)
  rw [oldComp_mk, oldComp_mk, ← map_smul, ← map_sub]
  exact congrArg (ideal D Sc cutoff _ _).mkQ (affine_slideRight D Sc cutoff s.word i)

variable (ν : List I) (i : I)
local notation "J" => oldContentAppend D Sc cutoff ν i
local notation "K" => oldContentAppend D Sc cutoff (i :: ν) i
variable (s : OldContentCategory D Sc cutoff ν)
local notation "γ" => oldContentEqualCross D Sc cutoff ν i s
/-- The literal positive last equal crossing is square-zero in the old content quotient. -/
theorem oldContentEqualCross_square : γ ≫ γ = 0 := oldCross_square D Sc cutoff i s.obj

/-- The first signed affine slide uses the literal two selected append dots. -/
theorem oldContentEqualCross_slideLeft :
    (show End (CategoryTheory.Functor.obj (J ⋙ K) s) from
      CategoryTheory.Functor.map K (oldContentAppendDot D Sc cutoff ν i s)) ≫ γ -
      koszulSign (D.parity i) (D.parity i) •
        (γ ≫ (show End (CategoryTheory.Functor.obj (J ⋙ K) s) from
          oldContentAppendDot D Sc cutoff (i :: ν) i (CategoryTheory.Functor.obj J s))) = 𝟙 _ := by
  rw [koszulSign_smul (R := k)]
  exact oldCross_slideLeft D Sc cutoff i s.obj

/-- The second signed affine slide retains the same positive crossing and dots. -/
theorem oldContentEqualCross_slideRight :
    γ ≫ (show End (CategoryTheory.Functor.obj (J ⋙ K) s) from
      CategoryTheory.Functor.map K (oldContentAppendDot D Sc cutoff ν i s)) -
      koszulSign (D.parity i) (D.parity i) •
        ((show End (CategoryTheory.Functor.obj (J ⋙ K) s) from
          oldContentAppendDot D Sc cutoff (i :: ν) i (CategoryTheory.Functor.obj J s)) ≫ γ) = 𝟙 _ := by
  rw [koszulSign_smul (R := k)]
  exact oldCross_slideRight D Sc cutoff i s.obj

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # The prescribed distinct mate on fixed old content

Brundan–Ellis (1.12), DeformedActionAssembly §4: compare the positive
rectangular content cup-crossing-cap with the chosen old-module mate.
Both lower and upper append functors retain their literal old arrows;
the two upper contents share a prescribed permutation index.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open CyclotomicCrossingTensor
universe u
namespace DistinctContent
private theorem even_of_app_one_zero
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {P Q : Superfunctor k C (SVec k)} (f : P ⟶ Q) (h : ∀ w, f.app 1 w = 0) :
    f ∈ parity (R := k) _ _ 0 := by
  apply Superfunctor.mem_parity_iff_isHomogeneous.mpr
  intro q hq
  rcases parity_eq_zero_or_one q with rfl | rfl
  · exact (hq rfl).elim
  · funext w
    exact h w

private theorem moduleMap_total_even
    {k C B : Type u} [CommRing k] [Category.{u} C] [Category.{u} B]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    (H : C ⥤ B) [H.Additive] [H.Linear k] [IsSuperfunctor k H]
    {P Q : Superfunctor k C (SVec k)} (f : P ⟶ Q) (h : ∀ w, f.app 1 w = 0) (w : B) :
    (BalancedInduction.moduleMap H f).total w = BalancedInduction.mapComponent H f 0 w := by
  have hf := even_of_app_one_zero f h
  have hh := IsSuperfunctor.map_mem (F := BalancedInduction.induction H) hf
  have hz := Superfunctor.app_eq_zero_of_mem hh (by decide : (1 : ZMod 2) ≠ 0) w
  change BalancedInduction.mapComponent H f 1 w = 0 at hz
  change BalancedInduction.mapComponent H f 0 w + BalancedInduction.mapComponent H f 1 w =
    BalancedInduction.mapComponent H f 0 w
  rw [hz, add_zero]

private theorem restriction_comparison_total
    {k C B : Type u} [CommRing k] [Category.{u} C] [Category.{u} B]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    (Q : C ⥤ B) [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q]
    {P : Superfunctor k C (SVec k)} {N T : Superfunctor k B (SVec k)}
    (a : P ⟶ (BalancedInduction.restriction Q).obj N) (b : N ⟶ T) (v : C) (x : P.obj v) :
    (a ≫ (BalancedInduction.restriction Q).map b).total v x =
      b.total (Q.obj v) (a.total v x) := by
  rw [Superfunctor.comp_total]
  rfl
private def restrictionCoefficientIso
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    (B : C ⥤ C) [B.Additive] [B.Linear k] [IsSuperfunctor k B]
    (N : Superfunctor k C (SVec k)) :
    ((BalancedInduction.restriction B).obj N).toFunctor ≅ B ⋙ N.toFunctor := Iso.refl _

private def restrictionCoendEquiv
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    (A B : C ⥤ C) [A.Additive] [A.Linear k] [IsSuperfunctor k A]
    [B.Additive] [B.Linear k] [IsSuperfunctor k B]
    (N : Superfunctor k C (SVec k)) (t : C) :
    BalancedInduction.Obj A ((BalancedInduction.restriction B).obj N).toFunctor t ≃ₗ[k]
      BalancedInduction.Obj A (B ⋙ N.toFunctor) t :=
  BalancedInduction.coefficientEquiv A (restrictionCoefficientIso B N) t

private theorem restrictionCoendEquiv_tensor
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    (A B : C ⥤ C) [A.Additive] [A.Linear k] [IsSuperfunctor k A]
    [B.Additive] [B.Linear k] [IsSuperfunctor k B]
    (N : Superfunctor k C (SVec k)) (s t : C) (g : A.obj s ⟶ t) (b : N.obj (B.obj s)) :
    restrictionCoendEquiv A B N t
      (BalancedInduction.tensor A ((BalancedInduction.restriction B).obj N).toFunctor s g b) =
      BalancedInduction.tensor A (B ⋙ N.toFunctor) s g b :=
  BalancedInduction.coefficientEquiv_tensor A (restrictionCoefficientIso B N) t s g b

private theorem bijective_of_square {V W U Z : Type u}
    (f : V → W) (a : V → U) (b : W → Z) (g : U → Z)
    (ha : Function.Bijective a) (hb : Function.Bijective b) (hg : Function.Bijective g)
    (h : ∀ x, b (f x) = g (a x)) : Function.Bijective f := by
  refine ⟨?_, ?_⟩
  · intro x y hxy
    apply ha.injective
    apply hg.injective
    rw [← h x, ← h y, hxy]
  · intro y
    obtain ⟨z, hz⟩ := hg.surjective (b y)
    obtain ⟨x, hx⟩ := ha.surjective z
    refine ⟨x, hb.injective ?_⟩
    rw [h x, hx, hz]

private theorem linearEquiv_toLinearMap_bijective
    {k V W : Type u} [CommRing k] [AddCommMonoid V] [Module k V]
    [AddCommMonoid W] [Module k W] (e : V ≃ₗ[k] W) :
    Function.Bijective e.toLinearMap := e.bijective

private theorem linearMap_comp_bijective
    {k V W U : Type u} [CommRing k] [AddCommMonoid V] [Module k V]
    [AddCommMonoid W] [Module k W] [AddCommMonoid U] [Module k U]
    (f : V →ₗ[k] W) (g : W →ₗ[k] U) (hf : Function.Bijective f) (hg : Function.Bijective g) :
    Function.Bijective (g ∘ₗ f) := hg.comp hf

end DistinctContent

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (ν : List I) (i j : I)

/-- The upper j-append uses the same chosen total content as the upper i-append. -/
def oldContentDistinctUpperAppend :
    OldContentCategory D Sc cutoff (i :: ν) ⥤ OldContentCategory D Sc cutoff (i :: j :: ν) :=
  oldContentAppendTo D Sc cutoff (i :: ν) j (i :: j :: ν) (List.Perm.swap i j ν)

instance : (oldContentDistinctUpperAppend D Sc cutoff ν i j).Additive := by
  dsimp only [oldContentDistinctUpperAppend]
  infer_instance
instance : Functor.Linear k (oldContentDistinctUpperAppend D Sc cutoff ν i j) := by
  dsimp only [oldContentDistinctUpperAppend]
  infer_instance
instance : IsSuperfunctor k (oldContentDistinctUpperAppend D Sc cutoff ν i j) := by
  dsimp only [oldContentDistinctUpperAppend]
  infer_instance

local notation "J" => oldContentAppend D Sc cutoff ν j
local notation "K" => oldContentAppend D Sc cutoff ν i
local notation "L" => oldContentAppend D Sc cutoff (j :: ν) i
local notation "M" => oldContentDistinctUpperAppend D Sc cutoff ν i j
local notation "Q₀" => oldContentInclusion D Sc cutoff ν
local notation "Qj" => oldContentInclusion D Sc cutoff (j :: ν)
local notation "Qi" => oldContentInclusion D Sc cutoff (i :: ν)
local notation "A" => append D Sc cutoff i
local notation "B" => append D Sc cutoff j

/-- The literal positive crossing from j,i to i,j in the common upper content. -/
def oldContentDistinctCross (s : OldContentCategory D Sc cutoff ν) :
    (J ⋙ L).obj s ⟶ (K ⋙ M).obj s := Distinct.crossComponent D Sc cutoff i j s.obj

theorem oldContentDistinctCross_supernatural :
    IsSupernatural k (D.parity i * D.parity j) (oldContentDistinctCross D Sc cutoff ν i j) where
  mem s := (Distinct.cross_supernatural D Sc cutoff i j).mem s.obj
  naturality := by
    intro s t p f hf
    exact (Distinct.cross_supernatural D Sc cutoff i j).naturality hf

/-- The independently prescribed content cup-crossing-cap, with both ordinary adjunctions. -/
def oldContentDistinctMateComponent
    (N : Superfunctor k (OldContentCategory D Sc cutoff (j :: ν)) (SVec k)) :
    BalancedInduction.induced K ((BalancedInduction.restriction J).obj N) ⟶
      (BalancedInduction.restriction M).obj (BalancedInduction.induced L N) :=
  BalancedInduction.orderedRectangularMateComponent J K L M
    (oldContentDistinctCross_supernatural D Sc cutoff ν i j) N

/-- The selected source chart first uses content i-induction, then j-restriction extension. -/
def oldContentDistinctSourceIso
    (N : Superfunctor k (OldContentCategory D Sc cutoff (j :: ν)) (SVec k)) :
    BalancedInduction.induced K ((BalancedInduction.restriction J).obj N) ≅
      (BalancedInduction.restriction Qi).obj
        (BalancedInduction.induced A ((BalancedInduction.restriction B).obj
          (BalancedInduction.induced Qj N))) :=
  oldContentAppendRestrictionIso D Sc cutoff ν i ((BalancedInduction.restriction J).obj N) ≪≫
    (BalancedInduction.restriction Qi).mapIso
      ((BalancedInduction.induction A).mapIso
        (oldContentRestrictionExtensionIso D Sc cutoff ν j N))

/-- The selected source chart on literal balanced coends. -/
def oldContentDistinctSourceDirectLinear
    (N : Superfunctor k (OldContentCategory D Sc cutoff (j :: ν)) (SVec k))
    (t : OldContentCategory D Sc cutoff (i :: ν)) :
    BalancedInduction.Obj K ((BalancedInduction.restriction J).obj N).toFunctor t →ₗ[k]
      BalancedInduction.Obj A ((BalancedInduction.restriction B).obj
        (BalancedInduction.induced Qj N)).toFunctor t.obj :=
  (oldContentDistinctSourceIso D Sc cutoff ν i j N).hom.total t

private theorem oldContentDistinctSourceLinear_apply
    (N : Superfunctor k (OldContentCategory D Sc cutoff (j :: ν)) (SVec k))
    (t : OldContentCategory D Sc cutoff (i :: ν))
    (z : BalancedInduction.Obj K ((BalancedInduction.restriction J).obj N).toFunctor t) :
    oldContentDistinctSourceDirectLinear D Sc cutoff ν i j N t z =
      BalancedInduction.mapComponent A (oldContentRestrictionExtensionIso D Sc cutoff ν j N).hom
        0 t.obj (oldContentAppendRestrictionLinear D Sc cutoff ν i
          ((BalancedInduction.restriction J).obj N) t z) := by
  have hodd (w : OldCategory D Sc cutoff) :
      (oldContentRestrictionExtensionIso D Sc cutoff ν j N).hom.app 1 w = 0 :=
    oldContentRestrictionExtensionComponent_one D Sc cutoff ν j N w
  have hm := DistinctContent.moduleMap_total_even A
    (oldContentRestrictionExtensionIso D Sc cutoff ν j N).hom hodd t.obj
  have hc := DistinctContent.restriction_comparison_total Qi
    (oldContentAppendRestrictionIso D Sc cutoff ν i ((BalancedInduction.restriction J).obj N)).hom
    ((BalancedInduction.induction A).map (oldContentRestrictionExtensionIso D Sc cutoff ν j N).hom) t z
  have hx := LinearMap.congr_fun hm
    ((oldContentAppendRestrictionIso D Sc cutoff ν i
      ((BalancedInduction.restriction J).obj N)).hom.total t z)
  exact hc.trans hx

/-- The chosen mixed source comparison inserts precisely the input inclusion unit. -/
theorem oldContentDistinctSourceDirectLinear_tensor
    (N : Superfunctor k (OldContentCategory D Sc cutoff (j :: ν)) (SVec k))
    (s : OldContentCategory D Sc cutoff ν) (t : OldContentCategory D Sc cutoff (i :: ν))
    (g : (A).obj s.obj ⟶ t.obj) (b : N.obj ((J).obj s)) :
    oldContentDistinctSourceDirectLinear D Sc cutoff ν i j N t
      (BalancedInduction.tensor K ((BalancedInduction.restriction J).obj N).toFunctor s g b) =
      BalancedInduction.tensor A ((BalancedInduction.restriction B).obj
        (BalancedInduction.induced Qj N)).toFunctor s.obj g
        (BalancedInduction.tensor Qj N.toFunctor ((J).obj s) (𝟙 ((B).obj s.obj)) b) := by
  rw [oldContentDistinctSourceLinear_apply]
  have h₁ := oldContentAppendRestrictionLinear_tensor D Sc cutoff ν i
    ((BalancedInduction.restriction J).obj N) s t g b
  have hStep := congrArg (BalancedInduction.mapComponent A
    (oldContentRestrictionExtensionIso D Sc cutoff ν j N).hom 0 t.obj) h₁
  refine hStep.trans ?_
  unfold BalancedInduction.inductionInsertedTensor
  have hm := BalancedInduction.mapComponent_tensor A
    (oldContentRestrictionExtensionIso D Sc cutoff ν j N).hom 0 t.obj s.obj g
    (BalancedInduction.tensor Q₀ ((BalancedInduction.restriction J).obj N).toFunctor s (𝟙 s.obj) b)
  have hf := oldContentRestrictionExtensionComponent_zero D Sc cutoff ν j N s.obj
  have hs := oldContentRestrictionExtensionLinear_tensor D Sc cutoff ν j N s.obj s (𝟙 s.obj) b
  have he : oldContentRestrictionExtensionComponent D Sc cutoff ν j 0 N s.obj
      (BalancedInduction.tensor Q₀ ((BalancedInduction.restriction J).obj N).toFunctor s (𝟙 s.obj) b) =
      BalancedInduction.tensor Qj N.toFunctor ((J).obj s) (𝟙 ((B).obj s.obj)) b := by
    rw [hf]
    exact hs.trans (congrArg (fun a => BalancedInduction.tensor Qj N.toFunctor
      ((J).obj s) a b) ((B).map_id s.obj))
  exact hm.trans (congrArg₂ (fun a z => BalancedInduction.tensor A
    ((BalancedInduction.restriction B).obj (BalancedInduction.induced Qj N)).toFunctor
      s.obj a z) (twist_zero g) he)

/-- The selected source chart followed by canonical ordinary coefficient coordinates. -/
def oldContentDistinctSourceLinear
    (N : Superfunctor k (OldContentCategory D Sc cutoff (j :: ν)) (SVec k))
    (t : OldContentCategory D Sc cutoff (i :: ν)) :
    BalancedInduction.Obj K ((BalancedInduction.restriction J).obj N).toFunctor t →ₗ[k]
      BalancedInduction.Obj A ((B) ⋙ (BalancedInduction.induced Qj N).toFunctor) t.obj :=
  (DistinctContent.restrictionCoendEquiv A B (BalancedInduction.induced Qj N) t.obj).toLinearMap ∘ₗ
    oldContentDistinctSourceDirectLinear D Sc cutoff ν i j N t

/-- Ordinary coefficient coordinates preserve the entire selected source tensor. -/
theorem oldContentDistinctSourceLinear_tensor
    (N : Superfunctor k (OldContentCategory D Sc cutoff (j :: ν)) (SVec k))
    (s : OldContentCategory D Sc cutoff ν) (t : OldContentCategory D Sc cutoff (i :: ν))
    (g : (A).obj s.obj ⟶ t.obj) (b : N.obj ((J).obj s)) :
    oldContentDistinctSourceLinear D Sc cutoff ν i j N t
      (BalancedInduction.tensor K ((BalancedInduction.restriction J).obj N).toFunctor s g b) =
      BalancedInduction.tensor A ((B) ⋙ (BalancedInduction.induced Qj N).toFunctor) s.obj g
        (BalancedInduction.tensor Qj N.toFunctor ((J).obj s) (𝟙 ((B).obj s.obj)) b) := by
  rw [oldContentDistinctSourceLinear, LinearMap.comp_apply,
    oldContentDistinctSourceDirectLinear_tensor, LinearEquiv.coe_coe]
  exact DistinctContent.restrictionCoendEquiv_tensor A B (BalancedInduction.induced Qj N)
    s.obj t.obj g (BalancedInduction.tensor Qj N.toFunctor ((J).obj s) (𝟙 ((B).obj s.obj)) b)

/-- The selected target chart on literal balanced coends. -/
def oldContentDistinctTargetLinear
    (N : Superfunctor k (OldContentCategory D Sc cutoff (j :: ν)) (SVec k))
    (t : OldContentCategory D Sc cutoff (i :: ν)) :
    BalancedInduction.Obj L N.toFunctor ((M).obj t) →ₗ[k]
      BalancedInduction.Obj A (BalancedInduction.induced Qj N).toFunctor ((B).obj t.obj) :=
  oldContentAppendRestrictionLinear D Sc cutoff (j :: ν) i N ((M).obj t)

/-- The chosen upper content comparison retains its literal old coefficient arrow. -/
theorem oldContentDistinctTargetLinear_tensor
    (N : Superfunctor k (OldContentCategory D Sc cutoff (j :: ν)) (SVec k))
    (s : OldContentCategory D Sc cutoff (j :: ν)) (t : OldContentCategory D Sc cutoff (i :: ν))
    (g : (A).obj s.obj ⟶ (B).obj t.obj) (b : N.obj s) :
    oldContentDistinctTargetLinear D Sc cutoff ν i j N t
      (BalancedInduction.tensor L N.toFunctor s g b) =
      BalancedInduction.tensor A (BalancedInduction.induced Qj N).toFunctor s.obj g
        (BalancedInduction.tensor Qj N.toFunctor s (𝟙 s.obj) b) :=
  oldContentAppendRestrictionLinear_tensor D Sc cutoff (j :: ν) i N s ((M).obj t) g b

/-- The entire content coefficient, read through the literal upper inclusion. -/
def oldContentDistinctCoefficient
    (s : OldContentCategory D Sc cutoff ν) (t : OldContentCategory D Sc cutoff (i :: ν))
    (g : (K).obj s ⟶ t) : (J ⋙ L).obj s ⟶ (M).obj t :=
  oldContentDistinctCross D Sc cutoff ν i j s ≫
    twist k (D.parity i * D.parity j) ((M).map g)

/-- Total parity transport commutes with the chosen content inclusion. -/
theorem oldContentDistinctCoefficient_eq
    (s : OldContentCategory D Sc cutoff ν) (t : OldContentCategory D Sc cutoff (i :: ν))
    (g : (K).obj s ⟶ t) :
    (oldContentInclusion D Sc cutoff (i :: j :: ν)).map
      (oldContentDistinctCoefficient D Sc cutoff ν i j s t g) =
      Distinct.crossComponent D Sc cutoff i j s.obj ≫
        twist k (D.parity i * D.parity j) ((B).map g) := by
  rw [oldContentDistinctCoefficient, Functor.map_comp, map_twist]
  rfl

private theorem oldContentAppend_obj_obj (μ : List I) (a : I)
    (s : OldContentCategory D Sc cutoff μ) :
    ((oldContentAppend D Sc cutoff μ a).obj s).obj =
      (append D Sc cutoff a).obj s.obj := rfl

private theorem oldContentInclusion_map (μ : List I)
    (s t : OldContentCategory D Sc cutoff μ) (f : s ⟶ t) :
    (oldContentInclusion D Sc cutoff μ).map f = f := rfl

/-- The whole prescribed positive mate commutes with both chosen E/F charts. -/
theorem oldContentDistinctMateLinear_square
    (N : Superfunctor k (OldContentCategory D Sc cutoff (j :: ν)) (SVec k))
    (t : OldContentCategory D Sc cutoff (i :: ν)) :
    oldContentDistinctTargetLinear D Sc cutoff ν i j N t ∘ₗ
        BalancedInduction.orderedRectangularMateLinear J K L M
          (oldContentDistinctCross_supernatural D Sc cutoff ν i j) N t =
      Distinct.moduleMateLinear D Sc cutoff i j (BalancedInduction.induced Qj N) t.obj ∘ₗ
        oldContentDistinctSourceLinear D Sc cutoff ν i j N t := by
  apply BalancedInduction.hom_ext
  intro s g b
  have hM := BalancedInduction.orderedRectangularMateLinear_tensor (k := k)
    J K L M (oldContentDistinctCross_supernatural D Sc cutoff ν i j) N s t g b
  generalize hCoeff : (oldContentDistinctCross D Sc cutoff ν i j s ≫
    twist k (D.parity i * D.parity j) ((M).map g)) = c' at hM
  have hL := congrArg (oldContentDistinctTargetLinear D Sc cutoff ν i j N t) hM
  have hT := oldContentDistinctTargetLinear_tensor D Sc cutoff ν i j N ((J).obj s) t c' b
  have hCoeffOld := congrArg (fun a : (J ⋙ L).obj s ⟶ (M).obj t =>
    (oldContentInclusion D Sc cutoff (i :: j :: ν)).map a) hCoeff
  have hCEq := hCoeffOld.symm.trans (oldContentDistinctCoefficient_eq D Sc cutoff ν i j s t g)
  simp only [oldContentInclusion_map] at hCEq
  have hS := oldContentDistinctSourceLinear_tensor D Sc cutoff ν i j N s t g b
  have hR := congrArg (Distinct.moduleMateLinear D Sc cutoff i j (BalancedInduction.induced Qj N) t.obj) hS
  have hO := Distinct.moduleMateLinear_tensor D Sc cutoff i j (BalancedInduction.induced Qj N)
    s.obj t.obj g (BalancedInduction.tensor Qj N.toFunctor ((J).obj s) (𝟙 ((B).obj s.obj)) b)
  generalize hPhysical : (Distinct.crossComponent D Sc cutoff i j s.obj ≫
    twist k (D.parity i * D.parity j) ((B).map g)) = d' at hCEq hO
  have hC := congrArg (fun a : (A).obj ((B).obj s.obj) ⟶ (B).obj t.obj =>
    BalancedInduction.tensor A (BalancedInduction.induced Qj N).toFunctor ((J).obj s).obj a
      (BalancedInduction.tensor Qj N.toFunctor ((J).obj s) (𝟙 ((B).obj s.obj)) b)) hCEq
  simp only [oldContentAppend_obj_obj] at hT hC
  simp only [LinearMap.comp_apply]
  exact (hL.trans (hT.trans hC)).trans (hR.trans hO).symm

private theorem oldContentInclusion_obj (μ : List I) (t : OldContentCategory D Sc cutoff μ) :
    (oldContentInclusion D Sc cutoff μ).obj t = t.obj := rfl

private theorem oldContentDistinctUpperAppend_obj_obj
    (t : OldContentCategory D Sc cutoff (i :: ν)) :
    ((M).obj t).obj = (B).obj t.obj := rfl

/-- The selected source chart is bijective after ordinary coefficient canonicalization. -/
theorem oldContentDistinctSourceLinear_bijective
    (N : Superfunctor k (OldContentCategory D Sc cutoff (j :: ν)) (SVec k))
    (t : OldContentCategory D Sc cutoff (i :: ν)) :
    Function.Bijective (oldContentDistinctSourceLinear D Sc cutoff ν i j N t) := by
  have hNative : Function.Bijective (oldContentDistinctSourceDirectLinear D Sc cutoff ν i j N t) := by
    have h := BalancedInduction.coendIsoLinear_bijective K A Qi
      ((BalancedInduction.restriction J).obj N)
      ((BalancedInduction.restriction B).obj (BalancedInduction.induced Qj N))
      (oldContentDistinctSourceIso D Sc cutoff ν i j N) t
    simpa only [oldContentDistinctSourceDirectLinear, BalancedInduction.coendIsoLinear,
      oldContentInclusion_obj] using h
  exact DistinctContent.linearMap_comp_bijective (k := k)
    (oldContentDistinctSourceDirectLinear D Sc cutoff ν i j N t)
    (DistinctContent.restrictionCoendEquiv A B (BalancedInduction.induced Qj N) t.obj).toLinearMap
    hNative (DistinctContent.linearEquiv_toLinearMap_bijective (k := k) _)

/-- The selected upper content comparison is bijective on the entire target coend. -/
theorem oldContentDistinctTargetLinear_bijective
    (N : Superfunctor k (OldContentCategory D Sc cutoff (j :: ν)) (SVec k))
    (t : OldContentCategory D Sc cutoff (i :: ν)) :
    Function.Bijective (oldContentDistinctTargetLinear D Sc cutoff ν i j N t) := by
  have h := BalancedInduction.coendIsoLinear_bijective L A
    (oldContentInclusion D Sc cutoff (i :: j :: ν)) N (BalancedInduction.induced Qj N)
    (oldContentAppendRestrictionIso D Sc cutoff (j :: ν) i N) ((M).obj t)
  simpa only [oldContentDistinctTargetLinear, oldContentAppendRestrictionLinear,
    BalancedInduction.coendIsoLinear, oldContentInclusion_obj,
    oldContentDistinctUpperAppend_obj_obj] using h

/-- The prescribed content mate is bijective, using the constructed old inverse and chosen charts. -/
theorem oldContentDistinctMateLinear_bijective (hij : i ≠ j)
    (N : Superfunctor k (OldContentCategory D Sc cutoff (j :: ν)) (SVec k))
    (t : OldContentCategory D Sc cutoff (i :: ν)) :
    Function.Bijective (BalancedInduction.orderedRectangularMateLinear J K L M
      (oldContentDistinctCross_supernatural D Sc cutoff ν i j) N t) := by
  have hOld : Function.Bijective (Distinct.moduleMateLinear D Sc cutoff i j
      (BalancedInduction.induced Qj N) t.obj) := by
    rw [← Distinct.moduleMateUnderlyingEquiv_toLinearMap D Sc cutoff i j hij
      (BalancedInduction.induced Qj N) t.obj]
    exact (Distinct.moduleMateUnderlyingEquiv D Sc cutoff i j hij
      (BalancedInduction.induced Qj N) t.obj).bijective
  apply DistinctContent.bijective_of_square
    (BalancedInduction.orderedRectangularMateLinear J K L M
      (oldContentDistinctCross_supernatural D Sc cutoff ν i j) N t)
    (oldContentDistinctSourceLinear D Sc cutoff ν i j N t)
    (oldContentDistinctTargetLinear D Sc cutoff ν i j N t)
    (Distinct.moduleMateLinear D Sc cutoff i j (BalancedInduction.induced Qj N) t.obj)
    (oldContentDistinctSourceLinear_bijective D Sc cutoff ν i j N t)
    (oldContentDistinctTargetLinear_bijective D Sc cutoff ν i j N t) hOld
  intro x
  exact LinearMap.congr_fun (oldContentDistinctMateLinear_square D Sc cutoff ν i j N t) x

/-- The actual positive content cup-crossing-cap has a linear inverse for every input module. -/
def oldContentDistinctMateEquiv (hij : i ≠ j)
    (N : Superfunctor k (OldContentCategory D Sc cutoff (j :: ν)) (SVec k))
    (t : OldContentCategory D Sc cutoff (i :: ν)) :
    BalancedInduction.Obj K ((BalancedInduction.restriction J).obj N).toFunctor t ≃ₗ[k]
      BalancedInduction.Obj L N.toFunctor ((M).obj t) :=
  BalancedInduction.orderedRectangularMateEquiv J K L M
    (oldContentDistinctCross_supernatural D Sc cutoff ν i j) N t
    (oldContentDistinctMateLinear_bijective D Sc cutoff ν i j hij N t)

@[simp] theorem oldContentDistinctMateEquiv_toLinearMap (hij : i ≠ j)
    (N : Superfunctor k (OldContentCategory D Sc cutoff (j :: ν)) (SVec k))
    (t : OldContentCategory D Sc cutoff (i :: ν)) :
    (oldContentDistinctMateEquiv D Sc cutoff ν i j hij N t).toLinearMap =
      BalancedInduction.orderedRectangularMateLinear J K L M
        (oldContentDistinctCross_supernatural D Sc cutoff ν i j) N t :=
  BalancedInduction.orderedRectangularMateEquiv_toLinearMap J K L M
    (oldContentDistinctCross_supernatural D Sc cutoff ν i j) N t _

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # The prescribed mate on entire chosen content coends

DeformedMatrixComparison (4), (5), principal matrix field. Genuine selected
E/F charts carry the independently given content cup-crossing-cap to the
literal old matrix mate on every coend vector, before finite parity shifts.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open CyclotomicCrossingTensor BalancedInduction
universe u
namespace BalancedInduction
private def mateLinear
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    (A : C ⥤ C) [A.Additive] [A.Linear k] [IsSuperfunctor k A]
    (M : Superfunctor k C (SVec k))
    (f : induced A ((restriction A).obj M) ⟶ (restriction A).obj (induced A M)) (t : C) :
    Obj A ((restriction A).obj M).toFunctor t →ₗ[k] Obj A M.toFunctor (A.obj t) := f.total t

private theorem mateLinear_apply
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    (A : C ⥤ C) [A.Additive] [A.Linear k] [IsSuperfunctor k A]
    (M : Superfunctor k C (SVec k))
    (f : induced A ((restriction A).obj M) ⟶ (restriction A).obj (induced A M)) (t : C)
    (x : Obj A ((restriction A).obj M).toFunctor t) :
    mateLinear A M f t x = f.total t x := rfl

private theorem coendComp_ext
    {k C A V W Z : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive A] [Linear k A] [AddCommMonoid V] [Module k V]
    [AddCommMonoid W] [Module k W] [AddCommMonoid Z] [Module k Z]
    (J : C ⥤ A) (M : C ⥤ SVec k) {w : A}
    (f : Obj J M w →ₗ[k] V) (g : V →ₗ[k] Z)
    (h : Obj J M w →ₗ[k] W) (l : W →ₗ[k] Z)
    (hh : ∀ s (a : J.obj s ⟶ w) (b : M.obj s),
      g (f (tensor J M s a b)) = l (h (tensor J M s a b))) : g ∘ₗ f = l ∘ₗ h := by
  classical
  apply LinearMap.cancel_right (Submodule.mkQ_surjective (relations J M w)) |>.mp
  apply DirectSum.linearMap_ext
  intro s
  apply TensorProduct.ext
  ext a b
  exact hh s a b
end BalancedInduction

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (ν : List I) (i : I)
local notation "J₀" => oldContentAppend D Sc cutoff ν i
local notation "J₁" => oldContentAppend D Sc cutoff (i :: ν) i
local notation "Q₁" => oldContentInclusion D Sc cutoff (i :: ν)
local notation "J" => append D Sc cutoff i

/-- The prescribed old mate on the literal raw coend carriers. -/
def oldMatrixMateLinear
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (t : OldCategory D Sc cutoff) :
    Obj J ((restriction J).obj M).toFunctor t →ₗ[k] Obj J M.toFunctor ((J).obj t) :=
  BalancedInduction.mateLinear J M (matrixMateComponent D Sc cutoff i M) t

/-- The raw map evaluates to the same prescribed module component. -/
theorem oldMatrixMateLinear_apply
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (t : OldCategory D Sc cutoff) (x : Obj J ((restriction J).obj M).toFunctor t) :
    oldMatrixMateLinear D Sc cutoff i M t x = (matrixMateComponent D Sc cutoff i M).total t x :=
  BalancedInduction.mateLinear_apply J M (matrixMateComponent D Sc cutoff i M) t x

/-- The prescribed mate forms a whole linear-map square under the chosen charts. -/
theorem oldContentMatrixCharts_mate_comp
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k))
    (t : OldContentCategory D Sc cutoff (i :: ν)) :
    (oldContentFELinearEquiv D Sc cutoff ν i N t).toLinearMap ∘ₗ
      orderedGridMateLinear J₀ J₁ (oldContentEqualCross_supernatural D Sc cutoff ν i) N t =
    oldMatrixMateLinear D Sc cutoff i (induced Q₁ N) t.obj ∘ₗ
      (oldContentEFLinearEquiv D Sc cutoff ν i N t).toLinearMap := by
  apply BalancedInduction.coendComp_ext J₀ ((restriction J₀).obj N).toFunctor
  intro s a b
  have h := oldContentMatrixCharts_mate_tensor D Sc cutoff ν i N s t a b
  have hm := oldMatrixMateLinear_apply D Sc cutoff i (induced Q₁ N) t.obj
    ((oldContentEFLinearEquiv D Sc cutoff ν i N t).toLinearMap
      (tensor J₀ ((restriction J₀).obj N).toFunctor s a b))
  exact h.trans hm.symm

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # Prescribed cap rows under the chosen content source chart

DeformedMatrixComparison (4), (5): the preceding E/F chart retains the
literal ordinary counit and lower dot powers before canonical target
parity coordinates. No cap compatibility premise is introduced.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open CyclotomicCrossingTensor BalancedInduction
universe u
private theorem coendComp_ext
    {k C A V W Z : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive A] [Linear k A] [AddCommMonoid V] [Module k V]
    [AddCommMonoid W] [Module k W] [AddCommMonoid Z] [Module k Z]
    (J : C ⥤ A) (M : C ⥤ SVec k) {w : A}
    (f : Obj J M w →ₗ[k] V) (g : V →ₗ[k] Z)
    (h : Obj J M w →ₗ[k] W) (l : W →ₗ[k] Z)
    (hh : ∀ s (a : J.obj s ⟶ w) (b : M.obj s),
      g (f (tensor J M s a b)) = l (h (tensor J M s a b))) : g ∘ₗ f = l ∘ₗ h := by
  classical
  apply LinearMap.cancel_right (Submodule.mkQ_surjective (BalancedInduction.relations J M w)) |>.mp
  apply DirectSum.linearMap_ext
  intro s
  apply TensorProduct.ext
  ext a b
  exact hh s a b

private theorem compose_intertwine
    {k V W Z : Type u} [CommRing k] [AddCommMonoid V] [Module k V]
    [AddCommMonoid W] [Module k W] [AddCommMonoid Z] [Module k Z]
    (C₁ : V →ₗ[k] W) (C₂ : W →ₗ[k] Z)
    (f : Module.End k V) (g : Module.End k W) (h : Module.End k Z)
    (h₁ : C₁ ∘ₗ f = g ∘ₗ C₁) (h₂ : C₂ ∘ₗ g = h ∘ₗ C₂) :
    (C₂ ∘ₗ C₁) ∘ₗ f = h ∘ₗ (C₂ ∘ₗ C₁) := by
  apply LinearMap.ext
  intro x
  exact (congrArg C₂ (LinearMap.congr_fun h₁ x)).trans (LinearMap.congr_fun h₂ (C₁ x))

namespace BalancedInduction
private theorem capDotLinear_intertwine
    {k C A W Z : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    [AddCommMonoid W] [Module k W] [AddCommMonoid Z] [Module k Z]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
    (N : Superfunctor k A (SVec k)) (w : A)
    (L : Obj J ((restriction J).obj N).toFunctor w →ₗ[k] W) (g : Module.End k W)
    (V : N.obj w →ₗ[k] Z) (c : W →ₗ[k] Z)
    (hd : L ∘ₗ transformLinear hα ((restriction J).obj N) w = g ∘ₗ L)
    (hc : V ∘ₗ restrictionCounitLinear J N w = c ∘ₗ L) (n : ℕ)
    (x : Obj J ((restriction J).obj N).toFunctor w) :
    V (capDotLinear J hα N n w x) = c ((g ^ n) (L x)) := by
  let f : Module.End k (Obj J ((restriction J).obj N).toFunctor w) :=
    transformLinear hα ((restriction J).obj N) w
  have h₀ := LinearMap.congr_fun hc ((f ^ n) x)
  have hp := intertwine_pow_apply L f g (fun y => LinearMap.congr_fun hd y) n x
  exact h₀.trans (congrArg c hp)

private theorem capDotLinear_apply_power
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
    (N : Superfunctor k A (SVec k)) (n : ℕ) (w : A)
    (x : Obj J ((restriction J).obj N).toFunctor w) :
    capDotLinear J hα N n w x = restrictionCounitLinear J N w
      (((transformLinear hα ((restriction J).obj N) w :
        Module.End k (Obj J ((restriction J).obj N).toFunctor w)) ^ n) x) := rfl
end BalancedInduction

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (ν : List I) (i : I)
local notation "J₀" => oldContentAppend D Sc cutoff ν i
local notation "Q₀" => oldContentInclusion D Sc cutoff ν
local notation "Q₁" => oldContentInclusion D Sc cutoff (i :: ν)
local notation "J" => append D Sc cutoff i

/-- The genuine selected source and value charts carry the independently
given content counit to the given old ordinary counit. -/
theorem oldContentEFLinearEquiv_counit
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k))
    (t : OldContentCategory D Sc cutoff (i :: ν)) :
    (oldContentValueLinearEquiv D Sc cutoff ν i N t).toLinearMap ∘ₗ
      restrictionCounitLinear J₀ N t =
    restrictionCounitLinear J (induced Q₁ N) t.obj ∘ₗ
      (oldContentEFLinearEquiv D Sc cutoff ν i N t).toLinearMap := by
  apply coendComp_ext J₀ ((restriction J₀).obj N).toFunctor
  intro s a b
  have hc := restrictionCounitLinear_tensor J₀ N s t a b
  have hl := congrArg (oldContentValueLinearEquiv D Sc cutoff ν i N t) hc
  have hv := oldContentValueLinearEquiv_apply D Sc cutoff ν i N t (N.map a b)
  have hLeft := hl.trans hv
  have he := oldContentEFRestrictionLinear_tensor D Sc cutoff ν i N s t a b
  have hStep := congrArg (restrictionCounitLinear J (induced Q₁ N) t.obj) he
  have hOld := restrictionCounitLinear_tensor J (induced Q₁ N) s.obj t.obj a
    (tensor Q₁ N.toFunctor ((J₀).obj s) (𝟙 ((J).obj s.obj)) b)
  have hu := LinearMap.congr_fun (unit_naturality Q₁ N.toFunctor a) b
  set_option backward.dsimp.instances true in
    dsimp only [restriction, Superfunctor.comp] at hStep hOld
  have hRight := hStep.trans hOld
  have hUnit : (induced Q₁ N).map a
      (tensor Q₁ N.toFunctor ((J₀).obj s) (𝟙 ((J).obj s.obj)) b) =
      tensor Q₁ N.toFunctor t (𝟙 t.obj) (N.map a b) := hu
  have hWhole := hLeft.trans (hUnit.symm.trans hRight.symm)
  rw [oldContentEFLinearEquiv_hom]
  set_option backward.dsimp.instances true in
    dsimp only [restriction, Superfunctor.comp] at hWhole ⊢
  exact hWhole

/-- The same selected preceding E/F source chart intertwines the literal
lower dot, including its complete coefficient twist. -/
theorem oldContentEFLinearEquiv_dot
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k))
    (t : OldContentCategory D Sc cutoff (i :: ν)) :
    (oldContentEFLinearEquiv D Sc cutoff ν i N t).toLinearMap ∘ₗ
      transformLinear (oldContentAppendDot_supernatural D Sc cutoff ν i)
        ((restriction J₀).obj N) t =
    inductionDot D Sc cutoff i ((restriction J).obj (induced Q₁ N)) t.obj ∘ₗ
      (oldContentEFLinearEquiv D Sc cutoff ν i N t).toLinearMap := by
  let C₁ := oldContentAppendRestrictionLinear D Sc cutoff ν i ((restriction J₀).obj N) t
  let C₂ := mapComponent J (oldContentRestrictionExtensionIso D Sc cutoff ν i N).hom 0 t.obj
  have h₁ := oldContentAppendRestrictionIso_dot D Sc cutoff ν i ((restriction J₀).obj N) t
  have h₂ := transform_mapComponent (oldAppendDot_supernatural D Sc cutoff i)
    (induced Q₀ ((restriction J₀).obj N))
    (oldContentRestrictionExtensionIso D Sc cutoff ν i N).hom 0 t.obj
  simp only [mul_zero, sign_zero, one_smul] at h₂
  dsimp only [inductionDot] at h₁ ⊢
  have hcomp := compose_intertwine _ _ _ _ _ h₁ h₂.symm
  have hfactor : (oldContentEFLinearEquiv D Sc cutoff ν i N t).toLinearMap = C₂ ∘ₗ C₁ := by
    apply LinearMap.ext
    intro x
    rw [oldContentEFLinearEquiv_hom]
    dsimp only [C₁, C₂, LinearMap.comp_apply]
    exact oldContentEFRestrictionLinear_apply D Sc cutoff ν i N t x
  rw [hfactor]
  exact hcomp

/-- Every prescribed dot/counit row is carried by the genuine selected
preceding E/F and value charts to the identical old cap row. -/
theorem oldContentEFLinearEquiv_capDot
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k))
    (t : OldContentCategory D Sc cutoff (i :: ν)) (n : ℕ)
    (x : Obj J₀ ((restriction J₀).obj N).toFunctor t) :
    oldContentValueLinearEquiv D Sc cutoff ν i N t
      (capDotLinear J₀ (oldContentAppendDot_supernatural D Sc cutoff ν i) N n t x) =
    capDotLinear J (oldAppendDot_supernatural D Sc cutoff i) (induced Q₁ N) n t.obj
      (oldContentEFLinearEquiv D Sc cutoff ν i N t x) := by
  have hd := oldContentEFLinearEquiv_dot D Sc cutoff ν i N t
  have hc := oldContentEFLinearEquiv_counit D Sc cutoff ν i N t
  have hp := BalancedInduction.capDotLinear_intertwine J₀
    (oldContentAppendDot_supernatural D Sc cutoff ν i) N t _ _ _ _ hd hc n x
  have ht := BalancedInduction.capDotLinear_apply_power J
    (oldAppendDot_supernatural D Sc cutoff i) (induced Q₁ N) n t.obj
    (oldContentEFLinearEquiv D Sc cutoff ν i N t x)
  dsimp only [inductionDot] at hp
  exact hp.trans ht.symm

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # Chosen content coordinates for finite unit and cap families

Brundan--Ellis (1.13)--(1.14), DeformedMatrixComparison (4), (5):
the canonical parity coordinates conjugate the selected E/F and value
linear equivalences. These are genuine whole finite-family equivalences,
independently of any inverse-matrix or chart-evenness premise.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open CyclotomicCrossingTensor BalancedInduction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (ν : List I) (i : I)
local notation "J₀" => oldContentAppend D Sc cutoff ν i
local notation "J₁" => oldContentAppend D Sc cutoff (i :: ν) i
local notation "Q₁" => oldContentInclusion D Sc cutoff (i :: ν)
local notation "J" => append D Sc cutoff i
local instance contentGridCoordinatesPi : PiSupercategory k
    (Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k)) := supermodulePiSupercategory
local instance oldGridCoordinatesPi : PiSupercategory k
    (Superfunctor k (OldCategory D Sc cutoff) (SVec k)) := supermodulePiSupercategory
variable (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k))
  (m : ℕ) (t : OldContentCategory D Sc cutoff (i :: ν))
local notation "M" => induced Q₁ N

/-- Every unit-family coordinate uses its selected plain chart and the
existing canonical source and target parity coordinates. -/
def oldContentUnitSlotEquiv (a : Option (Fin m)) :
    (gridUnitMatrixFamily J₀ (D.parity i) N m a).obj t ≃ₗ[k]
      (unitMatrixFamily D Sc cutoff i M m a).obj t.obj := by
  cases a with
  | none =>
    dsimp only [gridUnitMatrixFamily, unitMatrixFamily]
    exact shiftedModuleValueLinearEquiv
      (induced J₀ ((restriction J₀).obj N)) (induced J ((restriction J).obj M))
      t t.obj (oldContentEFLinearEquiv D Sc cutoff ν i N t) (D.parity i)
  | some r =>
    dsimp only [gridUnitMatrixFamily, unitMatrixFamily]
    exact shiftedModuleValueLinearEquiv N M t t.obj
      (oldContentValueLinearEquiv D Sc cutoff ν i N t) (r.val • D.parity i)

/-- Every cap-family coordinate retains its selected F/E or value chart. -/
def oldContentCapSlotEquiv (a : Option (Fin m)) :
    (gridCapMatrixFamily J₁ (D.parity i) N m a).obj t ≃ₗ[k]
      (capMatrixFamily D Sc cutoff i M m a).obj t.obj := by
  cases a with
  | none =>
    dsimp only [gridCapMatrixFamily, capMatrixFamily]
    exact shiftedModuleValueLinearEquiv
      ((restriction J₁).obj (induced J₁ N)) ((restriction J).obj (induced J M))
      t t.obj (oldContentFELinearEquiv D Sc cutoff ν i N t) (D.parity i)
  | some r =>
    dsimp only [gridCapMatrixFamily, capMatrixFamily]
    exact shiftedModuleValueLinearEquiv N M t t.obj
      (oldContentValueLinearEquiv D Sc cutoff ν i N t) (r.val • D.parity i)

/-- The whole finite unit source comparison is a genuine coordinate product. -/
def oldContentUnitFamilyEquiv :
    gridUnitMatrixSourceSpace J₀ (D.parity i) N m t ≃ₗ[k]
      unitMatrixSourceSpace D Sc cutoff i M m t.obj :=
  LinearEquiv.piCongrRight (oldContentUnitSlotEquiv D Sc cutoff ν i N m t)

/-- The whole finite cap target comparison is a genuine coordinate product. -/
def oldContentCapFamilyEquiv :
    gridCapMatrixTargetSpace J₁ (D.parity i) N m t ≃ₗ[k]
      capMatrixTargetSpace D Sc cutoff i M m t.obj :=
  LinearEquiv.piCongrRight (oldContentCapSlotEquiv D Sc cutoff ν i N m t)

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # Prescribed finite content entries in the chosen coordinates

Brundan--Ellis (1.13)--(1.14), DeformedMatrixComparison (4), (5):
principal and dotted fields retain the canonical source/target parity
coordinates under the genuine selected content charts.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open CyclotomicCrossingTensor BalancedInduction
universe u
namespace BalancedInduction
private theorem entryMate_degree_eq
    {k C A B : Type u} [CommRing k]
    [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
    [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    (K : A ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
    {p q : ZMod 2} {γ : ∀ s, (J ⋙ K).obj s ⟶ (J ⋙ K).obj s}
    (e : p = q) (hp : IsSupernatural k p γ) (hq : IsSupernatural k q γ)
    (N : Superfunctor k A (SVec k)) (w : A) :
    orderedGridMateLinear J K hp N w = orderedGridMateLinear J K hq N w := by
  cases e
  rfl
section GenericFields
variable {k C A B : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (K : A ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
local instance contentEntryGenericPi : PiSupercategory k (Superfunctor k A (SVec k)) :=
  supermodulePiSupercategory
private theorem unit_some_total {p : ZMod 2}
    {γ : ∀ s, (J ⋙ K).obj s ⟶ (J ⋙ K).obj s} (hγ : IsSupernatural k p γ)
    {β : ∀ s, K.obj s ⟶ K.obj s} (hβ : IsSupernatural k p β)
    (N : Superfunctor k A (SVec k)) (m : ℕ) (r : Fin m) (w : A) :
    SVec.toLinearMap ((gridUnitMatrixEntry J K hγ hβ N m (some r)).total w) =
      unitDotLinear K hβ N r.val w ∘ₗ
        SVec.toLinearMap (((SKM.homParityShiftDatum (k := k) (r.val • p)).iso N).hom.total w) :=
  gridUnitMatrixEntry_some_total J K hγ hβ N m r w
end GenericFields

end BalancedInduction

section GenericCoordinates
variable {k A B : Type u} [CommRing k]
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
  (M : Superfunctor k A (SVec k)) (N : Superfunctor k B (SVec k))
  (w : A) (v : B) (e : M.obj w ≃ₗ[k] N.obj v)
local instance entryCoordinateSourcePi : PiSupercategory k (Superfunctor k A (SVec k)) :=
  supermodulePiSupercategory
local instance entryCoordinateTargetPi : PiSupercategory k (Superfunctor k B (SVec k)) :=
  supermodulePiSupercategory

private theorem matrixPoint_source_coordinate (q : ZMod 2) :
    SVec.toLinearMap (((SKM.homParityShiftDatum (k := k) q).iso N).hom.total v) ∘ₗ
        (shiftedModuleValueLinearEquiv M N w v e q).toLinearMap =
      e.toLinearMap ∘ₗ SVec.toLinearMap (((SKM.homParityShiftDatum (k := k) q).iso M).hom.total w) := by
  apply LinearMap.ext
  intro b
  exact shiftedModuleValueLinearEquiv_hom_coordinate M N w v e q b

private theorem matrixPoint_target_coordinate (q : ZMod 2) :
    (shiftedModuleValueLinearEquiv M N w v e q).toLinearMap ∘ₗ
        SVec.toLinearMap (((SKM.homParityShiftDatum (k := k) q).iso M).inv.total w) =
      SVec.toLinearMap (((SKM.homParityShiftDatum (k := k) q).iso N).inv.total v) ∘ₗ e.toLinearMap := by
  apply LinearMap.ext
  intro b
  exact shiftedModuleValueLinearEquiv_inv_coordinate M N w v e q b

end GenericCoordinates

private theorem matrixColumn_decorate
    {k V W X Y A B : Type u} [CommRing k]
    [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]
    [AddCommMonoid X] [Module k X] [AddCommMonoid Y] [Module k Y]
    [AddCommMonoid A] [Module k A] [AddCommMonoid B] [Module k B]
    (c : W →ₗ[k] Y) (f : V →ₗ[k] W) (g : X →ₗ[k] Y) (d : V →ₗ[k] X)
    (z : A →ₗ[k] V) (z' : B →ₗ[k] X) (s : A →ₗ[k] B)
    (o : A →ₗ[k] W) (n : B →ₗ[k] Y)
    (h : c ∘ₗ f = g ∘ₗ d) (hz : z' ∘ₗ s = d ∘ₗ z)
    (ho : o = f ∘ₗ z) (hn : n = g ∘ₗ z') : c ∘ₗ o = n ∘ₗ s := by
  rw [ho, hn]
  apply LinearMap.ext
  intro b
  exact (LinearMap.congr_fun h (z b)).trans (congrArg g (LinearMap.congr_fun hz b).symm)

private theorem matrixRow_decorate
    {k V W X Y A B : Type u} [CommRing k]
    [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]
    [AddCommMonoid X] [Module k X] [AddCommMonoid Y] [Module k Y]
    [AddCommMonoid A] [Module k A] [AddCommMonoid B] [Module k B]
    (c : W →ₗ[k] Y) (f : V →ₗ[k] W) (g : X →ₗ[k] Y) (d : V →ₗ[k] X)
    (z : W →ₗ[k] A) (z' : Y →ₗ[k] B) (s : A →ₗ[k] B)
    (o : V →ₗ[k] A) (n : X →ₗ[k] B)
    (h : c ∘ₗ f = g ∘ₗ d) (hz : s ∘ₗ z = z' ∘ₗ c)
    (ho : o = z ∘ₗ f) (hn : n = z' ∘ₗ g) : s ∘ₗ o = n ∘ₗ d := by
  rw [ho, hn]
  apply LinearMap.ext
  intro b
  exact (LinearMap.congr_fun hz (f b)).trans (congrArg z' (LinearMap.congr_fun h b))

private theorem square_degree_reencode
    {k V W X Y : Type u} [CommRing k]
    [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]
    [AddCommMonoid X] [Module k X] [AddCommMonoid Y] [Module k Y]
    (c : W →ₗ[k] Y) (f f' : V →ₗ[k] W) (g : X →ₗ[k] Y) (d : V →ₗ[k] X)
    (he : f = f') (h : c ∘ₗ f = g ∘ₗ d) : c ∘ₗ f' = g ∘ₗ d := by
  rw [← he]
  exact h

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (ν : List I) (i : I)
local notation "J₀" => oldContentAppend D Sc cutoff ν i
local notation "J₁" => oldContentAppend D Sc cutoff (i :: ν) i
local notation "Q₁" => oldContentInclusion D Sc cutoff (i :: ν)
local notation "J" => append D Sc cutoff i
local instance contentEntryCoordinatesPi : PiSupercategory k
    (Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k)) := supermodulePiSupercategory
local instance oldEntryCoordinatesPi : PiSupercategory k
    (Superfunctor k (OldCategory D Sc cutoff) (SVec k)) := supermodulePiSupercategory

/-- The same literal crossing has degree p, using p²=p. -/
theorem oldContentMatrixCross_supernatural :
    IsSupernatural k (D.parity i) (oldContentEqualCross D Sc cutoff ν i) := by
  simpa only [SKM.zmod2_mul_self] using oldContentEqualCross_supernatural D Sc cutoff ν i

private theorem oldUnit_none_total
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (m : ℕ) (w : OldCategory D Sc cutoff) :
    SVec.toLinearMap ((unitMatrixEntry D Sc cutoff i M m none).total w) =
      oldMatrixMateLinear D Sc cutoff i M w ∘ₗ
        SVec.toLinearMap (((SKM.homParityShiftDatum (k := k) (D.parity i)).iso
          (induced J ((restriction J).obj M))).hom.total w) := by
  let e := (SKM.homParityShiftDatum (k := k) (D.parity i)).iso (induced J ((restriction J).obj M))
  change SVec.toLinearMap ((e.hom ≫ matrixMateComponent D Sc cutoff i M).total w) = _
  rw [Superfunctor.comp_total, SVec.toLinearMap_comp]
  rfl

private theorem oldUnit_some_total
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (m : ℕ) (r : Fin m) (w : OldCategory D Sc cutoff) :
    SVec.toLinearMap ((unitMatrixEntry D Sc cutoff i M m (some r)).total w) =
      unitDotLinear J (oldAppendDot_supernatural D Sc cutoff i) M r.val w ∘ₗ
        SVec.toLinearMap (((SKM.homParityShiftDatum (k := k) (r.val • D.parity i)).iso M).hom.total w) := by
  let e := (SKM.homParityShiftDatum (k := k) (r.val • D.parity i)).iso M
  change SVec.toLinearMap ((e.hom ≫ moduleUnitColumn D Sc cutoff i M r.val).total w) = _
  simp only [Superfunctor.comp_total, SVec.toLinearMap_comp, moduleUnitColumn_eq_unitDotColumn,
    unitDotColumn_total, e]

private theorem oldCap_none_total
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (m : ℕ) (w : OldCategory D Sc cutoff) :
    SVec.toLinearMap ((capMatrixEntry D Sc cutoff i M m none).total w) =
      SVec.toLinearMap (((SKM.homParityShiftDatum (k := k) (D.parity i)).iso
        ((restriction J).obj (induced J M))).inv.total w) ∘ₗ
          oldMatrixMateLinear D Sc cutoff i M w := by
  let e := (SKM.homParityShiftDatum (k := k) (D.parity i)).iso ((restriction J).obj (induced J M))
  change SVec.toLinearMap ((matrixMateComponent D Sc cutoff i M ≫ e.inv).total w) = _
  rw [Superfunctor.comp_total, SVec.toLinearMap_comp]
  rfl

private theorem oldCap_some_total
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (m : ℕ) (r : Fin m) (w : OldCategory D Sc cutoff) :
    SVec.toLinearMap ((capMatrixEntry D Sc cutoff i M m (some r)).total w) =
      SVec.toLinearMap (((SKM.homParityShiftDatum (k := k) (r.val • D.parity i)).iso M).inv.total w) ∘ₗ
        capDotLinear J (oldAppendDot_supernatural D Sc cutoff i) M r.val w := by
  let e := (SKM.homParityShiftDatum (k := k) (r.val • D.parity i)).iso M
  change SVec.toLinearMap ((moduleCapRow D Sc cutoff i M r.val ≫ e.inv).total w) = _
  simp only [Superfunctor.comp_total, SVec.toLinearMap_comp, moduleCapRow_eq_capDotRow,
    capDotRow_total, e]

/-- The chosen charts intertwine the unshifted principal entry. -/
private theorem oldContentEntry_mate
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k))
    (t : OldContentCategory D Sc cutoff (i :: ν)) :
    (oldContentFELinearEquiv D Sc cutoff ν i N t).toLinearMap ∘ₗ
      orderedGridMateLinear J₀ J₁ (oldContentMatrixCross_supernatural D Sc cutoff ν i) N t =
    oldMatrixMateLinear D Sc cutoff i (induced Q₁ N) t.obj ∘ₗ
      (oldContentEFLinearEquiv D Sc cutoff ν i N t).toLinearMap := by
  have he := BalancedInduction.entryMate_degree_eq J₀ J₁
    (SKM.zmod2_mul_self (D.parity i))
    (oldContentEqualCross_supernatural D Sc cutoff ν i)
    (oldContentMatrixCross_supernatural D Sc cutoff ν i) N t
  exact square_degree_reencode _ _ _ _ _ he
    (oldContentMatrixCharts_mate_comp D Sc cutoff ν i N t)

/-- The first prescribed unit field retains the canonical source coordinate. -/
theorem oldContentUnitEntry_none_square
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k))
    (m : ℕ) (t : OldContentCategory D Sc cutoff (i :: ν)) :
    (oldContentFELinearEquiv D Sc cutoff ν i N t).toLinearMap ∘ₗ
      SVec.toLinearMap ((gridUnitMatrixEntry J₀ J₁
        (oldContentMatrixCross_supernatural D Sc cutoff ν i)
        (oldContentAppendDot_supernatural D Sc cutoff (i :: ν) i) N m none).total t) =
    SVec.toLinearMap ((unitMatrixEntry D Sc cutoff i (induced Q₁ N) m none).total t.obj) ∘ₗ
      (oldContentUnitSlotEquiv D Sc cutoff ν i N m t none).toLinearMap := by
  have h := oldContentEntry_mate D Sc cutoff ν i N t
  have hz := matrixPoint_source_coordinate
    (induced J₀ ((restriction J₀).obj N)) (induced J ((restriction J).obj (induced Q₁ N)))
    t t.obj (oldContentEFLinearEquiv D Sc cutoff ν i N t) (D.parity i)
  have ho := gridUnitMatrixEntry_none_total J₀ J₁
    (oldContentMatrixCross_supernatural D Sc cutoff ν i)
    (oldContentAppendDot_supernatural D Sc cutoff (i :: ν) i) N m t
  have hn := oldUnit_none_total D Sc cutoff i (induced Q₁ N) m t.obj
  exact matrixColumn_decorate _ _ _ _ _ _ _ _ _ h hz ho hn

/-- Every prescribed dotted unit field retains its canonical source coordinate. -/
theorem oldContentUnitEntry_some_square
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k))
    (m : ℕ) (t : OldContentCategory D Sc cutoff (i :: ν)) (r : Fin m) :
    (oldContentFELinearEquiv D Sc cutoff ν i N t).toLinearMap ∘ₗ
      SVec.toLinearMap ((gridUnitMatrixEntry J₀ J₁
        (oldContentMatrixCross_supernatural D Sc cutoff ν i)
        (oldContentAppendDot_supernatural D Sc cutoff (i :: ν) i) N m (some r)).total t) =
    SVec.toLinearMap ((unitMatrixEntry D Sc cutoff i (induced Q₁ N) m (some r)).total t.obj) ∘ₗ
      (oldContentUnitSlotEquiv D Sc cutoff ν i N m t (some r)).toLinearMap := by
  have h : (oldContentFELinearEquiv D Sc cutoff ν i N t).toLinearMap ∘ₗ
      unitDotLinear J₁ (oldContentAppendDot_supernatural D Sc cutoff (i :: ν) i) N r.val t =
    unitDotLinear J (oldAppendDot_supernatural D Sc cutoff i) (induced Q₁ N) r.val t.obj ∘ₗ
      (oldContentValueLinearEquiv D Sc cutoff ν i N t).toLinearMap := by
    apply LinearMap.ext
    intro b
    exact oldContentFELinearEquiv_unitDot D Sc cutoff ν i N t r.val b
  have hz := matrixPoint_source_coordinate N (induced Q₁ N)
    t t.obj (oldContentValueLinearEquiv D Sc cutoff ν i N t) (r.val • D.parity i)
  have ho := BalancedInduction.unit_some_total J₀ J₁
    (oldContentMatrixCross_supernatural D Sc cutoff ν i)
    (oldContentAppendDot_supernatural D Sc cutoff (i :: ν) i) N m r t
  have hn := oldUnit_some_total D Sc cutoff i (induced Q₁ N) m r t.obj
  exact matrixColumn_decorate _ _ _ _ _ _ _ _ _ h hz ho hn

/-- The principal cap field retains the canonical target coordinate. -/
theorem oldContentCapEntry_none_square
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k))
    (m : ℕ) (t : OldContentCategory D Sc cutoff (i :: ν)) :
    (oldContentCapSlotEquiv D Sc cutoff ν i N m t none).toLinearMap ∘ₗ
      SVec.toLinearMap ((gridCapMatrixEntry J₀ J₁
        (oldContentMatrixCross_supernatural D Sc cutoff ν i)
        (oldContentAppendDot_supernatural D Sc cutoff ν i) N m none).total t) =
    SVec.toLinearMap ((capMatrixEntry D Sc cutoff i (induced Q₁ N) m none).total t.obj) ∘ₗ
      (oldContentEFLinearEquiv D Sc cutoff ν i N t).toLinearMap := by
  have h := oldContentEntry_mate D Sc cutoff ν i N t
  have hz := matrixPoint_target_coordinate
    ((restriction J₁).obj (induced J₁ N)) ((restriction J).obj (induced J (induced Q₁ N)))
    t t.obj (oldContentFELinearEquiv D Sc cutoff ν i N t) (D.parity i)
  have ho := gridCapMatrixEntry_none_total J₀ J₁
    (oldContentMatrixCross_supernatural D Sc cutoff ν i)
    (oldContentAppendDot_supernatural D Sc cutoff ν i) N m t
  have hn := oldCap_none_total D Sc cutoff i (induced Q₁ N) m t.obj
  exact matrixRow_decorate _ _ _ _ _ _ _ _ _ h hz ho hn

/-- Every dotted cap field retains the canonical target coordinate. -/
theorem oldContentCapEntry_some_square
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k))
    (m : ℕ) (t : OldContentCategory D Sc cutoff (i :: ν)) (r : Fin m) :
    (oldContentCapSlotEquiv D Sc cutoff ν i N m t (some r)).toLinearMap ∘ₗ
      SVec.toLinearMap ((gridCapMatrixEntry J₀ J₁
        (oldContentMatrixCross_supernatural D Sc cutoff ν i)
        (oldContentAppendDot_supernatural D Sc cutoff ν i) N m (some r)).total t) =
    SVec.toLinearMap ((capMatrixEntry D Sc cutoff i (induced Q₁ N) m (some r)).total t.obj) ∘ₗ
      (oldContentEFLinearEquiv D Sc cutoff ν i N t).toLinearMap := by
  have h : (oldContentValueLinearEquiv D Sc cutoff ν i N t).toLinearMap ∘ₗ
      capDotLinear J₀ (oldContentAppendDot_supernatural D Sc cutoff ν i) N r.val t =
    capDotLinear J (oldAppendDot_supernatural D Sc cutoff i) (induced Q₁ N) r.val t.obj ∘ₗ
      (oldContentEFLinearEquiv D Sc cutoff ν i N t).toLinearMap := by
    apply LinearMap.ext
    intro b
    exact oldContentEFLinearEquiv_capDot D Sc cutoff ν i N t r.val b
  have hz := matrixPoint_target_coordinate N (induced Q₁ N)
    t t.obj (oldContentValueLinearEquiv D Sc cutoff ν i N t) (r.val • D.parity i)
  have ho := gridCapMatrixEntry_some_total J₀ J₁
    (oldContentMatrixCross_supernatural D Sc cutoff ν i)
    (oldContentAppendDot_supernatural D Sc cutoff ν i) N m r t
  have hn := oldCap_some_total D Sc cutoff i (induced Q₁ N) m r t.obj
  exact matrixRow_decorate _ _ _ _ _ _ _ _ _ h hz ho hn

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # The old missing-colour unit inverse in content coordinates

Brundan–Ellis (1.13) at the empty boundary: the proved-zero principal
coordinate is removed from the prescribed global inverse, and the chosen
following F/E and shifted value charts transport its remaining columns.
The input module retains the full old coefficient algebra.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open BalancedInduction CyclotomicCrossingTensor
universe u

private def givenUnitIsoLinearEquiv {k : Type u} [CommRing k] {V W : SVec k}
    (e : V ≅ W) : V ≃ₗ[k] W where
  toLinearMap := e.hom
  invFun := e.inv
  left_inv x := congrArg (fun f : V ⟶ V => f x) e.hom_inv_id
  right_inv x := congrArg (fun f : W ⟶ W => f x) e.inv_hom_id

private def conjugateUnitIso {k : Type u} [CommRing k] {V W V' W' : SVec k}
    (v : V ≃ₗ[k] V') (w : W ≃ₗ[k] W') (e : V' ≅ W') : V ≅ W :=
  SVec.isoOfLinearEquiv (v.trans ((givenUnitIsoLinearEquiv e).trans w.symm))

private theorem conjugateUnitIso_hom {k : Type u} [CommRing k] {V W V' W' : SVec k}
    (v : V ≃ₗ[k] V') (w : W ≃ₗ[k] W') (e : V' ≅ W') (f : V ⟶ W)
    (h : w.toLinearMap.comp f = e.hom.comp v.toLinearMap) :
    (conjugateUnitIso v w e).hom = f := by
  apply SVec.hom_ext
  intro x
  apply w.injective
  change w (w.symm (e.hom (v x))) = w (f x)
  rw [LinearEquiv.apply_symm_apply]
  exact (LinearMap.congr_fun h x).symm

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (γ : List I) (i : I) (hi : i ∉ γ)
  (N : Superfunctor k (OldContentCategory D Sc cutoff γ) (SVec k))
  (w : OldContentCategory D Sc cutoff γ)
local notation "Q" => oldContentInclusion D Sc cutoff γ
local notation "G" => induced Q N
local notation "K" => oldContentAppend D Sc cutoff γ i
local notation "J" => append D Sc cutoff i
local notation "dK" => oldContentAppendDot_supernatural D Sc cutoff γ i
local notation "dJ" => oldAppendDot_supernatural D Sc cutoff i
local notation "count" => contentUnitCount D cutoff i (γ : Multiset I)

private theorem content_unitColumn_square (n : ℕ) :
    (oldContentFEChart D Sc cutoff γ i N w).toLinearMap.comp (unitDotLinear K dK N n w) =
      (unitDotLinear J dJ G n w.obj).comp (oldContentValueChart D Sc cutoff γ N w).toLinearMap := by
  apply LinearMap.ext
  intro b
  exact oldContentFEChart_unitDot D Sc cutoff γ i N w n b

private theorem globalUnitIso_hom :
    (missingColourUnitMatrixIso D Sc cutoff γ i hi N w).hom =
      unitColumnMatrix J dJ G count w.obj := by
  rw [missingColourUnitMatrixIso_hom]
  rfl

/-- The prescribed old inverse transported to native content module values,
with its actual finite shifted unit columns. No scalar-evaluation premise. -/
def contentMissingUnitMatrixIso :
    unitColumnSourceSpace (D.parity i) N count w ≅
      ((restriction K).obj ((induction K).obj N)).obj w :=
  conjugateUnitIso
    (V := unitColumnSourceSpace (D.parity i) N count w)
    (W := ((restriction K).obj ((induction K).obj N)).obj w)
    (V' := unitColumnSourceSpace (D.parity i) G count w.obj)
    (W' := ((restriction J).obj ((induction J).obj G)).obj w.obj)
    (unitColumnFamilyEquiv N G w w.obj (oldContentValueChart D Sc cutoff γ N w) (D.parity i) count)
    (oldContentFEChart D Sc cutoff γ i N w)
    (missingColourUnitMatrixIso D Sc cutoff γ i hi N w)

/-- Its forward field is the prescribed matrix of shifted ordinary unit/dot columns. -/
theorem contentMissingUnitMatrixIso_hom :
    (contentMissingUnitMatrixIso D Sc cutoff γ i hi N w).hom =
      unitColumnMatrix K dK N count w := by
  apply conjugateUnitIso_hom
  rw [globalUnitIso_hom]
  exact unitColumnMatrix_square K J dK dJ N G w w.obj
    (oldContentValueChart D Sc cutoff γ N w)
    (oldContentFEChart D Sc cutoff γ i N w).toLinearMap
    (content_unitColumn_square D Sc cutoff γ i N w) count

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # The old missing-colour inverse as a module isomorphism

Brundan–Ellis (1.13): the prescribed component inverses assemble with the
ordinary shifted unit columns to an even module inverse, including the
empty old content category and its full coefficient algebra.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open BalancedInduction CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (γ : List I) (i : I) (hi : i ∉ γ)
  (N : Superfunctor k (OldContentCategory D Sc cutoff γ) (SVec k))
local notation "K" => oldContentAppend D Sc cutoff γ i
local notation "hDot" => oldContentAppendDot_supernatural D Sc cutoff γ i
local notation "count" => contentUnitCount D cutoff i (γ : Multiset I)

/-- The constructed even inverse of the actual finite module unit matrix. -/
def contentMissingUnitModuleIso :
    OddMath.FiniteSupermodule.product (unitColumnModuleFamily (D.parity i) N count) ≅
      (restriction K).obj ((induction K).obj N) :=
  unitColumnModuleIso K hDot N count
    (contentMissingUnitMatrixIso D Sc cutoff γ i hi N)
    (contentMissingUnitMatrixIso_hom D Sc cutoff γ i hi N)

/-- The forward module field is exactly the prescribed ordinary shifted unit columns. -/
theorem contentMissingUnitModuleIso_hom :
    (contentMissingUnitModuleIso D Sc cutoff γ i hi N).hom = unitColumnModuleMap K hDot N count :=
  unitColumnModuleIso_hom K hDot N count _ _

end OddMath.QuiverHecke.ELVOld
end

end
