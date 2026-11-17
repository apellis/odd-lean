import OddMath.QuiverHecke.CyclotomicAction.ContentAppend.ContentAppendDot
import OddMath.QuiverHecke.CyclotomicAction.DistinctCrossing.DistinctCrossingQuotient
import OddMath.QuiverHecke.CyclotomicAction.ProbeVacuumCharts.ProbeCanonicalContent

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
namespace OddMath.QuiverHecke.ELV.ContentHomSupport
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

end OddMath.QuiverHecke.ELV.ContentHomSupport
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
namespace OddMath.QuiverHecke.ELV.ContentHomSupport
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

end OddMath.QuiverHecke.ELV.ContentHomSupport
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
namespace OddMath.QuiverHecke.ELV
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

end OddMath.QuiverHecke.ELV
end

end
