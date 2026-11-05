import OddMath.QuiverHecke.CyclotomicAction.ELVWeightTensorVacuum

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
