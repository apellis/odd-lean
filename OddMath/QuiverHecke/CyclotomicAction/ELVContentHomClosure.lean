import OddMath.QuiverHecke.CyclotomicAction.ELVContentHomSupport

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
