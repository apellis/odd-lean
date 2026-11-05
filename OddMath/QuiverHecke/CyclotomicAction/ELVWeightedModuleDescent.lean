import OddMath.QuiverHecke.CyclotomicAction.ELVOldSupermodules
import OddMath.QuiverHecke.CyclotomicAction.ELVTruncatedCategory

/-! # Descent of modules through the weighted coefficient ideal
The weighted quotient transport needed by SwappedVacuumCoordinates §6
uses the actual coefficientHomIdeal, including its odd generators.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- An old-category module annihilates every prescribed high-weight coefficient
at every word. Odd generators are included without changing the quotient. -/
def KillsWeightedCoefficients (N : ℕ)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) : Prop :=
  ∀ (v : List I) (a : SKM.SYM.CoefficientIndex D),
    N ≤ SKM.SYM.coefficientWeight D a →
      M.map (X := ⟨v⟩) (Y := ⟨v⟩)
        ((ideal D Sc cutoff v v).mkQ
          (coefficientIdentity D Sc cutoff v (SKM.SYM.coefficientBasis D k a))) = 0

/-- The existing old-module action before imposing weighted truncation. -/
def oldModuleRawMap (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (v w : List I) :
    hom D Sc cutoff v w →ₗ[k] (M.obj ⟨v⟩ →ₗ[k] M.obj ⟨w⟩) :=
  (M.toFunctor.mapLinearMap k).comp (ideal D Sc cutoff v w).mkQ

theorem oldModuleRawMap_comp
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (v t w : List I) (f : hom D Sc cutoff v t) (g : hom D Sc cutoff t w) :
    oldModuleRawMap D Sc cutoff M v w (f ≫ g) =
      (oldModuleRawMap D Sc cutoff M t w g).comp
        (oldModuleRawMap D Sc cutoff M v t f) := by
  exact M.toFunctor.map_comp
    ((ideal D Sc cutoff v t).mkQ f : (⟨v⟩ : OldCategory D Sc cutoff) ⟶ ⟨t⟩)
    ((ideal D Sc cutoff t w).mkQ g : (⟨t⟩ : OldCategory D Sc cutoff) ⟶ ⟨w⟩)

/-- Killing the coefficient generators kills the complete defining ideal,
without a flatness or parity restriction on the module. -/
theorem oldModuleRawMap_kills_truncatedIdeal (N : ℕ)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (hM : KillsWeightedCoefficients D Sc cutoff N M) (v w : List I) :
    truncatedIdeal D Sc cutoff N v w ≤
      LinearMap.ker (oldModuleRawMap D Sc cutoff M v w) := by
  apply sup_le
  · intro f hf
    change (M.toFunctor.mapLinearMap k) ((ideal D Sc cutoff v w).mkQ f) = 0
    have hz : (ideal D Sc cutoff v w).mkQ f = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr hf
    rw [hz, map_zero]
  · apply Submodule.span_le.mpr
    rintro _ ⟨t,a,ha,l,r,rfl⟩
    change oldModuleRawMap D Sc cutoff M v w
      (l ≫ coefficientIdentity D Sc cutoff t (SKM.SYM.coefficientBasis D k a) ≫ r) = 0
    rw [oldModuleRawMap_comp, oldModuleRawMap_comp]
    have hz : oldModuleRawMap D Sc cutoff M t t
        (coefficientIdentity D Sc cutoff t (SKM.SYM.coefficientBasis D k a)) = 0 :=
      hM t a ha
    rw [hz, LinearMap.comp_zero, LinearMap.zero_comp]

/-- The literal descended map on each actual truncated Hom. -/
def weightedModuleMap (N : ℕ)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (hM : KillsWeightedCoefficients D Sc cutoff N M) (v w : List I) :
    TruncatedOld D Sc cutoff N v w →ₗ[k] (M.obj ⟨v⟩ →ₗ[k] M.obj ⟨w⟩) :=
  (truncatedIdeal D Sc cutoff N v w).liftQ
    (oldModuleRawMap D Sc cutoff M v w)
    (oldModuleRawMap_kills_truncatedIdeal D Sc cutoff N M hM v w)

/-- The same module, with its action descended to the actual weighted
coefficient-truncated category. Its vector spaces are unchanged. -/
def weightedModuleFunctor (N : ℕ)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (hM : KillsWeightedCoefficients D Sc cutoff N M) :
    TruncatedCategory D Sc cutoff N ⥤ SVec k where
  obj v := M.obj ⟨v.word⟩
  map {v w} := weightedModuleMap D Sc cutoff N M hM v.word w.word
  map_id v := M.toFunctor.map_id (⟨v.word⟩ : OldCategory D Sc cutoff)
  map_comp {v t w} f g := by
    obtain ⟨f, rfl⟩ := (truncatedIdeal D Sc cutoff N v.word t.word).mkQ_surjective f
    obtain ⟨g, rfl⟩ := (truncatedIdeal D Sc cutoff N t.word w.word).mkQ_surjective g
    exact oldModuleRawMap_comp D Sc cutoff M v.word t.word w.word f g

instance weightedModuleFunctor_additive (N : ℕ)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (hM : KillsWeightedCoefficients D Sc cutoff N M) :
    (weightedModuleFunctor D Sc cutoff N M hM).Additive where
  map_add {v w} f g := (weightedModuleMap D Sc cutoff N M hM v.word w.word).map_add f g

instance weightedModuleFunctor_linear (N : ℕ)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (hM : KillsWeightedCoefficients D Sc cutoff N M) :
    (weightedModuleFunctor D Sc cutoff N M hM).Linear k where
  map_smul f c := (weightedModuleMap D Sc cutoff N M hM _ _).map_smul c f

instance weightedModuleFunctor_super (N : ℕ)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (hM : KillsWeightedCoefficients D Sc cutoff N M) :
    IsSuperfunctor k (weightedModuleFunctor D Sc cutoff N M hM) where
  map_mem := by
    intro v w p f hf
    change f ∈ truncatedParity D Sc cutoff N v.word w.word p at hf
    obtain ⟨a, ha, rfl⟩ := hf
    exact IsSuperfunctor.map_mem (F := M.toFunctor) (Submodule.mem_map_of_mem ha)

/-- No new vector space or quotient presentation is substituted for the module. -/
def weightedModule (N : ℕ)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (hM : KillsWeightedCoefficients D Sc cutoff N M) :
    Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k) :=
  ⟨weightedModuleFunctor D Sc cutoff N M hM⟩

/-- The canonical further quotient on the existing old category. -/
def oldTruncateFunctor (N : ℕ) :
    OldCategory D Sc cutoff ⥤ TruncatedCategory D Sc cutoff N where
  obj v := ⟨v.word⟩
  map {v w} := truncateOld D Sc cutoff N v.word w.word
  map_id _ := rfl
  map_comp {v t w} f g := by
    obtain ⟨f, rfl⟩ := (ideal D Sc cutoff v.word t.word).mkQ_surjective f
    obtain ⟨g, rfl⟩ := (ideal D Sc cutoff t.word w.word).mkQ_surjective g
    rfl

instance oldTruncateFunctor_additive (N : ℕ) :
    (oldTruncateFunctor D Sc cutoff N).Additive where
  map_add {v w} f g := (truncateOld D Sc cutoff N v.word w.word).map_add f g

instance oldTruncateFunctor_linear (N : ℕ) :
    (oldTruncateFunctor D Sc cutoff N).Linear k where
  map_smul {v w} f c := (truncateOld D Sc cutoff N v.word w.word).map_smul c f

instance oldTruncateFunctor_super (N : ℕ) :
    IsSuperfunctor k (oldTruncateFunctor D Sc cutoff N) where
  map_mem := by
    intro v w p f hf
    change f ∈ oldParity D Sc cutoff v.word w.word p at hf
    obtain ⟨a, ha, rfl⟩ := hf
    exact Submodule.mem_map_of_mem ha

/-- Pullback of a truncated module to the old category. -/
def weightedRestriction (N : ℕ)
    (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k)) :
    Superfunctor k (OldCategory D Sc cutoff) (SVec k) :=
  (⟨oldTruncateFunctor D Sc cutoff N⟩ :
    Superfunctor k (OldCategory D Sc cutoff) (TruncatedCategory D Sc cutoff N)).comp M

theorem weightedRestriction_kills (N : ℕ)
    (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k)) :
    KillsWeightedCoefficients D Sc cutoff N (weightedRestriction D Sc cutoff N M) := by
  intro v a ha
  have hm : coefficientIdentity D Sc cutoff v (SKM.SYM.coefficientBasis D k a) ∈
      coefficientHomIdeal D Sc cutoff N v v :=
    Submodule.subset_span ⟨v, a, ha, 𝟙 _, 𝟙 _, by simp only [Category.id_comp,
      Category.comp_id]⟩
  have hz : (truncatedIdeal D Sc cutoff N v v).mkQ
      (coefficientIdentity D Sc cutoff v (SKM.SYM.coefficientBasis D k a)) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.mem_sup_right hm)
  change (M.toFunctor.mapLinearMap k)
    ((truncatedIdeal D Sc cutoff N v v).mkQ
      (coefficientIdentity D Sc cutoff v (SKM.SYM.coefficientBasis D k a))) = 0
  rw [hz, map_zero]

/-- Natural module maps descend componentwise, retaining both parities. -/
def weightedModuleHom (N : ℕ)
    (M L : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (hM : KillsWeightedCoefficients D Sc cutoff N M)
    (hL : KillsWeightedCoefficients D Sc cutoff N L) (f : M ⟶ L) :
    weightedModule D Sc cutoff N M hM ⟶ weightedModule D Sc cutoff N L hL :=
  Superfunctor.homMk {
    app := fun p v => f.app p ⟨v.word⟩
    app_mem := fun p v => f.app_mem p ⟨v.word⟩
    naturality := by
      intro p v w q a ha
      change a ∈ truncatedParity D Sc cutoff N v.word w.word q at ha
      obtain ⟨b, hb, rfl⟩ := ha
      let b' : (⟨v.word⟩ : OldCategory D Sc cutoff) ⟶ ⟨w.word⟩ :=
        (ideal D Sc cutoff v.word w.word).mkQ b
      have hb' : b' ∈ parity (R := k) _ _ q := Submodule.mem_map_of_mem hb
      change f.app p ⟨w.word⟩ ∘ₗ M.map b' =
        koszulSign p q • (L.map b' ∘ₗ f.app p ⟨v.word⟩)
      exact f.naturality p b' hb' }

@[simp] theorem weightedModuleHom_id (N : ℕ)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (hM : KillsWeightedCoefficients D Sc cutoff N M) :
    weightedModuleHom D Sc cutoff N M M hM hM (𝟙 M) =
      𝟙 (weightedModule D Sc cutoff N M hM) := by
  apply Superfunctor.hom_ext
  intro p v
  rfl

@[simp] theorem weightedModuleHom_comp (N : ℕ)
    (M L P : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (hM : KillsWeightedCoefficients D Sc cutoff N M)
    (hL : KillsWeightedCoefficients D Sc cutoff N L)
    (hP : KillsWeightedCoefficients D Sc cutoff N P)
    (f : M ⟶ L) (g : L ⟶ P) :
    weightedModuleHom D Sc cutoff N M P hM hP (f ≫ g) =
      weightedModuleHom D Sc cutoff N M L hM hL f ≫
        weightedModuleHom D Sc cutoff N L P hL hP g := by
  apply Superfunctor.hom_ext
  intro p v
  rfl

/-- An existing module isomorphism descends with its prescribed maps and
both inverse products, without tensor-flatness hypotheses. -/
def weightedModuleIso (N : ℕ)
    (M L : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (hM : KillsWeightedCoefficients D Sc cutoff N M)
    (hL : KillsWeightedCoefficients D Sc cutoff N L) (e : M ≅ L) :
    weightedModule D Sc cutoff N M hM ≅ weightedModule D Sc cutoff N L hL where
  hom := weightedModuleHom D Sc cutoff N M L hM hL e.hom
  inv := weightedModuleHom D Sc cutoff N L M hL hM e.inv
  hom_inv_id := by
    rw [← weightedModuleHom_comp, e.hom_inv_id, weightedModuleHom_id]
  inv_hom_id := by
    rw [← weightedModuleHom_comp, e.inv_hom_id, weightedModuleHom_id]

end OddMath.QuiverHecke.ELVOld
