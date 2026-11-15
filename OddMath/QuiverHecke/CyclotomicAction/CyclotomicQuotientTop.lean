import OddMath.QuiverHecke.CyclotomicAction.EndpointPolynomials
import OddMath.QuiverHecke.CyclotomicAction.VacuumGrading
import OddMath.QuiverHecke.CyclotomicAction.ModuleInduction
import StringDiagrams.Super.BoxProduct
import OddMath.QuiverHecke.CyclotomicAction.TruncatedAppend
import OddMath.QuiverHecke.CyclotomicAction.MovingShiftRelations
import Mathlib.CategoryTheory.Whiskering
import OddMath.QuiverHecke.CyclotomicAction.TruncatedAppend
import OddMath.QuiverHecke.CyclotomicAction.ParabolicTransport
import OddMath.QuiverHecke.OutputShuffle
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Cyclotomic quotient top

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # The lower-balanced cyclotomic crossing tensor

The source of the right vertical arrow in `DeformedCyclotomicTopRow.md` §4
is balanced over the lower cyclotomic category, not a crossing image.
The last equal-colour crossing defines a map from this tensor to the enlarged
cyclotomic quotient. No injectivity of that map is asserted.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory TensorProduct
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

namespace CyclotomicCrossingTensor

/-- Right append on the full old cyclotomic category. -/
def append (i : I) : OldCategory D Sc cutoff ⥤ OldCategory D Sc cutoff where
  obj s := ⟨s.word ++ [i]⟩
  map {s t} := (ideal D Sc cutoff s.word t.word).mapQ
    (ideal D Sc cutoff (s.word ++ [i]) (t.word ++ [i]))
    (rightContext D Sc cutoff [i] s.word t.word)
    (fun _ hr => ideal_rightContext D Sc cutoff [i] hr)
  map_id s := by
    change (ideal D Sc cutoff _ _).mkQ (rightContext D Sc cutoff [i] _ _ (𝟙 _)) = _
    rw [rightContext_id]
    rfl
  map_comp {s t w} f g := by
    obtain ⟨f, rfl⟩ := (ideal D Sc cutoff s.word t.word).mkQ_surjective f
    obtain ⟨g, rfl⟩ := (ideal D Sc cutoff t.word w.word).mkQ_surjective g
    change (ideal D Sc cutoff _ _).mkQ (rightContext D Sc cutoff [i] _ _ (f ≫ g)) =
      (ideal D Sc cutoff _ _).mkQ
        (rightContext D Sc cutoff [i] _ _ f ≫ rightContext D Sc cutoff [i] _ _ g)
    rw [rightContext_comp]

/-- Total-parity twist on quotient morphisms, with no change of objects. -/
def parityFunctor (p : ZMod 2) : OldCategory D Sc cutoff ⥤ OldCategory D Sc cutoff where
  obj s := s
  map {s t} := oldTwist D Sc cutoff p s.word t.word
  map_id s := by
    change (ideal D Sc cutoff _ _).mkQ (twist k p (𝟙 _)) = _
    rw [twist_id]
    rfl
  map_comp {s t w} f g := by
    obtain ⟨f, rfl⟩ := (ideal D Sc cutoff s.word t.word).mkQ_surjective f
    obtain ⟨g, rfl⟩ := (ideal D Sc cutoff t.word w.word).mkQ_surjective g
    change (ideal D Sc cutoff _ _).mkQ (twist k p (f ≫ g)) =
      (ideal D Sc cutoff _ _).mkQ (twist k p f ≫ twist k p g)
    rw [twist_comp]

/-- The parity-shifted quotient Hom space, using total coefficient parity. -/
def shiftedHom (p : ZMod 2) (v w : List I) : SVec k where
  carrier := Old D Sc cutoff v w
  odd := oldProj D Sc cutoff v w (1 + p)
  odd_comp_odd := by
    apply LinearMap.ext
    intro b
    obtain ⟨b, rfl⟩ := (ideal D Sc cutoff v w).mkQ_surjective b
    change (ideal D Sc cutoff v w).mkQ (proj k (1 + p) (proj k (1 + p) b)) = _
    rw [proj_proj]
    rfl

/-- The right coefficient module has a twisted left action and ordinary right action. -/
def coefficient (p : ZMod 2) (i : I) (v : List I) :
    OldCategory D Sc cutoff ⥤ SVec k where
  obj s := shiftedHom D Sc cutoff p v (s.word ++ [i])
  map {s t} r := oldComp D Sc cutoff v (s.word ++ [i]) (t.word ++ [i]) |>.flip
    ((append D Sc cutoff i).map ((parityFunctor D Sc cutoff p).map r))
  map_id s := by
    apply LinearMap.ext
    intro b
    obtain ⟨b, rfl⟩ := (ideal D Sc cutoff v (s.word ++ [i])).mkQ_surjective b
    change (ideal D Sc cutoff _ _).mkQ
      (b ≫ rightContext D Sc cutoff [i] _ _ (twist k p (𝟙 _))) = _
    rw [twist_id, rightContext_id, Category.comp_id]
    rfl
  map_comp {s t w} r r' := by
    apply LinearMap.ext
    intro b
    obtain ⟨b, rfl⟩ := (ideal D Sc cutoff v (s.word ++ [i])).mkQ_surjective b
    obtain ⟨r, rfl⟩ := (ideal D Sc cutoff s.word t.word).mkQ_surjective r
    obtain ⟨r', rfl⟩ := (ideal D Sc cutoff t.word w.word).mkQ_surjective r'
    change (ideal D Sc cutoff _ _).mkQ
      (b ≫ rightContext D Sc cutoff [i] _ _ (twist k p (r ≫ r'))) =
      (ideal D Sc cutoff _ _).mkQ
        ((b ≫ rightContext D Sc cutoff [i] _ _ (twist k p r)) ≫
          rightContext D Sc cutoff [i] _ _ (twist k p r'))
    rw [twist_comp, rightContext_comp, Category.assoc]

/-- Matrix-Hom component of `Be ⊗_D Πᵖ(eB)`, with its prescribed lower balance. -/
abbrev Source (i : I) (v t : List I) :=
  BalancedInduction.Obj (append D Sc cutoff i)
    (coefficient D Sc cutoff (D.parity i) i v) (⟨t⟩ : OldCategory D Sc cutoff)

/-- A tensor in the prescribed source; neither factor is an image coordinate. -/
def tensor (i : I) (v s t : List I)
    (c : Old D Sc cutoff (s ++ [i]) t) (b : Old D Sc cutoff v (s ++ [i])) :
    Source D Sc cutoff i v t :=
  BalancedInduction.tensor (append D Sc cutoff i)
    (coefficient D Sc cutoff (D.parity i) i v) ⟨s⟩ c b

/-- The literal crossing word on affine representatives, in diagram order. -/
def crossing (i : I) (v s t : List I) :
    hom D Sc cutoff (s ++ [i]) t →ₗ[k]
      hom D Sc cutoff v (s ++ [i]) →ₗ[k] Old D Sc cutoff (v ++ [i]) (t ++ [i]) where
  toFun c :=
    (ideal D Sc cutoff (v ++ [i]) (t ++ [i])).mkQ ∘ₗ
      (Linear.rightComp k _ (affineUnit D Sc cutoff _ _ (crossLast D Sc s i i) ≫
        rightContext D Sc cutoff [i] _ _ c)) ∘ₗ rightContext D Sc cutoff [i] _ _
  map_add' c c' := by
    apply LinearMap.ext
    intro b
    simp only [LinearMap.comp_apply, Linear.rightComp_apply,
      LinearMap.add_apply, map_add, Preadditive.comp_add]
  map_smul' a c := by
    apply LinearMap.ext
    intro b
    simp only [LinearMap.comp_apply, Linear.rightComp_apply,
      LinearMap.smul_apply, map_smul, Linear.comp_smul, RingHom.id_apply]

/-- Both cyclotomic ideals descend separately before imposing lower balance. -/
def pairing (i : I) (v s t : List I) :
    Old D Sc cutoff (s ++ [i]) t →ₗ[k]
      Old D Sc cutoff v (s ++ [i]) →ₗ[k] Old D Sc cutoff (v ++ [i]) (t ++ [i]) :=
  LinearMap.liftQ₂ _ _ (crossing D Sc cutoff i v s t)
    (by
      intro c hc
      apply LinearMap.ext
      intro b
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      exact comp_ideal D Sc cutoff _
        (comp_ideal D Sc cutoff _ (ideal_rightContext D Sc cutoff [i] hc)))
    (by
      intro b hb
      ext c
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      exact ideal_comp D Sc cutoff (ideal_rightContext D Sc cutoff [i] hb) _)

@[simp] theorem pairing_mk (i : I) (v s t : List I)
    (c : hom D Sc cutoff (s ++ [i]) t) (b : hom D Sc cutoff v (s ++ [i])) :
    pairing D Sc cutoff i v s t ((ideal D Sc cutoff _ _).mkQ c)
      ((ideal D Sc cutoff _ _).mkQ b) =
    (ideal D Sc cutoff (v ++ [i]) (t ++ [i])).mkQ
      (rightContext D Sc cutoff [i] _ _ b ≫
        affineUnit D Sc cutoff _ _ (crossLast D Sc s i i) ≫
        rightContext D Sc cutoff [i] _ _ c) := rfl

/-- Lower cyclotomic balance retains the total-parity twist on the coefficient. -/
theorem pairing_balance (i : I) (v : List I) (s s' t : OldCategory D Sc cutoff)
    (r : s ⟶ s') (c : (append D Sc cutoff i).obj s' ⟶ t)
    (b : (coefficient D Sc cutoff (D.parity i) i v).obj s) :
    pairing D Sc cutoff i v s.word t.word ((append D Sc cutoff i).map r ≫ c) b =
      pairing D Sc cutoff i v s'.word t.word c
        ((coefficient D Sc cutoff (D.parity i) i v).map r b) := by
  obtain ⟨r, rfl⟩ := (ideal D Sc cutoff s.word s'.word).mkQ_surjective r
  obtain ⟨c, rfl⟩ := (ideal D Sc cutoff (s'.word ++ [i]) t.word).mkQ_surjective c
  obtain ⟨b, rfl⟩ := (ideal D Sc cutoff v (s.word ++ [i])).mkQ_surjective b
  change (ideal D Sc cutoff _ _).mkQ
    (rightContext D Sc cutoff [i] _ _ b ≫
      affineUnit D Sc cutoff _ _ (crossLast D Sc s.word i i) ≫
      rightContext D Sc cutoff [i] _ _ (rightContext D Sc cutoff [i] _ _ r ≫ c)) =
    (ideal D Sc cutoff _ _).mkQ
      (rightContext D Sc cutoff [i] _ _ (b ≫ rightContext D Sc cutoff [i] _ _
        (twist k (D.parity i) r)) ≫
        affineUnit D Sc cutoff _ _ (crossLast D Sc s'.word i i) ≫
        rightContext D Sc cutoff [i] _ _ c)
  have hp : D.parity i * D.parity i = D.parity i := by
    rcases parity_eq_zero_or_one (D.parity i) with h | h <;> simp [h]
  have h := crossLast_comp_rightContext D Sc cutoff i i r
  rw [hp] at h
  simp only [rightContext_comp, Category.assoc]
  rw [← Category.assoc (affineUnit D Sc cutoff _ _ (crossLast D Sc s.word i i)), h]
  simp only [Category.assoc]

/-- The prescribed crossing column after both cyclotomic descent and lower balance. -/
def toCyclotomic (i : I) (v t : List I) : Source D Sc cutoff i v t →ₗ[k]
    Old D Sc cutoff (v ++ [i]) (t ++ [i]) :=
  BalancedInduction.lift (append D Sc cutoff i)
    (coefficient D Sc cutoff (D.parity i) i v) ⟨t⟩
    (fun s => TensorProduct.lift (pairing D Sc cutoff i v s.word t))
    (fun s s' r c b => pairing_balance D Sc cutoff i v s s' ⟨t⟩ r c b)

@[simp] theorem toCyclotomic_tensor (i : I) (v s t : List I)
    (c : Old D Sc cutoff (s ++ [i]) t) (b : Old D Sc cutoff v (s ++ [i])) :
    toCyclotomic D Sc cutoff i v t (tensor D Sc cutoff i v s t c b) =
      pairing D Sc cutoff i v s t c b := by
  exact BalancedInduction.lift_tensor (append D Sc cutoff i)
    (coefficient D Sc cutoff (D.parity i) i v) ⟨t⟩ _ _ ⟨s⟩ c b

/-- In algebra order this is exactly `c τₙ b`, without a coefficient permutation. -/
theorem toCyclotomic_tensor_mk (i : I) (v s t : List I)
    (c : hom D Sc cutoff (s ++ [i]) t) (b : hom D Sc cutoff v (s ++ [i])) :
    toCyclotomic D Sc cutoff i v t (tensor D Sc cutoff i v s t
      ((ideal D Sc cutoff _ _).mkQ c) ((ideal D Sc cutoff _ _).mkQ b)) =
    (ideal D Sc cutoff (v ++ [i]) (t ++ [i])).mkQ
      (rightContext D Sc cutoff [i] _ _ b ≫
        affineUnit D Sc cutoff _ _ (crossLast D Sc s i i) ≫
        rightContext D Sc cutoff [i] _ _ c) := by
  rw [toCyclotomic_tensor, pairing_mk]

end CyclotomicCrossingTensor
end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # Actual supermodules on the full old ELV quotient category

The already proved old parity decomposition defines the supercategory
structure on the existing quotient category, with the established quotient
projections. Its source representables are actual superfunctors. These are
the untruncated coefficient modules needed to identify the prescribed
crossing source with induction of a parity-shifted restriction.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

instance oldSupercategory : Supercategory k (OldCategory D Sc cutoff) where
  parity v w := oldParity D Sc cutoff v.word w.word
  isInternal v w := oldParity_internal D Sc cutoff v.word w.word
  id_mem v := Submodule.mem_map_of_mem (Supercategory.id_mem (obj D Sc cutoff v.word))
  comp_mem := by
    rintro v t w p q f g ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact Submodule.mem_map_of_mem (Supercategory.comp_mem ha hb)

theorem oldCategory_proj (v w : OldCategory D Sc cutoff)
    (p : ZMod 2) (f : v ⟶ w) :
    Supercategory.proj k p f = oldProj D Sc cutoff v.word w.word p f := by
  refine Supercategory.induction_on (R := k) f (by simp) (fun q f hf => ?_)
    (fun f g hf hg => by simp only [map_add, hf, hg])
  rw [oldProj_of_mem D Sc cutoff hf p]
  by_cases h : q = p
  · subst q
    rw [ite_eq_left rfl, Supercategory.proj_of_mem hf]
  · rw [ite_eq_right h, Supercategory.proj_of_mem_ne hf h]

def oldRepresentableFunctor (v : OldCategory D Sc cutoff) :
    OldCategory D Sc cutoff ⥤ SVec k where
  obj := Supercategory.homSVec k (OldCategory D Sc cutoff) v
  map f :=
    { toFun := fun h => h ≫ f
      map_add' := fun h h' => Preadditive.add_comp _ _ _ _ _ _
      map_smul' := fun r h => Linear.smul_comp _ _ _ _ _ _ }
  map_id w := by ext h; exact Category.comp_id h
  map_comp f g := by ext h; exact (Category.assoc h f g).symm

instance oldRepresentableFunctor_additive (v : OldCategory D Sc cutoff) :
    (oldRepresentableFunctor D Sc cutoff v).Additive where
  map_add {w z} f g := by
    apply LinearMap.ext
    intro h
    exact Preadditive.comp_add v w z h f g

instance oldRepresentableFunctor_linear (v : OldCategory D Sc cutoff) :
    (oldRepresentableFunctor D Sc cutoff v).Linear k where
  map_smul {w z} f r := by
    apply LinearMap.ext
    intro h
    exact Linear.comp_smul v w z h r f

instance oldRepresentableFunctor_super (v : OldCategory D Sc cutoff) :
    IsSuperfunctor k (oldRepresentableFunctor D Sc cutoff v) where
  map_mem := by
    intro w z p f hf
    apply SVec.mem_parityHom_of_apply_mem
    intro q h hh
    change h ∈ (Supercategory.homSVec k (OldCategory D Sc cutoff) v w).part q at hh
    change h ≫ f ∈ (Supercategory.homSVec k (OldCategory D Sc cutoff) v z).part (q + p)
    exact (Supercategory.mem_homSVec_part_iff k).2
      (comp_mem ((Supercategory.mem_homSVec_part_iff k).1 hh) hf)

def oldRepresentable (v : OldCategory D Sc cutoff) :
    Superfunctor k (OldCategory D Sc cutoff) (SVec k) :=
  ⟨oldRepresentableFunctor D Sc cutoff v⟩

@[simp] theorem oldRepresentable_map (v w z : OldCategory D Sc cutoff)
    (f : w ⟶ z) (h : v ⟶ w) :
    (oldRepresentable D Sc cutoff v).map f h = h ≫ f := rfl

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # The existing old append functor preserves the full super grading

Right extension is the tensor of the identity on full ELV coefficients with
even affine right-whiskering. Its parity preservation passes to the actual
old cyclotomic quotient, including exterior coefficients. This equips the
independently defined append functor for actual supermodule induction.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

namespace CyclotomicCrossingTensor

instance append_additive (i : I) : (append D Sc cutoff i).Additive where
  map_add {v w} f g :=
    ((ideal D Sc cutoff v.word w.word).mapQ
      (ideal D Sc cutoff (v.word ++ [i]) (w.word ++ [i]))
      (rightContext D Sc cutoff [i] v.word w.word)
      (fun _ hr => ideal_rightContext D Sc cutoff [i] hr)).map_add f g

instance append_linear (i : I) : (append D Sc cutoff i).Linear k where
  map_smul {v w} f r :=
    ((ideal D Sc cutoff v.word w.word).mapQ
      (ideal D Sc cutoff (v.word ++ [i]) (w.word ++ [i]))
      (rightContext D Sc cutoff [i] v.word w.word)
      (fun _ hr => ideal_rightContext D Sc cutoff [i] hr)).map_smul r f

instance append_super (i : I) : IsSuperfunctor k (append D Sc cutoff i) where
  map_mem := by
    rintro v w p f ⟨a, ha, rfl⟩
    exact Submodule.mem_map_of_mem (rightContext_mem_parity D Sc cutoff [i] ha)

end CyclotomicCrossingTensor
end OddMath.QuiverHecke.ELVOld
end

end

section

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

@[simp] theorem oldModuleRawMap_apply
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (v w : List I) (f : hom D Sc cutoff v w) :
    oldModuleRawMap D Sc cutoff M v w f =
      M.map (X := ⟨v⟩) (Y := ⟨w⟩) ((ideal D Sc cutoff v w).mkQ f) := rfl

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

@[simp] theorem weightedModuleMap_mk (N : ℕ)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (hM : KillsWeightedCoefficients D Sc cutoff N M)
    (v w : List I) (f : hom D Sc cutoff v w) :
    weightedModuleMap D Sc cutoff N M hM v w
      ((truncatedIdeal D Sc cutoff N v w).mkQ f) =
      oldModuleRawMap D Sc cutoff M v w f := rfl

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
end

end

section

/-! # Append induction preserves weighted coefficient annihilation
The reservoir quotient transport in SwappedVacuumCoordinates §6 uses the
actual old append functor and balanced induction. Full coefficient parity
is retained in the scalar slide before applying coend balance.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

theorem oldQuotient_twist (v w : List I) (p : ZMod 2) (f : hom D Sc cutoff v w) :
    twist k p (X := (⟨v⟩ : OldCategory D Sc cutoff)) (Y := ⟨w⟩)
      ((ideal D Sc cutoff v w).mkQ f) =
      (ideal D Sc cutoff v w).mkQ
        (twist k p (X := obj D Sc cutoff v) (Y := obj D Sc cutoff w) f) := by
  simp only [twist_apply, oldCategory_proj, oldProj_mk, map_add, map_smul]

/-- The prescribed full coefficient monomial at an old word. -/
def oldCoefficientBasis (v : List I) (a : SKM.SYM.CoefficientIndex D) :
    (⟨v⟩ : OldCategory D Sc cutoff) ⟶ ⟨v⟩ :=
  (ideal D Sc cutoff v v).mkQ
    (coefficientIdentity D Sc cutoff v (SKM.SYM.coefficientBasis D k a))

/-- The complete output parity twist appears in the coefficient slide. -/
theorem oldCoefficientBasis_slide (v w : List I) (a : SKM.SYM.CoefficientIndex D)
    (f : (⟨v⟩ : OldCategory D Sc cutoff) ⟶ ⟨w⟩) :
    f ≫ oldCoefficientBasis D Sc cutoff w a =
      oldCoefficientBasis D Sc cutoff v a ≫
        twist k (a.2.card : ZMod 2) (X := (⟨v⟩ : OldCategory D Sc cutoff)) (Y := ⟨w⟩) f := by
  obtain ⟨f, rfl⟩ := (ideal D Sc cutoff v w).mkQ_surjective f
  have ha := SKM.SYM.elvModelQuotient_mem D (cutoff := cutoff)
    (SKM.SYM.coefficientBasis_mem_parity D k a)
  simp only [SKM.SYM.elvModelQuotient, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    AlgEquiv.symm_apply_apply] at ha
  have he := congrArg ((ideal D Sc cutoff v w).mkQ)
    (ELVPScalar.scalar_slide_homogeneous D Sc cutoff ha f)
  rw [oldQuotient_twist]
  exact he

@[simp] theorem append_oldCoefficientBasis (i : I) (v : List I)
    (a : SKM.SYM.CoefficientIndex D) :
    (CyclotomicCrossingTensor.append D Sc cutoff i).map
      (oldCoefficientBasis D Sc cutoff v a) =
      oldCoefficientBasis D Sc cutoff (v ++ [i]) a := by
  change (ideal D Sc cutoff (v ++ [i]) (v ++ [i])).mkQ
    (rightContext D Sc cutoff [i] v v
      (coefficientIdentity D Sc cutoff v (SKM.SYM.coefficientBasis D k a))) = _
  rw [rightContext_coefficientIdentity]
  rfl

/-- Actual old append induction preserves the annihilator class of the
weighted coefficient ideal, including its odd monomials. -/
theorem induced_killsWeightedCoefficients (N : ℕ) (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (hM : KillsWeightedCoefficients D Sc cutoff N M) :
    KillsWeightedCoefficients D Sc cutoff N
      (BalancedInduction.induced (CyclotomicCrossingTensor.append D Sc cutoff i) M) := by
  intro w a ha
  let J := CyclotomicCrossingTensor.append D Sc cutoff i
  change BalancedInduction.postcompose J M.toFunctor
    (oldCoefficientBasis D Sc cutoff w a) = 0
  apply BalancedInduction.hom_ext
  rintro ⟨v⟩ h m
  rw [BalancedInduction.postcompose_tensor, oldCoefficientBasis_slide]
  have hc : oldCoefficientBasis D Sc cutoff (v ++ [i]) a =
      J.map (oldCoefficientBasis D Sc cutoff v a) :=
    (append_oldCoefficientBasis D Sc cutoff i v a).symm
  rw [hc, BalancedInduction.balance]
  have hz : M.toFunctor.map (oldCoefficientBasis D Sc cutoff v a) = 0 := hM v a ha
  rw [hz, LinearMap.zero_apply]
  simp only [BalancedInduction.tensor, TensorProduct.tmul_zero, map_zero,
    LinearMap.zero_apply]

/-- The reservoir-side induced module consequently exists on the literal
weighted quotient, on the same balanced tensor vector spaces. -/
def weightedInducedModule (N : ℕ) (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (hM : KillsWeightedCoefficients D Sc cutoff N M) :
    Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k) :=
  weightedModule D Sc cutoff N
    (BalancedInduction.induced (CyclotomicCrossingTensor.append D Sc cutoff i) M)
    (induced_killsWeightedCoefficients D Sc cutoff N i M hM)

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # Induction along the weighted quotient
The actual quotient functor has a full-image restriction on modules. Its
balanced induction counit is an equivalence, proved by lifting quotient
arrows and balancing, without flatness (SwappedVacuumCoordinates §6).
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
variable {k : Type u} [CommRing k]
  {C D : Type u} [Category.{u} C] [Category.{u} D]
  [Preadditive D] [Linear k D]
  (J : C ⥤ D) [J.Full] (M : D ⥤ SVec k) [M.Additive] [M.Linear k]

/-- Fullness supplies the balancing arrow needed for the second counit
inverse product at an object in the literal image. -/
theorem unit_counit_of_full (v₀ : C) :
    (unit J (J ⋙ M) v₀).comp (counit J M (J.obj v₀)) = LinearMap.id := by
  apply hom_ext
  intro v h m
  calc
    (unit J (J ⋙ M) v₀ ∘ₗ counit J M (J.obj v₀)) (tensor J (J ⋙ M) v h m) =
        unit J (J ⋙ M) v₀ (M.map h m) :=
      congrArg (unit J (J ⋙ M) v₀) (counit_tensor J M (J.obj v₀) v h m)
    _ = tensor J (J ⋙ M) v₀ (𝟙 _) (M.map h m) := unit_apply J (J ⋙ M) v₀ _
    _ = tensor J (J ⋙ M) v h m := by
      have hb := balance J (J ⋙ M) (J.preimage h) (𝟙 (J.obj v₀)) m
      change tensor J (J ⋙ M) v ((J.map (J.preimage h)) ≫ 𝟙 (J.obj v₀)) m =
        tensor J (J ⋙ M) v₀ (𝟙 (J.obj v₀)) (M.map (J.map (J.preimage h)) m) at hb
      rw [Category.comp_id, Functor.map_preimage] at hb
      exact hb.symm

end OddMath.QuiverHecke.ELVOld.BalancedInduction

namespace OddMath.QuiverHecke.ELVOld
universe u
variable {k : Type u} [CommRing k]
  {C : Type u} [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]

/-- Lift an ordinary module isomorphism with even components. -/
def moduleIsoOfEvenNatIso (F G : Superfunctor k C (SVec k))
    (e : F.toFunctor ≅ G.toFunctor)
    (hh : ∀ w, e.hom.app w ∈ parity (R := k) _ _ 0)
    (hi : ∀ w, e.inv.app w ∈ parity (R := k) _ _ 0) : F ≅ G where
  hom := SuperNatTrans.ofNatTrans e.hom hh
  inv := SuperNatTrans.ofNatTrans e.inv hi
  hom_inv_id := by
    apply Superfunctor.hom_ext_parity
    · intro w
      simp [SuperNatTrans.ofNatTrans, Superfunctor.comp_app]
    · intro w
      simp [SuperNatTrans.ofNatTrans, Superfunctor.comp_app]
  inv_hom_id := by
    apply Superfunctor.hom_ext_parity
    · intro w
      simp [SuperNatTrans.ofNatTrans, Superfunctor.comp_app]
    · intro w
      simp [SuperNatTrans.ofNatTrans, Superfunctor.comp_app]

end OddMath.QuiverHecke.ELVOld

namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))
local notation "Q" => oldTruncateFunctor D Sc cutoff N

instance oldTruncateFunctor_full : (Q).Full where
  map_surjective {v w} f := truncateOld_surjective D Sc cutoff N v.word w.word f

/-- The inverse uses the old word with the same literal boundary. -/
def quotientInductionCounitInverse (w : TruncatedCategory D Sc cutoff N) :
    M.obj w →ₗ[k] BalancedInduction.Obj Q (Q ⋙ M.toFunctor) w :=
  BalancedInduction.unit Q (Q ⋙ M.toFunctor) ⟨w.word⟩

theorem quotientInductionCounit_right_inv (w : TruncatedCategory D Sc cutoff N) :
    (BalancedInduction.counit Q M.toFunctor w).comp
      (quotientInductionCounitInverse D Sc cutoff N M w) = LinearMap.id :=
  BalancedInduction.counit_unit Q M.toFunctor ⟨w.word⟩

theorem quotientInductionCounit_left_inv (w : TruncatedCategory D Sc cutoff N) :
    (quotientInductionCounitInverse D Sc cutoff N M w).comp
      (BalancedInduction.counit Q M.toFunctor w) = LinearMap.id :=
  BalancedInduction.unit_counit_of_full Q M.toFunctor ⟨w.word⟩

/-- The forward map is exactly the existing balanced adjunction counit. -/
def quotientInductionCounitEquiv (w : TruncatedCategory D Sc cutoff N) :
    BalancedInduction.Obj Q (Q ⋙ M.toFunctor) w ≃ₗ[k] M.obj w :=
  LinearEquiv.ofLinearMap (BalancedInduction.counit Q M.toFunctor w)
    (quotientInductionCounitInverse D Sc cutoff N M w)
    (quotientInductionCounit_right_inv D Sc cutoff N M w)
    (quotientInductionCounit_left_inv D Sc cutoff N M w)

@[simp] theorem quotientInductionCounitEquiv_tensor (w : TruncatedCategory D Sc cutoff N)
    (v : OldCategory D Sc cutoff) (h : (Q).obj v ⟶ w) (m : M.obj ((Q).obj v)) :
    quotientInductionCounitEquiv D Sc cutoff N M w
      (BalancedInduction.tensor Q (Q ⋙ M.toFunctor) v h m) = M.map h m :=
  BalancedInduction.counit_tensor Q M.toFunctor w v h m

/-- The pointwise equivalence is natural for the actual module action. -/
def quotientInductionCounitNatIso :
    (BalancedInduction.induced Q (weightedRestriction D Sc cutoff N M)).toFunctor ≅
      M.toFunctor :=
  NatIso.ofComponents (fun w =>
    { hom := BalancedInduction.counit Q M.toFunctor w
      inv := quotientInductionCounitInverse D Sc cutoff N M w
      hom_inv_id := quotientInductionCounit_left_inv D Sc cutoff N M w
      inv_hom_id := quotientInductionCounit_right_inv D Sc cutoff N M w })
    (fun a => BalancedInduction.counit_naturality Q M.toFunctor a)

/-- The actual quotient-induction counit is an even module isomorphism,
with the existing counit as its forward parity-zero component. -/
def quotientInductionCounitIso :
    BalancedInduction.induced Q (weightedRestriction D Sc cutoff N M) ≅ M :=
  moduleIsoOfEvenNatIso _ _ (quotientInductionCounitNatIso D Sc cutoff N M)
    (fun w => BalancedInduction.counit_mem Q M w)
    (fun w => BalancedInduction.unit_mem Q (weightedRestriction D Sc cutoff N M) ⟨w.word⟩)

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # Comparison of old and weighted-truncated append induction
The quotient-induction counit, ordinary composition of balanced induction
and the literal append/quotient square give the reservoir-side comparison
needed by SwappedVacuumCoordinates §6.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
variable {k : Type u} [CommRing k]
  {C D : Type u} [Category.{u} C] [Category.{u} D]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive D] [Linear k D] [Supercategory k D]

def inducedIsoOfFunctorEq (J K : C ⥤ D)
    [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    [K.Additive] [K.Linear k] [IsSuperfunctor k K]
    (h : J = K) (M : Superfunctor k C (SVec k)) :
    induced J M ≅ induced K M := by
  subst K
  exact Iso.refl _

end OddMath.QuiverHecke.ELVOld.BalancedInduction

namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
local notation "Q" => oldTruncateFunctor D Sc cutoff N

theorem weightedRestrictionModule_map
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (hM : KillsWeightedCoefficients D Sc cutoff N M)
    (v w : OldCategory D Sc cutoff) (f : v ⟶ w) :
    (weightedRestriction D Sc cutoff N (weightedModule D Sc cutoff N M hM)).map f =
      M.map f := by
  obtain ⟨a, rfl⟩ := (ideal D Sc cutoff v.word w.word).mkQ_surjective f
  rfl

/-- Restricting the descended module retains its old action. -/
def weightedRestrictionModuleIso
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (hM : KillsWeightedCoefficients D Sc cutoff N M) :
    weightedRestriction D Sc cutoff N (weightedModule D Sc cutoff N M hM) ≅ M :=
  moduleIsoOfEvenNatIso _ _
    (NatIso.ofComponents (fun v => Iso.refl (M.obj v)) (fun f => by
      change _ ≫ 𝟙 _ = 𝟙 _ ≫ _
      rw [Category.comp_id, Category.id_comp]
      exact weightedRestrictionModule_map D Sc cutoff N M hM _ _ f))
    (fun v => id_mem (M.obj v)) (fun v => id_mem (M.obj v))

/-- Induction along the quotient identifies an annihilated old module
with its literal descended module. -/
def quotientInducedWeightedModuleIso
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (hM : KillsWeightedCoefficients D Sc cutoff N M) :
    BalancedInduction.induced Q M ≅ weightedModule D Sc cutoff N M hM :=
  ((BalancedInduction.induction Q).mapIso
    (weightedRestrictionModuleIso D Sc cutoff N M hM)).symm ≪≫
      quotientInductionCounitIso D Sc cutoff N (weightedModule D Sc cutoff N M hM)

/-- Append commutes with the actual further quotient, on all old arrows. -/
theorem oldAppend_truncate (i : I) :
    CyclotomicCrossingTensor.append D Sc cutoff i ⋙ Q =
      Q ⋙ truncatedAppend D Sc cutoff N [i] := by
  refine Functor.hext (F := CyclotomicCrossingTensor.append D Sc cutoff i ⋙ Q)
    (G := Q ⋙ truncatedAppend D Sc cutoff N [i]) (fun _ => rfl) ?_
  intro v w f
  obtain ⟨a, rfl⟩ := (ideal D Sc cutoff v.word w.word).mkQ_surjective f
  rfl

/-- Old append induction of a restricted truncated module, descended by
the weighted annihilator theorem, is isomorphic to the existing truncated
append induction. Every comparison is an actual adjunction/composition map. -/
def appendWeightedModuleIso (i : I)
    (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k)) :
    weightedInducedModule D Sc cutoff N i
      (weightedRestriction D Sc cutoff N M)
      (weightedRestriction_kills D Sc cutoff N M) ≅
    BalancedInduction.induced (truncatedAppend D Sc cutoff N [i]) M :=
  let J := CyclotomicCrossingTensor.append D Sc cutoff i
  let T := truncatedAppend D Sc cutoff N [i]
  let R := weightedRestriction D Sc cutoff N M
  let F := BalancedInduction.induced J R
  let hF := induced_killsWeightedCoefficients D Sc cutoff N i R
    (weightedRestriction_kills D Sc cutoff N M)
  (quotientInducedWeightedModuleIso D Sc cutoff N F hF).symm ≪≫
    (BalancedInduction.inductionComp J Q).app R ≪≫
      BalancedInduction.inducedIsoOfFunctorEq (J ⋙ Q) (Q ⋙ T)
        (oldAppend_truncate D Sc cutoff N i) R ≪≫
      ((BalancedInduction.inductionComp Q T).app R).symm ≪≫
      (BalancedInduction.induction T).mapIso (quotientInductionCounitIso D Sc cutoff N M)

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # Naturality of weighted quotient induction
The old/truncated action comparison in SwappedVacuumCoordinates §6 must
intertwine all module maps, including both homogeneous parities.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
variable {k : Type u} [CommRing k]
  {C D : Type u} [Category.{u} C] [Category.{u} D]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive D] [Linear k D] [Supercategory k D]

def inductionFunctorIsoOfEq (J K : C ⥤ D)
    [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    [K.Additive] [K.Linear k] [IsSuperfunctor k K] (h : J = K) :
    induction (k := k) J ≅ induction (k := k) K := by
  subst K
  exact Iso.refl _

end OddMath.QuiverHecke.ELVOld.BalancedInduction

namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
local notation "Q" => oldTruncateFunctor D Sc cutoff N

@[simp] theorem weightedRestrictionModuleIso_inv_app
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (hM : KillsWeightedCoefficients D Sc cutoff N M) (p : ZMod 2)
    (v : OldCategory D Sc cutoff) :
    (weightedRestrictionModuleIso D Sc cutoff N M hM).inv.app p v =
      if p = 0 then LinearMap.id else 0 := rfl

@[simp] theorem quotientInductionCounitIso_hom
    (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k)) :
    (quotientInductionCounitIso D Sc cutoff N M).hom =
      (BalancedInduction.adjunctionCounit Q).app M := by
  apply Superfunctor.hom_ext
  intro p v
  rfl

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # Entries of the actual cyclotomic matrix ideal

The reverse matrix-ideal comparison needed by AppendMackeySource, section 4.
Every entry of an element of the actual Hn cyclotomic ideal belongs to the
ordinary cyclotomic morphism ideal. The proof uses actual finite-support
single matrices and composition closure; no tensor flatness or quotient
presentation is introduced.
-/
noncomputable section
open CategoryTheory StringDiagrams
open scoped Classical
namespace OddMath.QuiverHecke
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
  (a : I → _root_.Polynomial k) (n : ℕ)

private def cyclotomicEntrySpan : Submodule k (Hn D Sc (n + 1)) :=
  Submodule.span k {x | ∃ (t s : Word I (n + 1))
    (f : wordObj D Sc s ⟶ wordObj D Sc t),
    f ∈ cycHom D Sc a s.val t.val ∧ x = FiniteHomMatrix.single t s f}

private theorem entrySpan_mul_left (b : Hn D Sc (n + 1))
    {x : Hn D Sc (n + 1)} (hx : x ∈ cyclotomicEntrySpan D Sc a n) :
    b * x ∈ cyclotomicEntrySpan D Sc a n := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨t, s, f, hf, rfl⟩ := hx
    induction b using FiniteHomMatrix.induction with
    | hz =>
      rw [zero_mul]
      exact Submodule.zero_mem _
    | ha b c hb hc =>
      rw [add_mul]
      exact Submodule.add_mem _ hb hc
    | hs r q g =>
      by_cases h : q = t
      · subst t
        rw [FiniteHomMatrix.single_mul_single]
        exact Submodule.subset_span ⟨r, s, f ≫ g, cycHom_comp_right D Sc hf g, rfl⟩
      · rw [FiniteHomMatrix.single_mul_single_of_ne _ _ _ _ h]
        exact Submodule.zero_mem _
  | zero =>
    rw [mul_zero]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    rw [mul_add]
    exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [mul_smul_comm]
    exact Submodule.smul_mem _ c hx

private theorem entrySpan_mul_right {x : Hn D Sc (n + 1)}
    (hx : x ∈ cyclotomicEntrySpan D Sc a n) (b : Hn D Sc (n + 1)) :
    x * b ∈ cyclotomicEntrySpan D Sc a n := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨t, s, f, hf, rfl⟩ := hx
    induction b using FiniteHomMatrix.induction with
    | hz =>
      rw [mul_zero]
      exact Submodule.zero_mem _
    | ha b c hb hc =>
      rw [mul_add]
      exact Submodule.add_mem _ hb hc
    | hs r q g =>
      by_cases h : s = r
      · subst r
        rw [FiniteHomMatrix.single_mul_single]
        exact Submodule.subset_span ⟨t, q, g ≫ f, cycHom_comp_left D Sc g hf, rfl⟩
      · rw [FiniteHomMatrix.single_mul_single_of_ne _ _ _ _ h]
        exact Submodule.zero_mem _
  | zero =>
    rw [zero_mul]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    rw [add_mul]
    exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [smul_mul_assoc]
    exact Submodule.smul_mem _ c hx

omit [Fintype I] in
private theorem cyclotomicGenerator_mem_entrySpan (w : Word I (n + 1)) :
    cyclotomicGenerator D Sc a w ∈ cyclotomicEntrySpan D Sc a n := by
  rcases w with ⟨l, hl⟩
  cases l with
  | nil => simp at hl
  | cons j l =>
    change FiniteHomMatrix.single (obj := wordObj D Sc (n := n + 1))
      (⟨j :: l, hl⟩ : Word I (n + 1))
      (⟨j :: l, hl⟩ : Word I (n + 1)) (firstDotPoly D Sc a j l) ∈ _
    apply Submodule.subset_span
    refine ⟨⟨j :: l, hl⟩, ⟨j :: l, hl⟩, firstDotPoly D Sc a j l, ?_, rfl⟩
    apply Submodule.subset_span
    exact ⟨j, l, 𝟙 _, 𝟙 _, by simp⟩

omit [Fintype I] in
private theorem entrySpan_entry {x : Hn D Sc (n + 1)}
    (hx : x ∈ cyclotomicEntrySpan D Sc a n) (t s : Word I (n + 1)) :
    x (t, s) ∈ cycHom D Sc a s.val t.val := by
  let : DecidableEq (Word I (n + 1)) := Classical.decEq _
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, w, f, hf, rfl⟩ := hx
    by_cases ht : t = u
    · subst t
      by_cases hs : s = w
      · subst s
        simpa only [FiniteHomMatrix.single, DFinsupp.single_eq_same] using hf
      · have h : (u, s) ≠ (u, w) := fun h => hs (congrArg Prod.snd h)
        have hz : (FiniteHomMatrix.single (obj := wordObj D Sc (n := n + 1))
            u w f) (u, s) = 0 := DFinsupp.single_eq_of_ne h
        rw [hz]
        exact Submodule.zero_mem _
    · have h : (t, s) ≠ (u, w) := fun h => ht (congrArg Prod.fst h)
      have hz : (FiniteHomMatrix.single (obj := wordObj D Sc (n := n + 1))
          u w f) (t, s) = 0 := DFinsupp.single_eq_of_ne h
      rw [hz]
      exact Submodule.zero_mem _
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    change x (t, s) + y (t, s) ∈ _
    exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    change c • x (t, s) ∈ _
    exact Submodule.smul_mem _ c hx

/-- Each actual Hn ideal entry lies in the corresponding ordinary morphism ideal. -/
theorem cyclotomicIdeal_entry_mem_cycHom {x : Hn D Sc (n + 1)}
    (hx : x ∈ cyclotomicIdeal D Sc a n) (t s : Word I (n + 1)) :
    x (t, s) ∈ cycHom D Sc a s.val t.val := by
  have hs : x ∈ cyclotomicEntrySpan D Sc a n := by
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨w, b, rfl⟩ := hy
      exact entrySpan_mul_right D Sc a n (cyclotomicGenerator_mem_entrySpan D Sc a n w) b
    | zero => exact Submodule.zero_mem _
    | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
    | smul b x _ hx =>
      change b * x ∈ _
      exact entrySpan_mul_left D Sc a n b hx
  exact entrySpan_entry D Sc a n hs t s

/-- A single matrix belongs to the actual ideal exactly when its morphism does. -/
theorem single_mem_cyclotomicIdeal_iff (t s : Word I (n + 1))
    (f : wordObj D Sc s ⟶ wordObj D Sc t) :
    FiniteHomMatrix.single t s f ∈ cyclotomicIdeal D Sc a n ↔
      f ∈ cycHom D Sc a s.val t.val := by
  constructor
  · intro hf
    simpa only [FiniteHomMatrix.single, DFinsupp.single_eq_same] using
      cyclotomicIdeal_entry_mem_cycHom D Sc a n hf t s
  · exact single_mem_cyclotomicIdeal D Sc a n t s

end OddMath.QuiverHecke
end

end

section

/-!
# The ELV ideal-sum decomposition

The output-parabolic transport and the short/long shuffle endpoints give (IS2)
of `DeformedIdealSum.md`. All coefficients and cutoffs are retained over an
arbitrary commutative ground ring. The empty old word falls in the long case.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
open scoped TensorProduct
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

private theorem short_relation_mem (i j : I) (v l t s w : List I)
    (hl : l ≠ []) (es : s = j :: t) (el : s = l ++ [i])
    (F : (pres D Sc).obj (ob D (v ++ [i])) ⟶ (pres D Sc).obj (ob D s))
    (f : (pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D l))
    (hF : F ≫ eqToHom (congrArg (fun z => (pres D Sc).obj (ob D z)) el) =
      f ▷ (pres D Sc).obj (ob D [i]))
    (c : hom D Sc cutoff s w) :
    affineUnit D Sc cutoff _ _ F ≫
      (eqToHom (congrArg (obj D Sc cutoff) es) ≫ relation D Sc cutoff j t ≫
        eqToHom (congrArg (obj D Sc cutoff) es.symm)) ≫ c ∈
      appendRelations D Sc cutoff i v w := by
  subst s
  cases l with
  | nil => exact (hl rfl).elim
  | cons j' l =>
    have hh := List.cons.inj el
    obtain ⟨rfl, rfl⟩ := hh
    simp only [eqToHom_refl, Category.comp_id] at hF
    change F = affineRightContext D Sc [i] v (j :: l) f at hF
    rw [hF]
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    have H := appendRelations_mem D Sc cutoff i
      (comp_ideal D Sc cutoff (affineUnit D Sc cutoff v (j :: l) f)
        (relation_mem D Sc cutoff j l)) c
    rw [rightContext_comp, rightContext_affineUnit, rightContext_relation] at H
    simp only [Category.assoc] at H
    convert H using 1
    rfl

private theorem long_relation_mem (i j : I) (v t s w : List I)
    (es : s = j :: t) (el : s = i :: v)
    (F : (pres D Sc).obj (ob D (v ++ [i])) ⟶ (pres D Sc).obj (ob D s))
    (hF : F ≫ eqToHom (congrArg (fun z => (pres D Sc).obj (ob D z)) el) =
      lastToFirstHom D Sc i v)
    (c : hom D Sc cutoff s w) :
    affineUnit D Sc cutoff _ _ F ≫
      (eqToHom (congrArg (obj D Sc cutoff) es) ≫ relation D Sc cutoff j t ≫
        eqToHom (congrArg (obj D Sc cutoff) es.symm)) ≫ c ∈
      LinearMap.range (Linear.leftComp k (obj D Sc cutoff w) (appendW D Sc cutoff i v)) := by
  subst s
  obtain ⟨rfl, rfl⟩ := List.cons.inj el
  simp only [eqToHom_refl, Category.comp_id] at hF
  subst F
  refine ⟨c, ?_⟩
  simp only [Linear.leftComp_apply, appendW, eqToHom_refl, Category.id_comp, Category.assoc]

/-- Each output-parabolic ideal term lies in the append-old span plus the moving-strand image.
The short shuffle extends an old relation; the long shuffle factors through `appendW`. -/
theorem parabolic_term_mem_appendRelations_sup_range (i : I) (v w : List I)
    (j : I) (t : List I) (hN : [j].length + t.length = (v ++ [i]).length)
    (x : ShIdx hN) (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff)
    (b : hom D Sc cutoff (j :: t) w) :
    (affineUnit D Sc cutoff _ _ (shPsi D Sc [j].length x.1.1) ≫
      shuffleParabolic D Sc cutoff x a) ≫ relation D Sc cutoff j t ≫ b ∈
        appendRelations D Sc cutoff i v w ⊔
          LinearMap.range (Linear.leftComp k (obj D Sc cutoff w) (appendW D Sc cutoff i v)) := by
  obtain ⟨c, hc⟩ := outputParabolic_relation_transport D Sc cutoff x a
  rw [Category.assoc, ← Category.assoc (shuffleParabolic D Sc cutoff x a), hc]
  simp only [Category.assoc]
  have ht : t.length = v.length := by
    simp only [List.length_singleton, List.length_append] at hN
    omega
  obtain ⟨r, hr, he⟩ := OutputShuffle.shuffle_word_cases hN x.1
  rw [ht] at hr
  by_cases hs : r < v.length
  · let e := Categorification.TypeA.wordProd v.length (List.range r)
    have he' : cw (Categorification.TypeA.canWord (v ++ [i]).length x.1.1) =
        cw (Categorification.TypeA.canWord v.length e) := by
      rw [he, OutputShuffle.canWord_wordProd_range hs, OutputShuffle.cw_range]
    apply Submodule.mem_sup_left
    apply short_relation_mem D Sc cutoff i j v
      (shL v 1 e ++ shR v 1 e) (shR (v ++ [i]) 1 x.1.1) _ w
      _ (congrArg (fun l => l ++ shR (v ++ [i]) 1 x.1.1)
        (outputParabolic_first_block x))
      (OutputShuffle.short_target_of_word i v x.1.1 e he')
      (shPsi D Sc 1 x.1.1) (shPsi D Sc 1 e)
      (OutputShuffle.short_eq_of_word D Sc i v x.1.1 e he') (c ≫ b)
    intro hz
    have hh := congrArg List.length hz
    rw [List.length_append, length_shL (by omega : 1 ≤ v.length)] at hh
    simp only [List.length_nil] at hh
    omega
  · have he' : cw (Categorification.TypeA.canWord (v ++ [i]).length x.1.1) =
        crossingDescent v.length := by
      have : r = v.length := by omega
      simpa only [this] using he
    apply Submodule.mem_sup_right
    exact long_relation_mem D Sc cutoff i j v (shR (v ++ [i]) 1 x.1.1) _ w
      (congrArg (fun l => l ++ shR (v ++ [i]) 1 x.1.1) (outputParabolic_first_block x))
      (OutputShuffle.long_target_of_word D Sc i v x.1.1 he')
      (shPsi D Sc 1 x.1.1) (OutputShuffle.long_eq_of_word D Sc i v x.1.1 he') (c ≫ b)

/-- (IS2): containment of the full ELV ideal in the two prescribed summands. -/
theorem ideal_le_appendRelations_sup_range (i : I) (v w : List I) :
    ideal D Sc cutoff (v ++ [i]) w ≤ appendRelations D Sc cutoff i v w ⊔
      LinearMap.range (Linear.leftComp k (obj D Sc cutoff w) (appendW D Sc cutoff i v)) :=
  ideal_le_appendRelations_sup_range_of_parabolic_terms D Sc cutoff i v w
    (parabolic_term_mem_appendRelations_sup_range D Sc cutoff i v w)

/-- The ELV ideal is the sum of the append-old relations and the prescribed moving-strand image. -/
theorem ideal_eq_appendRelations_sup_range (i : I) (v w : List I) :
    ideal D Sc cutoff (v ++ [i]) w = appendRelations D Sc cutoff i v w ⊔
      LinearMap.range (Linear.leftComp k (obj D Sc cutoff w) (appendW D Sc cutoff i v)) := by
  apply le_antisymm (ideal_le_appendRelations_sup_range D Sc cutoff i v w)
  apply sup_le (appendRelations_le_ideal D Sc cutoff i v w)
  rintro _ ⟨b, rfl⟩
  exact ideal_comp D Sc cutoff (appendW_mem_ideal D Sc cutoff i v) b

end OddMath.QuiverHecke.ELVOld
end

end

section

/-!
# The cokernel of the full ELV P map

The ideal-sum equality identifies the kernel of the canonical append quotient
and its cokernel with the actual cyclotomic quotient on the enlarged word.
These are ground-ring linear maps; no polynomial module or projectivity
assertion is made.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The canonical quotient map imposing the remaining first-position relations. -/
def canonicalAppendTarget (i : I) (v w : List I) :
    AppendTarget D Sc cutoff i v w →ₗ[k] Old D Sc cutoff (v ++ [i]) w :=
  (appendRelations D Sc cutoff i v w).mapQ (ideal D Sc cutoff (v ++ [i]) w)
    LinearMap.id (appendRelations_le_ideal D Sc cutoff i v w)

@[simp] theorem canonicalAppendTarget_projection (i : I) (v w : List I)
    (f : hom D Sc cutoff (v ++ [i]) w) :
    canonicalAppendTarget D Sc cutoff i v w (appendProjection D Sc cutoff i v w f) =
      (ideal D Sc cutoff (v ++ [i]) w).mkQ f := rfl

theorem canonicalAppendTarget_surjective (i : I) (v w : List I) :
    Function.Surjective (canonicalAppendTarget D Sc cutoff i v w) := by
  intro z
  obtain ⟨f, rfl⟩ := (ideal D Sc cutoff (v ++ [i]) w).mkQ_surjective z
  exact ⟨appendProjection D Sc cutoff i v w f, rfl⟩

/-- The kernel is exactly the image of the prescribed descended P map. -/
theorem ker_canonicalAppendTarget (i : I) (v w : List I) :
    LinearMap.ker (canonicalAppendTarget D Sc cutoff i v w) =
      LinearMap.range (pMap D Sc cutoff i v w) := by
  ext z
  obtain ⟨f, rfl⟩ := appendProjection_surjective D Sc cutoff i v w z
  rw [LinearMap.mem_ker, canonicalAppendTarget_projection, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero]
  constructor
  · intro hf
    rw [ideal_eq_appendRelations_sup_range] at hf
    obtain ⟨r, hr, s, hs, he⟩ := Submodule.mem_sup.mp hf
    obtain ⟨b, rfl⟩ := hs
    refine ⟨projection D Sc cutoff i v w b, ?_⟩
    rw [← he, map_add, (appendProjection_eq_zero_iff D Sc cutoff i v w r).mpr hr, zero_add]
    rfl
  · rintro ⟨b, hb⟩
    obtain ⟨a, rfl⟩ := (relations D Sc cutoff i v w).mkQ_surjective b
    have hh : appendProjection D Sc cutoff i v w (appendW D Sc cutoff i v ≫ a) =
        appendProjection D Sc cutoff i v w f := hb
    have hr : appendW D Sc cutoff i v ≫ a - f ∈ appendRelations D Sc cutoff i v w := by
      apply (appendProjection_eq_zero_iff D Sc cutoff i v w _).mp
      rw [map_sub, hh, sub_self]
    have hi := appendRelations_le_ideal D Sc cutoff i v w hr
    have hw := ideal_comp D Sc cutoff (appendW_mem_ideal D Sc cutoff i v) a
    have H := (ideal D Sc cutoff (v ++ [i]) w).sub_mem hw hi
    simpa only [sub_sub_cancel] using H

/-- The cokernel of P is the actual enlarged-word cyclotomic quotient. -/
def pMapCokernelEquiv (i : I) (v w : List I) :
    (AppendTarget D Sc cutoff i v w ⧸ LinearMap.range (pMap D Sc cutoff i v w)) ≃ₗ[k]
      Old D Sc cutoff (v ++ [i]) w :=
  (Submodule.quotEquivOfEq _ _ (ker_canonicalAppendTarget D Sc cutoff i v w).symm).trans
    ((canonicalAppendTarget D Sc cutoff i v w).quotKerEquivOfSurjective
      (canonicalAppendTarget_surjective D Sc cutoff i v w))

@[simp] theorem pMapCokernelEquiv_mk (i : I) (v w : List I)
    (z : AppendTarget D Sc cutoff i v w) :
    pMapCokernelEquiv D Sc cutoff i v w (Submodule.Quotient.mk z) =
      canonicalAppendTarget D Sc cutoff i v w z := rfl

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # The canonical quotient of the short crossing tensor

The map changes the affine first factor to its cyclotomic class and changes
the lower balance from the affine category to its cyclotomic quotient.
The coefficient factor already has its prescribed cyclotomic quotient.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory TensorProduct
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
namespace CyclotomicCrossingTensor

/-- Words with the full affine coefficient-category Hom spaces. -/
structure AffineWord (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) where
  word : List I

instance : Category (AffineWord D Sc cutoff) where
  Hom v w := hom D Sc cutoff v.word w.word
  id v := 𝟙 (obj D Sc cutoff v.word)
  comp f g := f ≫ g
  id_comp := Category.id_comp
  comp_id := Category.comp_id
  assoc := Category.assoc

instance : Preadditive (AffineWord D Sc cutoff) where
  homGroup v w := inferInstanceAs (AddCommGroup (hom D Sc cutoff v.word w.word))
  add_comp := by
    intro v w z f g h
    exact Preadditive.add_comp (obj D Sc cutoff v.word) (obj D Sc cutoff w.word)
      (obj D Sc cutoff z.word) f g h
  comp_add := by
    intro v w z f g h
    exact Preadditive.comp_add (obj D Sc cutoff v.word) (obj D Sc cutoff w.word)
      (obj D Sc cutoff z.word) f g h

instance : Linear k (AffineWord D Sc cutoff) where
  homModule v w := inferInstanceAs (Module k (hom D Sc cutoff v.word w.word))
  smul_comp := by
    intro v w z r f g
    exact Linear.smul_comp (obj D Sc cutoff v.word) (obj D Sc cutoff w.word)
      (obj D Sc cutoff z.word) r f g
  comp_smul := by
    intro v w z f r g
    exact Linear.comp_smul (obj D Sc cutoff v.word) (obj D Sc cutoff w.word)
      (obj D Sc cutoff z.word) f r g

/-- The identity-on-words cyclotomic quotient. -/
def quotient : AffineWord D Sc cutoff ⥤ OldCategory D Sc cutoff where
  obj v := ⟨v.word⟩
  map {v w} := (ideal D Sc cutoff v.word w.word).mkQ
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Affine right append, before imposing either old ideal. -/
def affineAppend (i : I) : AffineWord D Sc cutoff ⥤ AffineWord D Sc cutoff where
  obj v := ⟨v.word ++ [i]⟩
  map {v w} := rightContext D Sc cutoff [i] v.word w.word
  map_id _ := rightContext_id D Sc cutoff [i] _
  map_comp f g := rightContext_comp D Sc cutoff [i] f g

/-- `Re ⊗_S Πᵖ(eB)`, balanced before quotienting the first factor. -/
abbrev ShortTarget (i : I) (v t : List I) :=
  BalancedInduction.Obj (affineAppend D Sc cutoff i)
    (quotient D Sc cutoff ⋙ coefficient D Sc cutoff (D.parity i) i v)
    (⟨t⟩ : AffineWord D Sc cutoff)

def shortTensor (i : I) (v s t : List I)
    (c : hom D Sc cutoff (s ++ [i]) t) (b : Old D Sc cutoff v (s ++ [i])) :
    ShortTarget D Sc cutoff i v t :=
  BalancedInduction.tensor (affineAppend D Sc cutoff i)
    (quotient D Sc cutoff ⋙ coefficient D Sc cutoff (D.parity i) i v) ⟨s⟩ c b

/-- Quotienting the first factor on one tensor summand. -/
def qSummand (i : I) (v s t : List I) :
    hom D Sc cutoff (s ++ [i]) t ⊗[k] Old D Sc cutoff v (s ++ [i]) →ₗ[k]
      Source D Sc cutoff i v t :=
  BalancedInduction.inclusion (append D Sc cutoff i)
    (coefficient D Sc cutoff (D.parity i) i v) ⟨t⟩ ⟨s⟩ ∘ₗ
      TensorProduct.map (ideal D Sc cutoff (s ++ [i]) t).mkQ LinearMap.id

@[simp] theorem qSummand_tmul (i : I) (v s t : List I)
    (c : hom D Sc cutoff (s ++ [i]) t) (b : Old D Sc cutoff v (s ++ [i])) :
    qSummand D Sc cutoff i v s t (c ⊗ₜ[k] b) =
      tensor D Sc cutoff i v s t ((ideal D Sc cutoff _ _).mkQ c) b := rfl

theorem qSummand_balance (i : I) (v s s' t : List I)
    (r : hom D Sc cutoff s s') (c : hom D Sc cutoff (s' ++ [i]) t)
    (b : Old D Sc cutoff v (s ++ [i])) :
    qSummand D Sc cutoff i v s t ((rightContext D Sc cutoff [i] _ _ r ≫ c) ⊗ₜ[k] b) =
      qSummand D Sc cutoff i v s' t (c ⊗ₜ[k]
        (coefficient D Sc cutoff (D.parity i) i v).map
          ((ideal D Sc cutoff s s').mkQ r) b) := by
  rw [qSummand_tmul, qSummand_tmul]
  exact BalancedInduction.balance (append D Sc cutoff i)
    (coefficient D Sc cutoff (D.parity i) i v)
    ((ideal D Sc cutoff s s').mkQ r)
    ((ideal D Sc cutoff (s' ++ [i]) t).mkQ c) b

/-- The canonical quotient changes only the first tensor factor. -/
def q (i : I) (v t : List I) : ShortTarget D Sc cutoff i v t →ₗ[k]
    Source D Sc cutoff i v t :=
  BalancedInduction.lift (affineAppend D Sc cutoff i)
    (quotient D Sc cutoff ⋙ coefficient D Sc cutoff (D.parity i) i v) ⟨t⟩
    (fun s => qSummand D Sc cutoff i v s.word t)
    (fun s s' r c b => qSummand_balance D Sc cutoff i v s.word s'.word t r c b)

@[simp] theorem q_shortTensor (i : I) (v s t : List I)
    (c : hom D Sc cutoff (s ++ [i]) t) (b : Old D Sc cutoff v (s ++ [i])) :
    q D Sc cutoff i v t (shortTensor D Sc cutoff i v s t c b) =
      tensor D Sc cutoff i v s t ((ideal D Sc cutoff _ _).mkQ c) b := by
  exact BalancedInduction.lift_tensor (affineAppend D Sc cutoff i)
    (quotient D Sc cutoff ⋙ coefficient D Sc cutoff (D.parity i) i v) ⟨t⟩ _ _ ⟨s⟩ c b

/-- The canonical quotient is surjective without flatness or projectivity. -/
theorem q_surjective (i : I) (v t : List I) : Function.Surjective (q D Sc cutoff i v t) := by
  classical
  intro z
  obtain ⟨z, rfl⟩ := (BalancedInduction.relations (append D Sc cutoff i)
    (coefficient D Sc cutoff (D.parity i) i v) ⟨t⟩).mkQ_surjective z
  induction z using DirectSum.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | add x y hx hy =>
    obtain ⟨x', hx'⟩ := hx
    obtain ⟨y', hy'⟩ := hy
    exact ⟨x' + y', by rw [map_add, hx', hy', map_add]⟩
  | of s z =>
    induction z using TensorProduct.inductionOn with
    | add x y hx hy =>
      obtain ⟨x', hx'⟩ := hx
      obtain ⟨y', hy'⟩ := hy
      exact ⟨x' + y', by rw [map_add, hx', hy', map_add, map_add]⟩
    | tmul c b =>
      obtain ⟨c, rfl⟩ := (ideal D Sc cutoff (s.word ++ [i]) t).mkQ_surjective c
      exact ⟨shortTensor D Sc cutoff i v s.word t c b, q_shortTensor D Sc cutoff i v s.word t c b⟩

/-- The descended vertical map has the literal crossing-column formula on lifts. -/
theorem toCyclotomic_q_shortTensor (i : I) (v s t : List I)
    (c : hom D Sc cutoff (s ++ [i]) t) (b : hom D Sc cutoff v (s ++ [i])) :
    toCyclotomic D Sc cutoff i v t
      (q D Sc cutoff i v t (shortTensor D Sc cutoff i v s t c
        ((ideal D Sc cutoff _ _).mkQ b))) =
    (ideal D Sc cutoff (v ++ [i]) (t ++ [i])).mkQ
      (rightContext D Sc cutoff [i] _ _ b ≫
        affineUnit D Sc cutoff _ _ (crossLast D Sc s i i) ≫
        rightContext D Sc cutoff [i] _ _ c) := by
  rw [q_shortTensor, toCyclotomic_tensor_mk]

end CyclotomicCrossingTensor
end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # Kernel of the canonical short-column quotient

The kernel is computed from the first-factor cyclotomic ideal on the prescribed
balanced tensor. No crossing-image source or injectivity assertion is used.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory TensorProduct
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
namespace CyclotomicCrossingTensor

/-- First-factor cyclotomic relations in the affine balanced source. -/
def firstIdeal (i : I) (v t : List I) : Submodule k (ShortTarget D Sc cutoff i v t) :=
  Submodule.span k {z | ∃ s, ∃ c : hom D Sc cutoff (s ++ [i]) t,
    c ∈ ideal D Sc cutoff (s ++ [i]) t ∧ ∃ b : Old D Sc cutoff v (s ++ [i]),
      shortTensor D Sc cutoff i v s t c b = z}

/-- Each indicated ideal tensor is killed by the canonical quotient. -/
theorem firstIdeal_le_ker_q (i : I) (v t : List I) :
    firstIdeal D Sc cutoff i v t ≤ LinearMap.ker (q D Sc cutoff i v t) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨s, c, hc, b, rfl⟩
  change q D Sc cutoff i v t _ = 0
  have hz : (ideal D Sc cutoff (s ++ [i]) t).mkQ c = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr hc
  rw [q_shortTensor, hz]
  change BalancedInduction.inclusion (append D Sc cutoff i)
    (coefficient D Sc cutoff (D.parity i) i v) ⟨t⟩ ⟨s⟩ (0 ⊗ₜ[k] b) = 0
  rw [zero_tmul, map_zero]

/-- The affine tensor pairing followed by the specified ideal quotient. -/
def quotientPair (i : I) (v s t : List I) :
    hom D Sc cutoff (s ++ [i]) t →ₗ[k]
      Old D Sc cutoff v (s ++ [i]) →ₗ[k]
        ShortTarget D Sc cutoff i v t ⧸ firstIdeal D Sc cutoff i v t :=
  LinearMap.compr₂
    ((TensorProduct.mk k _ _).compr₂
      (BalancedInduction.inclusion (affineAppend D Sc cutoff i)
        (quotient D Sc cutoff ⋙ coefficient D Sc cutoff (D.parity i) i v) ⟨t⟩ ⟨s⟩))
    (firstIdeal D Sc cutoff i v t).mkQ

/-- Descent in the first factor alone. -/
def inversePair (i : I) (v s t : List I) :
    Old D Sc cutoff (s ++ [i]) t →ₗ[k]
      Old D Sc cutoff v (s ++ [i]) →ₗ[k]
        ShortTarget D Sc cutoff i v t ⧸ firstIdeal D Sc cutoff i v t :=
  (ideal D Sc cutoff (s ++ [i]) t).liftQ (quotientPair D Sc cutoff i v s t) (by
    intro c hc
    apply LinearMap.ext
    intro b
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact Submodule.subset_span ⟨s, c, hc, b, rfl⟩)

@[simp] theorem inversePair_mk (i : I) (v s t : List I)
    (c : hom D Sc cutoff (s ++ [i]) t) (b : Old D Sc cutoff v (s ++ [i])) :
    inversePair D Sc cutoff i v s t ((ideal D Sc cutoff _ _).mkQ c) b =
      (firstIdeal D Sc cutoff i v t).mkQ (shortTensor D Sc cutoff i v s t c b) := rfl

theorem shortTensor_balance (i : I) (v s s' t : List I)
    (r : hom D Sc cutoff s s') (c : hom D Sc cutoff (s' ++ [i]) t)
    (b : Old D Sc cutoff v (s ++ [i])) :
    shortTensor D Sc cutoff i v s t (rightContext D Sc cutoff [i] _ _ r ≫ c) b =
      shortTensor D Sc cutoff i v s' t c
        ((coefficient D Sc cutoff (D.parity i) i v).map
          ((ideal D Sc cutoff s s').mkQ r) b) :=
  BalancedInduction.balance (affineAppend D Sc cutoff i)
    (quotient D Sc cutoff ⋙ coefficient D Sc cutoff (D.parity i) i v)
    (v := ⟨s⟩) (v' := ⟨s'⟩) r c b

theorem inversePair_balance (i : I) (v : List I) (s s' t : OldCategory D Sc cutoff)
    (r : s ⟶ s') (c : (append D Sc cutoff i).obj s' ⟶ t)
    (b : (coefficient D Sc cutoff (D.parity i) i v).obj s) :
    inversePair D Sc cutoff i v s.word t.word ((append D Sc cutoff i).map r ≫ c) b =
      inversePair D Sc cutoff i v s'.word t.word c
        ((coefficient D Sc cutoff (D.parity i) i v).map r b) := by
  obtain ⟨r, rfl⟩ := (ideal D Sc cutoff s.word s'.word).mkQ_surjective r
  obtain ⟨c, rfl⟩ := (ideal D Sc cutoff (s'.word ++ [i]) t.word).mkQ_surjective c
  exact congrArg (firstIdeal D Sc cutoff i v t.word).mkQ
    (shortTensor_balance D Sc cutoff i v s.word s'.word t.word r c b)

/-- The reverse map is defined on the lower-cyclotomic balanced tensor itself. -/
def inverse (i : I) (v t : List I) : Source D Sc cutoff i v t →ₗ[k]
    ShortTarget D Sc cutoff i v t ⧸ firstIdeal D Sc cutoff i v t :=
  BalancedInduction.lift (append D Sc cutoff i)
    (coefficient D Sc cutoff (D.parity i) i v) ⟨t⟩
    (fun s => TensorProduct.lift (inversePair D Sc cutoff i v s.word t))
    (fun s s' r c b => inversePair_balance D Sc cutoff i v s s' ⟨t⟩ r c b)

@[simp] theorem inverse_tensor_mk (i : I) (v s t : List I)
    (c : hom D Sc cutoff (s ++ [i]) t) (b : Old D Sc cutoff v (s ++ [i])) :
    inverse D Sc cutoff i v t (tensor D Sc cutoff i v s t
      ((ideal D Sc cutoff _ _).mkQ c) b) =
      (firstIdeal D Sc cutoff i v t).mkQ (shortTensor D Sc cutoff i v s t c b) := by
  exact BalancedInduction.lift_tensor (append D Sc cutoff i)
    (coefficient D Sc cutoff (D.parity i) i v) ⟨t⟩ _ _ ⟨s⟩ _ b

theorem inverse_q (i : I) (v t : List I) :
    inverse D Sc cutoff i v t ∘ₗ q D Sc cutoff i v t =
      (firstIdeal D Sc cutoff i v t).mkQ := by
  apply BalancedInduction.hom_ext
  intro s c b
  change inverse D Sc cutoff i v t
    (q D Sc cutoff i v t (shortTensor D Sc cutoff i v s.word t c b)) = _
  rw [q_shortTensor, inverse_tensor_mk]
  rfl

/-- Exact kernel equality for the canonical quotient, without a flatness assumption. -/
theorem ker_q (i : I) (v t : List I) :
    LinearMap.ker (q D Sc cutoff i v t) = firstIdeal D Sc cutoff i v t := by
  apply le_antisymm
  · intro z hz
    have h := congrArg (fun f => f z) (inverse_q D Sc cutoff i v t)
    change inverse D Sc cutoff i v t (q D Sc cutoff i v t z) =
      (firstIdeal D Sc cutoff i v t).mkQ z at h
    rw [LinearMap.mem_ker.mp hz, map_zero] at h
    exact (Submodule.Quotient.mk_eq_zero _).mp h.symm
  · exact firstIdeal_le_ker_q D Sc cutoff i v t

/-- The first tensor coordinate as a linear map, for ideal-sum descent. -/
def shortLeft (i : I) (v s t : List I) (b : Old D Sc cutoff v (s ++ [i])) :
    hom D Sc cutoff (s ++ [i]) t →ₗ[k] ShortTarget D Sc cutoff i v t :=
  BalancedInduction.inclusion (affineAppend D Sc cutoff i)
    (quotient D Sc cutoff ⋙ coefficient D Sc cutoff (D.parity i) i v) ⟨t⟩ ⟨s⟩ ∘ₗ
      (TensorProduct.mk k _ _).flip b

/-- Lower old relations already vanish by the prescribed balance. -/
theorem shortTensor_appendRelations (i : I) (v s t : List I)
    (c : hom D Sc cutoff (s ++ [i]) t) (hc : c ∈ appendRelations D Sc cutoff i s t)
    (b : Old D Sc cutoff v (s ++ [i])) :
    shortTensor D Sc cutoff i v s t c b = 0 := by
  have h : appendRelations D Sc cutoff i s t ≤ LinearMap.ker (shortLeft D Sc cutoff i v s t b) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨s', r, hr, c, rfl⟩
    change shortTensor D Sc cutoff i v s t (rightContext D Sc cutoff [i] _ _ r ≫ c) b = 0
    rw [shortTensor_balance]
    have hz : (coefficient D Sc cutoff (D.parity i) i v).map
        ((ideal D Sc cutoff s s').mkQ r) b = 0 := by
      obtain ⟨b, rfl⟩ := (ideal D Sc cutoff v (s ++ [i])).mkQ_surjective b
      change (ideal D Sc cutoff _ _).mkQ
        (b ≫ rightContext D Sc cutoff [i] _ _ (twist k (D.parity i) r)) = 0
      exact (Submodule.Quotient.mk_eq_zero _).mpr
        (comp_ideal D Sc cutoff b
          (ideal_rightContext D Sc cutoff [i] (twist_ideal D Sc cutoff _ hr)))
    rw [hz]
    change BalancedInduction.inclusion (affineAppend D Sc cutoff i)
      (quotient D Sc cutoff ⋙ coefficient D Sc cutoff (D.parity i) i v) ⟨t⟩ ⟨s'⟩
        (c ⊗ₜ[k] 0) = 0
    rw [tmul_zero, map_zero]
  exact h hc

/-- The literal lower moving-word generators, before constructing their balanced domain. -/
def movingImage (i : I) (v t : List I) : Submodule k (ShortTarget D Sc cutoff i v t) :=
  Submodule.span k {z | ∃ s, ∃ h : hom D Sc cutoff (i :: s) t,
    ∃ b : Old D Sc cutoff v (s ++ [i]),
      shortTensor D Sc cutoff i v s t (appendW D Sc cutoff i s ≫ h) b = z}

/-- The proved full-ELV ideal sum reduces the kernel to the actual lower moving word. -/
theorem firstIdeal_eq_movingImage (i : I) (v t : List I) :
    firstIdeal D Sc cutoff i v t = movingImage D Sc cutoff i v t := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨s, c, hc, b, rfl⟩
    rw [ideal_eq_appendRelations_sup_range] at hc
    obtain ⟨a, ha, w, ⟨h, rfl⟩, rfl⟩ := Submodule.mem_sup.mp hc
    change shortLeft D Sc cutoff i v s t b (a + (appendW D Sc cutoff i s ≫ h)) ∈ _
    rw [map_add]
    have hz := shortTensor_appendRelations D Sc cutoff i v s t a ha b
    change shortLeft D Sc cutoff i v s t b a = 0 at hz
    rw [hz, zero_add]
    exact Submodule.subset_span ⟨s, h, b, rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨s, h, b, rfl⟩
    exact Submodule.subset_span ⟨s, appendW D Sc cutoff i s ≫ h,
      ideal_comp D Sc cutoff (appendW_mem_ideal D Sc cutoff i s) h, b, rfl⟩

/-- Concrete kernel equality: the generators are `h W₋ ⊗ πᵖ b` in algebra order. -/
theorem ker_q_eq_movingImage (i : I) (v t : List I) :
    LinearMap.ker (q D Sc cutoff i v t) = movingImage D Sc cutoff i v t := by
  rw [ker_q, firstIdeal_eq_movingImage]

/-- The quotient by the literal moving-word relations is the prescribed source. -/
def quotientEquiv (i : I) (v t : List I) :
    (ShortTarget D Sc cutoff i v t ⧸ movingImage D Sc cutoff i v t) ≃ₗ[k]
      Source D Sc cutoff i v t :=
  (Submodule.quotEquivOfEq _ _ (ker_q_eq_movingImage D Sc cutoff i v t).symm).trans
    ((q D Sc cutoff i v t).quotKerEquivOfSurjective (q_surjective D Sc cutoff i v t))

@[simp] theorem quotientEquiv_mk (i : I) (v t : List I)
    (z : ShortTarget D Sc cutoff i v t) :
    quotientEquiv D Sc cutoff i v t (Submodule.Quotient.mk z) = q D Sc cutoff i v t z := rfl

end CyclotomicCrossingTensor
end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # The balanced short moving-word map

The domain is `Rf ⊗_(S,j_L) Π^epsilon(eB)`. The lower balance is
proved using the full ELV moving-word error, including exterior coefficients.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory TensorProduct
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
namespace CyclotomicCrossingTensor

/-- The resolution shift on the coefficient word of content beta. -/
def epsilon (i : I) (v : List I) : ZMod 2 :=
  D.parity i * wordSumParity D v + (cutoff i : ZMod 2) * D.parity i

/-- Left inclusion on the full affine coefficient category. -/
def affinePrepend (i : I) : AffineWord D Sc cutoff ⥤ AffineWord D Sc cutoff where
  obj s := ⟨i :: s.word⟩
  map {s t} := insert D Sc cutoff i s.word t.word
  map_id _ := insert_id D Sc cutoff i _
  map_comp f g := insert_comp D Sc cutoff i f g

/-- The prescribed epsilon-shifted balanced domain, before applying the moving word. -/
abbrev PprimeDomain (i : I) (v t : List I) :=
  BalancedInduction.Obj (affinePrepend D Sc cutoff i)
    (quotient D Sc cutoff ⋙ coefficient D Sc cutoff (epsilon D cutoff i v) i v)
    (⟨t⟩ : AffineWord D Sc cutoff)

def pprimeTensor (i : I) (v s t : List I)
    (h : hom D Sc cutoff (i :: s) t) (b : Old D Sc cutoff v (s ++ [i])) :
    PprimeDomain D Sc cutoff i v t :=
  BalancedInduction.tensor (affinePrepend D Sc cutoff i)
    (quotient D Sc cutoff ⋙ coefficient D Sc cutoff (epsilon D cutoff i v) i v) ⟨s⟩ h b

/-- On a supported coefficient corner, epsilon is the moving parity plus p. -/
theorem epsilon_eq_appendQ_add (i : I) (v s : List I)
    (hv : wordSumParity D (s ++ [i]) = wordSumParity D v) :
    epsilon D cutoff i v = appendQ D cutoff i s + D.parity i := by
  have hp : D.parity i * D.parity i = D.parity i := by
    rcases parity_eq_zero_or_one (D.parity i) with h | h <;> simp [h]
  unfold epsilon appendQ
  rw [← hv]
  simp only [wordSumParity, List.map_append, List.map_cons, List.map_nil,
    List.sum_append, List.sum_cons, List.sum_nil, add_zero]
  rw [mul_add, hp]
  ring

/-- Multiplication by W on one tensor summand. -/
def pprimeSummand (i : I) (v s t : List I) :
    hom D Sc cutoff (i :: s) t ⊗[k] Old D Sc cutoff v (s ++ [i]) →ₗ[k]
      ShortTarget D Sc cutoff i v t :=
  BalancedInduction.inclusion (affineAppend D Sc cutoff i)
    (quotient D Sc cutoff ⋙ coefficient D Sc cutoff (D.parity i) i v) ⟨t⟩ ⟨s⟩ ∘ₗ
    TensorProduct.map (Linear.leftComp k _ (appendW D Sc cutoff i s)) LinearMap.id

@[simp] theorem pprimeSummand_tmul (i : I) (v s t : List I)
    (h : hom D Sc cutoff (i :: s) t) (b : Old D Sc cutoff v (s ++ [i])) :
    pprimeSummand D Sc cutoff i v s t (h ⊗ₜ[k] b) =
      shortTensor D Sc cutoff i v s t (appendW D Sc cutoff i s ≫ h) b := rfl

/-- The full lower balance, not only scalar or homogeneous-generator balance. -/
theorem pprimeSummand_balance (i : I) (v s s' t : List I)
    (r : hom D Sc cutoff s s') (h : hom D Sc cutoff (i :: s') t)
    (b : Old D Sc cutoff v (s ++ [i])) :
    pprimeSummand D Sc cutoff i v s t ((insert D Sc cutoff i s s' r ≫ h) ⊗ₜ[k] b) =
      pprimeSummand D Sc cutoff i v s' t (h ⊗ₜ[k]
        (coefficient D Sc cutoff (epsilon D cutoff i v) i v).map
          ((ideal D Sc cutoff s s').mkQ r) b) := by
  obtain ⟨b, rfl⟩ := (ideal D Sc cutoff v (s ++ [i])).mkQ_surjective b
  by_cases hv : wordSumParity D (s ++ [i]) = wordSumParity D v
  · have he := appendRelations_comp D Sc cutoff i
      (appendError_mem_appendRelations D Sc cutoff i (twist k (appendQ D cutoff i s) r)) h
    have hz := shortTensor_appendRelations D Sc cutoff i v s t _ he
      ((ideal D Sc cutoff v (s ++ [i])).mkQ b)
    change shortLeft D Sc cutoff i v s t _ _ = 0 at hz
    rw [appendError_apply, twist_twist, Preadditive.sub_comp, map_sub, sub_eq_zero] at hz
    change shortTensor D Sc cutoff i v s t _ _ = shortTensor D Sc cutoff i v s t _ _ at hz
    rw [Category.assoc, Category.assoc] at hz
    rw [pprimeSummand_tmul, pprimeSummand_tmul, ← hz, shortTensor_balance]
    congr 1
    change (ideal D Sc cutoff _ _).mkQ
      (b ≫ rightContext D Sc cutoff [i] _ _
        (twist k (D.parity i) (twist k (appendQ D cutoff i s) r))) =
      (ideal D Sc cutoff _ _).mkQ
        (b ≫ rightContext D Sc cutoff [i] _ _ (twist k (epsilon D cutoff i v) r))
    rw [epsilon_eq_appendQ_add D cutoff i v s hv, add_comm (appendQ D cutoff i s), twist_add]
  · rw [hom_zero_of_wordParity_ne D Sc cutoff hv b, map_zero, map_zero,
      tmul_zero, tmul_zero, map_zero, map_zero]

/-- The descended moving-word map on the independently prescribed domain. -/
def pprime (i : I) (v t : List I) : PprimeDomain D Sc cutoff i v t →ₗ[k]
    ShortTarget D Sc cutoff i v t :=
  BalancedInduction.lift (affinePrepend D Sc cutoff i)
    (quotient D Sc cutoff ⋙ coefficient D Sc cutoff (epsilon D cutoff i v) i v) ⟨t⟩
    (fun s => pprimeSummand D Sc cutoff i v s.word t)
    (fun s s' r h b => pprimeSummand_balance D Sc cutoff i v s.word s'.word t r h b)

@[simp] theorem pprime_tensor (i : I) (v s t : List I)
    (h : hom D Sc cutoff (i :: s) t) (b : Old D Sc cutoff v (s ++ [i])) :
    pprime D Sc cutoff i v t (pprimeTensor D Sc cutoff i v s t h b) =
      shortTensor D Sc cutoff i v s t (appendW D Sc cutoff i s ≫ h) b := by
  exact BalancedInduction.lift_tensor (affinePrepend D Sc cutoff i)
    (quotient D Sc cutoff ⋙ coefficient D Sc cutoff (epsilon D cutoff i v) i v) ⟨t⟩ _ _ ⟨s⟩ h b

/-- The range is exactly the literal moving-word span. -/
theorem range_pprime (i : I) (v t : List I) :
    LinearMap.range (pprime D Sc cutoff i v t) = movingImage D Sc cutoff i v t := by
  classical
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩
    obtain ⟨z, rfl⟩ := (BalancedInduction.relations (affinePrepend D Sc cutoff i)
      (quotient D Sc cutoff ⋙ coefficient D Sc cutoff (epsilon D cutoff i v) i v) ⟨t⟩).mkQ_surjective z
    induction z using DirectSum.induction_on with
    | zero => simpa only [map_zero] using (movingImage D Sc cutoff i v t).zero_mem
    | add x y hx hy => simpa only [map_add] using (movingImage D Sc cutoff i v t).add_mem hx hy
    | of s z =>
      induction z using TensorProduct.inductionOn with
      | add x y hx hy => simpa only [map_add] using (movingImage D Sc cutoff i v t).add_mem hx hy
      | tmul h b =>
        change pprime D Sc cutoff i v t (pprimeTensor D Sc cutoff i v s.word t h b) ∈ _
        rw [pprime_tensor]
        exact Submodule.subset_span ⟨s.word, h, b, rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨s, h, b, rfl⟩
    exact ⟨pprimeTensor D Sc cutoff i v s t h b, pprime_tensor D Sc cutoff i v s t h b⟩

/-- Right exactness for the named moving-word map and canonical quotient. -/
theorem range_pprime_eq_ker_q (i : I) (v t : List I) :
    LinearMap.range (pprime D Sc cutoff i v t) = LinearMap.ker (q D Sc cutoff i v t) := by
  rw [range_pprime, ker_q_eq_movingImage]

end CyclotomicCrossingTensor
end OddMath.QuiverHecke.ELVOld
end

end
