import OddMath.QuiverHecke.CyclotomicAction.CyclotomicQuotientTop
import OddMath.QuiverHecke.CyclotomicAction.VacuumGrading
import OddMath.QuiverHecke.CyclotomicAction.ParabolicTransport
import OddMath.QuiverHecke.CyclotomicAction.AppendContent
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import OddMath.SKM.ELVCoefficientPowers
import Mathlib.RingTheory.Congruence.Hom

/-!
# Coefficient power annihilation

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # Coefficient annihilators under old append induction and restriction

The coefficient-power quotient in `SwappedNondegeneracy.md`, §2 requires
preservation of its own annihilator, rather than identification with a
weighted coefficient quotient. These results apply to every homogeneous
full ELV coefficient, including the even power generators of that ideal.
They retain the signed coefficient slide and actual balanced induction.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- A full ELV coefficient acting at an arbitrary old word. -/
def coefficientEndomorphism (v : List I)
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
    (⟨v⟩ : OldCategory D Sc cutoff) ⟶ ⟨v⟩ :=
  (ideal D Sc cutoff v v).mkQ (ELVPScalar.scalar D Sc cutoff v a)

theorem coefficientEndomorphism_mem (v : List I) {p : ZMod 2}
    {a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff}
    (ha : a ∈ SKM.SYM.elvCoefficientParity D cutoff p) :
    coefficientEndomorphism D Sc cutoff v a ∈
      parity (R := k) (⟨v⟩ : OldCategory D Sc cutoff) ⟨v⟩ p :=
  Submodule.mem_map_of_mem (ELVPScalar.scalar_mem D Sc cutoff v ha)

/-- Coefficient endomorphisms compose in the opposite multiplication
order. This order is material when two different odd colours occur. -/
theorem coefficientEndomorphism_comp (v : List I)
    (a b : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
    oldComp D Sc cutoff v v v (coefficientEndomorphism D Sc cutoff v a)
      (coefficientEndomorphism D Sc cutoff v b) =
      coefficientEndomorphism D Sc cutoff v (b * a) := by
  change (ideal D Sc cutoff v v).mkQ
    (ELVPScalar.scalar D Sc cutoff v a ≫ ELVPScalar.scalar D Sc cutoff v b) = _
  congr 1
  change BoxProd.tmulHom (X := obj D Sc cutoff v) (Y := obj D Sc cutoff v) a (𝟙 _) ≫
    BoxProd.tmulHom (X := obj D Sc cutoff v) (Y := obj D Sc cutoff v) b (𝟙 _) = _
  rw [BoxProd.tmulHom_comp_tmulHom_eq]
  simp only [twist_id, Category.comp_id, ← BoxProd.tmulHom_add_left,
    ← Preadditive.add_comp, proj_add_proj]
  rfl

/-- The full coefficient parity, rather than only affine parity, controls
the slide through an arbitrary old morphism. -/
theorem coefficientEndomorphism_slide {p : ZMod 2}
    {a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff}
    (ha : a ∈ SKM.SYM.elvCoefficientParity D cutoff p)
    (v w : List I) (f : (⟨v⟩ : OldCategory D Sc cutoff) ⟶ ⟨w⟩) :
    f ≫ coefficientEndomorphism D Sc cutoff w a =
      coefficientEndomorphism D Sc cutoff v a ≫ twist k p f := by
  obtain ⟨f, rfl⟩ := (ideal D Sc cutoff v w).mkQ_surjective f
  have h := congrArg ((ideal D Sc cutoff v w).mkQ)
    (ELVPScalar.scalar_slide_homogeneous D Sc cutoff ha f)
  rw [oldQuotient_twist]
  exact h

@[simp] theorem append_coefficientEndomorphism (i : I) (v : List I)
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
    (CyclotomicCrossingTensor.append D Sc cutoff i).map
      (X := ⟨v⟩) (Y := ⟨v⟩) (coefficientEndomorphism D Sc cutoff v a) =
      coefficientEndomorphism D Sc cutoff (v ++ [i]) a := by
  change (ideal D Sc cutoff (v ++ [i]) (v ++ [i])).mkQ
    (rightContext D Sc cutoff [i] v v (ELVPScalar.scalar D Sc cutoff v a)) = _
  rw [ELVPScalar.rightContext_scalar]
  rfl

/-- An old module annihilates this coefficient at every word. -/
def KillsCoefficient (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) : Prop :=
  ∀ v : List I, M.map (X := ⟨v⟩) (Y := ⟨v⟩)
    (coefficientEndomorphism D Sc cutoff v a) = 0

/-- Restriction preserves annihilation by each full coefficient. -/
theorem restriction_killsCoefficient (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff)
    (hM : KillsCoefficient D Sc cutoff M a) :
    KillsCoefficient D Sc cutoff
      ((BalancedInduction.restriction (CyclotomicCrossingTensor.append D Sc cutoff i)).obj M) a := by
  intro v
  change M.map (X := ⟨v ++ [i]⟩) (Y := ⟨v ++ [i]⟩)
    ((CyclotomicCrossingTensor.append D Sc cutoff i).map
      (X := ⟨v⟩) (Y := ⟨v⟩) (coefficientEndomorphism D Sc cutoff v a)) = 0
  rw [append_coefficientEndomorphism]
  exact hM _

/-- Actual balanced induction preserves the annihilator of every
homogeneous coefficient. No comparison with a weighted ideal is used. -/
theorem induced_killsCoefficient (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) {p : ZMod 2}
    {a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff}
    (ha : a ∈ SKM.SYM.elvCoefficientParity D cutoff p)
    (hM : KillsCoefficient D Sc cutoff M a) :
    KillsCoefficient D Sc cutoff
      (BalancedInduction.induced (CyclotomicCrossingTensor.append D Sc cutoff i) M) a := by
  intro w
  let J := CyclotomicCrossingTensor.append D Sc cutoff i
  change BalancedInduction.postcompose J M.toFunctor
    (coefficientEndomorphism D Sc cutoff w a) = 0
  apply BalancedInduction.hom_ext
  rintro ⟨v⟩ h m
  rw [BalancedInduction.postcompose_tensor, coefficientEndomorphism_slide D Sc cutoff ha]
  have hc : coefficientEndomorphism D Sc cutoff (v ++ [i]) a =
      J.map (X := ⟨v⟩) (Y := ⟨v⟩) (coefficientEndomorphism D Sc cutoff v a) :=
    (append_coefficientEndomorphism D Sc cutoff i v a).symm
  rw [hc, BalancedInduction.balance]
  have hz : M.toFunctor.map (X := ⟨v⟩) (Y := ⟨v⟩)
      (coefficientEndomorphism D Sc cutoff v a) = 0 := hM v
  rw [hz, LinearMap.zero_apply, BalancedInduction.tensor_zero_right]
  rfl

/-- In particular the defining powers of an even coefficient ideal remain
annihilating after actual induction. These are the paper's generators,
without replacing them by a larger weighted ideal. -/
theorem induced_killsEvenPower (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    {a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff}
    (ha : a ∈ SKM.SYM.elvCoefficientParity D cutoff 0) (L : ℕ)
    (hM : KillsCoefficient D Sc cutoff M (a ^ L)) :
    KillsCoefficient D Sc cutoff
      (BalancedInduction.induced (CyclotomicCrossingTensor.append D Sc cutoff i) M) (a ^ L) := by
  have hp : a ^ L ∈ SKM.SYM.elvCoefficientParity D cutoff 0 := by
    clear hM
    induction L with
    | zero => simpa only [pow_zero] using
        (SetLike.GradedOne.one_mem :
          (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ∈
            SKM.SYM.elvCoefficientParity D cutoff 0)
    | succ L ih => simpa only [pow_succ, add_zero] using
        SetLike.mul_mem_graded ih ha
  exact induced_killsCoefficient D Sc cutoff i M hp hM

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # Full faithfulness of the empty-word coefficient embedding

The identity B_0=A in `DeformedReservoirBound.md`, §2, and the coefficient
input of the literal power vacuum. The affine empty-word PBW coordinate
and the absence of old cyclotomic relations give the exact Hom comparison.
No coefficient independence of the oriented action is assumed.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped TensorProduct
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

private def emptyNormalIndex : NFIdx ([] : List I) [] := by
  have hc : Categorification.TypeA.canWord 0 (1 : Equiv.Perm (Fin 0)) = [] := by
    apply List.length_eq_zero_iff.mp
    rw [Categorification.TypeA.length_canWord, Categorification.TypeA.length_one]
  refine ⟨([], 1), by simp, by simp, ?_⟩
  simp only [List.map_nil, List.length_nil, hc, cw, List.reverse_nil, List.nil_append, pl, SChain]

private def affineEmptyCoordinate :
    ((pres D Sc).obj (ob D []) ⟶ (pres D Sc).obj (ob D [])) →ₗ[k] k :=
  (basisNF D Sc [] []).coord (emptyNormalIndex (I := I))

private theorem affineEmptyCoordinate_id : affineEmptyCoordinate D Sc (𝟙 _) = 1 := by
  rw [← vacuum_nf D Sc (emptyNormalIndex (I := I)), affineEmptyCoordinate, ← basisNF_apply]
  change ((basisNF D Sc [] []).repr ((basisNF D Sc [] []) (emptyNormalIndex (I := I))))
    (emptyNormalIndex (I := I)) = 1
  simp only [Module.Basis.repr_self, Finsupp.single_eq_same]

/-- Coefficients at the empty identity, with all exterior coefficients retained. -/
def emptyCoefficientEncoder : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff →ₗ[k]
    Old D Sc cutoff [] [] :=
  (ideal D Sc cutoff [] []).mkQ.comp (ELVPScalar.scalar D Sc cutoff [])

private def rawEmptyCoefficientDecoder : hom D Sc cutoff [] [] →ₗ[k]
    SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff :=
  (TensorProduct.rid k (SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff)).toLinearMap.comp
    (TensorProduct.map LinearMap.id (affineEmptyCoordinate D Sc))

/-- The affine-empty PBW coordinate decodes the literal old coefficient
corner. There is no first-position cyclotomic relation at the empty word. -/
def emptyCoefficientDecoder : Old D Sc cutoff [] [] →ₗ[k]
    SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff :=
  (ideal D Sc cutoff [] []).liftQ (rawEmptyCoefficientDecoder D Sc cutoff) (by
    intro f hf
    have hz : f = 0 := by simpa only [ideal_nil, Submodule.mem_bot] using hf
    rw [hz]
    exact Submodule.zero_mem _)

@[simp] theorem emptyCoefficientDecoder_encoder
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
    emptyCoefficientDecoder D Sc cutoff (emptyCoefficientEncoder D Sc cutoff a) = a := by
  change (TensorProduct.rid k (SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff))
    (a ⊗ₜ[k] affineEmptyCoordinate D Sc (𝟙 _)) = a
  rw [affineEmptyCoordinate_id, TensorProduct.rid_tmul, one_smul]

@[simp] theorem emptyCoefficientEncoder_decoder (z : Old D Sc cutoff [] []) :
    emptyCoefficientEncoder D Sc cutoff (emptyCoefficientDecoder D Sc cutoff z) = z := by
  obtain ⟨f, rfl⟩ := (ideal D Sc cutoff [] []).mkQ_surjective z
  have hf := vacuum_hom_span D Sc cutoff f
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨a, rfl⟩ := hf
    change emptyCoefficientEncoder D Sc cutoff
      (emptyCoefficientDecoder D Sc cutoff
        (emptyCoefficientEncoder D Sc cutoff (SKM.SYM.elvCoefficientQuotient D cutoff a))) =
      emptyCoefficientEncoder D Sc cutoff (SKM.SYM.elvCoefficientQuotient D cutoff a)
    rw [emptyCoefficientDecoder_encoder]
  | zero => simp only [map_zero]
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul r x _ hx => simp only [map_smul, hx]

/-- The complete old empty-word Hom is its full coefficient algebra. -/
def emptyCoefficientEquiv : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff ≃ₗ[k]
    Old D Sc cutoff [] [] :=
  LinearEquiv.ofLinearMap (emptyCoefficientEncoder D Sc cutoff) (emptyCoefficientDecoder D Sc cutoff)
    (by apply LinearMap.ext; intro z; exact emptyCoefficientEncoder_decoder D Sc cutoff z)
    (by apply LinearMap.ext; intro a; exact emptyCoefficientDecoder_encoder D Sc cutoff a)

/-- The original coefficient supercategory embeds at the empty old word. -/
def emptyCoefficientEmbedding :
    SuperalgebraCat (SKM.SYM.elvCoefficientParity (k := k) D cutoff) ⥤ OldCategory D Sc cutoff where
  obj _ := ⟨[]⟩
  map f := emptyCoefficientEncoder D Sc cutoff (SuperalgebraCat.toElem f)
  map_id _ := rfl
  map_comp f g := (coefficientEndomorphism_comp D Sc cutoff []
    (SuperalgebraCat.toElem f) (SuperalgebraCat.toElem g)).symm

instance emptyCoefficientEmbedding_additive :
    (emptyCoefficientEmbedding (k := k) D Sc cutoff).Additive where
  map_add := (emptyCoefficientEncoder D Sc cutoff).map_add _ _

instance emptyCoefficientEmbedding_linear :
    (emptyCoefficientEmbedding (k := k) D Sc cutoff).Linear k where
  map_smul f r := (emptyCoefficientEncoder D Sc cutoff).map_smul r (SuperalgebraCat.toElem f)

instance emptyCoefficientEmbedding_super :
    IsSuperfunctor k (emptyCoefficientEmbedding (k := k) D Sc cutoff) where
  map_mem hf := coefficientEndomorphism_mem D Sc cutoff [] hf

instance emptyCoefficientEmbedding_full : (emptyCoefficientEmbedding (k := k) D Sc cutoff).Full where
  map_surjective f := (emptyCoefficientEquiv D Sc cutoff).surjective f

instance emptyCoefficientEmbedding_faithful : (emptyCoefficientEmbedding (k := k) D Sc cutoff).Faithful where
  map_injective h := (emptyCoefficientEquiv D Sc cutoff).injective h

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # Modules annihilated by the even coefficient power ideal

The literal power-annihilated module subcategory in
`SwappedNondegeneracy.md`, §2, and the E/F restrictions used in
`DeformedReservoirBound.md`, §§1–2. The defining two-sided ideal is not
replaced by a weighted coefficient ideal.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The full coefficient action on an old module component, as a linear
map in the coefficient. Its multiplication order remains explicit. -/
def coefficientAction (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (v : List I) : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff →ₗ[k]
      (M.obj ⟨v⟩ →ₗ[k] M.obj ⟨v⟩) :=
  (M.toFunctor.mapLinearMap k).comp
    ((ideal D Sc cutoff v v).mkQ.comp (ELVPScalar.scalar D Sc cutoff v))

/-- All coefficients acting by zero on every component form a two-sided
ideal; both sides use the proved coefficient-composition order. -/
def coefficientAnnihilator (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :
    TwoSidedIdeal (SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :=
  TwoSidedIdeal.mk' {a | KillsCoefficient D Sc cutoff M a}
    (by intro v; exact map_zero (coefficientAction D Sc cutoff M v))
    (by
      intro a b ha hb v
      change coefficientAction D Sc cutoff M v (a + b) = 0
      rw [map_add, show coefficientAction D Sc cutoff M v a = 0 from ha v,
        show coefficientAction D Sc cutoff M v b = 0 from hb v, add_zero])
    (by
      intro a ha v
      change coefficientAction D Sc cutoff M v (-a) = 0
      rw [map_neg, show coefficientAction D Sc cutoff M v a = 0 from ha v, neg_zero])
    (by
      intro a b hb v
      rw [← coefficientEndomorphism_comp D Sc cutoff v b a]
      change M.toFunctor.map ((coefficientEndomorphism D Sc cutoff v b :
        (⟨v⟩ : OldCategory D Sc cutoff) ⟶ ⟨v⟩) ≫
          coefficientEndomorphism D Sc cutoff v a) = 0
      have hz : M.toFunctor.map (X := ⟨v⟩) (Y := ⟨v⟩)
          (coefficientEndomorphism D Sc cutoff v b) = 0 := hb v
      rw [Functor.map_comp, hz, Limits.zero_comp])
    (by
      intro a b ha v
      rw [← coefficientEndomorphism_comp D Sc cutoff v b a]
      change M.toFunctor.map ((coefficientEndomorphism D Sc cutoff v b :
        (⟨v⟩ : OldCategory D Sc cutoff) ⟶ ⟨v⟩) ≫
          coefficientEndomorphism D Sc cutoff v a) = 0
      have hz : M.toFunctor.map (X := ⟨v⟩) (Y := ⟨v⟩)
          (coefficientEndomorphism D Sc cutoff v a) = 0 := ha v
      rw [Functor.map_comp, hz, Limits.comp_zero])

@[simp] theorem mem_coefficientAnnihilator
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
    a ∈ coefficientAnnihilator D Sc cutoff M ↔ KillsCoefficient D Sc cutoff M a := by
  exact TwoSidedIdeal.mem_mk' _ _ _ _ _ _ a

variable {J : Type u}
  (c : J → SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) (L : J → ℕ)

/-- The paper's literal two-sided ideal generated by the chosen even
coefficient powers. Evenness is required for preservation, not definition. -/
def coefficientPowerIdeal : TwoSidedIdeal (SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :=
  TwoSidedIdeal.span (Set.range fun j => c j ^ L j)

/-- The exact ideal-annihilated object property, not only a weighted
annihilator or a condition on a selected vacuum vector. -/
def coefficientPowerProperty : ObjectProperty
    (Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :=
  fun M => coefficientPowerIdeal D cutoff c L ≤ coefficientAnnihilator D Sc cutoff M

/-- Annihilating the generators is equivalent to annihilating every
element of the full two-sided power ideal. -/
theorem coefficientPowerProperty_iff
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :
    coefficientPowerProperty D Sc cutoff c L M ↔
      ∀ j, KillsCoefficient D Sc cutoff M (c j ^ L j) := by
  rw [coefficientPowerProperty, coefficientPowerIdeal, TwoSidedIdeal.span_le]
  constructor
  · intro h j
    exact (mem_coefficientAnnihilator D Sc cutoff M _).mp (h (Set.mem_range_self j))
  · rintro h _ ⟨j, rfl⟩
    exact (mem_coefficientAnnihilator D Sc cutoff M _).mpr (h j)

/-- The full supermodule subcategory annihilated by the paper's ideal T. -/
abbrev CoefficientPowerModules := (coefficientPowerProperty D Sc cutoff c L).FullSubcategory

variable (hc : ∀ j, c j ∈ SKM.SYM.elvCoefficientParity D cutoff 0)

include hc in
theorem coefficientPowerProperty_induction (i : I)
    (M : CoefficientPowerModules D Sc cutoff c L) :
    coefficientPowerProperty D Sc cutoff c L
      ((BalancedInduction.induction (CyclotomicCrossingTensor.append D Sc cutoff i)).obj M.obj) := by
  apply (coefficientPowerProperty_iff D Sc cutoff c L _).mpr
  intro j
  exact induced_killsEvenPower D Sc cutoff i M.obj (hc j) (L j)
    ((coefficientPowerProperty_iff D Sc cutoff c L M.obj).mp M.property j)

theorem coefficientPowerProperty_restriction (i : I)
    (M : CoefficientPowerModules D Sc cutoff c L) :
    coefficientPowerProperty D Sc cutoff c L
      ((BalancedInduction.restriction (CyclotomicCrossingTensor.append D Sc cutoff i)).obj M.obj) := by
  apply (coefficientPowerProperty_iff D Sc cutoff c L _).mpr
  intro j
  exact restriction_killsCoefficient D Sc cutoff i M.obj _
    ((coefficientPowerProperty_iff D Sc cutoff c L M.obj).mp M.property j)

namespace CoefficientPowerModules

/-- The actual old E restricted to the literal power-annihilated objects,
using the existing full-supercategory restriction. -/
def induction (i : I) : Superfunctor k
    (CoefficientPowerModules D Sc cutoff c L) (CoefficientPowerModules D Sc cutoff c L) :=
  CyclotomicAction.fullLiftSuperfunctor
    (coefficientPowerProperty D Sc cutoff c L) (coefficientPowerProperty D Sc cutoff c L)
    ⟨BalancedInduction.induction (CyclotomicCrossingTensor.append D Sc cutoff i)⟩
    (fun M hM => coefficientPowerProperty_induction D Sc cutoff c L hc i ⟨M, hM⟩)

/-- The actual old F restricted to the same full supercategory. -/
def restriction (i : I) : Superfunctor k
    (CoefficientPowerModules D Sc cutoff c L) (CoefficientPowerModules D Sc cutoff c L) :=
  CyclotomicAction.fullLiftSuperfunctor
    (coefficientPowerProperty D Sc cutoff c L) (coefficientPowerProperty D Sc cutoff c L)
    ⟨BalancedInduction.restriction (CyclotomicCrossingTensor.append D Sc cutoff i)⟩
    (fun M hM => coefficientPowerProperty_restriction D Sc cutoff c L i ⟨M, hM⟩)

/-- All old-module maps between power-annihilated objects, of either
parity, remain literal morphisms of the full subcategory. -/
def restrictMap (M N : CoefficientPowerModules D Sc cutoff c L) (f : M.obj ⟶ N.obj) :
    M ⟶ N := ⟨f⟩

/-- Both maps of a chosen old-module isomorphism restrict together, with
their exact inverse products. -/
def restrictIso (M N : CoefficientPowerModules D Sc cutoff c L) (e : M.obj ≅ N.obj) :
    M ≅ N := (coefficientPowerProperty D Sc cutoff c L).isoMk e

@[simp] theorem restrictIso_hom (M N : CoefficientPowerModules D Sc cutoff c L)
    (e : M.obj ≅ N.obj) : (restrictIso D Sc cutoff c L M N e).hom.hom = e.hom := rfl

@[simp] theorem restrictIso_inv (M N : CoefficientPowerModules D Sc cutoff c L)
    (e : M.obj ≅ N.obj) : (restrictIso D Sc cutoff c L M N e).inv.hom = e.inv := rfl

/-- The chosen ordinary old induction/restriction adjunction restricts
with exactly its existing unit and counit components. -/
def adjunction (i : I) :
    (induction D Sc cutoff c L hc i).toFunctor ⊣ (restriction D Sc cutoff c L i).toFunctor where
  unit := {
    app M := ⟨(BalancedInduction.adjunction (CyclotomicCrossingTensor.append D Sc cutoff i)).unit.app M.obj⟩
    naturality := by
      intro M N f
      exact InducedCategory.hom_ext
        ((BalancedInduction.adjunction (CyclotomicCrossingTensor.append D Sc cutoff i)).unit.naturality f.hom) }
  counit := {
    app M := ⟨(BalancedInduction.adjunction (CyclotomicCrossingTensor.append D Sc cutoff i)).counit.app M.obj⟩
    naturality := by
      intro M N f
      exact InducedCategory.hom_ext
        ((BalancedInduction.adjunction (CyclotomicCrossingTensor.append D Sc cutoff i)).counit.naturality f.hom) }
  left_triangle_components M := InducedCategory.hom_ext
    ((BalancedInduction.adjunction (CyclotomicCrossingTensor.append D Sc cutoff i)).left_triangle_components M.obj)
  right_triangle_components M := InducedCategory.hom_ext
    ((BalancedInduction.adjunction (CyclotomicCrossingTensor.append D Sc cutoff i)).right_triangle_components M.obj)

@[simp] theorem adjunction_unit_hom (i : I) (M : CoefficientPowerModules D Sc cutoff c L) :
    ((adjunction D Sc cutoff c L hc i).unit.app M).hom =
      (BalancedInduction.adjunction (CyclotomicCrossingTensor.append D Sc cutoff i)).unit.app M.obj := rfl

@[simp] theorem adjunction_counit_hom (i : I) (M : CoefficientPowerModules D Sc cutoff c L) :
    ((adjunction D Sc cutoff c L hc i).counit.app M).hom =
      (BalancedInduction.adjunction (CyclotomicCrossingTensor.append D Sc cutoff i)).counit.app M.obj := rfl

/-- The chosen induction dot restricts as the same supernatural
transformation, including its original parity. -/
def inductionDot (i : I) : SuperNatTrans k
    (induction D Sc cutoff c L hc i).toFunctor (induction D Sc cutoff c L hc i).toFunctor :=
  CyclotomicAction.fullLiftTrans
    (coefficientPowerProperty D Sc cutoff c L) (coefficientPowerProperty D Sc cutoff c L)
    (fun M hM => coefficientPowerProperty_induction D Sc cutoff c L hc i ⟨M, hM⟩)
    (fun M hM => coefficientPowerProperty_induction D Sc cutoff c L hc i ⟨M, hM⟩)
    (BalancedInduction.transform (CyclotomicCrossingTensor.oldAppendDot_supernatural D Sc cutoff i))

@[simp] theorem inductionDot_app_hom (i : I) (p : ZMod 2)
    (M : CoefficientPowerModules D Sc cutoff c L) :
    ((inductionDot D Sc cutoff c L hc i).app p M).hom =
      (BalancedInduction.transform
        (CyclotomicCrossingTensor.oldAppendDot_supernatural D Sc cutoff i)).app p M.obj := rfl

end CoefficientPowerModules

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # Comparing power-annihilated and weighted coefficient modules

The quotient sandwich in `SwappedNondegeneracy.md`, §2 and
`DeformedReservoirBound.md`, §§1–2 gives contravariant module restriction
functors. The ideal containments remain explicit inputs; the weighted and
power quotients are not identified, and no evaluation kernel is assumed.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The coefficient-weight ideal in the actual full ELV coefficient
algebra, generated by the same monomials as `coefficientHomIdeal`. -/
def coefficientWeightedIdeal (N : ℕ) :
    TwoSidedIdeal (SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :=
  TwoSidedIdeal.span {b | ∃ a : SKM.SYM.CoefficientIndex D,
    N ≤ SKM.SYM.coefficientWeight D a ∧
      SKM.SYM.elvCoefficientQuotient D cutoff (SKM.SYM.coefficientBasis D k a) = b}

/-- Annihilating this coefficient ideal is exactly the existing literal
weighted-annihilation condition used for truncated-category descent. -/
theorem coefficientWeightedIdeal_le_annihilator_iff (N : ℕ)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :
    coefficientWeightedIdeal D cutoff N ≤ coefficientAnnihilator D Sc cutoff M ↔
      KillsWeightedCoefficients D Sc cutoff N M := by
  rw [coefficientWeightedIdeal, TwoSidedIdeal.span_le]
  constructor
  · intro h v a ha
    exact ((mem_coefficientAnnihilator D Sc cutoff M _).mp (h ⟨a, ha, rfl⟩)) v
  · rintro h _ ⟨a, ha, rfl⟩
    apply (mem_coefficientAnnihilator D Sc cutoff M _).mpr
    exact fun v => h v a ha

variable {J : Type u}
  (c : J → SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) (L : J → ℕ)

/-- If T is contained in a weighted ideal, every actual weighted module
pulls back to a power-annihilated old module. -/
def weightedToPower (N : ℕ)
    (hT : coefficientPowerIdeal D cutoff c L ≤ coefficientWeightedIdeal D cutoff N) :
    Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k) ⥤
      CoefficientPowerModules D Sc cutoff c L :=
  (coefficientPowerProperty D Sc cutoff c L).lift
    (BalancedInduction.restriction (oldTruncateFunctor D Sc cutoff N))
    (fun M => hT.trans
      ((coefficientWeightedIdeal_le_annihilator_iff D Sc cutoff N
        (weightedRestriction D Sc cutoff N M)).mpr
          (weightedRestriction_kills D Sc cutoff N M)))

/-- If a weighted ideal is contained in T, every power-annihilated old
module descends to the literal weighted category on unchanged carriers. -/
def powerToWeighted (N : ℕ)
    (hW : coefficientWeightedIdeal D cutoff N ≤ coefficientPowerIdeal D cutoff c L) :
    CoefficientPowerModules D Sc cutoff c L ⥤
      Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k) where
  obj M := weightedModule D Sc cutoff N M.obj
    ((coefficientWeightedIdeal_le_annihilator_iff D Sc cutoff N M.obj).mp
      (hW.trans M.property))
  map {M N'} f := weightedModuleHom D Sc cutoff N M.obj N'.obj _ _ f.hom
  map_id M := weightedModuleHom_id D Sc cutoff N M.obj _
  map_comp f g := weightedModuleHom_comp D Sc cutoff N _ _ _ _ _ _ f.hom g.hom

instance weightedToPower_additive (N : ℕ)
    (hT : coefficientPowerIdeal D cutoff c L ≤ coefficientWeightedIdeal D cutoff N) :
    (weightedToPower D Sc cutoff c L N hT).Additive := by
  unfold weightedToPower
  infer_instance

instance weightedToPower_linear (N : ℕ)
    (hT : coefficientPowerIdeal D cutoff c L ≤ coefficientWeightedIdeal D cutoff N) :
    (weightedToPower D Sc cutoff c L N hT).Linear k where
  map_smul f r := InducedCategory.hom_ext
    ((BalancedInduction.restriction (oldTruncateFunctor D Sc cutoff N)).map_smul r f)

instance weightedToPower_super (N : ℕ)
    (hT : coefficientPowerIdeal D cutoff c L ≤ coefficientWeightedIdeal D cutoff N) :
    IsSuperfunctor k (weightedToPower D Sc cutoff c L N hT) where
  map_mem hf := IsSuperfunctor.map_mem
    (F := BalancedInduction.restriction (oldTruncateFunctor D Sc cutoff N)) hf

instance powerToWeighted_additive (N : ℕ)
    (hW : coefficientWeightedIdeal D cutoff N ≤ coefficientPowerIdeal D cutoff c L) :
    (powerToWeighted D Sc cutoff c L N hW).Additive where
  map_add := by
    intro M N' f g
    apply Superfunctor.hom_ext
    intro p v
    rfl

instance powerToWeighted_linear (N : ℕ)
    (hW : coefficientWeightedIdeal D cutoff N ≤ coefficientPowerIdeal D cutoff c L) :
    (powerToWeighted D Sc cutoff c L N hW).Linear k where
  map_smul f r := by
    apply Superfunctor.hom_ext
    intro p v
    rfl

instance powerToWeighted_super (N : ℕ)
    (hW : coefficientWeightedIdeal D cutoff N ≤ coefficientPowerIdeal D cutoff c L) :
    IsSuperfunctor k (powerToWeighted D Sc cutoff c L N hW) where
  map_mem := by
    intro M N' p f hf
    have h : f.hom ∈ parity (R := k) M.obj N'.obj p := hf
    rw [Superfunctor.mem_parity_iff] at h ⊢
    funext v
    exact congrFun h ⟨v.word⟩

@[simp] theorem weightedToPower_obj_carrier (N : ℕ)
    (hT : coefficientPowerIdeal D cutoff c L ≤ coefficientWeightedIdeal D cutoff N)
    (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))
    (v : List I) :
    ((weightedToPower D Sc cutoff c L N hT).obj M).obj.obj ⟨v⟩ = M.obj ⟨v⟩ := rfl

@[simp] theorem powerToWeighted_obj_carrier (N : ℕ)
    (hW : coefficientWeightedIdeal D cutoff N ≤ coefficientPowerIdeal D cutoff c L)
    (M : CoefficientPowerModules D Sc cutoff c L) (v : List I) :
    ((powerToWeighted D Sc cutoff c L N hW).obj M).obj ⟨v⟩ = M.obj.obj ⟨v⟩ := rfl

@[simp] theorem weightedToPower_map_app (N : ℕ)
    (hT : coefficientPowerIdeal D cutoff c L ≤ coefficientWeightedIdeal D cutoff N)
    (M N' : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k)) (f : M ⟶ N')
    (p : ZMod 2) (v : List I) :
    (((weightedToPower D Sc cutoff c L N hT).map f).hom).app p ⟨v⟩ =
      f.app p ⟨v⟩ := rfl

@[simp] theorem powerToWeighted_map_app (N : ℕ)
    (hW : coefficientWeightedIdeal D cutoff N ≤ coefficientPowerIdeal D cutoff c L)
    (M N' : CoefficientPowerModules D Sc cutoff c L) (f : M ⟶ N') (p : ZMod 2)
    (v : List I) :
    ((powerToWeighted D Sc cutoff c L N hW).map f).app p ⟨v⟩ = f.hom.app p ⟨v⟩ := rfl

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # The power/weight sandwich in the actual ELV coefficient algebra

The universal bounds from `ELVCoefficientPowers` descend through the actual
ELV coefficient quotient to the literal module comparison functors of
`SwappedNondegeneracy.md`, §2. No weighted/power quotient equality or
vacuum evaluation-kernel identification is asserted.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The paper's even elementary generators in the actual full ELV
coefficient quotient. The higher killed generators cause no change. -/
def elementaryCoefficients (a : I × ℕ) :
    SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff :=
  SKM.SYM.elvCoefficientQuotient D cutoff (SKM.SYM.e D k a.1 a.2)

theorem elementaryCoefficients_even (a : I × ℕ) :
    elementaryCoefficients (k := k) D cutoff a ∈ SKM.SYM.elvCoefficientParity D cutoff 0 := by
  have h := SKM.SYM.elvModelQuotient_mem D (cutoff := cutoff)
    (SKM.SYM.polynomialExterior_e_mem_even D (k := k) a.1 a.2)
  simpa only [elementaryCoefficients, SKM.SYM.elvModelQuotient, AlgHom.comp_apply,
    AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply] using h

variable [Fintype I]

/-- The upper finite power bound descends to the actual ELV coefficient
algebra by killing its defining ideal and taking literal power images. -/
theorem weighted_le_elementaryPowerIdeal (L : I × ℕ → ℕ) :
    coefficientWeightedIdeal (k := k) D cutoff
      (SKM.SYM.elvPowerWeightBound D cutoff L + 1) ≤
        coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L := by
  let T := coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L
  let q := (SKM.SYM.elvCoefficientQuotient (k := k) D cutoff).toRingHom
  have hJ : SKM.SYM.elvCoefficientIdeal D k cutoff ≤ T.comap q := by
    intro a ha
    apply (TwoSidedIdeal.mem_comap q).mpr
    change SKM.SYM.elvCoefficientQuotient D cutoff a ∈ T
    rw [SKM.SYM.elvCoefficientQuotient_eq_zero D ha]
    exact TwoSidedIdeal.zero_mem _
  have hP : SKM.SYM.coefficientPowerIdeal D k L ≤ T.comap q := by
    apply TwoSidedIdeal.span_le.mpr
    rintro _ ⟨a, rfl⟩
    apply (TwoSidedIdeal.mem_comap q).mpr
    change SKM.SYM.elvCoefficientQuotient D cutoff (SKM.SYM.e D k a.1 a.2 ^ L a) ∈ T
    rw [map_pow]
    exact TwoSidedIdeal.subset_span (Set.mem_range_self a)
  apply TwoSidedIdeal.span_le.mpr
  rintro _ ⟨b, hb, rfl⟩
  apply (TwoSidedIdeal.mem_comap q).mp
  exact (sup_le hJ hP) (SKM.SYM.coefficientBasis_mem_elv_sup_power D k cutoff L b (by omega))

/-- The actual power-to-weighted module functor at the explicit finite
upper bound. No algebraic ideal-containment hypothesis remains. -/
def elementaryPowerToWeighted (L : I × ℕ → ℕ) :=
  powerToWeighted D Sc cutoff (elementaryCoefficients (k := k) D cutoff) L
    (SKM.SYM.elvPowerWeightBound D cutoff L + 1)
    (weighted_le_elementaryPowerIdeal D cutoff L)

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # The literal ELV coefficient power quotient

The coefficient instance of (BC) in `DeformedReservoirBound.md`, §2:
quotienting the actual ELV coefficient algebra by the literal elementary
power ideal agrees with the universal quotient by the sum of its two
defining ideals. All maps are induced by the original coefficient maps.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (cutoff : I → ℕ) (L : I × ℕ → ℕ)

abbrev CoefficientPowerQuotient :=
  (coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L).ringCon.Quotient

abbrev UniversalCoefficientPowerQuotient :=
  (SKM.SYM.elvCoefficientIdeal D k cutoff ⊔ SKM.SYM.coefficientPowerIdeal D k L).ringCon.Quotient

private theorem kernel_mem {A B : Type u} [Ring A] [Ring B] [Algebra k A] [Algebra k B]
    (f : A →ₐ[k] B) (a : A) :
    a ∈ TwoSidedIdeal.ofRingCon (RingCon.ker f.toRingHom) ↔ f a = 0 := by
  change f a = f 0 ↔ _
  rw [map_zero]

/-- The universal coefficient map into the actual quotient A/T. -/
def coefficientPowerQuotientMap : SKM.SYM D k →ₐ[k] CoefficientPowerQuotient (k := k) D cutoff L :=
  ((coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L).ringCon.mkₐ k).comp
    (SKM.SYM.elvCoefficientQuotient D cutoff)

private theorem universalPower_le_kernel :
    SKM.SYM.elvCoefficientIdeal D k cutoff ⊔ SKM.SYM.coefficientPowerIdeal D k L ≤
      TwoSidedIdeal.ofRingCon (RingCon.ker (coefficientPowerQuotientMap (k := k) D cutoff L).toRingHom) := by
  apply sup_le
  · intro a ha
    apply (kernel_mem _ _).mpr
    change (coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L).ringCon.mkₐ k
      (SKM.SYM.elvCoefficientQuotient D cutoff a) = 0
    rw [SKM.SYM.elvCoefficientQuotient_eq_zero D ha, map_zero]
  · apply TwoSidedIdeal.span_le.mpr
    rintro _ ⟨a, rfl⟩
    apply (kernel_mem _ _).mpr
    change (coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L).ringCon.mkₐ k
      (SKM.SYM.elvCoefficientQuotient D cutoff (SKM.SYM.e D k a.1 a.2 ^ L a)) = 0
    rw [map_pow]
    exact Quotient.sound (TwoSidedIdeal.subset_span (Set.mem_range_self a))

/-- The prescribed universal quotient maps to the literal actual quotient. -/
def universalToCoefficientPower : UniversalCoefficientPowerQuotient (k := k) D cutoff L →ₐ[k]
    CoefficientPowerQuotient (k := k) D cutoff L :=
  RingCon.liftₐ _ (coefficientPowerQuotientMap D cutoff L)
    (TwoSidedIdeal.ringCon_le_iff.mp (universalPower_le_kernel D cutoff L))

private def elvToUniversalPower : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff →ₐ[k]
    UniversalCoefficientPowerQuotient (k := k) D cutoff L :=
  RingCon.liftₐ _
    ((SKM.SYM.elvCoefficientIdeal D k cutoff ⊔ SKM.SYM.coefficientPowerIdeal D k L).ringCon.mkₐ k)
    (fun _ _ h => Quotient.sound
      ((show (SKM.SYM.elvCoefficientIdeal D k cutoff).ringCon ≤
        (SKM.SYM.elvCoefficientIdeal D k cutoff ⊔ SKM.SYM.coefficientPowerIdeal D k L).ringCon from
          TwoSidedIdeal.ringCon_le_iff.mp le_sup_left) h))

private theorem power_le_kernel :
    coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L ≤
      TwoSidedIdeal.ofRingCon (RingCon.ker (elvToUniversalPower (k := k) D cutoff L).toRingHom) := by
  apply TwoSidedIdeal.span_le.mpr
  rintro _ ⟨a, rfl⟩
  apply (kernel_mem _ _).mpr
  change elvToUniversalPower D cutoff L
    ((SKM.SYM.elvCoefficientQuotient D cutoff (SKM.SYM.e D k a.1 a.2)) ^ L a) = 0
  rw [← map_pow]
  change (SKM.SYM.elvCoefficientIdeal D k cutoff ⊔ SKM.SYM.coefficientPowerIdeal D k L).ringCon.mkₐ k
    (SKM.SYM.e D k a.1 a.2 ^ L a) = 0
  exact Quotient.sound ((le_sup_right : SKM.SYM.coefficientPowerIdeal D k L ≤
    SKM.SYM.elvCoefficientIdeal D k cutoff ⊔ SKM.SYM.coefficientPowerIdeal D k L)
      (TwoSidedIdeal.subset_span ⟨a, rfl⟩))

/-- The actual quotient A/T maps to the universal quotient, on the same
coefficient generators. -/
def coefficientPowerToUniversal : CoefficientPowerQuotient (k := k) D cutoff L →ₐ[k]
    UniversalCoefficientPowerQuotient (k := k) D cutoff L :=
  RingCon.liftₐ _ (elvToUniversalPower D cutoff L)
    (TwoSidedIdeal.ringCon_le_iff.mp (power_le_kernel D cutoff L))

@[simp] theorem universalToCoefficientPower_apply (a : SKM.SYM D k) :
    universalToCoefficientPower D cutoff L
      ((SKM.SYM.elvCoefficientIdeal D k cutoff ⊔ SKM.SYM.coefficientPowerIdeal D k L).ringCon.mkₐ k a) =
      coefficientPowerQuotientMap D cutoff L a := rfl

@[simp] theorem coefficientPowerToUniversal_apply (a : SKM.SYM D k) :
    coefficientPowerToUniversal D cutoff L (coefficientPowerQuotientMap D cutoff L a) =
      (SKM.SYM.elvCoefficientIdeal D k cutoff ⊔ SKM.SYM.coefficientPowerIdeal D k L).ringCon.mkₐ k a := rfl

private theorem actual_roundtrip :
    (universalToCoefficientPower (k := k) D cutoff L).comp (coefficientPowerToUniversal D cutoff L) =
      AlgHom.id k (CoefficientPowerQuotient (k := k) D cutoff L) := by
  apply AlgHom.ext
  intro x
  obtain ⟨a, rfl⟩ := RingCon.mkₐ_surjective (α := k)
    (coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L).ringCon x
  obtain ⟨b, rfl⟩ := RingCon.mkₐ_surjective (α := k) (SKM.SYM.elvCoefficientIdeal D k cutoff).ringCon a
  rfl

private theorem universal_roundtrip :
    (coefficientPowerToUniversal (k := k) D cutoff L).comp (universalToCoefficientPower D cutoff L) =
      AlgHom.id k (UniversalCoefficientPowerQuotient (k := k) D cutoff L) := by
  apply AlgHom.ext
  intro x
  obtain ⟨a, rfl⟩ := RingCon.mkₐ_surjective (α := k)
    (SKM.SYM.elvCoefficientIdeal D k cutoff ⊔ SKM.SYM.coefficientPowerIdeal D k L).ringCon x
  rfl

/-- The coefficient instance of (BC): the literal actual power quotient
is algebra-isomorphic to the universal quotient by J plus the powers. -/
def coefficientPowerQuotientEquiv : CoefficientPowerQuotient (k := k) D cutoff L ≃ₐ[k]
    UniversalCoefficientPowerQuotient (k := k) D cutoff L :=
  AlgEquiv.ofAlgHom (coefficientPowerToUniversal D cutoff L) (universalToCoefficientPower D cutoff L)
    (universal_roundtrip D cutoff L) (actual_roundtrip D cutoff L)

/-- The coefficient-algebra presentation kernel is exactly the sum of
the defining ELV ideal and elementary powers. This is not a statement
about the kernel of a vacuum action or diagram evaluation. -/
theorem coefficientPowerQuotientMap_eq_zero_iff (a : SKM.SYM D k) :
    coefficientPowerQuotientMap D cutoff L a = 0 ↔
      a ∈ SKM.SYM.elvCoefficientIdeal D k cutoff ⊔ SKM.SYM.coefficientPowerIdeal D k L := by
  constructor
  · intro h
    have hz := congrArg (coefficientPowerToUniversal D cutoff L) h
    rw [coefficientPowerToUniversal_apply, map_zero] at hz
    exact Quotient.exact hz
  · intro ha
    apply (coefficientPowerQuotientEquiv D cutoff L).injective
    exact (show (SKM.SYM.elvCoefficientIdeal D k cutoff ⊔
      SKM.SYM.coefficientPowerIdeal D k L).ringCon.mkₐ k a = 0 from Quotient.sound ha).trans
        (map_zero (coefficientPowerQuotientEquiv (k := k) D cutoff L)).symm

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # Parity on the literal coefficient power quotient

The parity part of the bigraded coefficient quotient in
`DeformedReservoirBound.md`, §§1–2. The actual ideal is generated by even
elementary powers, so its quotient retains the full exterior parity.
This file does not infer positive-dot nilpotence from finite dimension.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (cutoff : I → ℕ) (L : I × ℕ → ℕ)

private theorem powerIdeal_projection
    {a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff}
    (ha : a ∈ coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L)
    (p : ZMod 2) :
    GradedAlgebra.proj (SKM.SYM.elvCoefficientParity D cutoff) p a ∈
      coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L := by
  apply ELVQuotient.homogeneousIdeal_projection_mem
    (SKM.SYM.elvCoefficientParity D cutoff) (Set.range fun j =>
      elementaryCoefficients (k := k) D cutoff j ^ L j) _ ha p
  rintro _ ⟨j, rfl⟩
  refine ⟨0, ?_⟩
  simpa only [nsmul_zero] using
    SetLike.pow_mem_graded (L j) (elementaryCoefficients_even (k := k) D cutoff j)

private theorem powerQuotient_kernel_projection
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff)
    (ha : (coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L).ringCon.mkₐ k a = 0)
    (p : ZMod 2) :
    (coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L).ringCon.mkₐ k
      (GradedAlgebra.proj (SKM.SYM.elvCoefficientParity D cutoff) p a) = 0 :=
  Quotient.sound (powerIdeal_projection D cutoff L (Quotient.exact ha) p)

/-- The parity superspace on the literal actual A/T, on its unchanged
quotient carrier. No exterior generator is omitted or specialized. -/
abbrev coefficientPowerSpace : SVec k :=
  ELVQuotient.gradedQuotientSpace (SKM.SYM.elvCoefficientParity D cutoff)
    ((coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L).ringCon.mkₐ k)
    (RingCon.mkₐ_surjective (α := k) _)
    (powerQuotient_kernel_projection D cutoff L)

/-- The induced parity grading on the actual coefficient power quotient. -/
abbrev coefficientPowerParity : ZMod 2 → Submodule k (CoefficientPowerQuotient (k := k) D cutoff L) :=
  (coefficientPowerSpace (k := k) D cutoff L).part

instance coefficientPowerGradedAlgebra : GradedAlgebra (coefficientPowerParity (k := k) D cutoff L) :=
  ELVQuotient.gradedQuotientAlgebra (SKM.SYM.elvCoefficientParity D cutoff)
    ((coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L).ringCon.mkₐ k)
    (RingCon.mkₐ_surjective (α := k) _)
    (powerQuotient_kernel_projection D cutoff L)

/-- The actual quotient map preserves every homogeneous coefficient. -/
theorem coefficientPowerQuotient_mem {p : ZMod 2}
    {a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff}
    (ha : a ∈ SKM.SYM.elvCoefficientParity D cutoff p) :
    (coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L).ringCon.mkₐ k a ∈
      coefficientPowerParity (k := k) D cutoff L p :=
  ELVQuotient.gradedQuotientSpace_mem _ _ _ _ ha

/-- The projection on the power quotient is induced by the original
full-coefficient parity projection. -/
theorem coefficientPowerSpace_projection (p : ZMod 2)
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
    (coefficientPowerSpace (k := k) D cutoff L).proj p
      ((coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L).ringCon.mkₐ k a) =
    (coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L).ringCon.mkₐ k
      (GradedAlgebra.proj (SKM.SYM.elvCoefficientParity D cutoff) p a) :=
  ELVQuotient.gradedQuotientSpace_projection _ _ _ _ p a

/-- The regular left A-action on the literal power quotient, as a
functor from the original full coefficient supercategory. -/
def coefficientPowerRegularFunctor :
    SuperalgebraCat (SKM.SYM.elvCoefficientParity (k := k) D cutoff) ⥤ SVec k where
  obj _ := coefficientPowerSpace D cutoff L
  map f := {
    toFun := fun x => (coefficientPowerIdeal D cutoff
      (elementaryCoefficients (k := k) D cutoff) L).ringCon.mkₐ k (SuperalgebraCat.toElem f) * x
    map_add' := fun x y => mul_add _ x y
    map_smul' := fun r x => mul_smul_comm r _ x }
  map_id _ := by
    apply LinearMap.ext
    intro x
    change (coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L).ringCon.mkₐ k 1 * x = x
    rw [map_one, one_mul]
  map_comp f g := by
    apply LinearMap.ext
    intro x
    change (coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L).ringCon.mkₐ k
        (SuperalgebraCat.toElem g * SuperalgebraCat.toElem f) * x =
      ((coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L).ringCon.mkₐ k
        (SuperalgebraCat.toElem g)) *
      (((coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L).ringCon.mkₐ k
        (SuperalgebraCat.toElem f)) * x)
    rw [map_mul, mul_assoc]

instance coefficientPowerRegularFunctor_additive :
    (coefficientPowerRegularFunctor (k := k) D cutoff L).Additive where
  map_add := by
    intro v w f g
    apply LinearMap.ext
    intro x
    change CoefficientPowerQuotient (k := k) D cutoff L at x
    change (coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L).ringCon.mkₐ k
      (SuperalgebraCat.toElem f + SuperalgebraCat.toElem g) * x = _
    rw [map_add, add_mul]
    rfl

instance coefficientPowerRegularFunctor_linear :
    (coefficientPowerRegularFunctor (k := k) D cutoff L).Linear k where
  map_smul f r := by
    apply LinearMap.ext
    intro x
    change CoefficientPowerQuotient (k := k) D cutoff L at x
    change (coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L).ringCon.mkₐ k
      (r • SuperalgebraCat.toElem f) * x = _
    rw [map_smul, smul_mul_assoc]
    rfl

instance coefficientPowerRegularFunctor_super :
    IsSuperfunctor k (coefficientPowerRegularFunctor (k := k) D cutoff L) where
  map_mem := by
    intro v w p f hf
    apply SVec.mem_parityHom_of_apply_mem
    intro q x hx
    change CoefficientPowerQuotient (k := k) D cutoff L at x
    change x ∈ coefficientPowerParity (k := k) D cutoff L q at hx
    change (coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L).ringCon.mkₐ k
      (SuperalgebraCat.toElem f) * x ∈ coefficientPowerParity (k := k) D cutoff L (q + p)
    have hf' : SuperalgebraCat.toElem f ∈ SKM.SYM.elvCoefficientParity D cutoff p := hf
    have h := SetLike.mul_mem_graded (coefficientPowerQuotient_mem D cutoff L hf') hx
    simpa only [add_comm] using h

/-- The parity-graded regular coefficient quotient module used for the
power reservoir vacuum. Its old-word extension remains a separate map. -/
def coefficientPowerRegular : Superfunctor k
    (SuperalgebraCat (SKM.SYM.elvCoefficientParity (k := k) D cutoff)) (SVec k) :=
  ⟨coefficientPowerRegularFunctor D cutoff L⟩

@[simp] theorem coefficientPowerRegular_apply
    (v w : SuperalgebraCat (SKM.SYM.elvCoefficientParity (k := k) D cutoff)) (f : v ⟶ w)
    (x : CoefficientPowerQuotient (k := k) D cutoff L) :
    (coefficientPowerRegular D cutoff L).map f x =
      (coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L).ringCon.mkₐ k
        (SuperalgebraCat.toElem f) * x := rfl

/-- Every element of the entire defining power ideal acts by zero on
the regular coefficient quotient, on all vectors. -/
theorem coefficientPowerRegular_kills
    {a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff}
    (ha : a ∈ coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L)
    (x : CoefficientPowerQuotient (k := k) D cutoff L) :
    (coefficientPowerRegular D cutoff L).map
      (SuperalgebraCat.ofElem a : SuperalgebraCat.star _ ⟶ SuperalgebraCat.star _) x = 0 := by
  rw [coefficientPowerRegular_apply]
  have hz : (coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L).ringCon.mkₐ k a = 0 :=
    Quotient.sound ha
  rw [SuperalgebraCat.toElem_ofElem, hz, zero_mul]

end OddMath.QuiverHecke.ELVOld
end

end
