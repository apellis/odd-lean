/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVEndpointPresheaf
import OddMath.QuiverHecke.CyclotomicAction.ELVPInjective
import OddMath.QuiverHecke.CyclotomicAction.CentralPolynomialRightModule

/-! # Content modules for the ordinary ELV square resolution

The old ring is the finite Hom-matrix ring on words of a fixed content, with
its full ELV coefficients and old cyclotomic ideal. The endpoint modules
retain all enlarged target words and all old source words. The source action
is twisted by total parity; forgetting the grading does not erase this twist.
The central variable is the moving dot or moving square. No commutativity of
the old ring, flatness, or cyclotomic finite-dimensionality is imposed.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory Opposite MonoidalCategory
open scoped Classical TensorProduct
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The finite words of a fixed content, including the empty content. -/
abbrev ContentWords (ν : List I) := {v : List I // v.Perm ν}

instance contentWordsFintype (ν : List I) : Fintype (ContentWords ν) :=
  Fintype.ofFinset ν.permutations.toFinset (by intro v; change v ∈ ν.permutations.toFinset ↔ v.Perm ν; simp)

def contentObject (ν : List I) (v : ContentWords ν) : OldCategory D Sc cutoff := ⟨v.val⟩

/-- The ordinary noncommutative old cyclotomic content ring. -/
abbrev ContentRing (ν : List I) := OddMath.FiniteHomMatrix.Mat (contentObject D Sc cutoff ν)

/-- A fixed ambient row of the twisted prepend module. -/
abbrev SourceRow (p : ZMod 2) (i : I) (ν w : List I) :=
  OddMath.FiniteHomMatrix.RightModule (contentObject D Sc cutoff ν)
    (sourcePresheaf D Sc cutoff p i w)

/-- A fixed ambient row of the append module. -/
abbrev AppendRow (i : I) (ν w : List I) :=
  OddMath.FiniteHomMatrix.RightModule (contentObject D Sc cutoff ν)
    (appendPresheaf D Sc cutoff i w)

theorem sourcePull_central (p : ZMod 2) (i : I) {u v w : List I}
    (c : Old D Sc cutoff u v) (z : Target D Sc cutoff i v w) :
    centralSource D Sc cutoff i u w (sourcePull D Sc cutoff p i u v w c z) =
      sourcePull D Sc cutoff p i u v w c (centralSource D Sc cutoff i v w z) := by
  obtain ⟨c, rfl⟩ := (ideal D Sc cutoff u v).mkQ_surjective c
  obtain ⟨h, rfl⟩ := projection_surjective D Sc cutoff i v w z
  change projection D Sc cutoff i u w (movingPower D Sc cutoff i u _ ≫
    (insert D Sc cutoff i u v (twist k p c) ≫ h)) =
    projection D Sc cutoff i u w (insert D Sc cutoff i u v (twist k p c) ≫
      (movingPower D Sc cutoff i v _ ≫ h))
  rw [← Category.assoc, movingPower_insert D Sc cutoff i _ (centralDegree_even D i), Category.assoc]

theorem appendMovingPower_rightContext_cross (i : I) {u v : List I} (d : ℕ)
    (hd : d • D.parity i = 0) (c : hom D Sc cutoff u v) :
    appendMovingPower D Sc cutoff i u d ≫ rightContext D Sc cutoff [i] u v c =
      rightContext D Sc cutoff [i] u v c ≫ appendMovingPower D Sc cutoff i v d := by
  rw [appendMovingPower_whisker, appendMovingPower_whisker,
    trailing_comp_rightContext D Sc cutoff (v := u) (w := v)
      (hd ▸ firstDot_pow_parity D Sc i [] d)]
  simp only [twist_zero]

theorem appendPull_central (i : I) {u v w : List I}
    (c : Old D Sc cutoff u v) (z : AppendTarget D Sc cutoff i v w) :
    centralAppend D Sc cutoff i u w (appendPull D Sc cutoff i u v w c z) =
      appendPull D Sc cutoff i u v w c (centralAppend D Sc cutoff i v w z) := by
  obtain ⟨c, rfl⟩ := (ideal D Sc cutoff u v).mkQ_surjective c
  obtain ⟨h, rfl⟩ := appendProjection_surjective D Sc cutoff i v w z
  change appendProjection D Sc cutoff i u w (appendMovingPower D Sc cutoff i u _ ≫
    (rightContext D Sc cutoff [i] u v c ≫ h)) =
    appendProjection D Sc cutoff i u w (rightContext D Sc cutoff [i] u v c ≫
      (appendMovingPower D Sc cutoff i v _ ≫ h))
  rw [← Category.assoc,
    appendMovingPower_rightContext_cross D Sc cutoff i _ (centralDegree_even D i), Category.assoc]

/-- Central moving action as a natural transformation of all old quotient arrows. -/
def sourceCentralNat (p : ZMod 2) (i : I) (w : List I) :
    sourcePresheaf D Sc cutoff p i w ⟶ sourcePresheaf D Sc cutoff p i w where
  app v := ModuleCat.ofHom (centralSource D Sc cutoff i v.unop.word w)
  naturality a b f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact sourcePull_central D Sc cutoff p i f.unop z

def appendCentralNat (i : I) (w : List I) :
    appendPresheaf D Sc cutoff i w ⟶ appendPresheaf D Sc cutoff i w where
  app v := ModuleCat.ofHom (centralAppend D Sc cutoff i v.unop.word w)
  naturality a b f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact appendPull_central D Sc cutoff i f.unop z

/-- Moving dot/square on a full content row, linear over the ordinary old ring. -/
def sourceRowCentral (p : ZMod 2) (i : I) (ν w : List I) :
    SourceRow D Sc cutoff p i ν w →ₗ[(ContentRing D Sc cutoff ν)ᵐᵒᵖ]
      SourceRow D Sc cutoff p i ν w :=
  OddMath.FiniteHomMatrix.RightModule.map (contentObject D Sc cutoff ν)
    (sourceCentralNat D Sc cutoff p i w)

def appendRowCentral (i : I) (ν w : List I) :
    AppendRow D Sc cutoff i ν w →ₗ[(ContentRing D Sc cutoff ν)ᵐᵒᵖ]
      AppendRow D Sc cutoff i ν w :=
  OddMath.FiniteHomMatrix.RightModule.map (contentObject D Sc cutoff ν)
    (appendCentralNat D Sc cutoff i w)

theorem content_appendQ (i : I) (ν : List I) (v : ContentWords ν) :
    appendQ D cutoff i v.val = appendQ D cutoff i ν := by
  unfold appendQ wordSumParity
  rw [(v.property.map D.parity).sum_eq]

theorem pMap_sourcePull (i : I) {u v w : List I}
    (c : Old D Sc cutoff u v) (z : Target D Sc cutoff i v w) :
    pMap D Sc cutoff i u w (sourcePull D Sc cutoff (appendQ D cutoff i u) i u v w c z) =
      appendPull D Sc cutoff i u v w c (pMap D Sc cutoff i v w z) := by
  obtain ⟨c, rfl⟩ := (ideal D Sc cutoff u v).mkQ_surjective c
  obtain ⟨h, rfl⟩ := projection_surjective D Sc cutoff i v w z
  have he := appendRelations_comp D Sc cutoff i
    (appendError_mem_appendRelations D Sc cutoff i c) h
  have hz := (appendProjection_eq_zero_iff D Sc cutoff i u w _).mpr he
  rw [appendError_apply, Preadditive.sub_comp, map_sub, sub_eq_zero] at hz
  change appendProjection D Sc cutoff i u w (appendW D Sc cutoff i u ≫
    (insert D Sc cutoff i u v (twist k (appendQ D cutoff i u) c) ≫ h)) =
    appendProjection D Sc cutoff i u w (rightContext D Sc cutoff [i] u v c ≫
      (appendW D Sc cutoff i v ≫ h))
  simpa only [Category.assoc] using hz.symm

/-- P on all columns of a content row is right B-linear with the prescribed epsilon twist. -/
def pRow (i : I) (ν w : List I) :
    SourceRow D Sc cutoff (appendQ D cutoff i ν) i ν w →ₗ[(ContentRing D Sc cutoff ν)ᵐᵒᵖ]
      AppendRow D Sc cutoff i ν w where
  toFun z v := pMap D Sc cutoff i v.val w (z v)
  map_add' z z' := by funext v; exact map_add _ _ _
  map_smul' b z := by
    funext v
    simp only [RingHom.id_apply, OddMath.FiniteHomMatrix.RightModule.smul_apply]
    change pMap D Sc cutoff i v.val w
      (∑ t : ContentWords ν, sourcePull D Sc cutoff (appendQ D cutoff i ν) i v.val t.val w (b.unop (t,v)) (z t)) =
        ∑ t : ContentWords ν, appendPull D Sc cutoff i v.val t.val w (b.unop (t,v)) (pMap D Sc cutoff i t.val w (z t))
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro t _
    rw [← content_appendQ D cutoff i ν v]
    exact pMap_sourcePull D Sc cutoff i _ _

/-- All ambient rows; only the old-source matrix ring acts on the right. -/
abbrev SourceContent (p : ZMod 2) (i : I) (ν : List I) :=
  ∀ w : ContentWords (i :: ν), SourceRow D Sc cutoff p i ν w.val

abbrev AppendContent (i : I) (ν : List I) :=
  ∀ w : ContentWords (i :: ν), AppendRow D Sc cutoff i ν w.val

def sourceContentCentral (p : ZMod 2) (i : I) (ν : List I) :
    SourceContent D Sc cutoff p i ν →ₗ[(ContentRing D Sc cutoff ν)ᵐᵒᵖ]
      SourceContent D Sc cutoff p i ν :=
  LinearMap.pi fun w => (sourceRowCentral D Sc cutoff p i ν w.val).comp (LinearMap.proj w)

def appendContentCentral (i : I) (ν : List I) :
    AppendContent D Sc cutoff i ν →ₗ[(ContentRing D Sc cutoff ν)ᵐᵒᵖ]
      AppendContent D Sc cutoff i ν :=
  LinearMap.pi fun w => (appendRowCentral D Sc cutoff i ν w.val).comp (LinearMap.proj w)

def pContent (i : I) (ν : List I) :
    SourceContent D Sc cutoff (appendQ D cutoff i ν) i ν →ₗ[(ContentRing D Sc cutoff ν)ᵐᵒᵖ]
      AppendContent D Sc cutoff i ν :=
  LinearMap.pi fun w => (pRow D Sc cutoff i ν w.val).comp (LinearMap.proj w)

/-- K₀ as an ordinary right module over the polynomial ring of the old ring. -/
abbrev K0 (i : I) (ν : List I) :=
  CyclotomicAction.RightCentralPolynomialModule (appendContentCentral D Sc cutoff i ν)

/-- K₁ retains epsilon, the parity of the cyclotomic crossing map. -/
abbrev K1 (i : I) (ν : List I) :=
  CyclotomicAction.RightCentralPolynomialModule
    (sourceContentCentral D Sc cutoff (appendQ D cutoff i ν) i ν)

/-- K₁′ retains eta, without the parity of the moving cyclotomic relation. -/
abbrev K1Prime (i : I) (ν : List I) :=
  CyclotomicAction.RightCentralPolynomialModule
    (sourceContentCentral D Sc cutoff (D.parity i * wordSumParity D ν) i ν)

/-- The prescribed content map is an ordinary right B[s]-linear map. -/
def pPolynomial (i : I) (ν : List I) :
    K1 D Sc cutoff i ν →ₗ[(Polynomial (ContentRing D Sc cutoff ν))ᵐᵒᵖ] K0 D Sc cutoff i ν :=
  CyclotomicAction.RightCentralPolynomialModule.map _ _ (pContent D Sc cutoff i ν) (by
    intro z
    funext w v
    exact pMap_central D Sc cutoff i v.val w.val (z w v))

/-- Injectivity of P survives the ordinary right polynomial-module assembly. -/
theorem pPolynomial_injective (i : I) (ν : List I) :
    Function.Injective (pPolynomial D Sc cutoff i ν) := by
  intro z z' h
  funext w v
  apply pMap_injective D Sc cutoff i v.val w.val
  exact congrFun (congrFun h w) v

/-- On quotient elements, the polynomial map is the prescribed wordwise P. -/
@[simp] theorem pPolynomial_of (i : I) (ν : List I)
    (z : SourceContent D Sc cutoff (appendQ D cutoff i ν) i ν) :
    pPolynomial D Sc cutoff i ν
      (CyclotomicAction.RightCentralPolynomialModule.of _ z) =
    CyclotomicAction.RightCentralPolynomialModule.of _ (pContent D Sc cutoff i ν z) := rfl

/-- The polynomial variable on K₀ is the moving dot/square on every matrix component. -/
theorem K0_X (i : I) (ν : List I) (z : AppendContent D Sc cutoff i ν) :
    MulOpposite.op (Polynomial.X : Polynomial (ContentRing D Sc cutoff ν)) •
      CyclotomicAction.RightCentralPolynomialModule.of (appendContentCentral D Sc cutoff i ν) z =
    CyclotomicAction.RightCentralPolynomialModule.of _ (appendContentCentral D Sc cutoff i ν z) :=
  CyclotomicAction.RightCentralPolynomialModule.X_smul_of _ z

/-- The polynomial variable on K₁ uses the same central exponent, with epsilon unchanged. -/
theorem K1_X (i : I) (ν : List I)
    (z : SourceContent D Sc cutoff (appendQ D cutoff i ν) i ν) :
    MulOpposite.op (Polynomial.X : Polynomial (ContentRing D Sc cutoff ν)) •
      CyclotomicAction.RightCentralPolynomialModule.of
        (sourceContentCentral D Sc cutoff (appendQ D cutoff i ν) i ν) z =
    CyclotomicAction.RightCentralPolynomialModule.of _
      (sourceContentCentral D Sc cutoff (appendQ D cutoff i ν) i ν z) :=
  CyclotomicAction.RightCentralPolynomialModule.X_smul_of _ z

/-- Ground-ring PBW coordinates of the full source content module. The old word,
ambient word, moving shuffle and moving exponent are all retained. This is not
asserted to be a polynomial-linear finite-projective decomposition. -/
def sourceContentCoordinateEquiv (p : ZMod 2) (i : I) (ν : List I) :
    SourceContent D Sc cutoff p i ν ≃ₗ[k]
      (∀ w : ContentWords (i :: ν), ∀ v : ContentWords ν,
        PrependOldCoordinates D Sc cutoff i v.val w.val) :=
  LinearEquiv.piCongrRight fun w => LinearEquiv.piCongrRight fun v =>
    prependOldCoordinateEquiv D Sc cutoff p i v.val w.val

/-- The central action advances precisely one central block of the moving exponent,
without changing the old quotient coefficient or the PBW shuffle. -/
theorem centralSource_pair_shift (p : ZMod 2) {i : I} {v w : List I}
    (x : PrependIdx i v w) (b : Old D Sc cutoff v x.oldTarget) :
    centralSource D Sc cutoff i v w
      (pair D Sc cutoff p i
        ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] prependTail D Sc x) b) =
      pair D Sc cutoff p i
        ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
          prependTail D Sc (x.shift (centralDegree D i))) b :=
  movingPower_pair_shift D Sc cutoff p x _ (centralDegree_even D i) b

/-- The residue in the dot/square decomposition is unchanged by the central action. -/
theorem centralSource_residue {i : I} {v w : List I} (x : PrependIdx i v w) :
    (x.shift (centralDegree D i)).val.1 % centralDegree D i =
      x.val.1 % centralDegree D i := by
  change (centralDegree D i + x.val.1) % centralDegree D i = _
  simp

end OddMath.QuiverHecke.ELVOld
