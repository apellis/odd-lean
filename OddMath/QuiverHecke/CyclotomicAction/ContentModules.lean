import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Ring.Opposite
import Mathlib.Algebra.Polynomial.Coeff
import OddMath.QuiverHecke.CyclotomicAction.EndpointPolynomials
import OddMath.QuiverHecke.CyclotomicAction.CyclotomicQuotientTop
import OddMath.QuiverHecke.CyclotomicAction.ModuleInduction
import OddMath.QuiverHecke.CyclotomicAction.PrependCoordinates
import OddMath.QuiverHecke.CyclotomicAction.TruncatedAppend
import OddMath.QuiverHecke.AppendBasis
import OddMath.QuiverHecke.HomDimension
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import OddMath.QuiverHecke.CyclotomicAction.TruncatedAppend
import OddMath.QuiverHecke.CyclotomicAction.VacuumGrading
import OddMath.QuiverHecke.CyclotomicAction.AppendBalance

/-!
# Content modules

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-!
# Central polynomial modules

The central polynomial extension of an ordinary (possibly noncommutative) ring acts
on a module equipped with a linear endomorphism. This is infrastructure for the
polynomial actions in the cyclotomic construction.
-/

noncomputable section

namespace OddMath.QuiverHecke.CyclotomicAction

universe u v w

variable {R : Type u} [Ring R] {M : Type v} [AddCommGroup M] [Module R M]

/-- The underlying additive group, with its polynomial action specified by `f`. -/
def CentralPolynomialModule (_f : M →ₗ[R] M) := M

namespace CentralPolynomialModule

variable (f : M →ₗ[R] M)

instance : AddCommGroup (CentralPolynomialModule f) := inferInstanceAs (AddCommGroup M)

/-- Canonical additive identification with the original module. -/
def of : M ≃+ CentralPolynomialModule f := AddEquiv.refl M

/-- Evaluation in additive endomorphisms; linearity supplies centrality of `X`. -/
def actionHom : Polynomial R →+* AddMonoid.End M :=
  Polynomial.eval₂RingHom' (Module.toAddMonoidEnd R M) f.toAddMonoidHom (fun r => by
    apply AddMonoidHom.ext
    intro m
    exact (f.map_smul r m).symm)

instance : Module (Polynomial R) (CentralPolynomialModule f) :=
  Module.compHom M (actionHom f)

@[simp] theorem smul_of (p : Polynomial R) (m : M) :
    p • of f m = of f (actionHom f p m) := rfl

@[simp] theorem of_symm_smul (p : Polynomial R) (m : CentralPolynomialModule f) :
    (of f).symm (p • m) = actionHom f p ((of f).symm m) := rfl

@[simp] theorem actionHom_C (r : R) (m : M) :
    actionHom f (Polynomial.C r) m = r • m := by
  change (Polynomial.eval₂ (Module.toAddMonoidEnd R M) f.toAddMonoidHom
    (Polynomial.C r)) m = r • m
  rw [Polynomial.eval₂_C]
  rfl

@[simp] theorem actionHom_X (m : M) :
    actionHom f Polynomial.X m = f m := by
  change (Polynomial.eval₂ (Module.toAddMonoidEnd R M) f.toAddMonoidHom
    Polynomial.X) m = f m
  rw [Polynomial.eval₂_X]
  rfl

@[simp] theorem C_smul_of (r : R) (m : M) :
    Polynomial.C r • of f m = of f (r • m) := by simp

@[simp] theorem X_smul_of (m : M) :
    (Polynomial.X : Polynomial R) • of f m = of f (f m) := by simp

variable {N : Type w} [AddCommGroup N] [Module R N]
variable (g : N →ₗ[R] N) (h : M →ₗ[R] N)

/-- Intertwining the distinguished endomorphisms implies intertwining every polynomial. -/
theorem map_actionHom (hf : ∀ m, h (f m) = g (h m)) (p : Polynomial R) (m : M) :
    h (actionHom f p m) = actionHom g p (h m) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, map_add]
    change h (actionHom f p m + actionHom f q m) = _ + _
    rw [map_add, hp, hq]
  | monomial n r =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial]
    simp only [map_mul, map_pow]
    change h (actionHom f (Polynomial.C r) ((actionHom f Polynomial.X ^ n) m)) =
      actionHom g (Polynomial.C r) ((actionHom g Polynomial.X ^ n) (h m))
    rw [actionHom_C, actionHom_C, h.map_smul]
    congr 1
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ', pow_succ']
      change h (actionHom f Polynomial.X ((actionHom f Polynomial.X ^ n) m)) =
        actionHom g Polynomial.X ((actionHom g Polynomial.X ^ n) (h m))
      rw [actionHom_X, actionHom_X, hf, ih]

/-- An intertwining linear map, bundled over the central polynomial ring. -/
def map (hf : ∀ m, h (f m) = g (h m)) :
    CentralPolynomialModule f →ₗ[Polynomial R] CentralPolynomialModule g where
  toFun := fun m => of g (h ((of f).symm m))
  map_add' := by intros; exact h.map_add _ _
  map_smul' := by intros; exact map_actionHom f g h hf _ _

@[simp] theorem map_of (hf : ∀ m, h (f m) = g (h m)) (m : M) :
    map f g h hf (of f m) = of g (h m) := rfl

end CentralPolynomialModule
end OddMath.QuiverHecke.CyclotomicAction
end

end

section

/-!
# Right central polynomial modules

Restriction of the central polynomial action to the opposite of the ordinary
polynomial ring, for the right polynomial modules in the cyclotomic construction.
No commutativity of the coefficient ring is assumed.
-/

noncomputable section

namespace OddMath.QuiverHecke.CyclotomicAction

open MulOpposite

universe u v w

variable (R : Type u) [Ring R]

/-- Coefficientwise opposition, viewed as a homomorphism of rings. -/
def polynomialOpHom : (Polynomial R)ᵐᵒᵖ →+* Polynomial Rᵐᵒᵖ :=
  (RingEquiv.opOp (Polynomial Rᵐᵒᵖ)).symm.toRingHom.comp
    (RingHom.op (Polynomial.eval₂RingHom'
      ((RingHom.op (Polynomial.C (R := Rᵐᵒᵖ))).comp (RingEquiv.opOp R).toRingHom)
      (op Polynomial.X) (fun r => by
        change Commute (op (Polynomial.C (op r))) (op Polynomial.X)
        exact (Polynomial.commute_X (Polynomial.C (op r))).symm.op)))

@[simp] theorem polynomialOpHom_C (r : R) :
    polynomialOpHom R (op (Polynomial.C r)) = Polynomial.C (op r) := by
  simp [polynomialOpHom, Polynomial.eval₂RingHom']

@[simp] theorem polynomialOpHom_X :
    polynomialOpHom R (op Polynomial.X) = Polynomial.X := by
  simp [polynomialOpHom, Polynomial.eval₂RingHom']

@[simp] theorem polynomialOpHom_monomial (n : ℕ) (r : R) :
    polynomialOpHom R (op (Polynomial.monomial n r)) = Polynomial.monomial n (op r) := by
  rw [← Polynomial.C_mul_X_pow_eq_monomial]
  simp [op_mul, ← Polynomial.C_mul_X_pow_eq_monomial]

/-- The ring homomorphism takes the opposite of every coefficient. -/
@[simp] theorem polynomialOpHom_coeff (p : Polynomial R) (n : ℕ) :
    (polynomialOpHom R (op p)).coeff n = op (p.coeff n) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [op_add, map_add, Polynomial.coeff_add, hp, hq]
  | monomial k r =>
      rw [polynomialOpHom_monomial]
      by_cases hk : k = n <;> simp [Polynomial.coeff_monomial, hk]

variable {R} {M : Type v} [AddCommGroup M] [Module Rᵐᵒᵖ M]

/-- A right module over the ordinary central polynomial ring. -/
def RightCentralPolynomialModule (f : M →ₗ[Rᵐᵒᵖ] M) := CentralPolynomialModule f

namespace RightCentralPolynomialModule

variable (f : M →ₗ[Rᵐᵒᵖ] M)

instance : AddCommGroup (RightCentralPolynomialModule f) :=
  inferInstanceAs (AddCommGroup (CentralPolynomialModule f))

instance : Module (Polynomial R)ᵐᵒᵖ (RightCentralPolynomialModule f) :=
  Module.compHom (CentralPolynomialModule f) (polynomialOpHom R)

/-- The additive identification with the underlying right coefficient module. -/
def of : M ≃+ RightCentralPolynomialModule f := CentralPolynomialModule.of f

@[simp] theorem smul_of (p : (Polynomial R)ᵐᵒᵖ) (m : M) :
    p • of f m = of f (CentralPolynomialModule.actionHom f (polynomialOpHom R p) m) := rfl

@[simp] theorem C_smul_of (r : R) (m : M) :
    op (Polynomial.C r) • of f m = of f (op r • m) := by simp

@[simp] theorem X_smul_of (m : M) :
    op (Polynomial.X : Polynomial R) • of f m = of f (f m) := by simp

variable {N : Type w} [AddCommGroup N] [Module Rᵐᵒᵖ N]
variable (g : N →ₗ[Rᵐᵒᵖ] N) (h : M →ₗ[Rᵐᵒᵖ] N)

/-- Restrict an intertwining central-polynomial map to right ordinary polynomials. -/
def map (hf : ∀ m, h (f m) = g (h m)) :
    RightCentralPolynomialModule f →ₗ[(Polynomial R)ᵐᵒᵖ] RightCentralPolynomialModule g where
  toFun := CentralPolynomialModule.map f g h hf
  map_add' := (CentralPolynomialModule.map f g h hf).map_add
  map_smul' p m := (CentralPolynomialModule.map f g h hf).map_smul (polynomialOpHom R p) m

@[simp] theorem map_of (hf : ∀ m, h (f m) = g (h m)) (m : M) :
    map f g h hf (of f m) = of g (h m) := rfl

end RightCentralPolynomialModule
end OddMath.QuiverHecke.CyclotomicAction
end

end

section

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

/-- The prescribed content map is an ordinary right B[s]-linear map. -/
def pPolynomial (i : I) (ν : List I) :
    K1 D Sc cutoff i ν →ₗ[(Polynomial (ContentRing D Sc cutoff ν))ᵐᵒᵖ] K0 D Sc cutoff i ν :=
  CyclotomicAction.RightCentralPolynomialModule.map _ _ (pContent D Sc cutoff i ν) (by
    intro z
    funext w v
    exact pMap_central D Sc cutoff i v.val w.val (z w v))

/-- On quotient elements, the polynomial map is the prescribed wordwise P. -/
@[simp] theorem pPolynomial_of (i : I) (ν : List I)
    (z : SourceContent D Sc cutoff (appendQ D cutoff i ν) i ν) :
    pPolynomial D Sc cutoff i ν
      (CyclotomicAction.RightCentralPolynomialModule.of _ z) =
    CyclotomicAction.RightCentralPolynomialModule.of _ (pContent D Sc cutoff i ν z) := rfl

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # Untruncated old ELV categories of a fixed content
This restricts the existing old category, with its entire coefficient ring,
to a finite permutation class of words. Append is the existing canonical old
append functor. No coefficient truncation occurs.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The full old category on the finite permutation class of a word. -/
structure OldContentCategory (ν : List I) where
  obj : OldCategory D Sc cutoff
  wordPerm : obj.word.Perm ν

instance oldContentCategory (ν : List I) : Category (OldContentCategory D Sc cutoff ν) where
  Hom v w := v.obj ⟶ w.obj
  id v := 𝟙 v.obj
  comp f g := f ≫ g
  id_comp := Category.id_comp
  comp_id := Category.comp_id
  assoc := Category.assoc

instance oldContentPreadditive (ν : List I) : Preadditive (OldContentCategory D Sc cutoff ν) where
  homGroup v w := inferInstanceAs (AddCommGroup (v.obj ⟶ w.obj))
  add_comp := by intro v w z f g h; exact Preadditive.add_comp v.obj w.obj z.obj f g h
  comp_add := by intro v w z f g h; exact Preadditive.comp_add v.obj w.obj z.obj f g h

instance oldContentLinear (ν : List I) : Linear k (OldContentCategory D Sc cutoff ν) where
  homModule v w := inferInstanceAs (Module k (v.obj ⟶ w.obj))
  smul_comp := by intro v w z r f g; exact Linear.smul_comp v.obj w.obj z.obj r f g
  comp_smul := by intro v w z f r g; exact Linear.comp_smul v.obj w.obj z.obj f r g

instance oldContentSupercategory (ν : List I) :
    Supercategory k (OldContentCategory D Sc cutoff ν) where
  parity v w := parity (R := k) v.obj w.obj
  isInternal v w := Supercategory.isInternal v.obj w.obj
  id_mem v := id_mem v.obj
  comp_mem := Supercategory.comp_mem

/-- The inclusion preserves every quotient Hom, including exterior coefficients. -/
def oldContentInclusion (ν : List I) :
    OldContentCategory D Sc cutoff ν ⥤ OldCategory D Sc cutoff where
  obj v := v.obj
  map f := f

instance (ν : List I) : (oldContentInclusion D Sc cutoff ν).Full where
  map_surjective f := ⟨f,rfl⟩
instance (ν : List I) : (oldContentInclusion D Sc cutoff ν).Faithful where
  map_injective h := h
instance (ν : List I) : (oldContentInclusion D Sc cutoff ν).Additive where
  map_add := rfl
instance (ν : List I) : (oldContentInclusion D Sc cutoff ν).Linear k where
  map_smul _ _ := rfl
instance (ν : List I) : IsSuperfunctor k (oldContentInclusion D Sc cutoff ν) where
  map_mem h := h

/-- Extract the same finite content coordinate from an actual content object. -/
def oldContentWord (ν : List I) (v : OldContentCategory D Sc cutoff ν) : ContentWords ν :=
  ⟨v.obj.word,v.wordPerm⟩

/-- Append uses the existing canonical untruncated old functor. -/
def oldContentAppend (ν : List I) (i : I) :
    OldContentCategory D Sc cutoff ν ⥤ OldContentCategory D Sc cutoff (i :: ν) where
  obj v := ⟨(CyclotomicCrossingTensor.append D Sc cutoff i).obj v.obj,
    (v.wordPerm.append (List.Perm.refl [i])).trans
      (List.perm_append_comm : (ν ++ [i]).Perm ([i] ++ ν))⟩
  map f := (CyclotomicCrossingTensor.append D Sc cutoff i).map f
  map_id v := (CyclotomicCrossingTensor.append D Sc cutoff i).map_id v.obj
  map_comp f g := (CyclotomicCrossingTensor.append D Sc cutoff i).map_comp f g

instance (ν : List I) (i : I) : (oldContentAppend D Sc cutoff ν i).Additive where
  map_add := (CyclotomicCrossingTensor.append D Sc cutoff i).map_add
instance (ν : List I) (i : I) : (oldContentAppend D Sc cutoff ν i).Linear k where
  map_smul f r := (CyclotomicCrossingTensor.append D Sc cutoff i).map_smul r f
instance (ν : List I) (i : I) : IsSuperfunctor k (oldContentAppend D Sc cutoff ν i) where
  map_mem := Supercategory.map_mem (CyclotomicCrossingTensor.append D Sc cutoff i)

/-- Appending then including is literally the established old append functor. -/
theorem oldContentAppend_inclusion (ν : List I) (i : I) :
    oldContentAppend D Sc cutoff ν i ⋙ oldContentInclusion D Sc cutoff (i :: ν) =
      oldContentInclusion D Sc cutoff ν ⋙ CyclotomicCrossingTensor.append D Sc cutoff i := rfl

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # Tensor formulas for weighted append comparison
SwappedVacuumCoordinates §6 requires compatibility with the specified
generators, beyond pointwise or input-module naturality.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory

namespace OddMath.QuiverHecke.ELVOld
universe u
variable {k : Type u} [CommRing k]
  {C : Type u} [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]

theorem moduleIsoOfEvenNatIso_inv_total (F G : Superfunctor k C (SVec k))
    (e : F.toFunctor ≅ G.toFunctor)
    (hh : ∀ w, e.hom.app w ∈ parity (R := k) _ _ 0)
    (hi : ∀ w, e.inv.app w ∈ parity (R := k) _ _ 0) (w : C) :
    (moduleIsoOfEvenNatIso F G e hh hi).inv.total w = e.inv.app w := by
  change e.inv.app w + (0 : G.obj w ⟶ F.obj w) = e.inv.app w
  exact add_zero _

end OddMath.QuiverHecke.ELVOld

namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
variable {k : Type u} [CommRing k]
  {C D : Type u} [Category.{u} C] [Category.{u} D]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive D] [Linear k D] [Supercategory k D]

omit [Supercategory k D] in
private theorem tensor_identity_add_zero (J : C ⥤ D)
    (M : Superfunctor k C (SVec k)) (v : C) (w : D)
    (g h : J.obj v ⟶ w) (b : M.obj v) :
    tensor J M.toFunctor v g ((LinearMap.id : M.obj v →ₗ[k] M.obj v) b) +
      tensor J M.toFunctor v h ((0 : M.obj v →ₗ[k] M.obj v) b) =
        tensor J M.toFunctor v g b := by
  rw [LinearMap.id_apply, LinearMap.zero_apply, tensor_zero_right, add_zero]

end OddMath.QuiverHecke.ELVOld.BalancedInduction

namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
local notation "Q" => oldTruncateFunctor D Sc cutoff N

@[simp] theorem weightedRestrictionModuleIso_hom_app
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (hM : KillsWeightedCoefficients D Sc cutoff N M) (p : ZMod 2)
    (v : OldCategory D Sc cutoff) :
    (weightedRestrictionModuleIso D Sc cutoff N M hM).hom.app p v =
      if p = 0 then LinearMap.id else 0 := rfl

theorem quotientInductionCounitIso_inv_total
    (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))
    (w : TruncatedCategory D Sc cutoff N) :
    (quotientInductionCounitIso D Sc cutoff N M).inv.total w =
      BalancedInduction.unit Q (Q ⋙ M.toFunctor) ⟨w.word⟩ :=
  moduleIsoOfEvenNatIso_inv_total _ _ _ _ _ w

/-- The inverse quotient/descent comparison is the canonical unit tensor
on the same old vector space. -/
theorem quotientInducedWeightedModuleIso_inv_tensor
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (hM : KillsWeightedCoefficients D Sc cutoff N M)
    (w : TruncatedCategory D Sc cutoff N) (b : M.obj ⟨w.word⟩) :
    (quotientInducedWeightedModuleIso D Sc cutoff N M hM).inv.total w b =
      BalancedInduction.tensor Q M.toFunctor
        (⟨w.word⟩ : OldCategory D Sc cutoff) (𝟙 w) b := by
  let S := weightedModule D Sc cutoff N M hM
  let u := weightedRestrictionModuleIso D Sc cutoff N M hM
  let c := quotientInductionCounitIso D Sc cutoff N S
  let IQ := BalancedInduction.induction (k := k) Q
  have hc : c.inv.total w b =
      BalancedInduction.tensor Q (weightedRestriction D Sc cutoff N S).toFunctor
        (⟨w.word⟩ : OldCategory D Sc cutoff) (𝟙 w) b := by
    rw [quotientInductionCounitIso_inv_total]
    rfl
  have ht : (quotientInducedWeightedModuleIso D Sc cutoff N M hM).inv.total w =
      (IQ.map u.hom).total w ∘ₗ c.inv.total w := by
    change (c.inv ≫ IQ.map u.hom).total w = _
    exact Superfunctor.comp_total _ _ w
  have hv : (quotientInducedWeightedModuleIso D Sc cutoff N M hM).inv.total w b =
      (IQ.map u.hom).total w (c.inv.total w b) :=
    congrArg (fun f : S.obj w →ₗ[k] BalancedInduction.Obj Q M.toFunctor w => f b) ht
  refine hv.trans ?_
  refine (congrArg ((IQ.map u.hom).total w) hc).trans ?_
  change (BalancedInduction.moduleMap Q u.hom).total w
    (BalancedInduction.tensor Q (weightedRestriction D Sc cutoff N S).toFunctor
      (⟨w.word⟩ : OldCategory D Sc cutoff) (𝟙 w) b) = _
  rw [BalancedInduction.moduleMap_total_tensor]
  simp only [u, weightedRestrictionModuleIso_hom_app, ↓reduceIte, one_ne_zero]
  exact BalancedInduction.tensor_identity_add_zero Q M
    (⟨w.word⟩ : OldCategory D Sc cutoff) w (𝟙 w) (twist k 1 (𝟙 w)) b

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # Parity of weighted append comparison
The generator transport in SwappedVacuumCoordinates §6 uses the evenness of
the specified five-isomorphism comparison, before evaluating its unit tensors.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {k : Type u} [CommRing k]
  {C : Type u} [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]

theorem moduleIsoOfEvenNatIso_hom_mem (F G : Superfunctor k C (SVec k))
    (e : F.toFunctor ≅ G.toFunctor)
    (hh : ∀ w, e.hom.app w ∈ parity (R := k) _ _ 0)
    (hi : ∀ w, e.inv.app w ∈ parity (R := k) _ _ 0) :
    (moduleIsoOfEvenNatIso F G e hh hi).hom ∈ parity (R := k) F G 0 := by
  apply Superfunctor.mem_parity_iff_isHomogeneous.mpr
  intro q hq
  funext w
  change (if q = 0 then e.hom.app w else 0) = 0
  exact ite_eq_right hq

theorem moduleIsoOfEvenNatIso_inv_mem (F G : Superfunctor k C (SVec k))
    (e : F.toFunctor ≅ G.toFunctor)
    (hh : ∀ w, e.hom.app w ∈ parity (R := k) _ _ 0)
    (hi : ∀ w, e.inv.app w ∈ parity (R := k) _ _ 0) :
    (moduleIsoOfEvenNatIso F G e hh hi).inv ∈ parity (R := k) G F 0 :=
  Supercategory.inv_mem (moduleIsoOfEvenNatIso F G e hh hi)
    (moduleIsoOfEvenNatIso_hom_mem F G e hh hi)

end OddMath.QuiverHecke.ELVOld

namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
variable {k : Type u} [CommRing k]
  {C D : Type u} [Category.{u} C] [Category.{u} D]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive D] [Linear k D] [Supercategory k D]

end OddMath.QuiverHecke.ELVOld.BalancedInduction

namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
local notation "Q" => oldTruncateFunctor D Sc cutoff N

theorem weightedRestrictionModuleIso_hom_mem
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (hM : KillsWeightedCoefficients D Sc cutoff N M) :
    (weightedRestrictionModuleIso D Sc cutoff N M hM).hom ∈ parity (R := k) _ _ 0 := by
  unfold weightedRestrictionModuleIso
  exact moduleIsoOfEvenNatIso_hom_mem _ _ _ _ _

theorem quotientInductionCounitIso_hom_mem
    (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k)) :
    (quotientInductionCounitIso D Sc cutoff N M).hom ∈ parity (R := k) _ _ 0 := by
  rw [quotientInductionCounitIso_hom]
  exact BalancedInduction.adjunctionCounit_mem Q M

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # Content-indexed ELV module induction and restriction

The exact-content full subcategories retain every quotient morphism, its
coefficient action and super parity. Right append changes content by multiset
addition. Balanced induction along this functor is left adjoint to restriction
on all supernatural module maps. This is the content-indexed module-category
step of `DeformedActionAssembly.md` §5; it does not assert factor normalization,
biadjunction, or the defining relations of the full categorical action.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

/-- The full truncated ELV category on words of exactly the specified content. -/
structure ContentCategory (β : Multiset I) where
  obj : TruncatedCategory D Sc cutoff N
  content : (obj.word : Multiset I) = β

instance contentCategory (β : Multiset I) : Category (ContentCategory D Sc cutoff N β) where
  Hom v w := v.obj ⟶ w.obj
  id v := 𝟙 v.obj
  comp f g := f ≫ g
  id_comp := Category.id_comp
  comp_id := Category.comp_id
  assoc := Category.assoc

instance contentPreadditive (β : Multiset I) : Preadditive (ContentCategory D Sc cutoff N β) where
  homGroup v w := inferInstanceAs (AddCommGroup (v.obj ⟶ w.obj))
  add_comp := by intro v w z f g h; exact Preadditive.add_comp v.obj w.obj z.obj f g h
  comp_add := by intro v w z f g h; exact Preadditive.comp_add v.obj w.obj z.obj f g h

instance contentLinear (β : Multiset I) : Linear k (ContentCategory D Sc cutoff N β) where
  homModule v w := inferInstanceAs (Module k (v.obj ⟶ w.obj))
  smul_comp := by intro v w z r f g; exact Linear.smul_comp v.obj w.obj z.obj r f g
  comp_smul := by intro v w z f r g; exact Linear.comp_smul v.obj w.obj z.obj f r g

instance contentSupercategory (β : Multiset I) :
    Supercategory k (ContentCategory D Sc cutoff N β) where
  parity v w := parity (R := k) v.obj w.obj
  isInternal v w := Supercategory.isInternal v.obj w.obj
  id_mem v := id_mem v.obj
  comp_mem := Supercategory.comp_mem

/-- Inclusion is the identity on the entire quotient Hom module. -/
def contentInclusion (β : Multiset I) :
    ContentCategory D Sc cutoff N β ⥤ TruncatedCategory D Sc cutoff N where
  obj v := v.obj
  map f := f

instance contentInclusion_full (β : Multiset I) : (contentInclusion D Sc cutoff N β).Full where
  map_surjective f := ⟨f, rfl⟩
instance contentInclusion_faithful (β : Multiset I) :
    (contentInclusion D Sc cutoff N β).Faithful where
  map_injective h := h

/-- Append with an explicit common target content. -/
def contentAppendTo (β : Multiset I) (σ : List I) (γ : Multiset I)
    (hσ : β + (σ : Multiset I) = γ) :
    ContentCategory D Sc cutoff N β ⥤ ContentCategory D Sc cutoff N γ where
  obj v := ⟨(truncatedAppend D Sc cutoff N σ).obj v.obj, by
    change ((v.obj.word ++ σ : List I) : Multiset I) = γ
    rw [← Multiset.coe_add, v.content, hσ]⟩
  map f := (truncatedAppend D Sc cutoff N σ).map f
  map_id v := (truncatedAppend D Sc cutoff N σ).map_id v.obj
  map_comp f g := (truncatedAppend D Sc cutoff N σ).map_comp f g

/-- Append to the canonical target content. -/
def contentAppend (β : Multiset I) (σ : List I) :
    ContentCategory D Sc cutoff N β ⥤ ContentCategory D Sc cutoff N (β + (σ : Multiset I)) :=
  contentAppendTo D Sc cutoff N β σ _ rfl

instance contentAppend_additive (β : Multiset I) (σ : List I) :
    (contentAppend D Sc cutoff N β σ).Additive where
  map_add := (truncatedAppend D Sc cutoff N σ).map_add
instance contentAppend_linear (β : Multiset I) (σ : List I) :
    (contentAppend D Sc cutoff N β σ).Linear k where
  map_smul f r := (truncatedAppend D Sc cutoff N σ).map_smul r f
instance contentAppend_super (β : Multiset I) (σ : List I) :
    IsSuperfunctor k (contentAppend D Sc cutoff N β σ) where
  map_mem := Supercategory.map_mem (truncatedAppend D Sc cutoff N σ)

/-- Integer grading is inherited independently of super parity. -/
@[instance_reducible]
def contentGradedSupercategory (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous)
    (β : Multiset I) : GradedSupercategory k (ContentCategory D Sc cutoff N β) := by
  letI := truncatedGradedSupercategory D Sc cutoff N sy hc
  exact
    { degree := fun v w => GradedSupercategory.degree (R := k) v.obj w.obj
      isInternal_degree := fun v w => GradedSupercategory.isInternal_degree v.obj w.obj
      proj_mem_degree := fun p hf => GradedSupercategory.proj_mem_degree p hf
      id_mem_degree := fun v => GradedSupercategory.id_mem_degree v.obj
      comp_mem_degree := fun hf hg => GradedSupercategory.comp_mem_degree hf hg }

/-- All parity-graded modules and all supernatural maps at exact content. -/
abbrev ContentModules (β : Multiset I) :=
  Superfunctor k (ContentCategory D Sc cutoff N β) (SVec.{u} k)

/-- Balanced tensor induction from content `β` to content `β + σ`. -/
abbrev contentInduction (β : Multiset I) (σ : List I) :
    ContentModules D Sc cutoff N β ⥤ ContentModules D Sc cutoff N (β + (σ : Multiset I)) :=
  BalancedInduction.induction (contentAppend D Sc cutoff N β σ)

/-- The one-colour raising functor (`E` in the source convention). -/
abbrev contentE (β : Multiset I) (i : I) := contentInduction D Sc cutoff N β [i]

end OddMath.QuiverHecke.ELVOld
end

end

section

/-!
# Signed ELV append PBW normalization

Input-side append PBW coordinates with the full ELV coefficient algebra.
The coefficient parity twist is retained when moving a coefficient into
its old block. These affine coordinates precede descent through the
append-old relation span; no quotient independence is asserted here.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
open scoped TensorProduct Classical
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- Affine input PBW coordinates with the full ELV coefficient algebra. -/
def appendAffineEquiv (i : I) (v w : List I) :
    hom D Sc cutoff (v ++ [i]) w ≃ₗ[k]
      (AppendIdx i v w →₀ SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :=
  (TensorProduct.congr (LinearEquiv.refl k _)
    (appendBasis D Sc (i := i) (s := v) (t := w)).repr).trans
      (TensorProduct.finsuppScalarRight k k _ _)

@[simp] theorem appendAffineEquiv_tmul (i : I) (v w : List I)
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff)
    (f : (pres D Sc).obj (ob D (v ++ [i])) ⟶ (pres D Sc).obj (ob D w))
    (x : AppendIdx i v w) :
    appendAffineEquiv D Sc cutoff i v w (a ⊗ₜ[k] f) x =
      (appendBasis D Sc).repr f x • a := by
  change TensorProduct.finsuppScalarRight k k _ _
    ((TensorProduct.congr (LinearEquiv.refl k _) (appendBasis D Sc).repr) (a ⊗ₜ[k] f)) x = _
  rw [TensorProduct.congr_tmul, LinearEquiv.refl_apply,
    TensorProduct.finsuppScalarRight_apply_tmul_apply]

@[simp] theorem appendAffineEquiv_symm_single {i : I} {v w : List I}
    (x : AppendIdx i v w) (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
    (appendAffineEquiv D Sc cutoff i v w).symm (Finsupp.single x a) =
      a ⊗ₜ[k] appendElt D Sc x := by
  change (TensorProduct.congr (LinearEquiv.refl k _) (appendBasis D Sc).repr).symm
    ((TensorProduct.finsuppScalarRight k k _ _).symm (Finsupp.single x a)) = _
  rw [TensorProduct.finsuppScalarRight_symm_apply_single, TensorProduct.congr_symm_tmul]
  simp only [LinearEquiv.refl_symm, LinearEquiv.refl_apply, Module.Basis.repr_symm_single,
    one_smul, appendBasis_apply]

/-- New dots and moving crossings, with no old normal form or coefficient. -/
def appendTail {i : I} {v w : List I} (x : AppendIdx i v w) :
    (pres D Sc).obj (ob D (x.oldTarget ++ [i])) ⟶ (pres D Sc).obj (ob D w) :=
  cl D Sc _ _ (((List.replicate x.1.1 v.length).map PG.dot) ++
    cw (Categorification.TypeA.canWord (v ++ [i]).length x.1.2.2.2.1⁻¹))
    (by simpa only [tgt_append, tgt_map_dot, x.moving_target] using
      sChain_pl (x.oldTarget ++ [i]) (((List.replicate x.1.1 v.length).map PG.dot) ++
        cw (Categorification.TypeA.canWord (v ++ [i]).length x.1.2.2.2.1⁻¹)))

/-- The existing input-side basis has old-first categorical orientation. -/
theorem appendElt_insert_tail {i : I} {v w : List I} (x : AppendIdx i v w) :
    appendElt D Sc x = affineRightContext D Sc [i] v x.oldTarget x.old.nf ≫
      appendTail D Sc x := by
  rw [appendElt_eq_comp, cl_comp]
  rfl

/-- Parity of the new dots and moving crossings, excluding the old block. -/
def appendTailParity {i : I} {v w : List I} (x : AppendIdx i v w) : ZMod 2 :=
  ((pl (x.oldTarget ++ [i]) (((List.replicate x.1.1 v.length).map PG.dot) ++
    cw (Categorification.TypeA.canWord (v ++ [i]).length x.1.2.2.2.1⁻¹))).map
      fun z => z.2.1.parity D).sum

theorem appendTail_mem {i : I} {v w : List I} (x : AppendIdx i v w) :
    appendTail D Sc x ∈ parity (R := k) _ _ (appendTailParity D x) :=
  Presentation.diag_mem_homDeg' (degree_parity_mkD D _ _)

/-- Moving a homogeneous coefficient into the old block retains its Koszul sign. -/
theorem append_insert_coefficient {i : I} {v w : List I} (x : AppendIdx i v w)
    {q : ZMod 2} (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff)
    (ha : a ∈ SKM.SYM.elvCoefficientParity D cutoff q) :
    rightContext D Sc cutoff [i] v x.oldTarget (a ⊗ₜ[k] x.old.nf) ≫
      (((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] appendTail D Sc x) :
        hom D Sc cutoff (x.oldTarget ++ [i]) w) =
      koszulSign q (appendTailParity D x) • (a ⊗ₜ[k] appendElt D Sc x) := by
  rw [rightContext_tmul]
  change BoxProd.tmulHom (X := obj D Sc cutoff (v ++ [i]))
    (Y := obj D Sc cutoff (x.oldTarget ++ [i])) (SuperalgebraCat.ofElem a) _ ≫
    BoxProd.tmulHom (X := obj D Sc cutoff (x.oldTarget ++ [i]))
    (Y := obj D Sc cutoff w) (SuperalgebraCat.ofElem 1) _ = _
  rw [BoxProd.tmulHom_comp_tmulHom ha _ (SuperalgebraCat.ofElem 1)
    (appendTail_mem D Sc x)]
  change koszulSign q (appendTailParity D x) •
    ((1 * a) ⊗ₜ[k] (affineRightContext D Sc [i] v x.oldTarget x.old.nf ≫ appendTail D Sc x)) = _
  rw [one_mul, ← appendElt_insert_tail]

/-- Source-order normalization works for arbitrary, not only homogeneous, coefficients. -/
theorem append_insert_twisted_coefficient {i : I} {v w : List I}
    (x : AppendIdx i v w) (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
    rightContext D Sc cutoff [i] v x.oldTarget
        (coefficientTwist D cutoff (appendTailParity D x) a ⊗ₜ[k] x.old.nf) ≫
      (((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] appendTail D Sc x) :
        hom D Sc cutoff (x.oldTarget ++ [i]) w) = a ⊗ₜ[k] appendElt D Sc x := by
  induction a using DirectSum.Decomposition.inductionOn (SKM.SYM.elvCoefficientParity D cutoff) with
  | zero => simp only [map_zero, TensorProduct.zero_tmul, Limits.zero_comp]
  | add a b ha hb =>
    simp only [map_add, TensorProduct.add_tmul, Preadditive.add_comp, ha, hb]
  | @homogeneous q a =>
    have ht : coefficientTwist D cutoff (appendTailParity D x) a =
        sign k (appendTailParity D x * q) • (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :=
      twist_of_mem _ a.property
    rw [ht, ← TensorProduct.smul_tmul', map_smul, Linear.smul_comp,
      append_insert_coefficient D Sc cutoff x a a.property, koszulSign_smul (R := k),
      mul_comm q, sign_smul_sign_smul]

end OddMath.QuiverHecke.ELVOld
end

end

section

/-!
# ELV old-Hom extraction from append PBW coordinates

The append-coordinate extraction step, needed for the old-only
coordinate comparison in `DeformedGlobalQP.md` §1. Only the old normal-form
component of the existing `AppendIdx` is replaced; the moving exponent and
inverse shuffle remain unchanged. No finite-colour or flatness assumption is used.

`appendExtractOld_insert_comp_tail` extracts arbitrary full-ELV old
composition. `appendExtractOldQuotient_insert_tail_eq_zero_iff` identifies
the old ideal on a prescribed tail. The coefficient-parity normalization
and total old-Hom parity twist are both retained.

These are affine extraction maps with values in old Homs or their quotient.
Descent on all old-relation generators, simultaneous regrouped coordinate
inversion, moving-square shift, and difference injectivity remain open.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
open scoped TensorProduct Classical
namespace OddMath.QuiverHecke
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

namespace AppendIdx
variable {i : I} {v w : List I}
/-- Replace only the old normal form, keeping the moving exponent and shuffle. -/
def replaceOld (x : AppendIdx i v w) (y : NFIdx v x.oldTarget) : AppendIdx i v w :=
  ⟨(x.1.1, y.1.1, y.1.2, x.1.2.2.2), y.2.1, y.2.2.1, by
    have he := tgt_append_right [i] (t := v)
      (fits_cw (Categorification.TypeA.validWord_canWord v.length y.1.2))
    simpa only [appendCrossingWord, cw_append, tgt_append, he, y.tgt_cw]
      using x.moving_target⟩

theorem replaceOld_injective (x : AppendIdx i v w) : Function.Injective x.replaceOld := by
  intro y z h
  apply Subtype.ext
  exact Prod.ext (congrArg (fun a : AppendIdx i v w => a.1.2.1) h)
    (congrArg (fun a : AppendIdx i v w => a.1.2.2.1) h)

end AppendIdx
namespace ELVOld

/-- Coefficients of a fixed moving tail, with the mandatory coefficient-parity twist. -/
def appendTailCoefficients {i : I} {v w : List I} (x : AppendIdx i v w) :
    (NFIdx v x.oldTarget →₀ SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) →ₗ[k]
      (AppendIdx i v w →₀ SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :=
  Finsupp.lsum k fun y => (Finsupp.lsingle (x.replaceOld y)).comp
    (coefficientTwist D cutoff (appendTailParity D x))

/-- Replacing the old index leaves the moving diagram unchanged. -/
theorem appendElt_replaceOld {i : I} {v w : List I} (x : AppendIdx i v w)
    (y : NFIdx v x.oldTarget) :
    appendElt D Sc (x.replaceOld y) =
      affineRightContext D Sc [i] v x.oldTarget y.nf ≫ appendTail D Sc x := by
  change _ = (y.nf ▷ (pres D Sc).obj (ob D [i])) ≫ _
  rw [nf_whiskerRight]
  unfold appendTail appendElt
  rw [cl_comp]
  apply cl_eq_cl
  simp only [AppendIdx.gens, AppendIdx.replaceOld, List.append_assoc]

/-- The tail acts on every exterior coefficient by its coefficient-parity involution. -/
theorem append_insert_nf_tail {i : I} {v w : List I} (x : AppendIdx i v w)
    (y : NFIdx v x.oldTarget)
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
    rightContext D Sc cutoff [i] v x.oldTarget (a ⊗ₜ[k] y.nf) ≫
      ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
        appendTail D Sc x : hom D Sc cutoff (x.oldTarget ++ [i]) w) =
      coefficientTwist D cutoff (appendTailParity D x) a ⊗ₜ[k]
        appendElt D Sc (x.replaceOld y) := by
  induction a using DirectSum.Decomposition.inductionOn (SKM.SYM.elvCoefficientParity D cutoff) with
  | zero => simp only [map_zero, TensorProduct.zero_tmul, Limits.zero_comp]
  | add a b ha hb =>
    simp only [map_add, TensorProduct.add_tmul, Preadditive.add_comp, ha, hb]
  | @homogeneous q a =>
    have ht : coefficientTwist D cutoff (appendTailParity D x) a =
        sign k (appendTailParity D x * q) • (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :=
      twist_of_mem _ a.property
    rw [rightContext_tmul]
    change BoxProd.tmulHom (X := obj D Sc cutoff (v ++ [i]))
      (Y := obj D Sc cutoff (x.oldTarget ++ [i])) (SuperalgebraCat.ofElem a) _ ≫
      BoxProd.tmulHom (X := obj D Sc cutoff (x.oldTarget ++ [i]))
      (Y := obj D Sc cutoff w) (SuperalgebraCat.ofElem 1) _ = _
    rw [BoxProd.tmulHom_comp_tmulHom a.property _ (SuperalgebraCat.ofElem 1)
      (appendTail_mem D Sc x)]
    change koszulSign q (appendTailParity D x) •
      ((1 * (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff)) ⊗ₜ[k]
        (affineRightContext D Sc [i] v x.oldTarget y.nf ≫ appendTail D Sc x)) = _
    rw [one_mul, ← appendElt_replaceOld, ht, TensorProduct.smul_tmul',
      koszulSign_smul (R := k), mul_comm q]

/-- Extracting an arbitrary old coefficient followed by a prescribed moving tail. -/
theorem appendAffineEquiv_insert_tail {i : I} {v w : List I} (x : AppendIdx i v w)
    (r : hom D Sc cutoff v x.oldTarget) :
    appendAffineEquiv D Sc cutoff i v w
      (rightContext D Sc cutoff [i] v x.oldTarget r ≫
        ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
          appendTail D Sc x : hom D Sc cutoff (x.oldTarget ++ [i]) w)) =
      appendTailCoefficients D cutoff x (oldAffineEquiv D Sc cutoff v x.oldTarget r) := by
  obtain ⟨f, rfl⟩ := (oldAffineEquiv D Sc cutoff v x.oldTarget).symm.surjective r
  induction f using Finsupp.induction_linear with
  | zero => simp only [map_zero, Limits.zero_comp]
  | add f g hf hg => simp only [map_add, Preadditive.add_comp, hf, hg]
  | single y a =>
    rw [oldAffineEquiv_symm_single, append_insert_nf_tail]
    rw [← appendAffineEquiv_symm_single, LinearEquiv.apply_symm_apply]
    rw [← oldAffineEquiv_symm_single, LinearEquiv.apply_symm_apply]
    simp only [appendTailCoefficients, Finsupp.lsum_single, LinearMap.comp_apply,
      Finsupp.lsingle_apply]

/-- Restrict the existing PBW coordinates to one moving tail and regroup the old basis.
The normalization includes total old-Hom parity, not merely coefficient parity. -/
def appendExtractOld (p : ZMod 2) {i : I} {v w : List I} (x : AppendIdx i v w) :
    hom D Sc cutoff (v ++ [i]) w →ₗ[k] hom D Sc cutoff v x.oldTarget :=
  (twist k p).comp ((oldAffineEquiv D Sc cutoff v x.oldTarget).symm.toLinearMap.comp
    ((Finsupp.mapRange.linearMap (coefficientTwist D cutoff (appendTailParity D x))).comp
      ((Finsupp.lcomapDomain x.replaceOld x.replaceOld_injective).comp
        (appendAffineEquiv D Sc cutoff i v w).toLinearMap)))

/-- Actual extraction recovers an arbitrary old Hom coefficient, with its total twist. -/
theorem appendExtractOld_insert_tail (p : ZMod 2) {i : I} {v w : List I}
    (x : AppendIdx i v w) (r : hom D Sc cutoff v x.oldTarget) :
    appendExtractOld D Sc cutoff p x
      (rightContext D Sc cutoff [i] v x.oldTarget r ≫
        ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
          appendTail D Sc x : hom D Sc cutoff (x.oldTarget ++ [i]) w)) = twist k p r := by
  unfold appendExtractOld
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [appendAffineEquiv_insert_tail]
  have hc (f : NFIdx v x.oldTarget →₀ SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
      Finsupp.mapRange.linearMap (coefficientTwist D cutoff (appendTailParity D x))
        (Finsupp.lcomapDomain (R := k) x.replaceOld x.replaceOld_injective
          (appendTailCoefficients D cutoff x f)) = f := by
    induction f using Finsupp.induction_linear with
    | zero => simp only [map_zero]
    | add f g hf hg => simp only [map_add, hf, hg]
    | single y a =>
      simp only [appendTailCoefficients, Finsupp.lsum_single, LinearMap.comp_apply,
        Finsupp.lsingle_apply, Finsupp.lcomapDomain_apply,
        Finsupp.comapDomain_single,
        Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single]
      congr 1
      exact twist_twist _ _
  rw [hc, LinearEquiv.symm_apply_apply]

/-- A genuine old-quotient coordinate, obtained from the affine extraction. -/
def appendExtractOldQuotient (p : ZMod 2) {i : I} {v w : List I}
    (x : AppendIdx i v w) :
    hom D Sc cutoff (v ++ [i]) w →ₗ[k] Old D Sc cutoff v x.oldTarget :=
  (ideal D Sc cutoff v x.oldTarget).mkQ.comp (appendExtractOld D Sc cutoff p x)

@[simp] theorem appendExtractOldQuotient_insert_tail (p : ZMod 2)
    {i : I} {v w : List I} (x : AppendIdx i v w) (r : hom D Sc cutoff v x.oldTarget) :
    appendExtractOldQuotient D Sc cutoff p x
      (rightContext D Sc cutoff [i] v x.oldTarget r ≫
        ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
          appendTail D Sc x : hom D Sc cutoff (x.oldTarget ++ [i]) w)) =
      (ideal D Sc cutoff v x.oldTarget).mkQ (twist k p r) := by
  exact congrArg (ideal D Sc cutoff v x.oldTarget).mkQ
    (appendExtractOld_insert_tail D Sc cutoff p x r)

/-- On a fixed tail, the vanishing coordinate is exactly the old ideal. -/
theorem appendExtractOldQuotient_insert_tail_eq_zero_iff (p : ZMod 2)
    {i : I} {v w : List I} (x : AppendIdx i v w) (r : hom D Sc cutoff v x.oldTarget) :
    appendExtractOldQuotient D Sc cutoff p x
      (rightContext D Sc cutoff [i] v x.oldTarget r ≫
        ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
          appendTail D Sc x : hom D Sc cutoff (x.oldTarget ++ [i]) w)) = 0 ↔
      r ∈ ideal D Sc cutoff v x.oldTarget := by
  rw [appendExtractOldQuotient_insert_tail, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero]
  constructor
  · intro hr
    simpa only [twist_twist] using twist_ideal D Sc cutoff p hr
  · exact twist_ideal D Sc cutoff p

end ELVOld
end OddMath.QuiverHecke
end

end

section

/-!
# Cross-tail ELV extraction

The off-tail step of `ELVAppendCoordinates.md`, needed for the old-only
coordinate comparison in `DeformedGlobalQP.md` §1. The existing `AppendIdx`
is regrouped by moving exponent and shuffle, with both index inverse laws.
`appendExtractOld_insert_off_tail` proves vanishing on every different tail,
for arbitrary full-ELV old coefficients and total parity. No finite-colour
hypothesis, flatness, or independence assumption is added.

The index equivalence is not yet an old-quotient coordinate equivalence.
Vanishing on all old-only relation generators, simultaneous quotient inversion,
and the moving-square shift and cancellation remain open.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
open scoped TensorProduct Classical
namespace OddMath.QuiverHecke
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

namespace AppendIdx
variable {i : I} {v w : List I}
/-- The moving exponent and inverse-shuffle index, without the old normal form. -/
def tailKey (x : AppendIdx i v w) : ℕ × AppendShuffle (appendLen v i) :=
  (x.1.1, x.1.2.2.2)

@[simp] theorem tailKey_replaceOld (x : AppendIdx i v w) (y : NFIdx v x.oldTarget) :
    (x.replaceOld y).tailKey = x.tailKey := rfl

/-- Different moving tails have disjoint sets of old normal-form replacements. -/
theorem replaceOld_ne_of_tailKey_ne (x z : AppendIdx i v w)
    (h : x.tailKey ≠ z.tailKey) (y : NFIdx v x.oldTarget) (b : NFIdx v z.oldTarget) :
    x.replaceOld y ≠ z.replaceOld b := by
  intro he
  exact h (show (x.replaceOld y).tailKey = (z.replaceOld b).tailKey from congrArg tailKey he)

/-- The target word and shuffle recover the intermediate old target uniquely. -/
theorem oldTarget_eq_of_tailKey_eq (x z : AppendIdx i v w)
    (h : x.tailKey = z.tailKey) : x.oldTarget = z.oldTarget := by
  have hd : x.1.2.2.2 = z.1.2.2.2 :=
    congrArg (fun a : ℕ × AppendShuffle (appendLen v i) => a.2) h
  have he := x.moving_target.trans z.moving_target.symm
  rw [hd] at he
  have hs : (x.oldTarget ++ [i]).length = (v ++ [i]).length := by
    simp [oldTarget]
  have ht : (z.oldTarget ++ [i]).length = (v ++ [i]).length := by
    simp [oldTarget]
  have hh : x.oldTarget ++ [i] = z.oldTarget ++ [i] := by
    refine List.ext_getElem (hs.trans ht.symm) fun a ha hb => ?_
    let q : Fin (v ++ [i]).length :=
      Categorification.TypeA.wordProd (v ++ [i]).length
        (Categorification.TypeA.canWord (v ++ [i]).length z.1.2.2.2.1⁻¹)
        ⟨a, by omega⟩
    have hc := List.getElem_of_eq he (i := q.val) (by simpa only [length_tgt, hs] using q.isLt)
    rw [tgt_cw_getElem (Categorification.TypeA.validWord_canWord _ _) hs q,
      tgt_cw_getElem (Categorification.TypeA.validWord_canWord _ _) ht q] at hc
    simpa [q] using hc
  exact List.append_cancel_right hh

/-- Moving tails that occur in the existing append basis, forgetting the old index. -/
def Tail (i : I) (v w : List I) : Type :=
  ↥(Set.range (tailKey (i := i) (v := v) (w := w)))

namespace Tail
/-- Choose an existing append index over a tail; no new basis is chosen. -/
def representative (q : Tail i v w) : AppendIdx i v w := q.property.choose

@[simp] theorem representative_tailKey (q : Tail i v w) :
    q.representative.tailKey = q.val := q.property.choose_spec
end Tail

end AppendIdx
namespace ELVOld

/-- Off-tail restriction vanishes before either parity normalization. -/
theorem appendTailCoefficients_comap_off_tail {i : I} {v w : List I}
    (x z : AppendIdx i v w) (h : x.tailKey ≠ z.tailKey)
    (f : NFIdx v z.oldTarget →₀ SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
    Finsupp.lcomapDomain (R := k) x.replaceOld x.replaceOld_injective
      (appendTailCoefficients D cutoff z f) = 0 := by
  induction f using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add f g hf hg => simp only [map_add, hf, hg, add_zero]
  | single y a =>
    simp only [appendTailCoefficients, Finsupp.lsum_single, LinearMap.comp_apply,
      Finsupp.lsingle_apply]
    ext b
    simp only [Finsupp.lcomapDomain_apply, Finsupp.comapDomain_apply, Finsupp.zero_apply]
    exact Finsupp.single_eq_of_ne (x.replaceOld_ne_of_tailKey_ne z h b y)

/-- Every old coefficient on a different moving tail extracts to zero. -/
theorem appendExtractOld_insert_off_tail (p : ZMod 2) {i : I} {v w : List I}
    (x z : AppendIdx i v w) (h : x.tailKey ≠ z.tailKey)
    (r : hom D Sc cutoff v z.oldTarget) :
    appendExtractOld D Sc cutoff p x
      (rightContext D Sc cutoff [i] v z.oldTarget r ≫
        ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
          appendTail D Sc z : hom D Sc cutoff (z.oldTarget ++ [i]) w)) = 0 := by
  unfold appendExtractOld
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [appendAffineEquiv_insert_tail, appendTailCoefficients_comap_off_tail D cutoff x z h]
  simp only [map_zero]

/-- Off-tail extraction also vanishes in the old cyclotomic quotient. -/
theorem appendExtractOldQuotient_insert_off_tail (p : ZMod 2) {i : I} {v w : List I}
    (x z : AppendIdx i v w) (h : x.tailKey ≠ z.tailKey)
    (r : hom D Sc cutoff v z.oldTarget) :
    appendExtractOldQuotient D Sc cutoff p x
      (rightContext D Sc cutoff [i] v z.oldTarget r ≫
        ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
          appendTail D Sc z : hom D Sc cutoff (z.oldTarget ++ [i]) w)) = 0 := by
  change (ideal D Sc cutoff v x.oldTarget).mkQ
    (appendExtractOld D Sc cutoff p x _) = 0
  rw [appendExtractOld_insert_off_tail D Sc cutoff p x z h, map_zero]
end ELVOld
end OddMath.QuiverHecke
end

end

section

/-!
# Descent of ELV append extraction through all old relations

The old-only coordinate comparison needed by `DeformedGlobalQP.md` §1.
Cross-source rebasing retains the prescribed moving tail. A normal-form index
is selected only from a nonzero old Hom, so empty old Hom spaces are allowed.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
open scoped TensorProduct DirectSum Classical
namespace OddMath.QuiverHecke
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

namespace AppendIdx
variable {i : I} {v s w : List I}

private def shuffleTransport {n m n' m' : ℕ} (h : n + 1 = m)
    (h' : n' + 1 = m') (e : n = n') (d : AppendShuffle h) : AppendShuffle h' := by
  subst n'; subst m; subst m'; exact d

private theorem shuffle_word_transport {n m n' m' : ℕ} (h : n + 1 = m)
    (h' : n' + 1 = m') (e : n = n') (d : AppendShuffle h) :
    Categorification.TypeA.canWord m' (shuffleTransport h h' e d).1⁻¹ =
      Categorification.TypeA.canWord m d.1⁻¹ := by
  subst n'; subst m; subst m'; rfl

/-- Rebase a moving tail to another source using an actual old normal form. -/
def rebase (z : AppendIdx i s w) (y : NFIdx v z.oldTarget) : AppendIdx i v w := by
  have hl : v.length = s.length := by
    have hh := congrArg List.length y.tgt_cw
    simpa only [length_tgt, oldTarget] using hh
  refine ⟨(z.1.1, y.1.1, y.1.2, shuffleTransport (appendLen s i) (appendLen v i) hl.symm z.1.2.2.2), y.2.1, y.2.2.1, ?_⟩
  have he := tgt_append_right [i] (t := v)
    (fits_cw (Categorification.TypeA.validWord_canWord v.length y.1.2))
  simp only [appendCrossingWord, cw_append, tgt_append, he, y.tgt_cw]
  rw [shuffle_word_transport]
  exact z.moving_target

 theorem rebase_target (z : AppendIdx i s w) (y : NFIdx v z.oldTarget) :
    (z.rebase y).oldTarget = z.oldTarget := y.tgt_cw

end AppendIdx
namespace ELVOld

private theorem tail_cl_heq {a b w : List I} {L M : List PG}
    (hab : a = b) (hLM : L = M) (ha : SChain a (pl a L) w)
    (hb : SChain b (pl b M) w) : HEq (cl D Sc a w L ha) (cl D Sc b w M hb) := by
  subst b
  subst M
  rfl

/-- Rebasing changes only the old index, not the positioned moving diagram. -/
theorem appendTail_rebase {i : I} {v s w : List I} (z : AppendIdx i s w)
    (y : NFIdx v z.oldTarget) :
    HEq (appendTail D Sc (z.rebase y)) (appendTail D Sc z) := by
  apply tail_cl_heq
  · exact congrArg (fun t => t ++ [i]) (z.rebase_target y)
  · dsimp only [AppendIdx.rebase]
    have hl : v.length = s.length := by
      have hh := congrArg List.length y.tgt_cw
      simpa only [length_tgt, AppendIdx.oldTarget] using hh
    rw [AppendIdx.shuffle_word_transport, hl]

/-- Equal moving keys give the same positioned tail, including its source. -/
theorem appendTail_heq_of_tailKey_eq {i : I} {v w : List I}
    (x z : AppendIdx i v w) (h : x.tailKey = z.tailKey) :
    HEq (appendTail D Sc x) (appendTail D Sc z) := by
  apply tail_cl_heq
  · exact congrArg (fun t => t ++ [i]) (x.oldTarget_eq_of_tailKey_eq z h)
  · have hn := congrArg Prod.fst h
    have hd := congrArg Prod.snd h
    change x.1.1 = z.1.1 at hn
    change x.1.2.2.2 = z.1.2.2.2 at hd
    rw [hn, hd]

private theorem insert_tail_transport {i : I} {v t t' w : List I}
    (e : t = t') (r : hom D Sc cutoff v t)
    (f : (pres D Sc).obj (ob D (t ++ [i])) ⟶ (pres D Sc).obj (ob D w))
    (g : (pres D Sc).obj (ob D (t' ++ [i])) ⟶ (pres D Sc).obj (ob D w))
    (h : HEq f g) :
    rightContext D Sc cutoff [i] v t r ≫
      ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] f :
        hom D Sc cutoff (t ++ [i]) w) =
    rightContext D Sc cutoff [i] v t' (e ▸ r) ≫
      ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] g :
        hom D Sc cutoff (t' ++ [i]) w) := by
  subst t'
  cases h
  rfl

/-- Old ideal coefficients vanish at every moving coordinate. -/
theorem appendExtractOldQuotient_insert_ideal_tail (p : ZMod 2)
    {i : I} {v w : List I} (x z : AppendIdx i v w)
    (r : hom D Sc cutoff v z.oldTarget) (hr : r ∈ ideal D Sc cutoff v z.oldTarget) :
    appendExtractOldQuotient D Sc cutoff p x
      (rightContext D Sc cutoff [i] v z.oldTarget r ≫
        ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
          appendTail D Sc z : hom D Sc cutoff (z.oldTarget ++ [i]) w)) = 0 := by
  by_cases h : x.tailKey = z.tailKey
  · have ht := z.oldTarget_eq_of_tailKey_eq x h.symm
    rw [insert_tail_transport D Sc cutoff ht r _ _
      (appendTail_heq_of_tailKey_eq D Sc z x h.symm)]
    apply (appendExtractOldQuotient_insert_tail_eq_zero_iff D Sc cutoff p x _).mpr
    exact (show ∀ {t t' : List I} (e : t = t') (a : hom D Sc cutoff v t),
      a ∈ ideal D Sc cutoff v t → (e ▸ a) ∈ ideal D Sc cutoff v t' from
        by intro t t' e; subst t'; exact fun _ ha => ha) ht r hr
  · exact appendExtractOldQuotient_insert_off_tail D Sc cutoff p x z h r

/-- Cross-source old ideal coefficients vanish, without an inhabitation assumption on old Homs. -/
theorem appendExtractOldQuotient_insert_ideal_cross_source (p : ZMod 2)
    {i : I} {v s w : List I} (x : AppendIdx i v w) (z : AppendIdx i s w)
    (r : hom D Sc cutoff v z.oldTarget) (hr : r ∈ ideal D Sc cutoff v z.oldTarget) :
    appendExtractOldQuotient D Sc cutoff p x
      (rightContext D Sc cutoff [i] v z.oldTarget r ≫
        ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
          appendTail D Sc z : hom D Sc cutoff (z.oldTarget ++ [i]) w)) = 0 := by
  by_cases hz : r = 0
  · simp only [hz, map_zero, Limits.zero_comp]
  · obtain ⟨y⟩ := exists_oldIndex_of_ne_zero D Sc cutoff r hz
    have ht := (z.rebase_target y).symm
    rw [insert_tail_transport D Sc cutoff ht r _ _ (appendTail_rebase D Sc z y).symm]
    apply appendExtractOldQuotient_insert_ideal_tail
    exact (show ∀ {t t' : List I} (e : t = t') (a : hom D Sc cutoff v t),
      a ∈ ideal D Sc cutoff v t → (e ▸ a) ∈ ideal D Sc cutoff v t' from
        by intro t t' e; subst t'; exact fun _ ha => ha) ht r hr

/-- Every old-only generator has zero extracted old quotient coordinate, for arbitrary continuation. -/
theorem appendExtractOldQuotient_old_generator (p : ZMod 2)
    {i : I} {v s w : List I} (x : AppendIdx i v w)
    (r : hom D Sc cutoff v s) (hr : r ∈ ideal D Sc cutoff v s)
    (h : hom D Sc cutoff (s ++ [i]) w) :
    appendExtractOldQuotient D Sc cutoff p x (rightContext D Sc cutoff [i] v s r ≫ h) = 0 := by
  obtain ⟨f, rfl⟩ := (appendAffineEquiv D Sc cutoff i s w).symm.surjective h
  induction f using Finsupp.induction_linear with
  | zero => simp only [map_zero, Limits.comp_zero]
  | add f g hf hg => simp only [map_add, Preadditive.comp_add, hf, hg, add_zero]
  | single z a =>
    rw [appendAffineEquiv_symm_single, ← append_insert_twisted_coefficient D Sc cutoff z a,
      ← Category.assoc, ← rightContext_comp]
    exact appendExtractOldQuotient_insert_ideal_cross_source D Sc cutoff p x z _
      (ideal_comp D Sc cutoff hr _)

/-- Extraction kills the entire old-only relation span, not just prescribed-source tails. -/
theorem appendExtractOldQuotient_relations (p : ZMod 2)
    {i : I} {v w : List I} (x : AppendIdx i v w) :
    appendRelations D Sc cutoff i v w ≤ LinearMap.ker (appendExtractOldQuotient D Sc cutoff p x) := by
  apply Submodule.span_le.mpr
  rintro f ⟨s, r, hr, h, rfl⟩
  exact appendExtractOldQuotient_old_generator D Sc cutoff p x r hr h

/-- An actual old quotient coordinate on the old-only target. -/
def appendOldCoordinate (p : ZMod 2) {i : I} {v w : List I} (x : AppendIdx i v w) :
    AppendTarget D Sc cutoff i v w →ₗ[k] Old D Sc cutoff v x.oldTarget :=
  (appendRelations D Sc cutoff i v w).liftQ (appendExtractOldQuotient D Sc cutoff p x)
    (appendExtractOldQuotient_relations D Sc cutoff p x)

@[simp] theorem appendOldCoordinate_projection (p : ZMod 2)
    {i : I} {v w : List I} (x : AppendIdx i v w) (h : hom D Sc cutoff (v ++ [i]) w) :
    appendOldCoordinate D Sc cutoff p x (appendProjection D Sc cutoff i v w h) =
      appendExtractOldQuotient D Sc cutoff p x h := rfl

/-- Simultaneous old quotient coefficients, with finite support in the existing moving tails. -/
abbrev AppendOldCoordinates (i : I) (v w : List I) :=
  ⨁ (q : AppendIdx.Tail i v w), Old D Sc cutoff v q.representative.oldTarget

/-- Signed old quotient coefficient followed by an append continuation. -/
def appendPair (p : ZMod 2) (i : I) {v t w : List I}
    (h : hom D Sc cutoff (t ++ [i]) w) :
    Old D Sc cutoff v t →ₗ[k] AppendTarget D Sc cutoff i v w :=
  (ideal D Sc cutoff v t).liftQ
    ((appendProjection D Sc cutoff i v w).comp
      ((Linear.rightComp k _ h).comp ((rightContext D Sc cutoff [i] v t).comp (twist k p))))
    (fun _ hr => appendProjection_old_ideal D Sc cutoff i (twist_ideal D Sc cutoff p hr) h)

@[simp] theorem appendPair_mk (p : ZMod 2) (i : I) {v t w : List I}
    (h : hom D Sc cutoff (t ++ [i]) w) (b : hom D Sc cutoff v t) :
    appendPair D Sc cutoff p i h ((ideal D Sc cutoff v t).mkQ b) =
      appendProjection D Sc cutoff i v w
        (rightContext D Sc cutoff [i] v t (twist k p b) ≫ h) := rfl

/-- Reconstruct the old-only target from all moving-tail old quotient coefficients. -/
def appendOldReconstruct (p : ZMod 2) (i : I) (v w : List I) :
    AppendOldCoordinates D Sc cutoff i v w →ₗ[k] AppendTarget D Sc cutoff i v w :=
  DirectSum.toModule k _ _ fun q => appendPair D Sc cutoff p i
    ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
      appendTail D Sc q.representative)

/-- Reconstruction followed by extraction is the specified direct-sum component. -/
theorem appendOldCoordinate_reconstruct (p : ZMod 2) {i : I} {v w : List I}
    (q : AppendIdx.Tail i v w) (f : AppendOldCoordinates D Sc cutoff i v w) :
    appendOldCoordinate D Sc cutoff p q.representative
      (appendOldReconstruct D Sc cutoff p i v w f) = f q := by
  induction f using DirectSum.induction_on with
  | zero => simp only [map_zero, DFinsupp.zero_apply]
  | add f g hf hg => simp only [map_add, hf, hg, DirectSum.add_apply]
  | of t a =>
    change appendOldCoordinate D Sc cutoff p q.representative
      (appendOldReconstruct D Sc cutoff p i v w (DirectSum.lof k _ _ t a)) = _
    rw [appendOldReconstruct, DirectSum.toModule_lof]
    obtain ⟨r, rfl⟩ := (ideal D Sc cutoff v t.representative.oldTarget).mkQ_surjective a
    rw [appendPair_mk, appendOldCoordinate_projection]
    by_cases ht : t = q
    · subst t
      rw [appendExtractOldQuotient_insert_tail, twist_twist, DirectSum.of_eq_same]
    · rw [appendExtractOldQuotient_insert_off_tail]
      · symm
        exact DirectSum.of_eq_of_ne _ _ _ (Ne.symm ht)
      · intro h
        apply ht
        apply Subtype.ext
        exact t.representative_tailKey.symm.trans (h.symm.trans q.representative_tailKey)

/-- Simultaneous old quotient reconstruction is injective. -/
theorem appendOldReconstruct_injective (p : ZMod 2) (i : I) (v w : List I) :
    Function.Injective (appendOldReconstruct D Sc cutoff p i v w) := by
  intro f g h
  apply DFinsupp.ext
  intro q
  rw [← appendOldCoordinate_reconstruct D Sc cutoff p q f,
    ← appendOldCoordinate_reconstruct D Sc cutoff p q g, h]

private theorem appendOldReconstruct_range_tail (p : ZMod 2)
    {i : I} {v w : List I} (x : AppendIdx i v w) (r : hom D Sc cutoff v x.oldTarget) :
    appendProjection D Sc cutoff i v w
      (rightContext D Sc cutoff [i] v x.oldTarget r ≫
        ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
          appendTail D Sc x : hom D Sc cutoff (x.oldTarget ++ [i]) w)) ∈
      LinearMap.range (appendOldReconstruct D Sc cutoff p i v w) := by
  let q : AppendIdx.Tail i v w := ⟨x.tailKey, x, rfl⟩
  have hk : x.tailKey = q.representative.tailKey := q.representative_tailKey.symm
  have ht := x.oldTarget_eq_of_tailKey_eq q.representative hk
  refine ⟨DirectSum.lof k _ _ q
    ((ideal D Sc cutoff v q.representative.oldTarget).mkQ (twist k p (ht ▸ r))), ?_⟩
  rw [appendOldReconstruct, DirectSum.toModule_lof, appendPair_mk, twist_twist]
  exact congrArg (appendProjection D Sc cutoff i v w)
    (insert_tail_transport D Sc cutoff ht r _ _
      (appendTail_heq_of_tailKey_eq D Sc x q.representative hk)).symm

/-- Every old-only class has finite simultaneous old quotient coordinates. -/
theorem appendOldReconstruct_surjective (p : ZMod 2) (i : I) (v w : List I) :
    Function.Surjective (appendOldReconstruct D Sc cutoff p i v w) := by
  intro z
  obtain ⟨h, rfl⟩ := appendProjection_surjective D Sc cutoff i v w z
  obtain ⟨f, rfl⟩ := (appendAffineEquiv D Sc cutoff i v w).symm.surjective h
  change appendProjection D Sc cutoff i v w ((appendAffineEquiv D Sc cutoff i v w).symm f) ∈
    LinearMap.range (appendOldReconstruct D Sc cutoff p i v w)
  induction f using Finsupp.induction_linear with
  | zero => simp only [map_zero]; exact Submodule.zero_mem _
  | add f g hf hg => simp only [map_add]; exact Submodule.add_mem _ hf hg
  | single x a =>
    rw [appendAffineEquiv_symm_single, ← append_insert_twisted_coefficient D Sc cutoff x a]
    exact appendOldReconstruct_range_tail D Sc cutoff p x _

/-- The full ELV old-only quotient is the direct sum of old quotient Hom coordinates.
No flatness, finite-colour assumption, or moving cyclotomic relation is imposed. -/
def appendOldCoordinateEquiv (p : ZMod 2) (i : I) (v w : List I) :
    AppendTarget D Sc cutoff i v w ≃ₗ[k] AppendOldCoordinates D Sc cutoff i v w :=
  (LinearEquiv.ofBijective (appendOldReconstruct D Sc cutoff p i v w)
    ⟨appendOldReconstruct_injective D Sc cutoff p i v w,
      appendOldReconstruct_surjective D Sc cutoff p i v w⟩).symm

@[simp] theorem appendOldCoordinateEquiv_apply (p : ZMod 2) {i : I} {v w : List I}
    (z : AppendTarget D Sc cutoff i v w) (q : AppendIdx.Tail i v w) :
    appendOldCoordinateEquiv D Sc cutoff p i v w z q =
      appendOldCoordinate D Sc cutoff p q.representative z := by
  rw [← appendOldCoordinate_reconstruct D Sc cutoff p q]
  exact congrArg (appendOldCoordinate D Sc cutoff p q.representative)
    ((appendOldCoordinateEquiv D Sc cutoff p i v w).symm_apply_apply z)

/-- Reconstruction is the left inverse of simultaneous extraction. -/
@[simp] theorem appendOldReconstruct_coordinateEquiv (p : ZMod 2) (i : I) (v w : List I)
    (z : AppendTarget D Sc cutoff i v w) :
    appendOldReconstruct D Sc cutoff p i v w
      (appendOldCoordinateEquiv D Sc cutoff p i v w z) = z :=
  (appendOldCoordinateEquiv D Sc cutoff p i v w).symm_apply_apply z

/-- Reconstruction is the right inverse of simultaneous extraction as well. -/
@[simp] theorem appendOldCoordinateEquiv_reconstruct (p : ZMod 2) (i : I) (v w : List I)
    (f : AppendOldCoordinates D Sc cutoff i v w) :
    appendOldCoordinateEquiv D Sc cutoff p i v w
      (appendOldReconstruct D Sc cutoff p i v w f) = f :=
  (appendOldCoordinateEquiv D Sc cutoff p i v w).apply_symm_apply f

end ELVOld
end OddMath.QuiverHecke
end

end

section

/-!
# Append moving-power reduction with an old Hom continuation

A supporting slice for finite append-shuffle spanning in the all-content
reservoir argument. The bounded powers are placed at the source, before the
old Hom. Thus the old endomorphisms supplied by the monic recurrence compose
with that Hom without commuting exterior coefficients.

The finite supremum of ranges below is a finite submodule sum; its indices are
crossing skeletons and powers strictly below the concrete monic degree.
-/

noncomputable section
open CategoryTheory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I L k : Type u} [AddCommGroup L] [CommRing k]
  (D : SKM.Datum I L) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The source-positioned moving power, in the full coefficient category. -/
def appendSourcePower (i : I) (v : List I) (n : ℕ) :
    End (obj D Sc cutoff (v ++ [i])) :=
  (affineUnitEndHom D Sc cutoff (v ++ [i])
    (dotE D Sc (v ++ [i]) v.length)) ^ n

/-- Bounded powers followed by an arbitrary smaller old Hom and a fixed tail. -/
def boundedAppendContinuationSpan (N : ℕ) (i : I) (v t w : List I)
    (h : hom D Sc cutoff (t ++ [i]) w) :
    Submodule k (TruncatedOld D Sc cutoff N (v ++ [i]) w) :=
  Submodule.span k {z | ∃ j < (monicELVEndpointProduct D Sc cutoff i v).natDegree,
    ∃ r : hom D Sc cutoff v t,
      z = (truncatedIdeal D Sc cutoff N (v ++ [i]) w).mkQ
        (appendSourcePower D Sc cutoff i v j ≫
          rightContext D Sc cutoff [i] v t r ≫ h)}

/-- The concrete monic recurrence reduces powers even with an arbitrary old Hom
and continuation attached. This is not a generator-interface hypothesis. -/
theorem appendSourcePower_comp_mem_bounded (N : ℕ) (i : I)
    (v t w : List I) (n : ℕ) (r : hom D Sc cutoff v t)
    (h : hom D Sc cutoff (t ++ [i]) w) :
    (truncatedIdeal D Sc cutoff N (v ++ [i]) w).mkQ
      (appendSourcePower D Sc cutoff i v n ≫
        rightContext D Sc cutoff [i] v t r ≫ h) ∈
      boundedAppendContinuationSpan D Sc cutoff N i v t w h := by
  let F : Old D Sc cutoff (v ++ [i]) (v ++ [i]) →ₗ[k]
      TruncatedOld D Sc cutoff N (v ++ [i]) w :=
    (ideal D Sc cutoff (v ++ [i]) (v ++ [i])).liftQ
      (((truncatedIdeal D Sc cutoff N (v ++ [i]) w).mkQ).comp
        (Linear.rightComp k _ (rightContext D Sc cutoff [i] v t r ≫ h)))
      (by
        intro a ha
        exact (Submodule.Quotient.mk_eq_zero _).mpr
          (Submodule.mem_sup_left (ideal_comp D Sc cutoff ha _)))
  have hpow : (ideal D Sc cutoff (v ++ [i]) (v ++ [i])).mkQ
      (appendSourcePower D Sc cutoff i v n) ∈ _ :=
    movingDot_pow_mem_bounded_old_span D Sc cutoff i v n
  change F ((ideal D Sc cutoff (v ++ [i]) (v ++ [i])).mkQ
    (appendSourcePower D Sc cutoff i v n)) ∈ _
  generalize he : (ideal D Sc cutoff (v ++ [i]) (v ++ [i])).mkQ
    (appendSourcePower D Sc cutoff i v n) = z at *
  clear he
  induction hpow using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨a, j, hj, rfl⟩ := hz
    apply Submodule.subset_span
    refine ⟨j, hj, a ≫ r, ?_⟩
    change (truncatedIdeal D Sc cutoff N (v ++ [i]) w).mkQ
      ((rightContextEndHom D Sc cutoff i v a * appendSourcePower D Sc cutoff i v j) ≫
        (rightContext D Sc cutoff [i] v t r ≫ h)) = _
    simp only [End.mul_def, rightContextEndHom_apply, rightContext_comp, Category.assoc]
  | zero => simpa only [map_zero] using Submodule.zero_mem _
  | add a b _ _ ha hb => simpa only [map_add] using Submodule.add_mem _ ha hb
  | smul c a _ ha => simpa only [map_smul] using Submodule.smul_mem _ c ha

/-- The old Hom in each bounded continuation genuinely factors through its
coefficient-truncated quotient. -/
def appendBoundedOldMap (N : ℕ) (i : I) (v t w : List I) (j : ℕ)
    (h : hom D Sc cutoff (t ++ [i]) w) :
    TruncatedOld D Sc cutoff N v t →ₗ[k]
      TruncatedOld D Sc cutoff N (v ++ [i]) w :=
  (truncatedIdeal D Sc cutoff N v t).liftQ
    (((truncatedIdeal D Sc cutoff N (v ++ [i]) w).mkQ).comp
      ((Linear.leftComp k _ (appendSourcePower D Sc cutoff i v j)).comp
        ((Linear.rightComp k _ h).comp (rightContext D Sc cutoff [i] v t))))
    (by
      intro r hr
      exact (Submodule.Quotient.mk_eq_zero _).mpr
        (comp_truncatedIdeal D Sc cutoff N _
          (truncatedIdeal_comp D Sc cutoff N
            (truncatedIdeal_rightContext D Sc cutoff N [i] hr) h)))

@[simp] theorem appendBoundedOldMap_mk (N : ℕ) (i : I)
    (v t w : List I) (j : ℕ) (h : hom D Sc cutoff (t ++ [i]) w)
    (r : hom D Sc cutoff v t) :
    appendBoundedOldMap D Sc cutoff N i v t w j h
      ((truncatedIdeal D Sc cutoff N v t).mkQ r) =
      (truncatedIdeal D Sc cutoff N (v ++ [i]) w).mkQ
        (appendSourcePower D Sc cutoff i v j ≫
          rightContext D Sc cutoff [i] v t r ≫ h) := rfl

/-- A deliberately redundant finite indexing set for crossing-only append
continuations. Keeping the old permutation avoids any finite-colour assumption
or choice of representatives for possibly empty old Hom spaces. -/
def AppendCrossingSkeleton (i : I) (v w : List I) :=
  {p : Equiv.Perm (Fin v.length) × AppendShuffle (appendLen v i) //
    tgt (v ++ [i]) (cw (appendCrossingWord (appendLen v i) p)) = w}

instance appendCrossingSkeleton_finite (i : I) (v w : List I) :
    Finite (AppendCrossingSkeleton i v w) := by
  unfold AppendCrossingSkeleton
  infer_instance

/-- Realize a skeleton by an existing append index with zero moving and old dots. -/
def AppendCrossingSkeleton.index {i : I} {v w : List I}
    (q : AppendCrossingSkeleton i v w) : AppendIdx i v w :=
  ⟨(0, [], q.val), by simp, by simp, q.property⟩

/-- Every existing append basis term supplies one of the finite crossing skeletons. -/
def appendCrossingSkeleton {i : I} {v w : List I}
    (x : AppendIdx i v w) : AppendCrossingSkeleton i v w :=
  ⟨x.val.2.2, x.property.2.2⟩

@[simp] theorem appendCrossingSkeleton_oldTarget {i : I} {v w : List I}
    (x : AppendIdx i v w) :
    (appendCrossingSkeleton x).index.oldTarget = x.oldTarget := rfl

open StringDiagrams Supercategory MonoidalCategory
open scoped TensorProduct

theorem appendSourcePower_whisker (i : I) (v : List I) (n : ℕ) :
    appendSourcePower D Sc cutoff i v n =
      affineUnit D Sc cutoff (v ++ [i]) (v ++ [i]) ((pres D Sc).obj (ob D v) ◁ (dotE D Sc [i] 0 ^ n)) := by
  have he : (pres D Sc).obj (ob D v) ◁ (dotE D Sc [i] 0 ^ n) =
      dotE D Sc (v ++ [i]) v.length ^ n := by
    induction n with
    | zero => exact MonoidalSupercategory.whiskerLeft_id (R := k) _ _
    | succ n ih =>
      simp only [pow_succ, End.mul_def]
      exact (MonoidalSupercategory.whiskerLeft_comp (R := k)
        ((pres D Sc).obj (ob D v)) (dotE D Sc [i] 0) (dotE D Sc [i] 0 ^ n)).trans
          (congrArg₂ (fun f g => f ≫ g) (whiskerLeft_dotE D Sc v i rfl) ih)
  rw [he]
  exact (map_pow (affineUnitEndHom D Sc cutoff (v ++ [i])) _ n).symm

theorem appendTail_factor {i : I} {v w : List I} (x : AppendIdx i v w) :
    appendTail D Sc x =
      (dotE D Sc (x.oldTarget ++ [i]) x.oldTarget.length ^ x.val.1 : End _) ≫
        appendTail D Sc (appendCrossingSkeleton x).index := by
  have hl : x.oldTarget.length = v.length := by simp [AppendIdx.oldTarget]
  simp only [dotE_pow, appendTail, appendCrossingSkeleton_oldTarget]
  symm
  refine (cl_comp D Sc _ _ _ _).trans ?_
  apply cl_eq_cl
  simp only [appendCrossingSkeleton, AppendCrossingSkeleton.index, List.replicate_zero,
    List.map_nil, List.nil_append, List.map_replicate, hl]

theorem append_tail_normalize {i : I} {v w : List I} (x : AppendIdx i v w)
    (r : hom D Sc cutoff v x.oldTarget) :
    rightContext D Sc cutoff [i] v x.oldTarget r ≫
      affineUnit D Sc cutoff _ _ (appendTail D Sc x) =
    appendSourcePower D Sc cutoff i v x.val.1 ≫
      rightContext D Sc cutoff [i] v x.oldTarget
        (twist k (x.val.1 • D.parity i) r) ≫
      affineUnit D Sc cutoff _ _ (appendTail D Sc (appendCrossingSkeleton x).index) := by
  have hf := congrArg (affineUnit D Sc cutoff (x.oldTarget ++ [i]) w)
    (appendTail_factor D Sc x)
  have hc := affineUnit_comp D Sc cutoff
    (dotE D Sc (x.oldTarget ++ [i]) x.oldTarget.length ^ x.val.1)
    (appendTail D Sc (appendCrossingSkeleton x).index)
  rw [hf, hc]
  have hs := trailing_comp_rightContext D Sc cutoff (v := v) (w := x.oldTarget)
    (firstDot_pow_parity D Sc i [] x.val.1) (twist k (x.val.1 • D.parity i) r)
  rw [twist_twist, ← appendSourcePower_whisker, ← appendSourcePower_whisker] at hs
  have hp : affineUnit D Sc cutoff (x.oldTarget ++ [i]) (x.oldTarget ++ [i])
      (dotE D Sc (x.oldTarget ++ [i]) x.oldTarget.length ^ x.val.1) =
      appendSourcePower D Sc cutoff i x.oldTarget x.val.1 :=
    map_pow (affineUnitEndHom D Sc cutoff (x.oldTarget ++ [i])) _ x.val.1
  rw [hp, ← Category.assoc, ← hs, Category.assoc]

/-- The finite family of bounded powers and crossing-only append tails. -/
def appendFiniteRangeSpan (N : ℕ) (i : I) (v w : List I) :
    Submodule k (TruncatedOld D Sc cutoff N (v ++ [i]) w) :=
  ⨆ (q : AppendCrossingSkeleton i v w)
    (j : Fin (monicELVEndpointProduct D Sc cutoff i v).natDegree),
    LinearMap.range (appendBoundedOldMap D Sc cutoff N i v q.index.oldTarget w j.val
      (affineUnit D Sc cutoff _ _ (appendTail D Sc q.index)))

theorem append_tail_mem_finiteRangeSpan (N : ℕ) {i : I} {v w : List I}
    (x : AppendIdx i v w) (r : hom D Sc cutoff v x.oldTarget) :
    (truncatedIdeal D Sc cutoff N (v ++ [i]) w).mkQ
      (rightContext D Sc cutoff [i] v x.oldTarget r ≫
        affineUnit D Sc cutoff _ _ (appendTail D Sc x)) ∈
      appendFiniteRangeSpan D Sc cutoff N i v w := by
  rw [append_tail_normalize]
  apply (show boundedAppendContinuationSpan D Sc cutoff N i v x.oldTarget w
      (affineUnit D Sc cutoff _ _ (appendTail D Sc (appendCrossingSkeleton x).index)) ≤
      appendFiniteRangeSpan D Sc cutoff N i v w from ?_)
    (appendSourcePower_comp_mem_bounded D Sc cutoff N i v x.oldTarget w x.val.1 _ _)
  apply Submodule.span_le.mpr
  rintro z ⟨j, hj, r, rfl⟩
  apply Submodule.mem_iSup_of_mem (appendCrossingSkeleton x)
  apply Submodule.mem_iSup_of_mem (⟨j, hj⟩ : Fin _)
  exact ⟨(truncatedIdeal D Sc cutoff N v x.oldTarget).mkQ r, rfl⟩

/-- Concrete finite append shuffle spanning, with arbitrary full ELV coefficients. -/
theorem appendFiniteRangeSpan_eq_top (N : ℕ) (i : I) (v w : List I) :
    appendFiniteRangeSpan D Sc cutoff N i v w = ⊤ := by
  apply top_unique
  intro z hz
  clear hz
  obtain ⟨h, rfl⟩ := (truncatedIdeal D Sc cutoff N (v ++ [i]) w).mkQ_surjective z
  obtain ⟨f, rfl⟩ := (appendAffineEquiv D Sc cutoff i v w).symm.surjective h
  induction f using Finsupp.induction_linear with
  | zero => simp only [map_zero]; exact Submodule.zero_mem _
  | add f g hf hg => simp only [map_add]; exact Submodule.add_mem _ hf hg
  | single x a =>
    rw [appendAffineEquiv_symm_single, ← append_insert_twisted_coefficient D Sc cutoff x a]
    exact append_tail_mem_finiteRangeSpan D Sc cutoff N x _

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! Degree shifts of the finite append spanning maps. -/
noncomputable section
open CategoryTheory StringDiagrams MonoidalCategory
open scoped TensorProduct
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I L k : Type u} [AddCommGroup L] [CommRing k]
  (D : SKM.Datum I L) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous)

theorem affineUnit_mem_degree {v w : List I} {d : ℤ}
    {f : (pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D w)}
    (hf : f ∈ homDegree D sy Sc v w d) :
    affineUnit D Sc cutoff v w f ∈ elvHomDegree D sy Sc hc cutoff v w d := by
  let _ := elvCoefficientCategoryGrading (k := k) D sy cutoff
  let _ := gradedSupercategory D sy Sc hc
  have h := BoxProd.tmulHom_mem_degree (X := obj D Sc cutoff v)
    (Y := obj D Sc cutoff w)
    (GradedSupercategory.id_mem_degree (R := k) (obj D Sc cutoff v).fst) hf
  rw [zero_add] at h
  exact h

theorem appendSourcePower_mem_degree (i : I) (v : List I) (n : ℕ) :
    appendSourcePower D Sc cutoff i v n ∈
      elvHomDegree D sy Sc hc cutoff (v ++ [i]) (v ++ [i]) (2 * sy.d i * n) := by
  rw [appendSourcePower_whisker]
  apply affineUnit_mem_degree D Sc cutoff sy hc
  let _ := gradedSupercategory D sy Sc hc
  let _ := gradedMonoidalSupercategory D sy Sc hc
  have h : (dotE D Sc [i] 0 ^ n : End _) ∈ homDegree D sy Sc [i] [i]
      (2 * sy.d i * n) := by
    simpa only [firstDotPower, dotE_pow, List.map_replicate] using
      firstDotPower_mem_gdeg D sy Sc i [] n
  exact GradedMonoidalSupercategory.whiskerLeft_mem_degree ((pres D Sc).obj (ob D v)) h

/-- Sum of the generator degrees of the concrete tail diagram. -/
def appendTailDegree {i : I} {v w : List I} (x : AppendIdx i v w) : ℤ :=
  gsum D sy (pl (x.oldTarget ++ [i])
    (((List.replicate x.1.1 v.length).map PG.dot) ++
      cw (Categorification.TypeA.canWord (v ++ [i]).length x.1.2.2.2.1⁻¹)))

theorem appendTail_mem_degree {i : I} {v w : List I} (x : AppendIdx i v w) :
    appendTail D Sc x ∈ homDegree D sy Sc (x.oldTarget ++ [i]) w
      (appendTailDegree D sy x) :=
  Presentation.diag_mem_homDeg' (degree_gdeg_mkD D sy _ _)

/-- The source moving dots, old homogeneous term, and tail contribute additively. -/
theorem appendBoundedOldMap_mem_degree (N : ℕ) (i : I) (v t w : List I)
    (j : ℕ) {h : hom D Sc cutoff (t ++ [i]) w} {a b : ℤ}
    (hh : h ∈ elvHomDegree D sy Sc hc cutoff (t ++ [i]) w b)
    {r : TruncatedOld D Sc cutoff N v t}
    (hr : r ∈ truncatedDegree D Sc cutoff sy hc N v t a) :
    appendBoundedOldMap D Sc cutoff N i v t w j h r ∈
      truncatedDegree D Sc cutoff sy hc N (v ++ [i]) w (2 * sy.d i * j + (a + b)) := by
  obtain ⟨r, hr, rfl⟩ := hr
  rw [appendBoundedOldMap_mk]
  apply Submodule.mem_map_of_mem
  let _ := elvHomGrading D sy Sc hc cutoff
  exact GradedSupercategory.comp_mem_degree
    (appendSourcePower_mem_degree D Sc cutoff sy hc i v j)
    (GradedSupercategory.comp_mem_degree
      (rightContext_mem_degree D Sc cutoff sy hc [i] hr) hh)

/-- A supported smaller quotient gives supported range, with the concrete shift. -/
theorem appendBoundedOldMap_range_le (N : ℕ) (i : I) (v t w : List I)
    (j : ℕ) {h : hom D Sc cutoff (t ++ [i]) w} {b : ℤ}
    (hh : h ∈ elvHomDegree D sy Sc hc cutoff (t ++ [i]) w b)
    (S : Set ℤ)
    (hS : (⊤ : Submodule k (TruncatedOld D Sc cutoff N v t)) =
      ⨆ a ∈ S, truncatedDegree D Sc cutoff sy hc N v t a) :
    LinearMap.range (appendBoundedOldMap D Sc cutoff N i v t w j h) ≤
      ⨆ a ∈ S, truncatedDegree D Sc cutoff sy hc N (v ++ [i]) w
        (2 * sy.d i * j + (a + b)) := by
  rw [← Submodule.map_top, hS, Submodule.map_iSup]
  apply iSup_le
  intro a
  rw [Submodule.map_iSup]
  apply iSup_le
  intro ha
  apply le_trans _ (le_iSup_of_le a (le_iSup_of_le ha le_rfl))
  rintro z ⟨r, hr, rfl⟩
  exact appendBoundedOldMap_mem_degree D Sc cutoff sy hc N i v t w j hh hr

/-- All-content support propagation from smaller truncated Hom support. The
indices are finite when each `S q` is finite; no finite-colour assumption occurs. -/
theorem appendFiniteRange_degree_support (N : ℕ) (i : I) (v w : List I)
    (S : AppendCrossingSkeleton i v w → Set ℤ)
    (hS : ∀ q, (⊤ : Submodule k (TruncatedOld D Sc cutoff N v q.index.oldTarget)) =
      ⨆ a ∈ S q, truncatedDegree D Sc cutoff sy hc N v q.index.oldTarget a) :
    (⊤ : Submodule k (TruncatedOld D Sc cutoff N (v ++ [i]) w)) =
      ⨆ (q : AppendCrossingSkeleton i v w)
        (j : Fin (monicELVEndpointProduct D Sc cutoff i v).natDegree)
        (a : ℤ) (_ : a ∈ S q),
        truncatedDegree D Sc cutoff sy hc N (v ++ [i]) w
          (2 * sy.d i * j.val + (a + appendTailDegree D sy q.index)) := by
  apply le_antisymm _ le_top
  rw [← appendFiniteRangeSpan_eq_top D Sc cutoff N i v w]
  unfold appendFiniteRangeSpan
  apply iSup_le
  intro q
  apply iSup_le
  intro j
  exact le_trans (appendBoundedOldMap_range_le D Sc cutoff sy hc N i v
    q.index.oldTarget w j.val
    (affineUnit_mem_degree D Sc cutoff sy hc (appendTail_mem_degree D Sc sy q.index))
    (S q) (hS q)) (le_iSup_of_le q (le_iSup_of_le j le_rfl))

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # Finite integer support at arbitrary strand content

The coefficient-weight-truncated vacuum and the finite homogeneous append
spanning family give finite degree support by induction on the source word.
No rank, freeness, or bound on the number of words of a weight is used.
-/
noncomputable section
open CategoryTheory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I L k : Type u} [AddCommGroup L] [CommRing k]
  (D : SKM.Datum I L) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous) (N : ℕ)

/-- Finite smaller degree supports propagate through the concrete finite append family. -/
theorem truncatedAppend_finite_support (i : I) (v w : List I)
    (ih : ∀ t : List I, ∃ S : Set ℤ, S.Finite ∧
      (⊤ : Submodule k (TruncatedOld D Sc cutoff N v t)) =
        ⨆ n ∈ S, truncatedDegree D Sc cutoff sy hc N v t n) :
    ∃ S : Set ℤ, S.Finite ∧
      (⊤ : Submodule k (TruncatedOld D Sc cutoff N (v ++ [i]) w)) =
        ⨆ n ∈ S, truncatedDegree D Sc cutoff sy hc N (v ++ [i]) w n := by
  classical
  choose S hfin hs using ih
  let T : Set ℤ := ⋃ (q : AppendCrossingSkeleton i v w),
    ⋃ (j : Fin (monicELVEndpointProduct D Sc cutoff i v).natDegree),
      (fun a => 2 * sy.d i * j.val + (a + appendTailDegree D sy q.index)) '' S q.index.oldTarget
  have ht : T.Finite := Set.finite_iUnion fun q => Set.finite_iUnion fun j =>
    (hfin q.index.oldTarget).image _
  refine ⟨T, ht, le_antisymm ?_ le_top⟩
  rw [appendFiniteRange_degree_support D Sc cutoff sy hc N i v w
    (fun q => S q.index.oldTarget) (fun q => hs q.index.oldTarget)]
  refine iSup_le fun q => iSup_le fun j => iSup_le fun a => iSup_le fun ha => ?_
  exact le_iSup_of_le _ (le_iSup_of_le
    (Set.mem_iUnion.mpr ⟨q, Set.mem_iUnion.mpr ⟨j, ⟨a, ha, rfl⟩⟩⟩ :
      2 * sy.d i * j.val + (a + appendTailDegree D sy q.index) ∈ T) le_rfl)

/-- Arbitrary content has finite support whenever the coefficient degrees have a
uniform degree/weight bound. This bound is obtained from finite colours below. -/
theorem truncatedContent_finite_support_of_bound (M : ℤ) (hM : 0 ≤ M)
    (hbound : ∀ a, SKM.SYM.coefficientDegree D sy a ≤ M * SKM.SYM.coefficientWeight D a)
    (v w : List I) :
    ∃ S : Set ℤ, S.Finite ∧
      (⊤ : Submodule k (TruncatedOld D Sc cutoff N v w)) =
        ⨆ n ∈ S, truncatedDegree D Sc cutoff sy hc N v w n := by
  induction v using List.reverseRecOn generalizing w with
  | nil => exact ⟨Set.Icc 0 (M * N), Set.finite_Icc _ _,
      truncatedVacuum_support_of_bound D Sc cutoff sy hc N M hM hbound w⟩
  | append_singleton v i ih =>
      exact truncatedAppend_finite_support D Sc cutoff sy hc N i v w ih

/-- Finite colours give bounded integer support for every pair of words, including
arbitrarily repeated even, odd, and mixed colours. -/
theorem truncatedContent_finite_support [Finite I] (v w : List I) :
    ∃ S : Set ℤ, S.Finite ∧
      (⊤ : Submodule k (TruncatedOld D Sc cutoff N v w)) =
        ⨆ n ∈ S, truncatedDegree D Sc cutoff sy hc N v w n := by
  obtain ⟨M, hM, hb⟩ := SKM.SYM.exists_coefficientDegree_bound D sy
  exact truncatedContent_finite_support_of_bound D Sc cutoff sy hc N M hM hb v w

/-- A finite homogeneous spanning support kills all other homogeneous parts. -/
theorem truncatedDegree_eq_bot_of_support (v w : List I) (S : Set ℤ)
    (hS : (⊤ : Submodule k (TruncatedOld D Sc cutoff N v w)) =
      ⨆ n ∈ S, truncatedDegree D Sc cutoff sy hc N v w n)
    (n : ℤ) (hn : n ∉ S) :
    truncatedDegree D Sc cutoff sy hc N v w n = ⊥ := by
  have hp : (⊤ : Submodule k (TruncatedOld D Sc cutoff N v w)) ≤
      LinearMap.ker (truncatedDproj D Sc cutoff sy hc N v w n) := by
    rw [hS]
    refine iSup_le fun a => iSup_le fun ha => ?_
    intro z hz
    exact (truncatedDproj_of_mem D Sc cutoff sy hc N hz n).trans
      (ite_eq_right (by intro he; exact hn (he ▸ ha)))
  apply bot_unique
  intro z hz
  have he := truncatedDproj_of_mem D Sc cutoff sy hc N hz n
  rw [ite_eq_left rfl, hp (Submodule.mem_top : z ∈ (⊤ : Submodule k _))] at he
  exact he.symm

/-- An explicit loose symmetric interval extracted from a finite support. -/
theorem truncatedContent_bounded_of_finite_support (v w : List I)
    (h : ∃ S : Set ℤ, S.Finite ∧
      (⊤ : Submodule k (TruncatedOld D Sc cutoff N v w)) =
        ⨆ n ∈ S, truncatedDegree D Sc cutoff sy hc N v w n) :
    ∃ B : ℕ, ∀ n : ℤ, (n < -(B : ℤ) ∨ (B : ℤ) < n) →
      truncatedDegree D Sc cutoff sy hc N v w n = ⊥ := by
  classical
  obtain ⟨S, hf, hs⟩ := h
  refine ⟨hf.toFinset.sup Int.natAbs, fun n hn =>
    truncatedDegree_eq_bot_of_support D Sc cutoff sy hc N v w S hs n ?_⟩
  intro hmem
  have hnat : n.natAbs ≤ hf.toFinset.sup Int.natAbs :=
    Finset.le_sup (f := Int.natAbs) (hf.mem_toFinset.mpr hmem)
  have habs : |n| ≤ ((hf.toFinset.sup Int.natAbs : ℕ) : ℤ) := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast hnat
  have := abs_le.mp habs
  omega

/-- Actual bounded integer support at arbitrary content, from the coefficient
bound and the concrete cyclotomic recurrence, not from a support premise. -/
theorem truncatedContent_bounded_of_bound (M : ℤ) (hM : 0 ≤ M)
    (hbound : ∀ a, SKM.SYM.coefficientDegree D sy a ≤ M * SKM.SYM.coefficientWeight D a)
    (v w : List I) :
    ∃ B : ℕ, ∀ n : ℤ, (n < -(B : ℤ) ∨ (B : ℤ) < n) →
      truncatedDegree D Sc cutoff sy hc N v w n = ⊥ :=
  truncatedContent_bounded_of_finite_support D Sc cutoff sy hc N v w
    (truncatedContent_finite_support_of_bound D Sc cutoff sy hc N M hM hbound v w)

/-- Every coefficient-weight-truncated cyclotomic Hom has bounded integer
support for finite colours, without any restriction on strand content. -/
theorem truncatedContent_bounded [Finite I] (v w : List I) :
    ∃ B : ℕ, ∀ n : ℤ, (n < -(B : ℤ) ∨ (B : ℤ) < n) →
      truncatedDegree D Sc cutoff sy hc N v w n = ⊥ :=
  truncatedContent_bounded_of_finite_support D Sc cutoff sy hc N v w
    (truncatedContent_finite_support D Sc cutoff sy hc N v w)

end OddMath.QuiverHecke.ELVOld
end

end
