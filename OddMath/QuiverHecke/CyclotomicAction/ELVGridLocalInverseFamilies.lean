import OddMath.QuiverHecke.CyclotomicAction.ELVGridLocalInverse
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionGridMatrixNaturality
import OddMath.SKM.AugmentedInverseNaturality
import OddMath.Algebra.HomogeneousSuperfunctorIso

/-! # Input-natural local inverses of induction-grid matrices

Brundan–Ellis (1.13)–(1.14): the prescribed even matrix isomorphisms
supply inverse entries on all input modules. Their signed naturality
follows from that of the given forward mate and dotted columns or rows.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
variable {k C A B : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (K : A ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
  {p : ZMod 2} {γ : ∀ s, (J ⋙ K).obj s ⟶ (J ⋙ K).obj s}
  (hγ : IsSupernatural k p γ)
  {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
  {β : ∀ s, K.obj s ⟶ K.obj s} (hβ : IsSupernatural k p β)

/-- The prescribed negative-crossing mate on every input module. -/
def gridMateTransformation :
    (⟨restriction J ⋙ induction J⟩ :
      Superfunctor k (Superfunctor k A (SVec k)) (Superfunctor k A (SVec k))) ⟶
    ⟨induction K ⋙ restriction K⟩ :=
  (orderedGridMateComponent_supernatural J K hγ).toSuperNatTrans

/-- The ordinary unit/dot column on every input module. -/
def gridUnitColumnTransformation (n : ℕ) :
    Superfunctor.id k (Superfunctor k A (SVec k)) ⟶
    (⟨induction K ⋙ restriction K⟩ :
      Superfunctor k (Superfunctor k A (SVec k)) (Superfunctor k A (SVec k))) :=
  (gridUnitDotColumn_supernatural K hβ n).toSuperNatTrans

/-- The ordinary dot/counit row on every input module. -/
def gridCapRowTransformation (n : ℕ) :
    (⟨restriction J ⋙ induction J⟩ :
      Superfunctor k (Superfunctor k A (SVec k)) (Superfunctor k A (SVec k))) ⟶
    Superfunctor.id k (Superfunctor k A (SVec k)) :=
  (gridCapDotRow_supernatural J hα n).toSuperNatTrans

/-- Evaluation retains the ordinary unit column, with no coordinate shift. -/
theorem gridUnitColumnTransformation_total (n : ℕ) (N : Superfunctor k A (SVec k)) :
    (gridUnitColumnTransformation K hβ n).total N = unitDotColumn K hβ N n :=
  OddMath.HomogeneousSuperfunctorIso.homogeneous_total
    (F := Superfunctor.id k (Superfunctor k A (SVec k)))
    (G := ⟨induction K ⋙ restriction K⟩) (gridUnitDotColumn_supernatural K hβ n) N

/-- Evaluation retains the prescribed ordinary cap row. -/
theorem gridCapRowTransformation_total (n : ℕ) (N : Superfunctor k A (SVec k)) :
    (gridCapRowTransformation J hα n).total N = capDotRow J hα N n :=
  OddMath.HomogeneousSuperfunctorIso.homogeneous_total
    (F := ⟨restriction J ⋙ induction J⟩)
    (G := Superfunctor.id k (Superfunctor k A (SVec k)))
    (gridCapDotRow_supernatural J hα n) N

/-- The chosen unit inverses bundle without a separate inverse-naturality
assumption. Entries outside the finite window are zero. -/
def gridLocalInverseFromFamily (m : ℕ)
    (e : ∀ N, OddMath.FiniteSupermodule.product (gridUnitMatrixFamily J p N m) ≅
      (restriction K).obj (induced K N))
    (he : ∀ N, (e N).hom = gridUnitMatrixModuleMap J K hγ hβ N m) :
    SKM.SuperSumInvFrom (k := k) (gridMateTransformation J K hγ)
      (gridUnitColumnTransformation K hβ) p (fun n => n • p) m :=
  SKM.SuperSumInvFrom.ofSupernaturalComponents
    (fun N => gridLocalInverseFrom J K hγ hβ N m (e N) (he N))
    (orderedGridMateComponent_supernatural J K hγ)
    (gridUnitDotColumn_supernatural K hβ)

/-- The chosen cap inverses bundle with all odd input signs retained. -/
def gridLocalInverseToFamily (m : ℕ)
    (e : ∀ N, induced J ((restriction J).obj N) ≅
      OddMath.FiniteSupermodule.product (gridCapMatrixFamily K p N m))
    (he : ∀ N, (e N).hom = gridCapMatrixModuleMap J K hγ hα N m) :
    SKM.SuperSumInvTo (k := k) (gridMateTransformation J K hγ)
      (gridCapRowTransformation J hα) p (fun n => n • p) m :=
  SKM.SuperSumInvTo.ofSupernaturalComponents
    (fun N => gridLocalInverseTo J K hγ hα N m (e N) (he N))
    (orderedGridMateComponent_supernatural J K hγ)
    (gridCapDotRow_supernatural J hα)

end OddMath.QuiverHecke.ELVOld.BalancedInduction
