import Mathlib.CategoryTheory.Adjunction.Unique
import OddMath.QuiverHecke.CyclotomicAction.ProbeMixed.ProbeContentReindex
import OddMath.QuiverHecke.CyclotomicAction.ProbeVacuumCharts.ProbeCanonicalContent

/-!
# Probe reindex mate

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # The chosen append adjunction under OLD content reindexing

Brundan–Ellis (1.12)–(1.14) at canonical content representatives: compare
the actual balanced append functors through certificate-only OLD reindexing.
The comparison is the unique left-adjoint comparison for the literal
restriction square. It is even and retains the specified units and counits.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
open ELV ELV.BalancedInduction
universe u

private theorem leftUniq_hom_eq
    {C A : Type*} [Category* C] [Category* A] {F F' : C ⥤ A} {G : A ⥤ C}
    (a : F ⊣ G) (b : F' ⊣ G) (N : C) :
    (a.leftAdjointUniq b).hom.app N = F.map (b.unit.app N) ≫ a.counit.app (F'.obj N) := by
  calc
    _ = (a.homEquiv _ _).symm (b.unit.app N) :=
      (Equiv.eq_symm_apply _).mpr (Adjunction.homEquiv_leftAdjointUniq_hom_app a b N)
    _ = _ := a.homEquiv_counit _ _ _

private theorem leftUniq_hom_mem
    {k : Type u} {C A : Type*} [CommRing k] [Category* C] [Category* A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    {F F' : C ⥤ A} {G : A ⥤ C} [F.Additive] [F.Linear k] [IsSuperfunctor k F]
    (a : F ⊣ G) (b : F' ⊣ G)
    (hu : ∀ N, b.unit.app N ∈ parity (R := k) _ _ 0)
    (hc : ∀ N, a.counit.app N ∈ parity (R := k) _ _ 0) (N : C) :
    (a.leftAdjointUniq b).hom.app N ∈ parity (R := k) _ _ 0 := by
  rw [leftUniq_hom_eq]
  exact comp_mem (Supercategory.map_mem F (hu N)) (hc (F'.obj N))

private theorem composite_unit_mem
    {k : Type u} {C A B : Type*} [CommRing k] [Category* C] [Category* A] [Category* B]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    [Preadditive B] [Linear k B] [Supercategory k B]
    {F : C ⥤ A} {G : A ⥤ C} {H : A ⥤ B} {K : B ⥤ A}
    [G.Additive] [G.Linear k] [IsSuperfunctor k G]
    (a : F ⊣ G) (b : H ⊣ K)
    (ha : ∀ N, a.unit.app N ∈ parity (R := k) _ _ 0)
    (hb : ∀ N, b.unit.app N ∈ parity (R := k) _ _ 0) (N : C) :
    (a.comp b).unit.app N ∈ parity (R := k) _ _ 0 := by
  rw [Adjunction.comp_unit_app]
  exact comp_mem (ha N) (Supercategory.map_mem G (hb (F.obj N)))

private theorem composite_counit_mem
    {k : Type u} {C A B : Type*} [CommRing k] [Category* C] [Category* A] [Category* B]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    [Preadditive B] [Linear k B] [Supercategory k B]
    {F : C ⥤ A} {G : A ⥤ C} {H : A ⥤ B} {K : B ⥤ A}
    [H.Additive] [H.Linear k] [IsSuperfunctor k H]
    (a : F ⊣ G) (b : H ⊣ K)
    (ha : ∀ N, a.counit.app N ∈ parity (R := k) _ _ 0)
    (hb : ∀ N, b.counit.app N ∈ parity (R := k) _ _ 0) (N : B) :
    (a.comp b).counit.app N ∈ parity (R := k) _ _ 0 := by
  rw [Adjunction.comp_counit_app]
  exact comp_mem (Supercategory.map_mem H (ha (K.obj N))) (hb N)

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  {ν μ : List I} (h : ν.Perm μ)

/-- Reindex OLD modules by the literal inverse certificate change. -/
abbrev oldModuleReindex :
    Superfunctor k (OldContentCategory D Sc cutoff ν) (SVec k) ⥤
      Superfunctor k (OldContentCategory D Sc cutoff μ) (SVec k) :=
  restriction (oldContentReindex D Sc cutoff h.symm)

/-- Certificate changes give a strict equivalence on all OLD module maps. -/
def oldModuleReindexEquivalence :
    Superfunctor k (OldContentCategory D Sc cutoff ν) (SVec k) ≌
      Superfunctor k (OldContentCategory D Sc cutoff μ) (SVec k) where
  functor := oldModuleReindex D Sc cutoff h
  inverse := restriction (oldContentReindex D Sc cutoff h)
  unitIso := eqToIso (by rfl)
  counitIso := eqToIso (by rfl)

/-- The strict reindex adjunction has identity unit and counit. -/
def oldModuleReindexAdjunction :
    oldModuleReindex D Sc cutoff h ⊣ restriction (oldContentReindex D Sc cutoff h) :=
  (oldModuleReindexEquivalence D Sc cutoff h).toAdjunction

theorem oldModuleReindexAdjunction_unit_mem
    (N : Superfunctor k (OldContentCategory D Sc cutoff ν) (SVec k)) :
    (oldModuleReindexAdjunction D Sc cutoff h).unit.app N ∈ parity (R := k) _ _ 0 :=
  id_mem N

theorem oldModuleReindexAdjunction_counit_mem
    (N : Superfunctor k (OldContentCategory D Sc cutoff μ) (SVec k)) :
    (oldModuleReindexAdjunction D Sc cutoff h).counit.app N ∈ parity (R := k) _ _ 0 :=
  id_mem N

variable (i : I) {ν' μ' : List I} (hν : (i :: ν).Perm ν') (hμ : (i :: μ).Perm μ')
  (h' : ν'.Perm μ')
local notation "J" => oldContentAppendTo D Sc cutoff ν i ν' hν
local notation "K" => oldContentAppendTo D Sc cutoff μ i μ' hμ
local notation "Q" => oldContentReindex D Sc cutoff h
local notation "Q'" => oldContentReindex D Sc cutoff h'

/-- The first composite uses the actual balanced append adjunction. -/
def oldAppendReindexLeftAdjunction :
    induction J ⋙ oldModuleReindex D Sc cutoff h' ⊣ restriction Q' ⋙ restriction J :=
  (adjunction J).comp (oldModuleReindexAdjunction D Sc cutoff h')

/-- The literal restriction square identifies the other composite right adjoint. -/
def oldAppendReindexRightAdjunction :
    oldModuleReindex D Sc cutoff h ⋙ induction K ⊣ restriction Q' ⋙ restriction J :=
  (oldModuleReindexAdjunction D Sc cutoff h).comp (adjunction K)

/-- The canonical append comparison between arbitrary OLD list representatives. -/
def oldAppendReindexIso :
    induction J ⋙ oldModuleReindex D Sc cutoff h' ≅
      oldModuleReindex D Sc cutoff h ⋙ induction K :=
  (oldAppendReindexLeftAdjunction D Sc cutoff i hν h').leftAdjointUniq
    (oldAppendReindexRightAdjunction D Sc cutoff h i hν hμ h')

theorem oldAppendReindexIso_hom_mem
    (N : Superfunctor k (OldContentCategory D Sc cutoff ν) (SVec k)) :
    (oldAppendReindexIso D Sc cutoff h i hν hμ h').hom.app N ∈ parity (R := k) _ _ 0 := by
  apply leftUniq_hom_mem
  · exact composite_unit_mem _ _
      (oldModuleReindexAdjunction_unit_mem D Sc cutoff h) (adjunctionUnit_mem K)
  · exact composite_counit_mem _ _ (adjunctionCounit_mem J)
      (oldModuleReindexAdjunction_counit_mem D Sc cutoff h')

/-- The comparison retains the chosen composite unit. -/
theorem oldAppendReindexIso_unit
    (N : Superfunctor k (OldContentCategory D Sc cutoff ν) (SVec k)) :
    (oldAppendReindexLeftAdjunction D Sc cutoff i hν h').unit.app N ≫
        (restriction Q' ⋙ restriction J).map
          ((oldAppendReindexIso D Sc cutoff h i hν hμ h').hom.app N) =
      (oldAppendReindexRightAdjunction D Sc cutoff h i hν hμ h').unit.app N :=
  Adjunction.unit_leftAdjointUniq_hom_app _ _ N

/-- The comparison retains the chosen composite counit. -/
theorem oldAppendReindexIso_counit
    (N : Superfunctor k (OldContentCategory D Sc cutoff μ') (SVec k)) :
    (oldAppendReindexIso D Sc cutoff h i hν hμ h').hom.app
        ((restriction Q' ⋙ restriction J).obj N) ≫
      (oldAppendReindexRightAdjunction D Sc cutoff h i hν hμ h').counit.app N =
        (oldAppendReindexLeftAdjunction D Sc cutoff i hν h').counit.app N :=
  Adjunction.leftAdjointUniq_hom_app_counit _ _ N

end OddMath.QuiverHecke

namespace OddMath.QuiverHecke
open ELV ELV.BalancedInduction
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  {ν μ : List I} (h : ν.Perm μ) (i : I)
  {ν' μ' : List I} (hν : (i :: ν).Perm ν') (hμ : (i :: μ).Perm μ') (h' : ν'.Perm μ')

/-- The canonical even append comparison restricts to the actual evaluated probe categories. -/
def probeAppendReindexIso :
    probeEvaluatedAppendTo D Sc m ν i ν' hν ⋙ probeEvaluatedReindex D Sc m h' ≅
      probeEvaluatedReindex D Sc m h ⋙ probeEvaluatedAppendTo D Sc m μ i μ' hμ :=
  NatIso.ofComponents
    (fun N => ObjectProperty.isoMk (ProbeEvaluatesCoefficients D m Sc μ')
      ((oldAppendReindexIso D Sc (probeCutoff D m) h i hν hμ h').app N.obj))
    (by
      intro N N' f
      apply InducedCategory.hom_ext
      exact (oldAppendReindexIso D Sc (probeCutoff D m) h i hν hμ h').hom.naturality f.hom)

theorem probeAppendReindexIso_hom_mem (N : ProbeEvaluatedModules D Sc m ν) :
    (probeAppendReindexIso D Sc m h i hν hμ h').hom.app N ∈ parity (R := k) _ _ 0 :=
  oldAppendReindexIso_hom_mem D Sc (probeCutoff D m) h i hν hμ h' N.obj

end OddMath.QuiverHecke
end

end

section

/-! # Two append inductions under OLD representative changes

Brundan–Ellis (1.7)–(1.8), (1.12)–(1.14): the pair comparison is
the composite of the specified lower and upper append-adjunction
comparisons. It is even and retains both arrows of every nested tensor.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
open ELV ELV.BalancedInduction
universe u

private theorem moduleMap_total_even
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    {M N : Superfunctor k C (SVec k)} (f : M ⟶ N)
    (hf : f ∈ parity (R := k) _ _ 0) (w : A) :
    (moduleMap J f).total w = mapComponent J f 0 w := by
  change mapComponent J f 0 w + mapComponent J f 1 w = _
  have h : mapComponent J f 1 w = 0 := by
    apply hom_ext J M.toFunctor (w := w)
    intro s g b
    rw [mapComponent_tensor, Superfunctor.app_eq_zero_of_mem hf (q := 1) (by decide),
      LinearMap.zero_apply, tensor_zero_right]
    rfl
  rw [h, add_zero]

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  {ν₀ μ₀ : List I} (q₀ : ν₀.Perm μ₀) (i j : I)
  {ν₁ μ₁ ν₂ μ₂ : List I}
  (a₁ : (i :: ν₀).Perm ν₁) (b₁ : (i :: μ₀).Perm μ₁) (q₁ : ν₁.Perm μ₁)
  (a₂ : (j :: ν₁).Perm ν₂) (b₂ : (j :: μ₁).Perm μ₂) (q₂ : ν₂.Perm μ₂)
local notation "J" => oldContentAppendTo D Sc cutoff ν₀ i ν₁ a₁
local notation "K" => oldContentAppendTo D Sc cutoff μ₀ i μ₁ b₁
local notation "L" => oldContentAppendTo D Sc cutoff ν₁ j ν₂ a₂
local notation "M" => oldContentAppendTo D Sc cutoff μ₁ j μ₂ b₂
local notation "R₀" => oldModuleReindex D Sc cutoff q₀
local notation "R₁" => oldModuleReindex D Sc cutoff q₁
local notation "R₂" => oldModuleReindex D Sc cutoff q₂
local notation "e₁" => oldAppendReindexIso D Sc cutoff q₀ i a₁ b₁ q₁
local notation "e₂" => oldAppendReindexIso D Sc cutoff q₁ j a₂ b₂ q₂

/-- The chosen forward append comparison with its module endpoints specified. -/
def oldAppendReindexModuleHom
    (N : Superfunctor k (OldContentCategory D Sc cutoff ν₀) (SVec k)) :
    (R₁).obj (induced J N) ⟶ induced K ((R₀).obj N) := (e₁).hom.app N

local notation "c₁" => oldAppendReindexModuleHom D Sc cutoff q₀ i a₁ b₁ q₁
local notation "c₂" => oldAppendReindexModuleHom D Sc cutoff q₁ j a₂ b₂ q₂

attribute [local irreducible] oldAppendReindexLinear oldAppendReindexModuleHom oldAppendReindexIso

/-- Compose the chosen upper and lower adjunction comparisons, without a new gauge. -/
def oldAppendPairReindexIso :
    (induction J ⋙ induction L) ⋙ R₂ ≅ R₀ ⋙ (induction K ⋙ induction M) :=
  Functor.isoWhiskerLeft (induction J) e₂ ≪≫ Functor.isoWhiskerRight e₁ (induction M)

/-- Fix both nested coend carriers before evaluating the pair comparison. -/
def oldAppendPairReindexLinear
    (N : Superfunctor k (OldContentCategory D Sc cutoff ν₀) (SVec k))
    (w : OldContentCategory D Sc cutoff μ₂) :
    Obj L (induced J N).toFunctor ((oldContentReindex D Sc cutoff q₂.symm).obj w) →ₗ[k]
      Obj M (induced K ((R₀).obj N)).toFunctor w :=
  ((oldAppendPairReindexIso D Sc cutoff q₀ i j a₁ b₁ q₁ a₂ b₂ q₂).hom.app N).total w

end OddMath.QuiverHecke

namespace OddMath.QuiverHecke
open ELV ELV.BalancedInduction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  {ν₀ μ₀ : List I} (q₀ : ν₀.Perm μ₀) (i j : I)
  {ν₁ μ₁ ν₂ μ₂ : List I}
  (a₁ : (i :: ν₀).Perm ν₁) (b₁ : (i :: μ₀).Perm μ₁) (q₁ : ν₁.Perm μ₁)
  (a₂ : (j :: ν₁).Perm ν₂) (b₂ : (j :: μ₁).Perm μ₂) (q₂ : ν₂.Perm μ₂)
local notation "cut" => probeCutoff D m
local notation "e" => oldAppendPairReindexIso D Sc cut q₀ i j a₁ b₁ q₁ a₂ b₂ q₂

/-- Restrict exactly the selected pair comparison to the full evaluated categories. -/
def probeAppendPairReindexIso :
    (probeEvaluatedAppendTo D Sc m ν₀ i ν₁ a₁ ⋙
      probeEvaluatedAppendTo D Sc m ν₁ j ν₂ a₂) ⋙ probeEvaluatedReindex D Sc m q₂ ≅
      probeEvaluatedReindex D Sc m q₀ ⋙
        (probeEvaluatedAppendTo D Sc m μ₀ i μ₁ b₁ ⋙
          probeEvaluatedAppendTo D Sc m μ₁ j μ₂ b₂) :=
  NatIso.ofComponents
    (fun N => ObjectProperty.isoMk (ProbeEvaluatesCoefficients D m Sc μ₂) ((e).app N.obj))
    (by
      intro N N' f
      apply InducedCategory.hom_ext
      exact (e).hom.naturality f.hom)

end OddMath.QuiverHecke
end

end
