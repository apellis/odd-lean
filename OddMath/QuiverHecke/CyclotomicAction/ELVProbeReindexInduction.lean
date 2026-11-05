import OddMath.QuiverHecke.CyclotomicAction.ELVProbeAppendToAdjunction
import Mathlib.CategoryTheory.Adjunction.Unique

/-! # The chosen append adjunction under OLD content reindexing

Brundan–Ellis (1.12)–(1.14) at canonical content representatives: compare
the actual balanced append functors through certificate-only OLD reindexing.
The comparison is the unique left-adjoint comparison for the literal
restriction square. It is even and retains the specified units and counits.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
open ELVOld ELVOld.BalancedInduction
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
open ELVOld ELVOld.BalancedInduction
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
