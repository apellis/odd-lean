import OddMath.QuiverHecke.CyclotomicAction.ProbeWeightDot
import Mathlib.CategoryTheory.Adjunction.Unique
import OddMath.QuiverHecke.CyclotomicAction.ModuleInduction
import OddMath.QuiverHecke.CyclotomicAction.ProbeVacuumCharts
import OddMath.QuiverHecke.CyclotomicAction.ContentHom
import OddMath.QuiverHecke.CyclotomicAction.InductionMixed
import OddMath.QuiverHecke.CyclotomicAction.GlobalWeightRouquier
import OddMath.QuiverHecke.CyclotomicAction.WeightMixed
import OddMath.QuiverHecke.CyclotomicAction.InductionGridRouquier
import OddMath.QuiverHecke.CyclotomicAction.DistinctSlides
import OddMath.QuiverHecke.CyclotomicAction.InductionGridMate

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
end

end

section

/-! # Balanced tensors under OLD representative changes

The canonical append comparison used for Brundan–Ellis (1.12)–(1.14)
preserves the literal unit tensors. Its tensor formula identifies the chosen
append operators at arbitrary content representatives.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
open ELVOld ELVOld.BalancedInduction
universe u

private theorem restriction_comparison_total
    {k C A B : Type u} [CommRing k] [Category.{u} C] [Category.{u} A] [Category.{u} B]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    [Preadditive B] [Linear k B] [Supercategory k B]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    (Q : A ⥤ B) [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q]
    {M : Superfunctor k C (SVec k)} {N P : Superfunctor k B (SVec k)}
    (a : M ⟶ (restriction Q ⋙ restriction J).obj N) (b : N ⟶ P) (v : C) (x : M.obj v) :
    (a ≫ (restriction Q ⋙ restriction J).map b).total v x =
      b.total (Q.obj (J.obj v)) (a.total v x) := by
  rw [Superfunctor.comp_total]
  rfl

private theorem unit_total_apply
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    (M : Superfunctor k C (SVec k)) (v : C) (x : M.obj v) :
    ((adjunction J).unit.app M).total v x = unit J M.toFunctor v x := by
  change (unit J M.toFunctor v + 0) x = _
  rw [add_zero]

private theorem restriction_total_apply
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (Q : C ⥤ A) [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q]
    {N P : Superfunctor k A (SVec k)} (b : N ⟶ P) (v : C) (x : N.obj (Q.obj v)) :
    ((restriction Q).map b).total v x = b.total (Q.obj v) x := rfl

private theorem even_map_naturality
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {M N : Superfunctor k C (SVec k)} (e : M ⟶ N)
    (he : e ∈ parity (R := k) _ _ 0) {v w : C} (g : v ⟶ w) (b : M.obj v) :
    e.total w (M.map g b) = N.map g (e.total v b) := by
  rw [HomogeneousSuperfunctorIso.total_eq_app e he w,
    HomogeneousSuperfunctorIso.total_eq_app e he v]
  exact congrArg (fun f : M.obj v ⟶ N.obj w => f b) (e.toNatTrans.naturality g)

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  {ν μ : List I} (h : ν.Perm μ) (i : I)
  {ν' μ' : List I} (hν : (i :: ν).Perm ν') (hμ : (i :: μ).Perm μ') (h' : ν'.Perm μ')
local notation "J" => oldContentAppendTo D Sc cutoff ν i ν' hν
local notation "K" => oldContentAppendTo D Sc cutoff μ i μ' hμ
local notation "Q" => oldContentReindex D Sc cutoff h
local notation "Q'" => oldContentReindex D Sc cutoff h'
local notation "E" => oldAppendReindexIso D Sc cutoff h i hν hμ h'

theorem oldAppendReindexLeftAdjunction_unit
    (N : Superfunctor k (OldContentCategory D Sc cutoff ν) (SVec k)) :
    (oldAppendReindexLeftAdjunction D Sc cutoff i hν h').unit.app N =
      (adjunction J).unit.app N := by
  rw [oldAppendReindexLeftAdjunction, Adjunction.comp_unit_app]
  change (adjunction J).unit.app N ≫ (restriction J).map (𝟙 _) = _
  rw [(restriction J).map_id]
  exact Category.comp_id _

theorem oldAppendReindexRightAdjunction_unit
    (N : Superfunctor k (OldContentCategory D Sc cutoff ν) (SVec k)) :
    (oldAppendReindexRightAdjunction D Sc cutoff h i hν hμ h').unit.app N =
      (restriction Q).map ((adjunction K).unit.app ((oldModuleReindex D Sc cutoff h).obj N)) := by
  rw [oldAppendReindexRightAdjunction, Adjunction.comp_unit_app]
  change 𝟙 _ ≫ (restriction Q).map _ = _
  rw [Category.id_comp]

/-- The adjunction comparison sends the chosen unit to the chosen unit. -/
theorem oldAppendReindexIso_hom_unit
    (N : Superfunctor k (OldContentCategory D Sc cutoff ν) (SVec k))
    (s : OldContentCategory D Sc cutoff ν) (b : N.obj s) :
    ((E).hom.app N).total ((Q').obj ((J).obj s)) (unit J N.toFunctor s b) =
      unit K ((oldModuleReindex D Sc cutoff h).obj N).toFunctor ((Q).obj s) b := by
  have he := oldAppendReindexIso_unit D Sc cutoff h i hν hμ h' N
  rw [oldAppendReindexLeftAdjunction_unit, oldAppendReindexRightAdjunction_unit] at he
  let V := (induction J ⋙ oldModuleReindex D Sc cutoff h').obj N
  let W := (oldModuleReindex D Sc cutoff h ⋙ induction K).obj N
  let e : V ⟶ W := (E).hom.app N
  let a : N ⟶ (restriction Q' ⋙ restriction J).obj V := (adjunction J).unit.app N
  let r : N ⟶ (restriction Q' ⋙ restriction J).obj W :=
    (restriction Q).map ((adjunction K).unit.app ((oldModuleReindex D Sc cutoff h).obj N))
  have he' : a ≫ (restriction Q' ⋙ restriction J).map e = r := he
  have hv := congrArg (fun f : N ⟶ (restriction Q' ⋙ restriction J).obj W => f.total s b) he'
  have hc := restriction_comparison_total J Q' a e s b
  have hu := unit_total_apply J N s b
  have hr := restriction_total_apply Q
    ((adjunction K).unit.app ((oldModuleReindex D Sc cutoff h).obj N)) s b
  have hv' := unit_total_apply K ((oldModuleReindex D Sc cutoff h).obj N) ((Q).obj s) b
  have ht : e.total ((Q').obj ((J).obj s)) (a.total s b) = r.total s b := hc.symm.trans hv
  have hul : a.total s b = unit J N.toFunctor s b := hu
  have hur : r.total s b =
      unit K ((oldModuleReindex D Sc cutoff h).obj N).toFunctor ((Q).obj s) b := hr.trans hv'
  exact (congrArg (e.total ((Q').obj ((J).obj s))) hul).symm.trans (ht.trans hur)

/-- The forward comparison in its two fixed balanced coend carriers. -/
def oldAppendReindexLinear
    (N : Superfunctor k (OldContentCategory D Sc cutoff ν) (SVec k))
    (w : OldContentCategory D Sc cutoff μ') :
    Obj J N.toFunctor ((oldContentReindex D Sc cutoff h'.symm).obj w) →ₗ[k]
      Obj K ((oldModuleReindex D Sc cutoff h).obj N).toFunctor w :=
  ((E).hom.app N).total w

/-- The comparison only changes the source permutation certificate of a tensor. -/
theorem oldAppendReindexIso_hom_tensor
    (N : Superfunctor k (OldContentCategory D Sc cutoff ν) (SVec k))
    (s : OldContentCategory D Sc cutoff ν) (w : OldContentCategory D Sc cutoff μ')
    (g : (J).obj s ⟶ (oldContentReindex D Sc cutoff h'.symm).obj w) (b : N.obj s) :
    oldAppendReindexLinear D Sc cutoff h i hν hμ h' N w (tensor J N.toFunctor s g b) =
      tensor K ((oldModuleReindex D Sc cutoff h).obj N).toFunctor ((Q).obj s) g b := by
  let V := (induction J ⋙ oldModuleReindex D Sc cutoff h').obj N
  let W := (oldModuleReindex D Sc cutoff h ⋙ induction K).obj N
  let e : V ⟶ W := (E).hom.app N
  let a : (Q').obj ((J).obj s) ⟶ w := g
  have hn := even_map_naturality e (oldAppendReindexIso_hom_mem D Sc cutoff h i hν hμ h' N)
    a (unit J N.toFunctor s b)
  have hL : V.map a (unit J N.toFunctor s b) = tensor J N.toFunctor s g b :=
    postcompose_unit J N.toFunctor (v := s)
      (w := (oldContentReindex D Sc cutoff h'.symm).obj w) g b
  have hu := oldAppendReindexIso_hom_unit D Sc cutoff h i hν hμ h' N s b
  have hr := congrArg (W.map a) hu
  have hR : W.map a (unit K ((oldModuleReindex D Sc cutoff h).obj N).toFunctor ((Q).obj s) b) =
      tensor K ((oldModuleReindex D Sc cutoff h).obj N).toFunctor ((Q).obj s) g b :=
    postcompose_unit K ((oldModuleReindex D Sc cutoff h).obj N).toFunctor
      (v := (Q).obj s) (w := w) g b
  exact (congrArg (e.total w) hL).symm.trans (hn.trans (hr.trans hR))

end OddMath.QuiverHecke

namespace OddMath.QuiverHecke
open ELVOld ELVOld.BalancedInduction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  {ν μ : List I} (h : ν.Perm μ) (i : I)
  {ν' μ' : List I} (hν : (i :: ν).Perm ν') (hμ : (i :: μ).Perm μ') (h' : ν'.Perm μ')

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
open ELVOld ELVOld.BalancedInduction
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
open ELVOld ELVOld.BalancedInduction
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

section

/-! # The chosen OLD crossing under pair representative changes

Brundan–Ellis (1.7)–(1.8), (1.12): compare the positive rectangular
crossing through the selected lower/upper append comparisons. The
coefficient crossing is the same OLD quotient arrow at every stored list.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
open ELVOld ELVOld.BalancedInduction ELVOld.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (ν : List I) (i j : I) {νj νi ν₂ : List I}
  (hj : (j :: ν).Perm νj) (hi : (i :: ν).Perm νi)
  (hL : (i :: νj).Perm ν₂) (hM : (j :: νi).Perm ν₂)
local notation "J" => oldContentAppendTo D Sc cutoff ν j νj hj
local notation "K" => oldContentAppendTo D Sc cutoff ν i νi hi
local notation "L" => oldContentAppendTo D Sc cutoff νj i ν₂ hL
local notation "M" => oldContentAppendTo D Sc cutoff νi j ν₂ hM

/-- The physical positive crossing at four prescribed stored contents. -/
def oldAppendToCross (s : OldContentCategory D Sc cutoff ν) :
    ((J) ⋙ (L)).obj s ⟶ ((K) ⋙ (M)).obj s :=
  Distinct.crossComponent D Sc cutoff i j s.obj

theorem oldAppendToCross_supernatural :
    IsSupernatural k (D.parity i * D.parity j) (oldAppendToCross D Sc cutoff ν i j hj hi hL hM) where
  mem s := (Distinct.cross_supernatural D Sc cutoff i j).mem s.obj
  naturality hf := (Distinct.cross_supernatural D Sc cutoff i j).naturality hf
local notation "hc" => oldAppendToCross_supernatural D Sc cutoff ν i j hj hi hL hM

/-- The prescribed flatten-cross-expand map in its fixed two coend carriers. -/
def oldAppendToCrossLinear
    (N : Superfunctor k (OldContentCategory D Sc cutoff ν) (SVec k))
    (w : OldContentCategory D Sc cutoff ν₂) :
    Obj M (induced K N).toFunctor w →ₗ[k] Obj L (induced J N).toFunctor w :=
  (rectangularCrossComponent J K L M hc N).total w

local notation "r₀" => List.Perm.refl ν
local notation "rj" => List.Perm.refl (j :: ν)
local notation "ri" => List.Perm.refl (i :: ν)
local notation "rL" => List.Perm.refl (i :: j :: ν)
local notation "rM" => List.Perm.swap i j ν
local notation "h₂" => List.Perm.trans (List.Perm.cons i hj) hL
local notation "J₀" => oldContentAppendTo D Sc cutoff ν j (j :: ν) rj
local notation "K₀" => oldContentAppendTo D Sc cutoff ν i (i :: ν) ri
local notation "L₀" => oldContentAppendTo D Sc cutoff (j :: ν) i (i :: j :: ν) rL
local notation "M₀" => oldContentAppendTo D Sc cutoff (i :: ν) j (i :: j :: ν) rM
local notation "Q₀" => oldContentReindex D Sc cutoff r₀
local notation "Qi" => oldContentReindex D Sc cutoff hi
local notation "Q₂inv" => oldContentReindex D Sc cutoff (List.Perm.symm h₂)
local notation "R₀" => oldModuleReindex D Sc cutoff r₀
local notation "χ₀" => oldAppendToCrossLinear D Sc cutoff ν i j rj ri rL rM
local notation "α₀" => oldAppendToCross D Sc cutoff ν i j rj ri rL rM
local notation "S" => oldAppendPairReindexLinear D Sc cutoff r₀ i j ri hi hi rM hM h₂
local notation "T" => oldAppendPairReindexLinear D Sc cutoff r₀ j i rj hj hj rL hL h₂

attribute [local irreducible] oldAppendToCrossLinear oldAppendPairReindexLinear
  oldAppendReindexIso oldAppendPairReindexIso

local notation "eS" => oldAppendPairReindexIso D Sc cutoff r₀ i j ri hi hi rM hM h₂
local notation "eT" => oldAppendPairReindexIso D Sc cutoff r₀ j i rj hj hj rL hL h₂
local notation "hc₀" => oldAppendToCross_supernatural D Sc cutoff ν i j rj ri rL rM

end OddMath.QuiverHecke

namespace OddMath.QuiverHecke
open ELVOld ELVOld.BalancedInduction CyclotomicAction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (ν : List I) (i j : I) {νj νi ν₂ : List I}
  (hj : (j :: ν).Perm νj) (hi : (i :: ν).Perm νi)
  (hL : (i :: νj).Perm ν₂) (hM : (j :: νi).Perm ν₂)
local notation "cut" => probeCutoff D m
local notation "J" => oldContentAppendTo D Sc cut ν j νj hj
local notation "K" => oldContentAppendTo D Sc cut ν i νi hi
local notation "L" => oldContentAppendTo D Sc cut νj i ν₂ hL
local notation "M" => oldContentAppendTo D Sc cut νi j ν₂ hM
local notation "hc" => oldAppendToCross_supernatural D Sc cut ν i j hj hi hL hM
local notation "Src" => probeEvaluatedAppendTo D Sc m ν i νi hi ⋙
  probeEvaluatedAppendTo D Sc m νi j ν₂ hM
local notation "Tgt" => probeEvaluatedAppendTo D Sc m ν j νj hj ⋙
  probeEvaluatedAppendTo D Sc m νj i ν₂ hL

/-- The prescribed positive crossing component in the full evaluated categories. -/
def probeAppendToCrossComponent (N : ProbeEvaluatedModules D Sc m ν) : (Src).obj N ⟶ (Tgt).obj N :=
  ⟨rectangularCrossComponent J K L M hc N.obj⟩

private theorem appendToCrossSource_closed
    (N : Superfunctor k (OldContentCategory D Sc cut ν) (SVec k))
    (hN : ProbeEvaluatesCoefficients D m Sc ν N) :
    ProbeEvaluatesCoefficients D m Sc ν₂ ((induction K ⋙ induction M).obj N) :=
  ((Src).obj ⟨N, hN⟩).property

private theorem appendToCrossTarget_closed
    (N : Superfunctor k (OldContentCategory D Sc cut ν) (SVec k))
    (hN : ProbeEvaluatesCoefficients D m Sc ν N) :
    ProbeEvaluatesCoefficients D m Sc ν₂ ((induction J ⋙ induction L).obj N) :=
  ((Tgt).obj ⟨N, hN⟩).property

/-- The whole positive stored-target crossing, natural on even and odd input maps. -/
def probeAppendToCross :
    (⟨Src⟩ : Superfunctor k (ProbeEvaluatedModules D Sc m ν) (ProbeEvaluatedModules D Sc m ν₂)) ⟶
      (⟨Tgt⟩ : Superfunctor k (ProbeEvaluatedModules D Sc m ν) (ProbeEvaluatedModules D Sc m ν₂)) :=
  fullLiftTrans (ProbeEvaluatesCoefficients D m Sc ν) (ProbeEvaluatesCoefficients D m Sc ν₂)
    (appendToCrossSource_closed D Sc m ν i j hi hM)
    (appendToCrossTarget_closed D Sc m ν i j hj hL)
    (rectangularCrossComponent_supernatural J K L M hc).toSuperNatTrans

theorem probeAppendToCross_direct_total (N : ProbeEvaluatedModules D Sc m ν) :
    ((probeAppendToCross D Sc m ν i j hj hi hL hM).total N).hom =
      rectangularCrossComponent J K L M hc N.obj := by
  change (rectangularCrossComponent_supernatural J K L M hc).toSuperNatTrans.total N.obj = _
  exact HomogeneousSuperfunctorIso.homogeneous_total
    (F := (⟨induction K ⋙ induction M⟩ : Superfunctor k
      (Superfunctor k (OldContentCategory D Sc cut ν) (SVec k))
      (Superfunctor k (OldContentCategory D Sc cut ν₂) (SVec k))))
    (G := (⟨induction J ⋙ induction L⟩ : Superfunctor k
      (Superfunctor k (OldContentCategory D Sc cut ν) (SVec k))
      (Superfunctor k (OldContentCategory D Sc cut ν₂) (SVec k))))
    (rectangularCrossComponent_supernatural J K L M hc) N.obj

theorem probeAppendToCross_total (N : ProbeEvaluatedModules D Sc m ν) :
    (probeAppendToCross D Sc m ν i j hj hi hL hM).total N =
      probeAppendToCrossComponent D Sc m ν i j hj hi hL hM N :=
  InducedCategory.hom_ext (probeAppendToCross_direct_total D Sc m ν i j hj hi hL hM N)

local notation "r₀" => List.Perm.refl ν
local notation "rj" => List.Perm.refl (j :: ν)
local notation "ri" => List.Perm.refl (i :: ν)
local notation "rL" => List.Perm.refl (i :: j :: ν)
local notation "rM" => List.Perm.swap i j ν
local notation "h₂" => List.Perm.trans (List.Perm.cons i hj) hL
local notation "Q₂inv" => oldContentReindex D Sc cut (List.Perm.symm h₂)
local notation "J₀" => oldContentAppendTo D Sc cut ν j (j :: ν) rj
local notation "K₀" => oldContentAppendTo D Sc cut ν i (i :: ν) ri
local notation "L₀" => oldContentAppendTo D Sc cut (j :: ν) i (i :: j :: ν) rL
local notation "M₀" => oldContentAppendTo D Sc cut (i :: ν) j (i :: j :: ν) rM
local notation "eS" => oldAppendPairReindexIso D Sc cut r₀ i j ri hi hi rM hM h₂
local notation "eT" => oldAppendPairReindexIso D Sc cut r₀ j i rj hj hj rL hL h₂
local notation "ES" => probeAppendPairReindexIso D Sc m r₀ i j ri hi hi rM hM h₂
local notation "ET" => probeAppendPairReindexIso D Sc m r₀ j i rj hj hj rL hL h₂
local notation "hc₀" => oldAppendToCross_supernatural D Sc cut ν i j rj ri rL rM

end OddMath.QuiverHecke
end

end

section

/-! # The prescribed distinct mate at stored OLD contents

Brundan–Ellis (1.12): transport the positive cup-crossing-cap through
the specified lower and upper append-adjunction comparisons. The
single-coend formula retains every coefficient twist.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
open ELVOld ELVOld.BalancedInduction
universe u
attribute [local irreducible] oldAppendReindexLinear oldAppendReindexIso orderedRectangularMateLinear

private theorem rectangular_square_point {k V W V' W' : Type*} [CommRing k]
    [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]
    [AddCommMonoid V'] [Module k V'] [AddCommMonoid W'] [Module k W']
    (a : V →ₗ[k] W) (b : V' →ₗ[k] W') (l : V →ₗ[k] V') (r : W →ₗ[k] W')
    (v : V) (w : W) (v' : V') (w' : W')
    (ha : a v = w) (hr : r w = w') (hl : l v = v') (hb : b v' = w') :
    (r ∘ₗ a) v = (b ∘ₗ l) v :=
  (congrArg r ha).trans (hr.trans ((congrArg b hl).trans hb).symm)

private theorem iso_total_bijective
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {F G : Superfunctor k C (SVec k)} (e : F ≅ G) (w : C) :
    Function.Bijective (e.hom.total w) := by
  have hl : Function.LeftInverse (e.inv.total w) (e.hom.total w) := by
    intro x
    have h := congrArg (fun f : End F => f.total w x) e.hom_inv_id
    rw [Superfunctor.comp_total] at h
    change e.inv.total w (e.hom.total w x) = (LinearMap.id + 0) x at h
    simpa only [add_zero, LinearMap.id_apply] using h
  have hr : Function.RightInverse (e.inv.total w) (e.hom.total w) := by
    intro x
    have h := congrArg (fun f : End G => f.total w x) e.inv_hom_id
    rw [Superfunctor.comp_total] at h
    change e.hom.total w (e.inv.total w x) = (LinearMap.id + 0) x at h
    simpa only [add_zero, LinearMap.id_apply] using h
  exact ⟨hl.injective, hr.surjective⟩

private theorem bijective_of_linear_square {k V W V' W' : Type*} [CommRing k]
    [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]
    [AddCommMonoid V'] [Module k V'] [AddCommMonoid W'] [Module k W']
    (a : V →ₗ[k] W) (b : V' →ₗ[k] W') (l : V →ₗ[k] V') (r : W →ₗ[k] W')
    (hl : Function.Bijective l) (hr : Function.Bijective r) (ha : Function.Bijective a)
    (hsq : r ∘ₗ a = b ∘ₗ l) : Function.Bijective b := by
  apply (Function.Bijective.of_comp_iff (b : V' → W') hl).mp
  change Function.Bijective ((b ∘ₗ l) : V → W')
  rw [← hsq]
  exact hr.comp ha

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (ν : List I) (i j : I) {νj νi ν₂ : List I}
  (hj : (j :: ν).Perm νj) (hi : (i :: ν).Perm νi)
  (hL : (i :: νj).Perm ν₂) (hM : (j :: νi).Perm ν₂)
local notation "J₀" => oldContentAppendTo D Sc cutoff ν j (j :: ν) (List.Perm.refl _)
local notation "K₀" => oldContentAppendTo D Sc cutoff ν i (i :: ν) (List.Perm.refl _)
local notation "L₀" => oldContentAppendTo D Sc cutoff (j :: ν) i (i :: j :: ν) (List.Perm.refl _)
local notation "M₀" => oldContentAppendTo D Sc cutoff (i :: ν) j (i :: j :: ν) (List.Perm.swap i j ν)
local notation "J" => oldContentAppendTo D Sc cutoff ν j νj hj
local notation "K" => oldContentAppendTo D Sc cutoff ν i νi hi
local notation "L" => oldContentAppendTo D Sc cutoff νj i ν₂ hL
local notation "M" => oldContentAppendTo D Sc cutoff νi j ν₂ hM
local notation "Qj" => oldContentReindex D Sc cutoff hj
local notation "QiInv" => oldContentReindex D Sc cutoff hi.symm
local notation "Rj" => oldModuleReindex D Sc cutoff hj
local notation "h₂" => List.Perm.trans (List.Perm.cons i hj) hL
local notation "hc₀" => oldAppendToCross_supernatural D Sc cutoff ν i j
  (List.Perm.refl (j :: ν)) (List.Perm.refl (i :: ν))
  (List.Perm.refl (i :: j :: ν)) (List.Perm.swap i j ν)
local notation "hc" => oldAppendToCross_supernatural D Sc cutoff ν i j hj hi hL hM

/-- The lower-i comparison keeps the prescribed lower-j restriction. -/
def oldReindexDistinctSourceLinear
    (N : Superfunctor k (OldContentCategory D Sc cutoff (j :: ν)) (SVec k))
    (t : OldContentCategory D Sc cutoff νi) :
    Obj K₀ ((restriction J₀).obj N).toFunctor ((QiInv).obj t) →ₗ[k]
      Obj K ((restriction J).obj ((Rj).obj N)).toFunctor t :=
  oldAppendReindexLinear D Sc cutoff (List.Perm.refl ν) i
    (List.Perm.refl (i :: ν)) hi hi ((restriction J₀).obj N) t

/-- The upper-i comparison keeps the prescribed upper-j restriction. -/
def oldReindexDistinctTargetLinear
    (N : Superfunctor k (OldContentCategory D Sc cutoff (j :: ν)) (SVec k))
    (t : OldContentCategory D Sc cutoff νi) :
    Obj L₀ N.toFunctor ((M₀).obj ((QiInv).obj t)) →ₗ[k]
      Obj L ((Rj).obj N).toFunctor ((M).obj t) :=
  oldAppendReindexLinear D Sc cutoff hj i (List.Perm.refl (i :: j :: ν)) hL h₂ N ((M).obj t)

theorem oldReindexDistinctSourceLinear_tensor
    (N : Superfunctor k (OldContentCategory D Sc cutoff (j :: ν)) (SVec k))
    (s : OldContentCategory D Sc cutoff ν) (t : OldContentCategory D Sc cutoff νi)
    (g : (K₀).obj s ⟶ (QiInv).obj t) (v : N.obj ((J₀).obj s)) :
    oldReindexDistinctSourceLinear D Sc cutoff ν i j hj hi N t
        (tensor K₀ ((restriction J₀).obj N).toFunctor (w := (QiInv).obj t) s g v) =
      tensor K ((restriction J).obj ((Rj).obj N)).toFunctor (w := t) s g v := by
  have h := oldAppendReindexIso_hom_tensor D Sc cutoff (List.Perm.refl ν) i
    (List.Perm.refl (i :: ν)) hi hi ((restriction J₀).obj N) s t g v
  set_option backward.dsimp.instances true in
    dsimp only [oldReindexDistinctSourceLinear, oldModuleReindex] at h ⊢
  convert! h using 1

theorem oldReindexDistinctTargetLinear_tensor
    (N : Superfunctor k (OldContentCategory D Sc cutoff (j :: ν)) (SVec k))
    (s : OldContentCategory D Sc cutoff (j :: ν)) (t : OldContentCategory D Sc cutoff νi)
    (g : (L₀).obj s ⟶ (M₀).obj ((QiInv).obj t)) (v : N.obj s) :
    oldReindexDistinctTargetLinear D Sc cutoff ν i j hj hi hL hM N t
        (tensor L₀ N.toFunctor (w := (M₀).obj ((QiInv).obj t)) s g v) =
      tensor L ((Rj).obj N).toFunctor (w := (M).obj t) ((Qj).obj s) g v := by
  let g' : (L₀).obj s ⟶ (oldContentReindex D Sc cutoff (List.Perm.symm h₂)).obj ((M).obj t) := g
  have h := oldAppendReindexIso_hom_tensor D Sc cutoff hj i
    (List.Perm.refl (i :: j :: ν)) hL h₂ N s ((M).obj t) g' v
  set_option backward.dsimp.instances true in
    dsimp only [oldReindexDistinctTargetLinear, oldModuleReindex, g'] at h ⊢
  convert! h using 1

/-- The positive mate intertwines the selected source and target comparisons on all vectors. -/
theorem oldReindexDistinctLinear_mate
    (N : Superfunctor k (OldContentCategory D Sc cutoff (j :: ν)) (SVec k))
    (t : OldContentCategory D Sc cutoff νi) :
    oldReindexDistinctTargetLinear D Sc cutoff ν i j hj hi hL hM N t ∘ₗ
        orderedRectangularMateLinear J₀ K₀ L₀ M₀ hc₀ N ((QiInv).obj t) =
      orderedRectangularMateLinear J K L M hc ((Rj).obj N) t ∘ₗ
        oldReindexDistinctSourceLinear D Sc cutoff ν i j hj hi N t := by
  let N₀ := N
  let N₁ := (Rj).obj N
  let t₀ := (QiInv).obj t
  let V := Obj K₀ ((restriction J₀).obj N₀).toFunctor t₀
  let W := Obj L₀ N₀.toFunctor ((M₀).obj t₀)
  let V' := Obj K ((restriction J).obj N₁).toFunctor t
  let W' := Obj L N₁.toFunctor ((M).obj t)
  let a : V →ₗ[k] W := orderedRectangularMateLinear J₀ K₀ L₀ M₀ hc₀ N₀ t₀
  let b : V' →ₗ[k] W' := orderedRectangularMateLinear J K L M hc N₁ t
  let l : V →ₗ[k] V' := oldReindexDistinctSourceLinear D Sc cutoff ν i j hj hi N t
  let r : W →ₗ[k] W' := oldReindexDistinctTargetLinear D Sc cutoff ν i j hj hi hL hM N t
  change r ∘ₗ a = b ∘ₗ l
  apply hom_ext K₀ ((restriction J₀).obj N₀).toFunctor (w := t₀)
  intro s g v
  have h₀ := orderedRectangularMateLinear_tensor J₀ K₀ L₀ M₀ hc₀ N₀ s t₀ g v
  have h₃ := orderedRectangularMateLinear_tensor J K L M hc N₁ s t g v
  let v₀ : V := tensor K₀ ((restriction J₀).obj N₀).toFunctor (w := t₀) s g v
  let z₀ : W := tensor L₀ N₀.toFunctor (w := (M₀).obj t₀) ((J₀).obj s)
    (oldAppendToCross D Sc cutoff ν i j (List.Perm.refl _) (List.Perm.refl _)
      (List.Perm.refl _) (List.Perm.swap i j ν) s ≫
      twist k (D.parity i * D.parity j) ((M₀).map g)) v
  let v₁ : V' := tensor K ((restriction J).obj N₁).toFunctor (w := t) s g v
  let z₁ : W' := tensor L N₁.toFunctor (w := (M).obj t) ((J).obj s)
    (oldAppendToCross D Sc cutoff ν i j hj hi hL hM s ≫
      twist k (D.parity i * D.parity j) ((M).map g)) v
  have ha : a v₀ = z₀ := by convert! h₀ using 1
  have hr : r z₀ = z₁ := by
    dsimp only [r, z₀, z₁, N₀, N₁]
    rw [oldReindexDistinctTargetLinear_tensor]
    rfl
  have hl : l v₀ = v₁ := by
    dsimp only [l, v₀, v₁, N₀, N₁]
    rw [oldReindexDistinctSourceLinear_tensor]
  have hb : b v₁ = z₁ := by convert! h₃ using 1
  exact rectangular_square_point (k := k) (V := V) (W := W) (V' := V') (W' := W')
    a b l r v₀ z₀ v₁ z₁ ha hr hl hb

theorem oldReindexDistinctSourceLinear_bijective
    (N : Superfunctor k (OldContentCategory D Sc cutoff (j :: ν)) (SVec k))
    (t : OldContentCategory D Sc cutoff νi) :
    Function.Bijective (oldReindexDistinctSourceLinear D Sc cutoff ν i j hj hi N t) := by
  unfold oldReindexDistinctSourceLinear oldAppendReindexLinear
  let U := (restriction J₀).obj N
  exact iso_total_bijective
    (F := (induction K₀ ⋙ oldModuleReindex D Sc cutoff hi).obj U)
    (G := (oldModuleReindex D Sc cutoff (List.Perm.refl ν) ⋙ induction K).obj U)
    ((oldAppendReindexIso D Sc cutoff (List.Perm.refl ν) i
      (List.Perm.refl (i :: ν)) hi hi).app U) t

theorem oldReindexDistinctTargetLinear_bijective
    (N : Superfunctor k (OldContentCategory D Sc cutoff (j :: ν)) (SVec k))
    (t : OldContentCategory D Sc cutoff νi) :
    Function.Bijective (oldReindexDistinctTargetLinear D Sc cutoff ν i j hj hi hL hM N t) := by
  unfold oldReindexDistinctTargetLinear oldAppendReindexLinear
  exact iso_total_bijective
    (F := (induction L₀ ⋙ oldModuleReindex D Sc cutoff h₂).obj N)
    (G := (oldModuleReindex D Sc cutoff hj ⋙ induction L).obj N)
    ((oldAppendReindexIso D Sc cutoff hj i (List.Perm.refl (i :: j :: ν)) hL h₂).app N)
    ((M).obj t)

/-- The existing OLD PBW inverse makes the stored-target mate bijective on reindexed inputs. -/
theorem oldAppendToDistinctMateLinear_bijective_reindex (hij : i ≠ j)
    (N : Superfunctor k (OldContentCategory D Sc cutoff (j :: ν)) (SVec k))
    (t : OldContentCategory D Sc cutoff νi) :
    Function.Bijective (orderedRectangularMateLinear J K L M hc ((Rj).obj N) t) := by
  have hstd : Function.Bijective (orderedRectangularMateLinear J₀ K₀ L₀ M₀ hc₀ N ((QiInv).obj t)) :=
    oldContentDistinctMateLinear_bijective D Sc cutoff ν i j hij N ((QiInv).obj t)
  exact bijective_of_linear_square
    (orderedRectangularMateLinear J₀ K₀ L₀ M₀ hc₀ N ((QiInv).obj t))
    (orderedRectangularMateLinear J K L M hc ((Rj).obj N) t)
    (oldReindexDistinctSourceLinear D Sc cutoff ν i j hj hi N t)
    (oldReindexDistinctTargetLinear D Sc cutoff ν i j hj hi hL hM N t)
    (oldReindexDistinctSourceLinear_bijective D Sc cutoff ν i j hj hi N t)
    (oldReindexDistinctTargetLinear_bijective D Sc cutoff ν i j hj hi hL hM N t) hstd
    (oldReindexDistinctLinear_mate D Sc cutoff ν i j hj hi hL hM N t)

/-- All stored-target inputs are covered by the strict reindex equivalence. -/
theorem oldAppendToDistinctMateLinear_bijective (hij : i ≠ j)
    (N : Superfunctor k (OldContentCategory D Sc cutoff νj) (SVec k))
    (t : OldContentCategory D Sc cutoff νi) :
    Function.Bijective (orderedRectangularMateLinear J K L M hc N t) := by
  let N₀ := (oldModuleReindex D Sc cutoff hj.symm).obj N
  have hb := oldAppendToDistinctMateLinear_bijective_reindex D Sc cutoff ν i j hj hi hL hM hij N₀ t
  have hN : (Rj).obj N₀ = N := rfl
  exact Eq.mp (congrArg (fun P : Superfunctor k (OldContentCategory D Sc cutoff νj) (SVec k) =>
    Function.Bijective (orderedRectangularMateLinear J K L M hc P t)) hN) hb

/-- The actual positive stored-target mate with its constructed OLD inverse. -/
def oldAppendToDistinctMateModuleIso (hij : i ≠ j)
    (N : Superfunctor k (OldContentCategory D Sc cutoff νj) (SVec k)) :
    induced K ((restriction J).obj N) ≅ (restriction M).obj (induced L N) :=
  rectangularMateModuleIso J K L M hc N
    (fun t => oldAppendToDistinctMateLinear_bijective D Sc cutoff ν i j hj hi hL hM hij N t)

theorem oldAppendToDistinctMateModuleIso_hom (hij : i ≠ j)
    (N : Superfunctor k (OldContentCategory D Sc cutoff νj) (SVec k)) :
    (oldAppendToDistinctMateModuleIso D Sc cutoff ν i j hj hi hL hM hij N).hom =
      orderedRectangularMateComponent J K L M hc N :=
  rectangularMateModuleIso_hom J K L M hc N _

end OddMath.QuiverHecke

namespace OddMath.QuiverHecke
open ELVOld ELVOld.BalancedInduction CyclotomicAction
open BicategoryStruct
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (ν : List I) (i j : I) {νj νi ν₂ : List I}
  (hj : (j :: ν).Perm νj) (hi : (i :: ν).Perm νi)
  (hL : (i :: νj).Perm ν₂) (hM : (j :: νi).Perm ν₂)
local notation "cut" => probeCutoff D m
local notation "J" => oldContentAppendTo D Sc cut ν j νj hj
local notation "K" => oldContentAppendTo D Sc cut ν i νi hi
local notation "L" => oldContentAppendTo D Sc cut νj i ν₂ hL
local notation "M" => oldContentAppendTo D Sc cut νi j ν₂ hM
local notation "hc" => oldAppendToCross_supernatural D Sc cut ν i j hj hi hL hM
local notation "S" => probeEvaluatedRestrictTo D Sc m ν j νj hj ⋙
  probeEvaluatedAppendTo D Sc m ν i νi hi
local notation "T" => probeEvaluatedAppendTo D Sc m νj i ν₂ hL ⋙
  probeEvaluatedRestrictTo D Sc m νi j ν₂ hM
local notation "P" => ProbeEvaluatesCoefficients D m Sc νj
local notation "Q" => ProbeEvaluatesCoefficients D m Sc νi

private theorem appendToMateSource_closed
    (N : Superfunctor k (OldContentCategory D Sc cut νj) (SVec k)) (hN : P N) :
    Q ((rectangularMateSourceFunctor (k := k) J K).obj N) :=
  ((S).obj ⟨N, hN⟩).property

private theorem appendToMateTarget_closed
    (N : Superfunctor k (OldContentCategory D Sc cut νj) (SVec k)) (hN : P N) :
    Q ((rectangularMateTargetFunctor (k := k) L M).obj N) :=
  ((T).obj ⟨N, hN⟩).property

/-- The prescribed lower restriction-induction at the stored contents. -/
abbrev probeAppendToDistinctMateSource :
    Superfunctor k (ProbeEvaluatedModules D Sc m νj) (ProbeEvaluatedModules D Sc m νi) :=
  fullLiftSuperfunctor P Q (rectangularMateSourceFunctor (k := k) J K)
    (appendToMateSource_closed D Sc m ν i j hj hi)

/-- The prescribed upper induction-restriction at the common stored target. -/
abbrev probeAppendToDistinctMateTarget :
    Superfunctor k (ProbeEvaluatedModules D Sc m νj) (ProbeEvaluatedModules D Sc m νi) :=
  fullLiftSuperfunctor P Q (rectangularMateTargetFunctor (k := k) L M)
    (appendToMateTarget_closed D Sc m i j hL hM)

def probeAppendToDistinctMateComponent (N : ProbeEvaluatedModules D Sc m νj) :
    (probeAppendToDistinctMateSource D Sc m ν i j hj hi).obj N ⟶
      (probeAppendToDistinctMateTarget D Sc m i j hL hM).obj N :=
  ⟨orderedRectangularMateComponent J K L M hc N.obj⟩

/-- The whole stored-target positive cup-crossing-cap, with all module maps retained. -/
def probeAppendToDistinctMate :
    probeAppendToDistinctMateSource D Sc m ν i j hj hi ⟶
      probeAppendToDistinctMateTarget D Sc m i j hL hM :=
  fullLiftTrans P Q (appendToMateSource_closed D Sc m ν i j hj hi)
    (appendToMateTarget_closed D Sc m i j hL hM) (rectangularMateHom J K L M hc)

theorem probeAppendToDistinctMate_mem :
    probeAppendToDistinctMate D Sc m ν i j hj hi hL hM ∈ parity (R := k) _ _
      (D.parity i * D.parity j) :=
  Superfunctor.mem_parity_iff_isHomogeneous.mpr
    (fullLiftTrans_homogeneous P Q (appendToMateSource_closed D Sc m ν i j hj hi)
      (appendToMateTarget_closed D Sc m i j hL hM) _
      (Superfunctor.mem_parity_iff_isHomogeneous.mp (rectangularMateHom_mem J K L M hc)))

theorem probeAppendToDistinctMate_total (N : ProbeEvaluatedModules D Sc m νj) :
    (probeAppendToDistinctMate D Sc m ν i j hj hi hL hM).total N =
      probeAppendToDistinctMateComponent D Sc m ν i j hj hi hL hM N := by
  apply InducedCategory.hom_ext
  change (rectangularMateHom J K L M hc).total N.obj = _
  exact rectangularMateHom_total J K L M hc N.obj

/-- The constructed OLD inverse is a map in the same full evaluated subcategory. -/
def probeAppendToDistinctMateModuleIso (hij : i ≠ j) (N : ProbeEvaluatedModules D Sc m νj) :
    (probeAppendToDistinctMateSource D Sc m ν i j hj hi).obj N ≅
      (probeAppendToDistinctMateTarget D Sc m i j hL hM).obj N :=
  ObjectProperty.isoMk Q
    (oldAppendToDistinctMateModuleIso D Sc cut ν i j hj hi hL hM hij N.obj)

theorem probeAppendToDistinctMateModuleIso_hom (hij : i ≠ j) (N : ProbeEvaluatedModules D Sc m νj) :
    (probeAppendToDistinctMateModuleIso D Sc m ν i j hj hi hL hM hij N).hom =
      (probeAppendToDistinctMate D Sc m ν i j hj hi hL hM).total N := by
  rw [probeAppendToDistinctMate_total]
  apply InducedCategory.hom_ext
  exact oldAppendToDistinctMateModuleIso_hom D Sc cut ν i j hj hi hL hM hij N.obj

local notation "Ei" => probeAppendToE D Sc m ν i νi hi
local notation "V" => probeAppendToE D Sc m νj i ν₂ hL
local notation "A" => probeAppendToRightAdjunction D Sc m ν j νj hj
local notation "B" => probeAppendToRightAdjunction D Sc m νi j ν₂ hM

end OddMath.QuiverHecke
end

end

section

/-! # The selected OLD probe weight mixed mate

Brundan–Ellis (1.12): bend the selected weight crossing by the actual
lower and upper right adjunctions. A missing lower-i predecessor makes
both mixed-functor coordinates zero when the colours differ.
-/
noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open ELVOld CyclotomicAction
universe u

private theorem iso_between_zero
    {C : Type*} [Category C] [Limits.HasZeroMorphisms C] {M P : C} (f : M ⟶ P)
    (hM : Limits.IsZero M) (hP : Limits.IsZero P) : IsIso f := by
  let : Limits.HasZeroObject C := ⟨⟨M, hM⟩⟩
  rw [hM.eq_of_src f 0]
  exact (Limits.isIsoZero_iff_source_target_isZero M P).mpr ⟨hM, hP⟩

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (i j : I) (Λ : X) {x₀ xj xi xu : X}
  (h₁ : x₀ + D.α j = xj) (h₂ : xj + D.α i = xu)
  (h₃ : x₀ + D.α i = xi) (h₄ : xi + D.α j = xu)
local notation "Ei₀" => probeOldE D Sc m i Λ h₃
local notation "Ei₁" => probeOldE D Sc m i Λ h₂
local notation "Fj₀" => probeOldF D Sc m j Λ h₁
local notation "Fj₁" => probeOldF D Sc m j Λ h₄
local notation "Adj₀" => probeOldActionAdjunction D Sc m j Λ h₁
local notation "Adj₁" => probeOldActionAdjunction D Sc m j Λ h₄
local notation "Cross" => probeOldActionCross D Sc m Λ j i h₃ h₄ h₁ h₂

/-- The actual product-weight cup, selected crossing and cap. -/
def probeOldWeightMixedMate : Fj₀ ≫ Ei₀ ⟶ Ei₁ ≫ Fj₁ :=
  SKM.rectangularMate Adj₀ Adj₁ Ei₀ Ei₁ Cross

theorem probeOldWeightMixedMate_mem :
    probeOldWeightMixedMate D Sc m i j Λ h₁ h₂ h₃ h₄ ∈ parity (R := k) _ _
      (D.parity i * D.parity j) := by
  have h := SKM.rectangularMate_piscat_mem Adj₀ Adj₁ Ei₀ Ei₁ Cross
    (probeOldActionCross_mem D Sc m Λ j i h₃ h₄ h₁ h₂)
  simpa only [probeOldWeightMixedMate, mul_comm] using h

/-- Both adjunctions retain their different weight corners. -/
theorem probeOldWeightMixedMate_app (p : ZMod 2) (M : ProbeOldWeightProduct D Sc m Λ xj) :
    (probeOldWeightMixedMate D Sc m i j Λ h₁ h₂ h₃ h₄).app p M =
      (Adj₁).unit.app 0 ((Ei₀).obj ((Fj₀).obj M)) ≫
        (Fj₁).map ((Cross).app p ((Fj₀).obj M)) ≫
          (Fj₁).map ((Ei₁).map ((Adj₀).counit.app 0 M)) :=
  SKM.rectangularMate_piscat_app Adj₀ Adj₁ Ei₀ Ei₁ Cross
    (fun W => Superfunctor.app_eq_zero_of_mem (Adj₁).unit_mem (by decide) W)
    (fun W => Superfunctor.app_eq_zero_of_mem (Adj₀).counit_mem (by decide) W) p M

/-- Every output coordinate keeps the selected weight cup, crossing and cap. -/
theorem probeOldWeightMixedMate_app_block (p : ZMod 2)
    (M : ProbeOldWeightProduct D Sc m Λ xj) (δ : WeightBlocks D Λ xi) :
    (probeOldWeightMixedMate D Sc m i j Λ h₁ h₂ h₃ h₄).app p M δ =
      (probeOldWeightUnitApp D Sc m j Λ h₄ δ ((Ei₀).obj ((Fj₀).obj M)) ≫
        (probeOldBlockRes D Sc m j Λ h₄ δ).map
          ((Cross).app p ((Fj₀).obj M) (blockSucc D Λ j h₄ δ))) ≫
        (probeOldBlockRes D Sc m j Λ h₄ δ).map
          ((probeOldInductionComponent D Sc m i Λ h₂ (blockSucc D Λ j h₄ δ)).map
            ((probeOldWeightCounit D Sc m j Λ h₁).app M)) := by
  have h := congrFun (probeOldWeightMixedMate_app D Sc m i j Λ h₁ h₂ h₃ h₄ p M) δ
  dsimp only [probeOldActionAdjunction, ordinaryEvenSuperAdjunction, probeOldWeightAdjunction,
    SuperNatTrans.ofNatTrans, probeOldWeightUnit, probeOldF, probeOldE, probeOldEFunctor,
    productFunctor, Superfunctor.map, Superfunctor.obj] at h ⊢
  simp only [Pi.comp_apply] at h
  dsimp only [Functor.pi'] at h
  exact h.trans (Category.assoc _ _ _).symm

/-- Adding j does not create a missing i-predecessor at distinct colours. -/
theorem probeOldMixedPredecessor_iff (hij : i ≠ j) (δ : WeightBlocks D Λ xi) :
    (∃ γ, blockSucc D Λ i h₂ γ = blockSucc D Λ j h₄ δ) ↔
      ∃ β, blockSucc D Λ i h₃ β = δ := by
  rw [exists_blockSucc_iff, exists_blockSucc_iff]
  simp only [blockSucc_val, Multiset.mem_add, Multiset.mem_singleton]
  constructor
  · rintro (h | h)
    · exact (hij h).elim
    · exact h
  · exact Or.inr

theorem probeOldWeightMixedSource_isZero (δ : WeightBlocks D Λ xi)
    (hδ : ¬ ∃ β, blockSucc D Λ i h₃ β = δ) (M : ProbeOldWeightProduct D Sc m Λ xj) :
    Limits.IsZero (((Fj₀ ≫ Ei₀).obj M) δ) :=
  probeOldInductionComponent_isZero D Sc m i Λ h₃ δ hδ ((Fj₀).obj M)

theorem probeOldWeightMixedTarget_isZero (hij : i ≠ j) (δ : WeightBlocks D Λ xi)
    (hδ : ¬ ∃ β, blockSucc D Λ i h₃ β = δ) (M : ProbeOldWeightProduct D Sc m Λ xj) :
    Limits.IsZero (((Ei₁ ≫ Fj₁).obj M) δ) := by
  have hUpper : ¬ ∃ γ, blockSucc D Λ i h₂ γ = blockSucc D Λ j h₄ δ :=
    fun h => hδ ((probeOldMixedPredecessor_iff D i j Λ h₂ h₃ h₄ hij δ).mp h)
  have hZero := probeOldInductionComponent_isZero D Sc m i Λ h₂
    (blockSucc D Λ j h₄ δ) hUpper M
  exact (probeOldBlockRes D Sc m j Λ h₄ δ).toFunctor.map_isZero hZero

/-- The prescribed sideways crossing is invertible on every absent output sector. -/
theorem probeOldWeightMixedMate_absent_isIso (hij : i ≠ j) (δ : WeightBlocks D Λ xi)
    (hδ : ¬ ∃ β, blockSucc D Λ i h₃ β = δ) (p : ZMod 2)
    (M : ProbeOldWeightProduct D Sc m Λ xj) :
    IsIso ((probeOldWeightMixedMate D Sc m i j Λ h₁ h₂ h₃ h₄).app p M δ) :=
  iso_between_zero _
    (probeOldWeightMixedSource_isZero D Sc m i j Λ h₁ h₃ δ hδ M)
    (probeOldWeightMixedTarget_isZero D Sc m i j Λ h₂ h₃ h₄ hij δ hδ M)

end OddMath.QuiverHecke
end

end

section

/-! # The chosen stored-target OLD probe dot in the module grid

Brundan–Ellis (1.8): the actual chosen probe block dot retains the
literal signed OLD append transformation used by the induction-grid
slide relations. Only full scalar-evaluation certificates are forgotten.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
open ELVOld ELVOld.BalancedInduction CyclotomicAction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (i : I) (Λ : X) {x y : X} (h : x + D.α i = y)

/-- The physical signed dot of the actual stored-target block append. -/
def probeOldBlockDotArrow (β : WeightBlocks D Λ x)
    (s : OldContentCategory D Sc (probeCutoff D m) β.1.toList) :
    (probeOldBlockAppend D Sc m i Λ h β).obj s ⟶ (probeOldBlockAppend D Sc m i Λ h β).obj s :=
  CyclotomicCrossingTensor.oldAppendDotComponent D Sc (probeCutoff D m) i s.obj

theorem probeOldBlockDotArrow_supernatural (β : WeightBlocks D Λ x) :
    IsSupernatural k (D.parity i) (probeOldBlockDotArrow D Sc m i Λ h β) where
  mem s := (CyclotomicCrossingTensor.oldAppendDot_supernatural D Sc (probeCutoff D m) i).mem s.obj
  naturality hf := (CyclotomicCrossingTensor.oldAppendDot_supernatural D Sc (probeCutoff D m) i).naturality hf

/-- Every chosen block-dot component is the literal OLD induction-grid dot. -/
theorem probeOldBlockDot_app (β : WeightBlocks D Λ x)
    (p : ZMod 2) (M : ProbeCanonicalModules D Sc m β.1) :
    ((probeOldBlockDot D Sc m i Λ h β).app p M).hom =
      (inductionModuleDot (probeOldBlockAppend D Sc m i Λ h β)
        (probeOldBlockDotArrow_supernatural D Sc m i Λ h β)).app p M.obj := by
  unfold probeOldBlockDot probeAppendToInductionDot inductionModuleDot
  dsimp only [IsSupernatural.toSuperNatTrans]
  split_ifs <;> rfl

/-- Total evaluation also retains the exact signed OLD grid dot. -/
theorem probeOldBlockDot_total (β : WeightBlocks D Λ x)
    (M : ProbeCanonicalModules D Sc m β.1) :
    ((probeOldBlockDot D Sc m i Λ h β).total M).hom =
      (inductionModuleDot (probeOldBlockAppend D Sc m i Λ h β)
        (probeOldBlockDotArrow_supernatural D Sc m i Λ h β)).total M.obj := by
  change ((probeOldBlockDot D Sc m i Λ h β).app 0 M).hom +
    ((probeOldBlockDot D Sc m i Λ h β).app 1 M).hom = _
  rw [probeOldBlockDot_app, probeOldBlockDot_app]
  rfl

end OddMath.QuiverHecke
end

end

section

/-! # Distinct slides on the selected OLD probe block pairs

Brundan–Ellis (1.8): the positive rectangular crossing and independently
chosen dots satisfy both slides at arbitrary canonical stored targets.
The literal OLD quotient equations supply the source relations.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
open ELVOld ELVOld.BalancedInduction ELVOld.CyclotomicCrossingTensor CyclotomicAction
universe u
private theorem total_smul {k C A : Type*} [CommRing k]
    [Category C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category A] [Preadditive A] [Linear k A] [Supercategory k A]
    {F G : Superfunctor k C A} (a : k) (f : F ⟶ G) (N : C) :
    (a • f).total N = a • f.total N := by
  change a • f.app 0 N + a • f.app 1 N = a • (f.app 0 N + f.app 1 N)
  exact (smul_add _ _ _).symm

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
section Pair
variable (i j : I) (Λ : X) {x₀ x₁ xu : X}
  (h₁ : x₀ + D.α j = x₁) (h₂ : x₁ + D.α i = xu)

abbrev probeOldPairUpperInd (β : WeightBlocks D Λ x₀) (ε : WeightBlocks D Λ xu)
    (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε) :
    Superfunctor k (ProbeCanonicalModules D Sc m (blockSucc D Λ j h₁ β).1)
      (ProbeCanonicalModules D Sc m ε.1) :=
  ⟨probeEvaluatedAppendTo D Sc m (blockSucc D Λ j h₁ β).1.toList i ε.1.toList
    (probeOldPairUpper_perm D i j Λ h₁ h₂ β ε hε)⟩

abbrev probeOldPairUpperDot (β : WeightBlocks D Λ x₀) (ε : WeightBlocks D Λ xu)
    (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε) :=
  probeAppendToInductionDot D Sc m (blockSucc D Λ j h₁ β).1.toList i ε.1.toList
    (probeOldPairUpper_perm D i j Λ h₁ h₂ β ε hε)

abbrev probeOldBlockPairOuterDotTo (β : WeightBlocks D Λ x₀) (ε : WeightBlocks D Λ xu)
    (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε) :
    End (probeOldBlockPairIndTo D Sc m i j Λ h₁ h₂ β ε hε) :=
  Superfunctor.whiskerLeft (probeOldBlockInd D Sc m j Λ h₁ β)
    (probeOldPairUpperDot D Sc m i j Λ h₁ h₂ β ε hε)

abbrev probeOldBlockPairInnerDotTo (β : WeightBlocks D Λ x₀) (ε : WeightBlocks D Λ xu)
    (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε) :
    End (probeOldBlockPairIndTo D Sc m i j Λ h₁ h₂ β ε hε) :=
  Superfunctor.whiskerRight (probeOldBlockDot D Sc m j Λ h₁ β)
    (probeOldPairUpperInd D Sc m i j Λ h₁ h₂ β ε hε)

local notation "K" => probeOldBlockAppend D Sc m j Λ h₁
local notation "U" => probeOldPairUpperAppend D Sc m i j Λ h₁ h₂

theorem probeOldBlockPairOuterDotTo_total
    (β : WeightBlocks D Λ x₀) (ε : WeightBlocks D Λ xu)
    (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε) (N : ProbeCanonicalModules D Sc m β.1) :
    ((probeOldBlockPairOuterDotTo D Sc m i j Λ h₁ h₂ β ε hε).total N).hom =
      dotEnd (U β ε hε) (probeAppendToDot_supernatural D Sc m (blockSucc D Λ j h₁ β).1.toList i ε.1.toList
        (probeOldPairUpper_perm D i j Λ h₁ h₂ β ε hε)) ((induction (K β)).obj N.obj) := by
  change ((probeAppendToInductionDot D Sc m (blockSucc D Λ j h₁ β).1.toList i ε.1.toList
    (probeOldPairUpper_perm D i j Λ h₁ h₂ β ε hε)).total
      ((probeOldBlockInd D Sc m j Λ h₁ β).obj N)).hom = _
  rw [probeAppendToInductionDot_total]
  rfl

theorem probeOldBlockPairInnerDotTo_total
    (β : WeightBlocks D Λ x₀) (ε : WeightBlocks D Λ xu)
    (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε) (N : ProbeCanonicalModules D Sc m β.1) :
    ((probeOldBlockPairInnerDotTo D Sc m i j Λ h₁ h₂ β ε hε).total N).hom =
      (induction (U β ε hε)).map
        (dotEnd (K β) (probeOldBlockDotArrow_supernatural D Sc m j Λ h₁ β) N.obj) := by
  change (induction (U β ε hε)).map (((probeOldBlockDot D Sc m j Λ h₁ β).app 0 N).hom) +
    (induction (U β ε hε)).map (((probeOldBlockDot D Sc m j Λ h₁ β).app 1 N).hom) = _
  rw [← Functor.map_add]
  change (induction (U β ε hε)).map (((probeOldBlockDot D Sc m j Λ h₁ β).total N).hom) = _
  rw [probeOldBlockDot_total, inductionModuleDot_total]
end Pair

section Crossing
variable (i j : I) (Λ : X) {x₀ xj xi xu : X}
  (h₁ : x₀ + D.α j = xj) (h₂ : xj + D.α i = xu)
  (h₃ : x₀ + D.α i = xi) (h₄ : xi + D.α j = xu)
local notation "sw" => blockSucc₂_swap D i j Λ h₁ h₂ h₃ h₄
local notation "J" => probeOldBlockAppend D Sc m i Λ h₃
local notation "K" => probeOldBlockAppend D Sc m j Λ h₁
local notation "L" => (fun β ε hε => probeOldPairUpperAppend D Sc m j i Λ h₃ h₄ β ε (sw hε))
local notation "U" => probeOldPairUpperAppend D Sc m i j Λ h₁ h₂
local notation "hc" => probeOldBlockDistinctCrossArrow_supernatural D Sc m i j Λ h₁ h₂ h₃ h₄

theorem probeOldBlockDistinctCross_total
    (β : WeightBlocks D Λ x₀) (ε : WeightBlocks D Λ xu)
    (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε) (N : ProbeCanonicalModules D Sc m β.1) :
    ((probeOldBlockDistinctCross D Sc m i j Λ h₁ h₂ h₃ h₄ β ε hε).total N).hom =
      rectangularCrossComponent (J β) (K β) (L β ε hε) (U β ε hε) (hc β ε hε) N.obj := by
  change ((probeOldBlockDistinctCross D Sc m i j Λ h₁ h₂ h₃ h₄ β ε hε).app 0 N).hom +
    ((probeOldBlockDistinctCross D Sc m i j Λ h₁ h₂ h₃ h₄ β ε hε).app 1 N).hom = _
  rw [probeOldBlockDistinctCross_app, probeOldBlockDistinctCross_app]
  exact OddMath.HomogeneousSuperfunctorIso.homogeneous_total
    (F := ⟨(induction (K β)).comp (induction (U β ε hε))⟩)
    (G := ⟨(induction (J β)).comp (induction (L β ε hε))⟩)
    (rectangularCrossComponent_supernatural (J β) (K β) (L β ε hε) (U β ε hε) (hc β ε hε)) N.obj

/-- The chosen crossing carries the source outer dot to the target inner dot. -/
theorem probeOldBlockDistinctCross_slide_inner (hij : i ≠ j)
    (β : WeightBlocks D Λ x₀) (ε : WeightBlocks D Λ xu)
    (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε) :
    probeOldBlockDistinctCross D Sc m i j Λ h₁ h₂ h₃ h₄ β ε hε ≫
      probeOldBlockPairInnerDotTo D Sc m j i Λ h₃ h₄ β ε (sw hε) =
    sign k (D.parity i * D.parity j) •
      (probeOldBlockPairOuterDotTo D Sc m i j Λ h₁ h₂ β ε hε ≫
        probeOldBlockDistinctCross D Sc m i j Λ h₁ h₂ h₃ h₄ β ε hε) := by
  apply OddMath.HomogeneousSuperfunctorIso.total_ext
  intro N
  rw [Superfunctor.comp_total, total_smul, Superfunctor.comp_total]
  apply InducedCategory.hom_ext
  change ((probeOldBlockDistinctCross D Sc m i j Λ h₁ h₂ h₃ h₄ β ε hε).total N).hom ≫
      ((probeOldBlockPairInnerDotTo D Sc m j i Λ h₃ h₄ β ε (sw hε)).total N).hom =
    sign k (D.parity i * D.parity j) •
      (((probeOldBlockPairOuterDotTo D Sc m i j Λ h₁ h₂ β ε hε).total N).hom ≫
        ((probeOldBlockDistinctCross D Sc m i j Λ h₁ h₂ h₃ h₄ β ε hε).total N).hom)
  rw [probeOldBlockDistinctCross_total, probeOldBlockPairInnerDotTo_total,
    probeOldBlockPairOuterDotTo_total]
  have hr := rectangularCrossComponent_slide_inner_outer (J β) (K β) (L β ε hε) (U β ε hε)
    (hc β ε hε) (probeOldBlockDotArrow_supernatural D Sc m i Λ h₃ β)
    (probeAppendToDot_supernatural D Sc m (blockSucc D Λ j h₁ β).1.toList i ε.1.toList
      (probeOldPairUpper_perm D i j Λ h₁ h₂ β ε hε))
    (sign k (D.parity i * D.parity j))
    (fun s => Distinct.crossComponent_slide_first D Sc (probeCutoff D m) hij.symm s.obj) N.obj
  convert! hr using 1

/-- The other chosen dot follows the opposite strand through the same crossing. -/
theorem probeOldBlockDistinctCross_slide_outer (hij : i ≠ j)
    (β : WeightBlocks D Λ x₀) (ε : WeightBlocks D Λ xu)
    (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε) :
    probeOldBlockDistinctCross D Sc m i j Λ h₁ h₂ h₃ h₄ β ε hε ≫
      probeOldBlockPairOuterDotTo D Sc m j i Λ h₃ h₄ β ε (sw hε) =
    sign k (D.parity i * D.parity j) •
      (probeOldBlockPairInnerDotTo D Sc m i j Λ h₁ h₂ β ε hε ≫
        probeOldBlockDistinctCross D Sc m i j Λ h₁ h₂ h₃ h₄ β ε hε) := by
  apply OddMath.HomogeneousSuperfunctorIso.total_ext
  intro N
  rw [Superfunctor.comp_total, total_smul, Superfunctor.comp_total]
  apply InducedCategory.hom_ext
  change ((probeOldBlockDistinctCross D Sc m i j Λ h₁ h₂ h₃ h₄ β ε hε).total N).hom ≫
      ((probeOldBlockPairOuterDotTo D Sc m j i Λ h₃ h₄ β ε (sw hε)).total N).hom =
    sign k (D.parity i * D.parity j) •
      (((probeOldBlockPairInnerDotTo D Sc m i j Λ h₁ h₂ β ε hε).total N).hom ≫
        ((probeOldBlockDistinctCross D Sc m i j Λ h₁ h₂ h₃ h₄ β ε hε).total N).hom)
  rw [probeOldBlockDistinctCross_total, probeOldBlockPairOuterDotTo_total,
    probeOldBlockPairInnerDotTo_total]
  have hr := rectangularCrossComponent_slide_outer_inner (J β) (K β) (L β ε hε) (U β ε hε)
    (hc β ε hε)
    (probeAppendToDot_supernatural D Sc m (blockSucc D Λ i h₃ β).1.toList j ε.1.toList
      (probeOldPairUpper_perm D j i Λ h₃ h₄ β ε (sw hε)))
    (probeOldBlockDotArrow_supernatural D Sc m j Λ h₁ β)
    (sign k (D.parity i * D.parity j))
    (fun s => Distinct.crossComponent_slide_last D Sc (probeCutoff D m) hij.symm s.obj) N.obj
  convert! hr using 1
end Crossing
end OddMath.QuiverHecke
end

end

section

/-! # Supported mixed OLD probe weight coordinates

Brundan–Ellis (1.12): identify the prescribed source and target of the
weight mixed mate with the actual four stored-target append functors.
Every target permutation and selected predecessor is retained.
-/
noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open ELVOld ELVOld.BalancedInduction CyclotomicAction
universe u

private theorem rectangularCross_parity_change
    {k C A B E : Type u} [CommRing k]
    [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
    [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
    [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    (K : C ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
    (L : A ⥤ E) [L.Additive] [L.Linear k] [IsSuperfunctor k L]
    (U : B ⥤ E) [U.Additive] [U.Linear k] [IsSuperfunctor k U]
    {p q : ZMod 2} {α : ∀ s, (J ⋙ L).obj s ⟶ (K ⋙ U).obj s}
    (hp : p = q) (hα : IsSupernatural k p α) (hβ : IsSupernatural k q α)
    (N : Superfunctor k C (SVec k)) :
    rectangularCrossComponent J K L U hα N = rectangularCrossComponent J K L U hβ N := by
  subst q
  rfl

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)

/-- The stored target permutation determined by an actual weight predecessor. -/
theorem probeOldBlockTarget_perm (i : I) (Λ : X) {x y : X} (h : x + D.α i = y)
    (β : WeightBlocks D Λ x) (δ : WeightBlocks D Λ y) (hβ : blockSucc D Λ i h β = δ) :
    (i :: β.1.toList).Perm δ.1.toList := by
  apply Multiset.coe_eq_coe.mp
  rw [Multiset.coe_toList]
  change {i} + (β.1.toList : Multiset I) = δ.1
  rw [Multiset.coe_toList]
  exact congrArg Subtype.val hβ

/-- The selected block induction with its target kept as the literal output block. -/
abbrev probeOldBlockIndTo (i : I) (Λ : X) {x y : X} (h : x + D.α i = y)
    (β : WeightBlocks D Λ x) (δ : WeightBlocks D Λ y) (hβ : blockSucc D Λ i h β = δ) :
    Superfunctor k (ProbeCanonicalModules D Sc m β.1) (ProbeCanonicalModules D Sc m δ.1) :=
  ⟨probeEvaluatedAppendTo D Sc m β.1.toList i δ.1.toList
    (probeOldBlockTarget_perm D i Λ h β δ hβ)⟩

theorem probeOldInductionComponent_obj_of (i : I) (Λ : X) {x y : X} (h : x + D.α i = y)
    (β : WeightBlocks D Λ x) (δ : WeightBlocks D Λ y) (hβ : blockSucc D Λ i h β = δ)
    (M : ProbeOldWeightProduct D Sc m Λ x) :
    (probeOldInductionComponent D Sc m i Λ h δ).obj M =
      (probeOldBlockIndTo D Sc m i Λ h β δ hβ).obj (M β) := by
  subst δ
  exact probeOldInductionComponent_obj_blockSucc D Sc m i Λ h β M

theorem probeOldInductionComponent_map_of (i : I) (Λ : X) {x y : X} (h : x + D.α i = y)
    (β : WeightBlocks D Λ x) (δ : WeightBlocks D Λ y) (hβ : blockSucc D Λ i h β = δ)
    {M N : ProbeOldWeightProduct D Sc m Λ x} (f : M ⟶ N) :
    (probeOldInductionComponent D Sc m i Λ h δ).map f =
      eqToHom (probeOldInductionComponent_obj_of D Sc m i Λ h β δ hβ M) ≫
        (probeOldBlockIndTo D Sc m i Λ h β δ hβ).map (f β) ≫
          eqToHom (probeOldInductionComponent_obj_of D Sc m i Λ h β δ hβ N).symm := by
  subst δ
  exact probeOldInductionComponent_map_blockSucc D Sc m i Λ h β f

variable (i j : I) (Λ : X) {x₀ xj xi xu : X}
  (h₁ : x₀ + D.α j = xj) (h₂ : xj + D.α i = xu)
  (h₃ : x₀ + D.α i = xi) (h₄ : xi + D.α j = xu)
  (β : WeightBlocks D Λ x₀)
local notation "δj" => blockSucc D Λ j h₁ β
local notation "δi" => blockSucc D Λ i h₃ β
local notation "ε" => blockSucc D Λ j h₄ (blockSucc D Λ i h₃ β)
local notation "hComm" => blockSucc_comm D Λ i j h₁ h₂ h₃ h₄ β
local notation "hj" => probeOldBlockTarget_perm D j Λ h₁ β δj rfl
local notation "hi" => probeOldBlockTarget_perm D i Λ h₃ β δi rfl
local notation "hL" => probeOldBlockTarget_perm D i Λ h₂ δj ε hComm
local notation "hU" => probeOldBlockTarget_perm D j Λ h₄ δi ε rfl
local notation "Fj" => probeOldF D Sc m j Λ h₁
local notation "Ei" => probeOldE D Sc m i Λ h₃
local notation "J" => probeOldBlockAppend D Sc m j Λ h₁ β
local notation "K" => probeOldBlockAppend D Sc m i Λ h₃ β
local notation "U" => probeOldBlockAppend D Sc m j Λ h₄ δi
local notation "L" => oldContentAppendTo D Sc (probeCutoff D m)
  (Multiset.toList (Subtype.val δj)) i (Multiset.toList (Subtype.val ε)) hL
local notation "hα" => oldAppendToCross_supernatural D Sc (probeCutoff D m)
  (Multiset.toList (Subtype.val β)) i j hj hi hL hU
local notation "sourcePairEq" => probeOldEFunctor_comp₂_to D Sc m j i Λ h₃ h₄ β ε rfl
local notation "targetPairEq" => probeOldEFunctor_comp₂_to D Sc m i j Λ h₁ h₂ β ε hComm

attribute [local irreducible] rectangularCrossComponent

/-- The supported source is the stored-target lower restriction-induction. -/
theorem probeOldWeightMixedSource_obj (M : ProbeOldWeightProduct D Sc m Λ xj) :
    (((probeOldF D Sc m j Λ h₁ ≫ probeOldE D Sc m i Λ h₃).obj M) δi) =
      (probeAppendToDistinctMateSource D Sc m β.1.toList i j hj hi).obj (M δj) :=
  probeOldInductionComponent_obj_blockSucc D Sc m i Λ h₃ β ((Fj).obj M)

/-- The supported target uses the same literal common upper block. -/
theorem probeOldWeightMixedTarget_obj (M : ProbeOldWeightProduct D Sc m Λ xj) :
    (((probeOldE D Sc m i Λ h₂ ≫ probeOldF D Sc m j Λ h₄).obj M) δi) =
      (probeAppendToDistinctMateTarget D Sc m i j hL hU).obj (M δj) := by
  exact congrArg (fun P => (probeOldBlockRes D Sc m j Λ h₄ δi).obj P)
    (probeOldInductionComponent_obj_of D Sc m i Λ h₂ δj ε hComm M)

/-- The selected positive block crossing is the constructed stored-target crossing. -/
theorem probeOldBlockDistinctCross_mixed_eq :
    probeOldBlockDistinctCross D Sc m j i Λ h₃ h₄ h₁ h₂ β ε rfl =
      probeAppendToCross D Sc m β.1.toList i j hj hi hL hU := by
  let F := probeOldBlockPairIndTo D Sc m j i Λ h₃ h₄ β ε rfl
  let G := probeOldBlockPairIndTo D Sc m i j Λ h₁ h₂ β ε hComm
  apply HomogeneousSuperfunctorIso.total_ext (F := F) (G := G)
  intro N
  apply InducedCategory.hom_ext
  have hb := probeOldBlockDistinctCross_total D Sc m j i Λ h₃ h₄ h₁ h₂ β ε rfl N
  have hg := probeAppendToCross_direct_total D Sc m β.1.toList i j hj hi hL hU N
  have hblock : IsSupernatural k (D.parity j * D.parity i)
      (oldAppendToCross D Sc (probeCutoff D m) β.1.toList i j hj hi hL hU) :=
    probeOldBlockDistinctCrossArrow_supernatural D Sc m j i Λ h₃ h₄ h₁ h₂ β ε rfl
  have hx := rectangularCross_parity_change J K L U
    (mul_comm (D.parity j) (D.parity i)) hblock hα N.obj
  exact hb.trans (hx.trans hg.symm)

/-- The actual selected weight crossing retains its occupied rectangular coordinate. -/
theorem probeOldWeightMixedCross_comparison (hij : i ≠ j) (p : ZMod 2)
    (M : ProbeOldWeightProduct D Sc m Λ xj) :
    (probeOldActionCross D Sc m Λ j i h₃ h₄ h₁ h₂).app p ((Fj).obj M) ε =
      (eqToHom (Functor.congr_obj sourcePairEq ((Fj).obj M)) ≫
        (probeAppendToCross D Sc m β.1.toList i j hj hi hL hU).app p (((Fj).obj M) β)) ≫
        eqToHom (Functor.congr_obj targetPairEq ((Fj).obj M)).symm := by
  rw [probeOldActionCross_distinct D Sc m Λ j i hij.symm h₃ h₄ h₁ h₂]
  change probeOldWeightDistinctCrossComponent D Sc m j i Λ h₃ h₄ h₁ h₂ p ((Fj).obj M) ε = _
  rw [probeOldWeightDistinctCrossComponent_of D Sc m j i Λ h₃ h₄ h₁ h₂ p ((Fj).obj M) β ε rfl,
    probeOldWeightDistinctCrossVia_component D Sc m j i Λ h₃ h₄ h₁ h₂ β ε rfl p ((Fj).obj M),
    probeOldBlockDistinctCross_mixed_eq D Sc m i j Λ h₁ h₂ h₃ h₄ β]
  simp only [Category.assoc]

end OddMath.QuiverHecke
end

end

section

/-! # The selected probe weight cup and cap in mixed coordinates

Brundan–Ellis (1.12): paste the actual weight adjunction maps through
the occupied stored-content coordinates of the prescribed crossing.
-/
noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open ELVOld ELVOld.BalancedInduction CyclotomicAction
universe u

private theorem unit_transport
    {C A : Type*} [Category* C] [Category* A] (E : C ⥤ A) (F : A ⥤ C) (a : E ⊣ F)
    {P Q : C} {W : A} (hPQ : P = Q) (hWP : W = E.obj P) (hWQ : W = E.obj Q) :
    ((a.unit.app P ≫ F.map (eqToHom hWP.symm)) ≫ F.map (eqToHom hWQ)) =
      eqToHom hPQ ≫ a.unit.app Q := by
  subst Q
  subst W
  simp only [eqToHom_refl, CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]
  exact Category.comp_id _

private theorem map_counit_transport
    {A E : Type*} [Category* A] [Category* E] (L : A ⥤ E)
    {Y Z T : A} {P Q : E} (hYZ : Y = Z) (hP : P = L.obj Y)
    (hQ : Q = L.obj T) (hPZ : P = L.obj Z) (f : Z ⟶ T) :
    (eqToHom hP ≫ L.map (eqToHom hYZ ≫ f) ≫ eqToHom hQ.symm) ≫ eqToHom hQ =
      eqToHom hPZ ≫ L.map f := by
  subst Z
  subst P
  subst Q
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (i j : I) (Λ : X) {x₀ xj xi xu : X}
  (h₁ : x₀ + D.α j = xj) (h₂ : xj + D.α i = xu)
  (h₃ : x₀ + D.α i = xi) (h₄ : xi + D.α j = xu)
  (β : WeightBlocks D Λ x₀)
local notation "δj" => blockSucc D Λ j h₁ β
local notation "δi" => blockSucc D Λ i h₃ β
local notation "ε" => blockSucc D Λ j h₄ (blockSucc D Λ i h₃ β)
local notation "hComm" => blockSucc_comm D Λ i j h₁ h₂ h₃ h₄ β
local notation "ν" => Multiset.toList (Subtype.val β)
local notation "νj" => Multiset.toList (Subtype.val δj)
local notation "νi" => Multiset.toList (Subtype.val δi)
local notation "ν₂" => Multiset.toList (Subtype.val ε)
local notation "hj" => probeOldBlockTarget_perm D j Λ h₁ β δj rfl
local notation "hi" => probeOldBlockTarget_perm D i Λ h₃ β δi rfl
local notation "hL" => probeOldBlockTarget_perm D i Λ h₂ δj ε hComm
local notation "hU" => probeOldBlockTarget_perm D j Λ h₄ δi ε rfl
local notation "Fj" => probeOldF D Sc m j Λ h₁
local notation "Ei" => probeOldE D Sc m i Λ h₃
local notation "IndU" => probeOldBlockInd D Sc m j Λ h₄ δi
local notation "ResU" => probeOldBlockRes D Sc m j Λ h₄ δi
local notation "IndL" => probeOldBlockIndTo D Sc m i Λ h₂ δj ε hComm
local notation "sourcePairEq" => probeOldEFunctor_comp₂_to D Sc m j i Λ h₃ h₄ β ε rfl
local notation "targetPairEq" => probeOldEFunctor_comp₂_to D Sc m i j Λ h₁ h₂ β ε hComm

/-- The selected upper cup respects the source and pair coordinates. -/
theorem probeOldWeightMixedUnit_comparison (M : ProbeOldWeightProduct D Sc m Λ xj) :
    probeOldWeightUnitApp D Sc m j Λ h₄ δi ((Ei).obj ((Fj).obj M)) ≫
        (ResU).map (eqToHom (Functor.congr_obj sourcePairEq ((Fj).obj M))) =
      eqToHom (probeOldWeightMixedSource_obj D Sc m i j Λ h₁ h₃ β M) ≫
        (probeAppendToUnit D Sc m νi j ν₂ hU).app
          ((probeAppendToDistinctMateSource D Sc m ν i j hj hi).obj (M δj)) := by
  have h := unit_transport (IndU).toFunctor (ResU).toFunctor (probeOldBlockAdj D Sc m j Λ h₄ δi)
    (probeOldWeightMixedSource_obj D Sc m i j Λ h₁ h₃ β M)
    (probeOldInductionComponent_obj_blockSucc D Sc m j Λ h₄ δi ((Ei).obj ((Fj).obj M)))
    (Functor.congr_obj sourcePairEq ((Fj).obj M))
  dsimp only [probeOldWeightUnitApp, probeOldBlockAdj, probeAppendToAdjunction] at h ⊢
  exact h

/-- The selected lower cap respects the pair and target coordinates. -/
theorem probeOldWeightMixedCounit_comparison (M : ProbeOldWeightProduct D Sc m Λ xj) :
    (probeOldInductionComponent D Sc m i Λ h₂ ε).map
        ((probeOldWeightCounit D Sc m j Λ h₁).app M) ≫
        eqToHom (probeOldInductionComponent_obj_of D Sc m i Λ h₂ δj ε hComm M) =
      eqToHom (Functor.congr_obj targetPairEq ((Fj).obj M)) ≫
        (IndL).map ((probeAppendToCounit D Sc m ν j νj hj).app (M δj)) := by
  have hm := probeOldInductionComponent_map_of D Sc m i Λ h₂ δj ε hComm
    ((probeOldWeightCounit D Sc m j Λ h₁).app M)
  dsimp only [probeOldWeightCounit] at hm
  rw [probeOldWeightCounitComponent_blockSucc] at hm
  have ht := congrArg (fun f => f ≫
    eqToHom (probeOldInductionComponent_obj_of D Sc m i Λ h₂ δj ε hComm M)) hm
  have h := map_counit_transport (IndL).toFunctor
    (probeOldInductionComponent_obj_blockSucc D Sc m j Λ h₁ β ((Fj).obj M))
    (probeOldInductionComponent_obj_of D Sc m i Λ h₂ δj ε hComm
      ((probeOldE D Sc m j Λ h₁).obj ((Fj).obj M)))
    (probeOldInductionComponent_obj_of D Sc m i Λ h₂ δj ε hComm M)
    (Functor.congr_obj targetPairEq ((Fj).obj M))
    ((probeOldBlockAdj D Sc m j Λ h₁ β).counit.app (M δj))
  dsimp only [probeOldBlockAdj, probeAppendToAdjunction] at h ht ⊢
  exact ht.trans h

end OddMath.QuiverHecke
end

end

section

/-! # The selected equal-colour mate under OLD content reindexing

Brundan–Ellis (1.13)–(1.14): compare the prescribed negative
cup-crossing-cap by its single-coend tensor formula. The append adjunction
comparisons retain the whole coefficient arrow and its super twist.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
open ELVOld ELVOld.BalancedInduction
universe u
attribute [local irreducible] oldAppendReindexLinear oldAppendReindexIso orderedGridMateLinear
private theorem linear_square_point {k V W V' W' : Type*} [CommRing k]
    [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]
    [AddCommMonoid V'] [Module k V'] [AddCommMonoid W'] [Module k W']
    (a : V →ₗ[k] W) (b : V' →ₗ[k] W') (l : V →ₗ[k] V') (r : W →ₗ[k] W')
    (v : V) (w : W) (v' : V') (w' : W')
    (ha : a v = w) (hr : r w = w') (hl : l v = v') (hb : b v' = w') :
    (r ∘ₗ a) v = (b ∘ₗ l) v :=
  (congrArg r ha).trans (hr.trans ((congrArg b hl).trans hb).symm)

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (ν : List I) (i : I) {ν₁ ν₂ : List I}
  (h₁ : (i :: ν).Perm ν₁) (h₂ : (i :: ν₁).Perm ν₂)
local notation "J₀" => oldContentAppendTo D Sc cutoff ν i (i :: ν) (List.Perm.refl _)
local notation "K₀" => oldContentAppendTo D Sc cutoff (i :: ν) i (i :: i :: ν) (List.Perm.refl _)
local notation "J" => oldContentAppendTo D Sc cutoff ν i ν₁ h₁
local notation "K" => oldContentAppendTo D Sc cutoff ν₁ i ν₂ h₂
local notation "Q⁻¹" => oldContentReindex D Sc cutoff h₁.symm
local notation "R₁" => oldModuleReindex D Sc cutoff h₁

/-- The physical equal crossing at the two prescribed stored-target appends. -/
def oldAppendToEqualCross (s : OldContentCategory D Sc cutoff ν) :
    (J ⋙ K).obj s ⟶ (J ⋙ K).obj s :=
  CyclotomicCrossingTensor.equalCrossComponent D Sc cutoff i s.obj

theorem oldAppendToEqualCross_supernatural :
    IsSupernatural k (D.parity i) (oldAppendToEqualCross D Sc cutoff ν i h₁ h₂) := by
  have h : IsSupernatural k (D.parity i * D.parity i)
      (oldAppendToEqualCross D Sc cutoff ν i h₁ h₂) := {
    mem := fun s => (CyclotomicCrossingTensor.equalCross_supernatural D Sc cutoff i).mem s.obj
    naturality := fun hf =>
      (CyclotomicCrossingTensor.equalCross_supernatural D Sc cutoff i).naturality hf }
  simpa only [SKM.zmod2_mul_self] using h
local notation "hγ₀" => oldAppendToEqualCross_supernatural D Sc cutoff ν i
  (List.Perm.refl (i :: ν)) (List.Perm.refl (i :: i :: ν))
local notation "hγ" => oldAppendToEqualCross_supernatural D Sc cutoff ν i h₁ h₂

/-- The selected lower comparison, with the local coend carriers fixed. -/
def oldReindexLowerLoopLinear
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k))
    (t : OldContentCategory D Sc cutoff ν₁) :
    Obj J₀ ((restriction J₀).obj N).toFunctor ((Q⁻¹).obj t) →ₗ[k]
      Obj J ((restriction J).obj ((R₁).obj N)).toFunctor t :=
  oldAppendReindexLinear D Sc cutoff (List.Perm.refl ν) i
    (List.Perm.refl (i :: ν)) h₁ h₁ ((restriction J₀).obj N) t

/-- The selected upper comparison, with the local coend carriers fixed. -/
def oldReindexUpperLoopLinear
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k))
    (t : OldContentCategory D Sc cutoff ν₁) :
    Obj K₀ N.toFunctor ((K₀).obj ((Q⁻¹).obj t)) →ₗ[k]
      Obj K ((R₁).obj N).toFunctor ((K).obj t) :=
  oldAppendReindexLinear D Sc cutoff h₁ i (List.Perm.refl (i :: i :: ν)) h₂
    ((h₁.cons i).trans h₂) N ((K).obj t)

/-- The upper loop comparison keeps a complete coefficient and vector. -/
theorem oldReindexUpperLoopLinear_tensor
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k))
    (t : OldContentCategory D Sc cutoff ν₁)
    (s : OldContentCategory D Sc cutoff (i :: ν))
    (g : (K₀).obj s ⟶ (K₀).obj ((Q⁻¹).obj t)) (v : N.obj s) :
    oldReindexUpperLoopLinear D Sc cutoff ν i h₁ h₂ N t (tensor K₀ N.toFunctor (w := (K₀).obj ((Q⁻¹).obj t)) s g v) =
      tensor K ((R₁).obj N).toFunctor (w := (K).obj t) ((oldContentReindex D Sc cutoff h₁).obj s) g v := by
  let g' : (K₀).obj s ⟶
      (oldContentReindex D Sc cutoff ((h₁.cons i).trans h₂).symm).obj ((K).obj t) := g
  have h := oldAppendReindexIso_hom_tensor D Sc cutoff h₁ i
    (List.Perm.refl (i :: i :: ν)) h₂ ((h₁.cons i).trans h₂) N s ((K).obj t) g' v
  set_option backward.dsimp.instances true in
    dsimp only [oldReindexUpperLoopLinear, oldModuleReindex, g'] at h ⊢
  convert! h using 1

/-- The lower loop comparison keeps a complete coefficient and vector. -/
theorem oldReindexLowerLoopLinear_tensor
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k))
    (t : OldContentCategory D Sc cutoff ν₁) (s : OldContentCategory D Sc cutoff ν)
    (g : (J₀).obj s ⟶ (Q⁻¹).obj t) (v : N.obj ((J₀).obj s)) :
    oldReindexLowerLoopLinear D Sc cutoff ν i h₁ N t
        (tensor J₀ ((restriction J₀).obj N).toFunctor (w := (Q⁻¹).obj t) s g v) =
      tensor J ((restriction J).obj ((R₁).obj N)).toFunctor (w := t) s g v := by
  have h := oldAppendReindexIso_hom_tensor D Sc cutoff (List.Perm.refl ν) i
    (List.Perm.refl (i :: ν)) h₁ h₁ ((restriction J₀).obj N) s t g v
  set_option backward.dsimp.instances true in
    dsimp only [oldReindexLowerLoopLinear, oldModuleReindex] at h ⊢
  convert! h using 1

/-- The exact negative mate intertwines the chosen lower and upper comparisons. -/
theorem oldReindexLoopLinear_mate
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k))
    (t : OldContentCategory D Sc cutoff ν₁) :
    oldReindexUpperLoopLinear D Sc cutoff ν i h₁ h₂ N t ∘ₗ
        orderedGridMateLinear J₀ K₀ hγ₀ N ((Q⁻¹).obj t) =
      orderedGridMateLinear J K hγ ((R₁).obj N) t ∘ₗ oldReindexLowerLoopLinear D Sc cutoff ν i h₁ N t := by
  let N₀ := N
  let N₁ := (R₁).obj N
  let t₀ := (Q⁻¹).obj t
  let V := Obj J₀ ((restriction J₀).obj N₀).toFunctor t₀
  let W := Obj K₀ N₀.toFunctor ((K₀).obj t₀)
  let V' := Obj J ((restriction J).obj ((R₁).obj N)).toFunctor t
  let W' := Obj K ((R₁).obj N).toFunctor ((K).obj t)
  let a : V →ₗ[k] W := orderedGridMateLinear J₀ K₀ hγ₀ N₀ t₀
  let b : V' →ₗ[k] W' := orderedGridMateLinear J K hγ N₁ t
  let l : V →ₗ[k] V' := oldReindexLowerLoopLinear D Sc cutoff ν i h₁ N t
  let r : W →ₗ[k] W' := oldReindexUpperLoopLinear D Sc cutoff ν i h₁ h₂ N t
  change r ∘ₗ a = b ∘ₗ l
  apply hom_ext J₀ ((restriction J₀).obj N₀).toFunctor (w := t₀)
  intro s g v
  have h₀ := orderedGridMateLinear_tensor J₀ K₀ hγ₀ N₀ s t₀ g v
  have h₃ := orderedGridMateLinear_tensor J K hγ N₁ s t g v
  let v₀ : V := tensor J₀ ((restriction J₀).obj N₀).toFunctor (w := t₀) s g v
  let z₀ : W := tensor K₀ N₀.toFunctor (w := (K₀).obj t₀) ((J₀).obj s)
    (-(oldAppendToEqualCross D Sc cutoff ν i (List.Perm.refl _) (List.Perm.refl _) s ≫
      twist k (D.parity i) ((K₀).map g))) v
  let v₁ : V' := tensor J ((restriction J).obj N₁).toFunctor (w := t) s g v
  let z₁ : W' := tensor K N₁.toFunctor (w := (K).obj t) ((J).obj s)
    (-(oldAppendToEqualCross D Sc cutoff ν i h₁ h₂ s ≫
      twist k (D.parity i) ((K).map g))) v
  have ha : a v₀ = z₀ := by convert! h₀ using 1
  have hr : r z₀ = z₁ := by
    dsimp only [r, z₀, z₁, N₀, N₁]
    rw [oldReindexUpperLoopLinear_tensor]
    rfl
  have hl : l v₀ = v₁ := by
    dsimp only [l, v₀, v₁, N₀, N₁]
    rw [oldReindexLowerLoopLinear_tensor]
  have hb : b v₁ = z₁ := by convert! h₃ using 1
  exact linear_square_point (k := k) (V := V) (W := W) (V' := V') (W' := W')
    a b l r v₀ z₀ v₁ z₁ ha hr hl hb
end OddMath.QuiverHecke
end

end

section

/-! # Chosen local fields at stored probe representatives

Brundan–Ellis (1.7)–(1.8), (1.13)–(1.14): the stored-target evaluated
append functors retain the physical dots, negative crossing and ordered
ordinary-adjunction mate. All homogeneous components are identified with
the specified OLD module maps.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open ELVOld ELVOld.BalancedInduction CyclotomicAction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (ν : List I) (i : I) {ν₁ ν₂ : List I}
  (h₁ : (i :: ν).Perm ν₁) (h₂ : (i :: ν₁).Perm ν₂)
local notation "cut" => probeCutoff D m
local notation "J" => oldContentAppendTo D Sc cut ν i ν₁ h₁
local notation "K" => oldContentAppendTo D Sc cut ν₁ i ν₂ h₂
local notation "hγ" => oldAppendToEqualCross_supernatural D Sc cut ν i h₁ h₂
local notation "P₀" => ProbeEvaluatesCoefficients D m Sc ν
local notation "P₁" => ProbeEvaluatesCoefficients D m Sc ν₁
local notation "P₂" => ProbeEvaluatesCoefficients D m Sc ν₂
local notation "E₀" => probeEvaluatedAppendTo D Sc m ν i ν₁ h₁
local notation "E₁" => probeEvaluatedAppendTo D Sc m ν₁ i ν₂ h₂

private theorem appendPair_closed
    (N : Superfunctor k (OldContentCategory D Sc cut ν) (SVec k)) (hN : P₀ N) :
    P₂ (((inductionModuleCell (k := k) J) ≫ inductionModuleCell (k := k) K).obj N) :=
  ((E₀ ⋙ E₁).obj ⟨N, hN⟩).property

/-- The chosen negative crossing at two actual stored-target append functors. -/
def probeAppendToEqualCross :
    End (⟨E₀ ⋙ E₁⟩ : Superfunctor k (ProbeEvaluatedModules D Sc m ν)
      (ProbeEvaluatedModules D Sc m ν₂)) :=
  fullLiftTrans P₀ P₂ (appendPair_closed D Sc m ν i h₁ h₂)
    (appendPair_closed D Sc m ν i h₁ h₂) (inductionModuleCross J K hγ)

theorem probeAppendToEqualCross_total (N : ProbeEvaluatedModules D Sc m ν) :
    ((probeAppendToEqualCross D Sc m ν i h₁ h₂).total N).hom =
      (inductionModuleCross J K hγ).total N.obj := rfl

theorem probeAppendToInductionDot_app (q : ZMod 2) (N : ProbeEvaluatedModules D Sc m ν) :
    ((probeAppendToInductionDot D Sc m ν i ν₁ h₁).app q N).hom =
      (inductionModuleDot J (probeAppendToDot_supernatural D Sc m ν i ν₁ h₁)).app q N.obj := by
  change (if q = D.parity i then probeAppendToDotComponent D Sc m ν i ν₁ h₁ N else 0).hom =
    if q = D.parity i then transformComponent (probeAppendToDot_supernatural D Sc m ν i ν₁ h₁) N.obj else 0
  split_ifs <;> rfl

/-- Ordered powers of the chosen dot on stored-target evaluated induction. -/
abbrev probeAppendToDotPower (n : ℕ) :
    End (⟨E₀⟩ : Superfunctor k (ProbeEvaluatedModules D Sc m ν) (ProbeEvaluatedModules D Sc m ν₁)) :=
  SKM.rouquierPower (a := probeEvaluatedTarget D Sc m ν) (b := probeEvaluatedTarget D Sc m ν₁)
    (E := probeAppendToE D Sc m ν i ν₁ h₁) (probeAppendToInductionDot D Sc m ν i ν₁ h₁) n

/-- The corresponding ordered powers in the OLD module categories. -/
abbrev oldAppendToDotPower (n : ℕ) : End (inductionModuleCell (k := k) J) :=
  SKM.rouquierPower
    (a := inductionModulePiCategory (k := k) (OldContentCategory D Sc cut ν))
    (b := inductionModulePiCategory (k := k) (OldContentCategory D Sc cut ν₁))
    (E := inductionModuleCell (k := k) J)
    (inductionModuleDot J (probeAppendToDot_supernatural D Sc m ν i ν₁ h₁)) n

/-- Every homogeneous component of every ordered dot power is retained. -/
theorem probeAppendToDotPower_app (n : ℕ) (q : ZMod 2) (N : ProbeEvaluatedModules D Sc m ν) :
    ((probeAppendToDotPower D Sc m ν i h₁ n).app q N).hom =
      (oldAppendToDotPower D Sc m ν i h₁ n).app q N.obj := by
  induction n generalizing q with
  | zero =>
    change (if q = 0 then 𝟙 ((E₀).obj N) else 0).hom =
      if q = 0 then 𝟙 ((inductionModuleCell (k := k) J).obj N.obj) else 0
    split_ifs <;> rfl
  | succ n ih =>
    change ((probeAppendToDotPower D Sc m ν i h₁ n).app 0 N).hom ≫
        ((probeAppendToInductionDot D Sc m ν i ν₁ h₁).app q N).hom +
      ((probeAppendToDotPower D Sc m ν i h₁ n).app 1 N).hom ≫
        ((probeAppendToInductionDot D Sc m ν i ν₁ h₁).app (q + 1) N).hom =
      (oldAppendToDotPower D Sc m ν i h₁ n).app 0 N.obj ≫
        (inductionModuleDot J (probeAppendToDot_supernatural D Sc m ν i ν₁ h₁)).app q N.obj +
      (oldAppendToDotPower D Sc m ν i h₁ n).app 1 N.obj ≫
        (inductionModuleDot J (probeAppendToDot_supernatural D Sc m ν i ν₁ h₁)).app (q + 1) N.obj
    rw [ih 0, ih 1, probeAppendToInductionDot_app, probeAppendToInductionDot_app]

local notation "R₀" => probeEvaluatedTarget D Sc m ν
local notation "R₁" => probeEvaluatedTarget D Sc m ν₁
local notation "R₂" => probeEvaluatedTarget D Sc m ν₂
local notation "e₀" => probeAppendToE D Sc m ν i ν₁ h₁
local notation "f₀" => probeAppendToF D Sc m ν i ν₁ h₁
local notation "e₁" => probeAppendToE D Sc m ν₁ i ν₂ h₂
local notation "f₁" => probeAppendToF D Sc m ν₁ i ν₂ h₂
local notation "A₀" => probeAppendToRightAdjunction D Sc m ν i ν₁ h₁
local notation "A₁" => probeAppendToRightAdjunction D Sc m ν₁ i ν₂ h₂

/-- The ordered mate of the selected negative crossing and selected right adjunctions. -/
def probeAppendToMate :
    (⟨probeEvaluatedRestrictTo D Sc m ν i ν₁ h₁ ⋙ E₀⟩ :
      Superfunctor k (ProbeEvaluatedModules D Sc m ν₁) (ProbeEvaluatedModules D Sc m ν₁)) ⟶
    ⟨E₁ ⋙ probeEvaluatedRestrictTo D Sc m ν₁ i ν₂ h₂⟩ :=
  SKM.rouquierMate (a := R₀) (b := R₁) (c := R₂)
    («E₁» := e₀) («F₁» := f₀) («E₂» := e₁) («F₂» := f₁)
    A₀ A₁ (probeAppendToEqualCross D Sc m ν i h₁ h₂)

/-- Every component of the ordered mate is the prescribed OLD component. -/
theorem probeAppendToMate_app (q : ZMod 2) (N : ProbeEvaluatedModules D Sc m ν₁) :
    ((probeAppendToMate D Sc m ν i h₁ h₂).app q N).hom =
      (SKM.rouquierMate (inductionModuleAdjunction (k := k) J)
        (inductionModuleAdjunction (k := k) K) (inductionModuleCross J K hγ)).app q N.obj := by
  unfold probeAppendToMate
  erw [SKM.rouquierMate_piscat_app, SKM.rouquierMate_piscat_app]
  rfl

end OddMath.QuiverHecke
end

end

section

/-! # The chosen rank-one probe weight mate in stored coordinates

Brundan–Ellis (1.13)–(1.14): the principal entry uses the prescribed
negative equal crossing, the upper unit and the lower counit. Its
occupied coordinate is the same selected stored-target Rouquier mate.
-/
noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open ELVOld ELVOld.BalancedInduction CyclotomicAction
universe u
private theorem mate_transport
    {A B : Type*} [Category* A] [Category* B] (R : A ⥤ B)
    {P Q : B} {S T V S' T' V' : A}
    (hP : P = Q) (hS : S = S') (hT : T = T') (hV : V = V')
    (η : P ⟶ R.obj S) (χ : S ⟶ T) (ε : T ⟶ V)
    (η' : Q ⟶ R.obj S') (χ' : S' ⟶ T') (ε' : T' ⟶ V')
    (hu : η ≫ R.map (eqToHom hS) = eqToHom hP ≫ η')
    (hx : χ = (eqToHom hS ≫ χ') ≫ eqToHom hT.symm)
    (hc : ε ≫ eqToHom hV = eqToHom hT ≫ ε') :
    ((η ≫ R.map χ) ≫ R.map ε) ≫ R.map (eqToHom hV) =
      eqToHom hP ≫ (η' ≫ R.map χ' ≫ R.map ε') := by
  subst Q
  subst S'
  subst T'
  subst V'
  simp only [eqToHom_refl, CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp] at hu hx hc ⊢
  rw [hu, hx, hc]
  exact Category.assoc _ _ _

private theorem storedMate_expansion
    {I X k : Type u} [AddCommGroup X] [CommRing k]
    (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
    (ν : List I) (i : I) {ν₁ ν₂ : List I}
    (h₁ : (i :: ν).Perm ν₁) (h₂ : (i :: ν₁).Perm ν₂)
    (p : ZMod 2) (N : ProbeEvaluatedModules D Sc m ν₁) :
    (probeAppendToMate D Sc m ν i h₁ h₂).app p N =
      (probeAppendToUnit D Sc m ν₁ i ν₂ h₂).app
          ((probeEvaluatedAppendTo D Sc m ν i ν₁ h₁).obj
            ((probeEvaluatedRestrictTo D Sc m ν i ν₁ h₁).obj N)) ≫
        (probeEvaluatedRestrictTo D Sc m ν₁ i ν₂ h₂).map
          ((probeAppendToEqualCross D Sc m ν i h₁ h₂).app p
            ((probeEvaluatedRestrictTo D Sc m ν i ν₁ h₁).obj N)) ≫
        (probeEvaluatedRestrictTo D Sc m ν₁ i ν₂ h₂).map
          ((probeEvaluatedAppendTo D Sc m ν₁ i ν₂ h₂).map
            ((probeAppendToCounit D Sc m ν i ν₁ h₁).app N)) := by
  unfold probeAppendToMate
  erw [SKM.rouquierMate_piscat_app]
  rfl

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (i : I) (Λ : X) {x₀ x₁ x₂ : X}
  (h₁ : x₀ + D.α i = x₁) (h₂ : x₁ + D.α i = x₂)
local notation "A₁" => probeOldActionAdjunction D Sc m i Λ h₁
local notation "A₂" => probeOldActionAdjunction D Sc m i Λ h₂
local notation "Cross" => probeOldActionCross D Sc m Λ i i h₁ h₂ h₁ h₂
local notation "φ" => SKM.rouquierMate A₁ A₂ Cross
local notation "E" => probeOldE D Sc m i Λ h₁
local notation "F" => probeOldF D Sc m i Λ h₁

/-- The prescribed rank-one mate is the same selected cup-crossing-cap. -/
theorem probeOldWeightRouquierMate_eq :
    φ = probeOldWeightMixedMate D Sc m i i Λ h₁ h₂ h₁ h₂ :=
  SKM.rouquierMate_piscat_eq_rectangular A₁ A₂ Cross

theorem probeOldWeightRouquierMate_mem : φ ∈ parity (R := k) _ _ (D.parity i) := by
  rw [probeOldWeightRouquierMate_eq]
  simpa only [SKM.zmod2_mul_self] using
    probeOldWeightMixedMate_mem D Sc m i i Λ h₁ h₂ h₁ h₂

variable (β : WeightBlocks D Λ x₀)
local notation "δ" => blockSucc D Λ i h₁ β
local notation "ε" => blockSucc D Λ i h₂ (blockSucc D Λ i h₁ β)
local notation "ν" => Multiset.toList (Subtype.val β)
local notation "ν₁" => Multiset.toList (Subtype.val δ)
local notation "ν₂" => Multiset.toList (Subtype.val ε)
local notation "hl" => probeOldBlockTarget_perm D i Λ h₁ β (blockSucc D Λ i h₁ β) rfl
local notation "hu" => probeOldBlockTarget_perm D i Λ h₂ δ (blockSucc D Λ i h₂ δ) rfl
local notation "Res" => probeOldBlockRes D Sc m i Λ h₂ δ
local notation "Ind" => probeOldBlockInd D Sc m i Λ h₂ δ
local notation "pairEq" => probeOldEFunctor_comp₂_to D Sc m i i Λ h₁ h₂ β ε rfl

/-- Both negative equal crossings are the same whole selected stored map. -/
theorem probeOldBlockEqualCross_stored_eq :
    probeOldBlockEqualCross D Sc m i Λ h₁ h₂ β =
      probeAppendToEqualCross D Sc m ν i hl hu := by
  apply HomogeneousSuperfunctorIso.total_ext
  intro N
  apply InducedCategory.hom_ext
  rw [probeOldBlockEqualCross_total, probeAppendToEqualCross_total]

private theorem cross_comparison (p : ZMod 2) (M : ProbeOldWeightProduct D Sc m Λ x₁) :
    (Cross).app p ((F).obj M) ε =
      (eqToHom (Functor.congr_obj pairEq ((F).obj M)) ≫
        (probeAppendToEqualCross D Sc m ν i hl hu).app p (((F).obj M) β)) ≫
        eqToHom (Functor.congr_obj pairEq ((F).obj M)).symm := by
  rw [probeOldActionCross_equal]
  change probeOldWeightEqualCrossComponent D Sc m i Λ h₁ h₂ p ((F).obj M) ε = _
  rw [probeOldWeightEqualCrossComponent_of D Sc m i Λ h₁ h₂ p ((F).obj M) β ε rfl,
    probeOldWeightEqualCrossVia_component, probeOldBlockEqualCross_stored_eq]
  simp only [Category.assoc]

/-- Every occupied principal component retains the selected stored mate at every parity. -/
theorem probeOldWeightRouquierMate_comparison (p : ZMod 2)
    (M : ProbeOldWeightProduct D Sc m Λ x₁) :
    (φ).app p M δ ≫
        eqToHom (probeOldWeightMixedTarget_obj D Sc m i i Λ h₁ h₂ h₁ h₂ β M) =
      eqToHom (probeOldWeightMixedSource_obj D Sc m i i Λ h₁ h₁ β M) ≫
        (probeAppendToMate D Sc m ν i hl hu).app p (M δ) := by
  have hU := probeOldWeightMixedUnit_comparison D Sc m i i Λ h₁ h₁ h₂ β M
  have hX := cross_comparison D Sc m i Λ h₁ h₂ β p M
  have hC := probeOldWeightMixedCounit_comparison D Sc m i i Λ h₁ h₂ h₁ h₂ β M
  have hp := mate_transport (Res).toFunctor
    (probeOldWeightMixedSource_obj D Sc m i i Λ h₁ h₁ β M)
    (Functor.congr_obj pairEq ((F).obj M))
    (Functor.congr_obj pairEq ((F).obj M))
    (probeOldInductionComponent_obj_blockSucc D Sc m i Λ h₂ δ M)
    (probeOldWeightUnitApp D Sc m i Λ h₂ δ ((E).obj ((F).obj M)))
    ((Cross).app p ((F).obj M) ε)
    ((probeOldInductionComponent D Sc m i Λ h₂ ε).map
      ((probeOldWeightCounit D Sc m i Λ h₁).app M))
    ((probeAppendToUnit D Sc m ν₁ i ν₂ hu).app
      ((probeEvaluatedAppendTo D Sc m ν i ν₁ hl).obj
        ((probeEvaluatedRestrictTo D Sc m ν i ν₁ hl).obj (M δ))))
    ((probeAppendToEqualCross D Sc m ν i hl hu).app p (((F).obj M) β))
    ((Ind).map ((probeAppendToCounit D Sc m ν i ν₁ hl).app (M δ)))
    hU hX hC
  rw [eqToHom_map] at hp
  have hlc := storedMate_expansion D Sc m ν i hl hu p (M δ)
  have hr := congrArg (fun f =>
    eqToHom (probeOldWeightMixedSource_obj D Sc m i i Λ h₁ h₁ β M) ≫ f) hlc.symm
  have ha := congrArg (fun f => f ≫
    eqToHom (probeOldWeightMixedTarget_obj D Sc m i i Λ h₁ h₂ h₁ h₂ β M))
    (probeOldWeightMixedMate_app_block D Sc m i i Λ h₁ h₂ h₁ h₂ p M δ)
  rw [probeOldWeightRouquierMate_eq]
  exact ha.trans (hp.trans hr)

end OddMath.QuiverHecke
end

end

section

/-! # The chosen mate comparison as an OLD module map

Brundan–Ellis (1.13)–(1.14): lift the single-coend reindexing square to
entire module maps. The two comparison maps remain the prescribed append
adjunction comparisons, and the crossing mate retains its negative sign.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
open ELVOld ELVOld.BalancedInduction
universe u
attribute [local irreducible] oldAppendReindexLinear oldAppendReindexIso orderedGridMateLinear

private theorem restriction_total
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (Q : C ⥤ A) [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q]
    {M N : Superfunctor k A (SVec k)} (f : M ⟶ N) (t : C) :
    ((restriction Q).map f).total t = f.total (Q.obj t) := rfl

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (ν : List I) (i : I) {ν₁ ν₂ : List I}
  (h₁ : (i :: ν).Perm ν₁) (h₂ : (i :: ν₁).Perm ν₂)
local notation "J₀" => oldContentAppendTo D Sc cutoff ν i (i :: ν) (List.Perm.refl _)
local notation "K₀" => oldContentAppendTo D Sc cutoff (i :: ν) i (i :: i :: ν) (List.Perm.refl _)
local notation "J" => oldContentAppendTo D Sc cutoff ν i ν₁ h₁
local notation "K" => oldContentAppendTo D Sc cutoff ν₁ i ν₂ h₂
local notation "Q⁻¹" => oldContentReindex D Sc cutoff h₁.symm
local notation "R₁" => oldModuleReindex D Sc cutoff h₁
local notation "hγ₀" => oldAppendToEqualCross_supernatural D Sc cutoff ν i
  (List.Perm.refl (i :: ν)) (List.Perm.refl (i :: i :: ν))
local notation "hγ" => oldAppendToEqualCross_supernatural D Sc cutoff ν i h₁ h₂

/-- The lower loop map is the selected lower append comparison. -/
def oldReindexLowerLoopModuleHom
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k)) :
    (R₁).obj (induced J₀ ((restriction J₀).obj N)) ⟶
      induced J ((restriction J).obj ((R₁).obj N)) :=
  (oldAppendReindexIso D Sc cutoff (List.Perm.refl ν) i
    (List.Perm.refl (i :: ν)) h₁ h₁).hom.app ((restriction J₀).obj N)

/-- The upper loop map is the selected upper append comparison under restriction. -/
def oldReindexUpperLoopModuleHom
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k)) :
    (R₁).obj ((restriction K₀).obj (induced K₀ N)) ⟶
      (restriction K).obj (induced K ((R₁).obj N)) :=
  (restriction K).map
    ((oldAppendReindexIso D Sc cutoff h₁ i (List.Perm.refl (i :: i :: ν)) h₂
      ((h₁.cons i).trans h₂)).hom.app N)

theorem oldReindexLowerLoopModuleHom_total
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k))
    (t : OldContentCategory D Sc cutoff ν₁) :
    (oldReindexLowerLoopModuleHom D Sc cutoff ν i h₁ N).total t =
      oldReindexLowerLoopLinear D Sc cutoff ν i h₁ N t := by
  unfold oldReindexLowerLoopModuleHom oldReindexLowerLoopLinear oldAppendReindexLinear
  rfl

theorem oldReindexUpperLoopModuleHom_total
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k))
    (t : OldContentCategory D Sc cutoff ν₁) :
    (oldReindexUpperLoopModuleHom D Sc cutoff ν i h₁ h₂ N).total t =
      oldReindexUpperLoopLinear D Sc cutoff ν i h₁ h₂ N t := by
  unfold oldReindexUpperLoopModuleHom oldReindexUpperLoopLinear oldAppendReindexLinear
  rfl

/-- The same prescribed negative mate square on complete OLD module maps. -/
theorem oldReindexLoopModuleHom_mate
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k)) :
    (R₁).map (orderedGridMateComponent J₀ K₀ hγ₀ N) ≫
        oldReindexUpperLoopModuleHom D Sc cutoff ν i h₁ h₂ N =
      oldReindexLowerLoopModuleHom D Sc cutoff ν i h₁ N ≫
        orderedGridMateComponent J K hγ ((R₁).obj N) := by
  let V := (R₁).obj (induced J₀ ((restriction J₀).obj N))
  let W := (restriction K).obj (induced K ((R₁).obj N))
  apply HomogeneousSuperfunctorIso.total_ext (F := V) (G := W)
  intro t
  rw [Superfunctor.comp_total, Superfunctor.comp_total,
    oldReindexLowerLoopModuleHom_total, oldReindexUpperLoopModuleHom_total]
  change oldReindexUpperLoopLinear D Sc cutoff ν i h₁ h₂ N t ∘ₗ
      ((restriction Q⁻¹).map (orderedGridMateComponent J₀ K₀ hγ₀ N)).total t =
    (orderedGridMateComponent J K hγ ((R₁).obj N)).total t ∘ₗ
      oldReindexLowerLoopLinear D Sc cutoff ν i h₁ N t
  rw [restriction_total]
  have h := oldReindexLoopLinear_mate D Sc cutoff ν i h₁ h₂ N t
  unfold orderedGridMateLinear at h
  exact h
end OddMath.QuiverHecke
end

end
