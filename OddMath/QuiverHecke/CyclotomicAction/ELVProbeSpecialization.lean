import OddMath.QuiverHecke.CyclotomicAction.ELVProbeCoefficients
import OddMath.QuiverHecke.CyclotomicAction.ELVOldCategory
import OddMath.QuiverHecke.CyclotomicAction.AppendMackeyMap
import OddMath.QuiverHecke.CyclotomicAction.ProbeWordEntries

/-! # Descent of the prescribed scalar probe specialization
The canonical binomial coefficient values send each original ELV relation to
the prescribed ordinary first-dot relation. The signed scalar Hom functor
therefore descends through the existing cyclotomic ideals, compatibly with
append. This is the probe-factor specialization of InvertibleDotProbe.md
Sections 1 and 5; positive-weight coefficient truncation is not used.
-/
noncomputable section
open CategoryTheory StringDiagrams
open OddMath.SKM.SYM
open scoped Classical
namespace OddMath.QuiverHecke
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (m : I → ℕ) (Sc : SKM.Scalars D k)
local notation "cut" => probeCutoff D m
local notation "a" => probePolynomial (k := k) (probeDotExponent D) m
local notation "F" => elvProbeAffineSpecialization D m Sc

/-- Every original first relation maps to its prescribed probe first relation. -/
theorem elvProbeAffineSpecialization_relation (i : I) (v : List I) :
    (F).map (ELVOld.relation D Sc cut i v) = firstDotPoly D Sc a i v := by
  unfold ELVOld.relation
  split_ifs with hi
  · change (F).map (elvQuotientMap D Sc cut _ _ (elvCyclotomic D Sc ⟨i,hi⟩ v (cut i))) = _
    rw [elvAffineScalarSpecialization_elvCyclotomic]
    have hc : elvMonicCoefficient D k ⟨i,hi⟩ (cut i) = probeMonicCoefficient (k := k) D m i := by
      funext j
      simp [probeMonicCoefficient, hi]
    rw [hc, scalarCoefficientPolynomial_probe]
    rfl
  · change (F).map (elvQuotientMap D Sc cut _ _ (evenCyclotomic D Sc i v (cut i))) = _
    rw [elvAffineScalarSpecialization_evenCyclotomic]
    have hc : evenMonicCoefficient D k i (cut i) = probeMonicCoefficient (k := k) D m i := by
      funext j
      simp [probeMonicCoefficient, hi]
    rw [hc, scalarCoefficientPolynomial_probe]
    rfl

/-- The existing scalar Hom map as a linear map, before cyclotomic descent. -/
def elvProbeScalarHom (v w : List I) :
    ELVOld.hom D Sc cut v w →ₗ[k]
      ((pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D w)) :=
  (F).toFunctor.mapLinearMap k

theorem elvProbeScalarHom_comp {v t w : List I}
    (f : ELVOld.hom D Sc cut v t) (g : ELVOld.hom D Sc cut t w) :
    elvProbeScalarHom D m Sc v w (f ≫ g) =
      elvProbeScalarHom D m Sc v t f ≫ elvProbeScalarHom D m Sc t w g :=
  (F).toFunctor.map_comp f g

theorem elvProbeScalarHom_id (v : List I) :
    elvProbeScalarHom D m Sc v v (𝟙 (ELVOld.obj D Sc cut v)) = 𝟙 ((pres D Sc).obj (ob D v)) :=
  (F).toFunctor.map_id _

theorem elvProbeScalarHom_relation (i : I) (v : List I) :
    elvProbeScalarHom D m Sc (i::v) (i::v) (ELVOld.relation D Sc cut i v) =
      firstDotPoly D Sc a i v :=
  elvProbeAffineSpecialization_relation D m Sc i v

/-- The actual ELV cyclotomic ideal maps into the existing ordinary Hom ideal. -/
theorem elvProbeAffineSpecialization_ideal {v w : List I}
    {f : ELVOld.hom D Sc cut v w} (hf : f ∈ ELVOld.ideal D Sc cut v w) :
    elvProbeScalarHom D m Sc v w f ∈ cycHom D Sc a v w := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨i, t, p, q, rfl⟩ := hf
    rw [elvProbeScalarHom_comp, elvProbeScalarHom_comp, elvProbeScalarHom_relation]
    exact Submodule.subset_span ⟨i, t, elvProbeScalarHom D m Sc _ _ p, elvProbeScalarHom D m Sc _ _ q, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add f g _ _ hf hg => rw [map_add]; exact Submodule.add_mem _ hf hg
  | smul c f _ hf => rw [map_smul]; exact Submodule.smul_mem _ c hf

/-- The scalar Hom functor descends through the original cyclotomic ideals. -/
def elvProbeOldHom (v w : List I) :
    ELVOld.Old D Sc cut v w →ₗ[k]
      (((pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D w)) ⧸ cycHom D Sc a v w) :=
  (ELVOld.ideal D Sc cut v w).liftQ
    ((cycHom D Sc a v w).mkQ.comp (elvProbeScalarHom D m Sc v w)) (by
      intro f hf
      change (cycHom D Sc a v w).mkQ ((F).map f) = 0
      exact (Submodule.Quotient.mk_eq_zero _).mpr (elvProbeAffineSpecialization_ideal D m Sc hf))

@[simp] theorem elvProbeOldHom_mk (v w : List I) (f : ELVOld.hom D Sc cut v w) :
    elvProbeOldHom D m Sc v w ((ELVOld.ideal D Sc cut v w).mkQ f) =
      (cycHom D Sc a v w).mkQ ((F).map f) := rfl

theorem elvProbeOldHom_surjective (v w : List I) :
    Function.Surjective (elvProbeOldHom D m Sc v w) := by
  intro y
  obtain ⟨f, rfl⟩ := (cycHom D Sc a v w).mkQ_surjective y
  obtain ⟨g, hg⟩ := elvAffineScalarSpecialization_surjective D Sc cut
    (probeScalarValues D m) (probeScalarValues_vanish D m) v w f
  refine ⟨(ELVOld.ideal D Sc cut v w).mkQ g, ?_⟩
  rw [elvProbeOldHom_mk, hg]

/-- Append on the original ELV old quotient, using its existing ideal stability. -/
def elvProbeOldRightContext (σ v w : List I) :
    ELVOld.Old D Sc cut v w →ₗ[k] ELVOld.Old D Sc cut (v++σ) (w++σ) :=
  (ELVOld.ideal D Sc cut v w).liftQ
    ((ELVOld.ideal D Sc cut (v++σ) (w++σ)).mkQ.comp (ELVOld.rightContext D Sc cut σ v w)) (by
      intro f hf
      change (ELVOld.ideal D Sc cut (v++σ) (w++σ)).mkQ _ = 0
      exact (Submodule.Quotient.mk_eq_zero _).mpr (ELVOld.ideal_rightContext D Sc cut σ hf))

/-- Append on the existing ordinary cyclotomic Hom quotient. -/
def probeCycHomRightContext (σ v w : List I) :
    (((pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D w)) ⧸ cycHom D Sc a v w) →ₗ[k]
      (((pres D Sc).obj (ob D (v++σ)) ⟶ (pres D Sc).obj (ob D (w++σ))) ⧸
        cycHom D Sc a (v++σ) (w++σ)) :=
  (cycHom D Sc a v w).liftQ
    ((cycHom D Sc a (v++σ) (w++σ)).mkQ.comp (ELVOld.affineRightContext D Sc σ v w)) (by
      intro f hf
      change (cycHom D Sc a (v++σ) (w++σ)).mkQ _ = 0
      exact (Submodule.Quotient.mk_eq_zero _).mpr (cycHom_whiskerRight D Sc hf σ))

/-- The descended scalar Hom map commutes with append. -/
theorem elvProbeOldHom_rightContext (σ v w : List I) (f : ELVOld.Old D Sc cut v w) :
    elvProbeOldHom D m Sc (v++σ) (w++σ) (elvProbeOldRightContext D m Sc σ v w f) =
      probeCycHomRightContext D m Sc σ v w (elvProbeOldHom D m Sc v w f) := by
  obtain ⟨f, rfl⟩ := (ELVOld.ideal D Sc cut v w).mkQ_surjective f
  change (cycHom D Sc a (v++σ) (w++σ)).mkQ
      ((F).map (ELVOld.rightContext D Sc cut σ v w f)) =
    (cycHom D Sc a (v++σ) (w++σ)).mkQ
      (ELVOld.affineRightContext D Sc σ v w ((F).map f))
  congr 1
  exact elvAffineScalarSpecialization_rightContext D Sc cut
    (probeScalarValues D m) (probeScalarValues_vanish D m) σ v w f

/-- The existing ordinary Hom quotient maps to its literal probe matrix entry. -/
def probeCycHomWordEntry {n : ℕ} (s t : Word I (n+1)) :
    (((pres D Sc).obj (ob D s.val) ⟶ (pres D Sc).obj (ob D t.val)) ⧸
      cycHom D Sc a s.val t.val) →ₗ[k] CyclotomicAlgebra D Sc a n :=
  (cycHom D Sc a s.val t.val).liftQ
    { toFun := cyclotomicWordEntry D Sc a s t
      map_add' := by
        intro f g
        change cyclotomicMk D Sc a n (FiniteHomMatrix.single t s (f+g)) = _
        rw [FiniteHomMatrix.single_add, map_add]
        rfl
      map_smul' := by
        intro c f
        change cyclotomicMk D Sc a n (FiniteHomMatrix.single t s (c • f)) = _
        rw [FiniteHomMatrix.single_smul, map_smul]
        rfl } (by
      intro f hf
      change cyclotomicMk D Sc a n (FiniteHomMatrix.single t s f) = 0
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      exact single_mem_cyclotomicIdeal D Sc a n t s hf)

/-- The scalar Hom functor descends into the actual probe cyclotomic algebra. -/
def elvProbeWordEntry {n : ℕ} (s t : Word I (n+1)) :
    ELVOld.Old D Sc cut s.val t.val →ₗ[k] CyclotomicAlgebra D Sc a n :=
  (probeCycHomWordEntry D m Sc s t).comp (elvProbeOldHom D m Sc s.val t.val)

@[simp] theorem elvProbeWordEntry_mk {n : ℕ} (s t : Word I (n+1))
    (f : ELVOld.hom D Sc cut s.val t.val) :
    elvProbeWordEntry D m Sc s t ((ELVOld.ideal D Sc cut s.val t.val).mkQ f) =
      cyclotomicWordEntry D Sc a s t ((F).map f) := rfl

variable [Fintype I]

end OddMath.QuiverHecke
