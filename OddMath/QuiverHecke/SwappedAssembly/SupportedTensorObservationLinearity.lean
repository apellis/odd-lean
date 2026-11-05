import OddMath.QuiverHecke.SwappedAssembly.SupportedTensorUnitObservation

/-! # Linearity of the canonical tensor matrix observation

SwappedVacuumCoordinates §§3–7: the canonical original-weight source-unit
observation is linear on the actual supported matrix module. No
faithfulness of regular-probe evaluation is asserted.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath.SKM
namespace OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
open CyclotomicAction ELVOld
universe u
private def totalLinear {k : Type u} [CommRing k]
    (A B : PiSCat.{u,u,u + 1} k) (F G : A ⟶ B) (R : A) :
    (F ⟶ G) →ₗ[k] (F.obj R ⟶ G.obj R) where
  toFun f := f.total R
  map_add' f g := by
    change (f.app 0 R + g.app 0 R) + (f.app 1 R + g.app 1 R) =
      (f.app 0 R + f.app 1 R) + (g.app 0 R + g.app 1 R)
    abel
  map_smul' r f := by
    change r • f.app 0 R + r • f.app 1 R = r • (f.app 0 R + f.app 1 R)
    exact (smul_add _ _ _).symm

private def moduleEvaluate {k : Type u} [CommRing k] {C : Type u}
    [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
    (M N : Superfunctor k C (SVec k)) (w : C) (b : M.obj w) :
    (M ⟶ N) →ₗ[k] N.obj w where
  toFun f := f.total w b
  map_add' f g := by
    change (f.app 0 w b + g.app 0 w b) + (f.app 1 w b + g.app 1 w b) =
      (f.app 0 w b + f.app 1 w b) + (g.app 0 w b + g.app 1 w b)
    abel
  map_smul' r f := by
    change r • f.app 0 w b + r • f.app 1 w b = r • (f.app 0 w b + f.app 1 w b)
    exact (smul_add _ _ _).symm

variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : Datum I X) (Sc : Scalars D k) (m cutoff : I → ℕ) (ΛP ΛR : X) (L : I × ℕ → ℕ)
  (hP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hR : ∀ i, (cutoff i : ℤ) = D.h i ΛR) (s : List I)
local notation "Tw" => parameterTwist D Sc
local notation "N" => PowerWordContent.powerBound D cutoff L
local notation "R" => WeightTensorVacuum.regularProbe D Tw m ΛP
local notation "cS" => tensorSourceContent D ΛP ΛR s
local notation "β" => tensorSourceWordBlock D ΛP ΛR s
local notation "w" => PowerWordContentCyclicity.wordObject D Tw cutoff L s.reverse (s.reverse : Multiset I) rfl

private def wordValueEquiv (ν ρ : List I) :
    (PowerWordWeight.wordAt D Tw cutoff L ν (ρ : Multiset I)).obj
      (PowerWordContentCyclicity.wordObject D Tw cutoff L ρ (ρ : Multiset I) rfl) ≃ₗ[k]
      (powerWordModule D Tw cutoff L ν).obj (OldCategory.mk ρ) :=
  LinearEquiv.refl k _

/-- The canonical matrix observation, bundled as a linear map through
its literal whole-Hom, regular-probe, global-chart and quotient maps. -/
def tensorMatrixQuotientObservationLinear {a : Obj (SKM.sig D)}
    (hEnd : (ΛP - contentWeight D (0 : I →₀ ℕ)) + (-ΛR + contentWeight D (0 : I →₀ ℕ)) = a.endR)
    (p : SPath a.word (0,cS) (0,0)) (hup : ∀ c ∈ a.word, c.l.1 = true) :
    matrixModule D Sc m cutoff N ΛP ΛR
      (tensorSourceFamily D Sc m cutoff ΛP ΛR L s) (tensorTargetFamily D Sc m cutoff ΛP ΛR L) a →ₗ[k]
      ((coefficientObj D Sc s ⟶ coefficientObj D Sc (a.word.map (fun c : Col I X => c.l.2))) ⧸
        PowerWordQuotientCoordinates.kernel D Sc cutoff L s (a.word.map (fun c : Col I X => c.l.2))) := by
  let row := tensorOriginalWordEntry D Sc m cutoff ΛP ΛR L hP hR s hEnd p hup
  let value := totalLinear (probeOldWeightSpace D Tw m ΛP (-ΛP))
    (elvWeightSpace D Tw cutoff N ΛR (ReservoirWord.weight D ΛR cS))
    (tensorOriginalRowSource D Sc m cutoff ΛP ΛR L s)
    (TensorReservoirWords.pathHom D Tw m cutoff L ΛP ΛR p hup) R
  let evaluate := moduleEvaluate
    (((tensorOriginalRowSource D Sc m cutoff ΛP ΛR L s).obj R) β)
    (((TensorReservoirWords.pathHom D Tw m cutoff L ΛP ΛR p hup).obj R) β) w
    (tensorOriginalSourceUnit D Sc m cutoff ΛP ΛR L hP hR s)
  let chart := ((tensorPathValueChart D Sc m cutoff ΛP ΛR L p hup).hom β).total w
  let coordinate := PowerWordQuotientCoordinates.coordinate D Sc cutoff L s (a.word.map (fun c : Col I X => c.l.2))
  let wordValue := (wordValueEquiv D Sc cutoff L
    (a.word.map (fun c : Col I X => c.l.2)).reverse s.reverse).toLinearMap
  exact coordinate.comp (wordValue.comp (chart.comp (evaluate.comp
    ((LinearMap.proj β).comp (value.comp row)))))

end OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
