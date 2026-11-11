import OddMath.QuiverHecke.SwappedAssembly.PointwiseLeftwardInverse
import OddMath.QuiverHecke.SwappedAssembly.Sigma.PaddedResidualInversion

/-! # Pointwise leftward inverses on supported central inputs

Brundan–Ellis (1.13)–(1.14): the chosen ELV coefficient supplies raw
leftward data, and supported central inputs satisfy the five local
positive or negative inverse identities. Invertibility is supplied by
the supported padded residual theorem, not a raw-global premise.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath.SKM
namespace OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
open CyclotomicAction ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : Datum I X) (Sc : Scalars D k) (m cutoff : I → ℕ) (bound : ℕ)
  (ΛP ΛR : X)
  (hP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)
local notation "P" => elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR
local instance pointwiseLeftwardHomPi (A B : PiSCat.{u,u,u+1} k) :
    PiSupercategory k (A ⟶ B) := PiTwoSupercategory.homPiLeft A B

/-- The chosen raw leftward data use the chosen ELV crossing coefficient,
with inverse entries selected separately at each input. -/
def pointwiseLeftwardData [Finite I]
    (hdot : TruncatedAppendDotNilpotent D (parameterTwist D Sc) cutoff bound) :
    (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).LeftwardData :=
  (P).leftwardOfPointwiseAugmentedInverse
    (elvProbeCrossCoeffOf D Sc m cutoff bound ΛP ΛR hP hR hdot)

variable [Finite I] (hdot : TruncatedAppendDotNilpotent D (parameterTwist D Sc) cutoff bound)
  (hwin : ReservoirWindowIdeal D Sc m cutoff bound ΛP ΛR hP hR)

local notation "c" =>
  elvProbeCrossCoeffOf D Sc m cutoff bound ΛP ΛR hP hR hdot
local notation "L" =>
  pointwiseLeftwardData D Sc m cutoff bound ΛP ΛR hP hR hdot

include hwin in
/-- Every supported central input satisfies the positive inverse equations
for the selected leftward data at nonnegative height. -/
theorem centralPointwiseLeftward_posInverseAt [Fact Sc.PureNilpotent] (i : I) (t : Sector I)
    (Z : H D (parameterTwist D Sc) m cutoff bound ΛP ΛR t)
    (hh : 0 ≤ D.h i ((P).wt t)) :
    (P).PosInverseAt c i ((P).wt t) t t Z.obj
      (fun q p => (L).lcrossSame i ((P).wt t) q p Z.obj)
      (fun n r p => (L).dcup i n ((P).wt t) r p Z.obj) := by
  let := (centralAugmentedMatrix_isIsoOf D Sc m cutoff bound ΛP ΛR hP hR hdot hwin i t Z).1 hh
  exact (P).leftwardOfPointwiseAugmentedInverse_posInverseAt c
    i ((P).wt t) t t Z.obj rfl hh

include hwin in
/-- Every supported central input satisfies the negative inverse equations
for the selected leftward data at negative height. -/
theorem centralPointwiseLeftward_negInverseAt [Fact Sc.PureNilpotent] (i : I) (t : Sector I)
    (Z : H D (parameterTwist D Sc) m cutoff bound ΛP ΛR t)
    (hh : D.h i ((P).wt t) < 0) :
    (P).NegInverseAt c i ((P).wt t) t t Z.obj
      (fun q p => (L).lcrossSame i ((P).wt t) q p Z.obj)
      (fun n q r => (L).dcap i n ((P).wt t) q r Z.obj) := by
  let := (centralAugmentedMatrix_isIsoOf D Sc m cutoff bound ΛP ΛR hP hR hdot hwin i t Z).2 hh.le
  exact (P).leftwardOfPointwiseAugmentedInverse_negInverseAt c
    i ((P).wt t) t t Z.obj rfl hh

/-- The chosen pointwise data retain the off-weight normalization. -/
theorem pointwiseLeftwardData_vanishesOffWeight :
    (L).VanishesOffWeight :=
  (P).leftwardOfPointwiseAugmentedInverse_vanishesOffWeight c

end OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
