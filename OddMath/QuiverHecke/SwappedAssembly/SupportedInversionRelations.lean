import OddMath.QuiverHecke.SwappedAssembly.PointwiseLeftwardInverse
import OddMath.QuiverHecke.SwappedAssembly.SupportedWhiskerReduction
import OddMath.QuiverHecke.SwappedAssembly.SupportedRelationLifting

/-! # Inversion relations on retained Hom inputs

Brundan–Ellis (1.11)–(1.14): pointwise equal-colour inverse identities
on a path-closed family of Hom objects suffice for the exact native
layer-representation inversion relations on that family. The existing
distinct-colour permutation inverse is retained unchanged.
-/
noncomputable section
namespace OddMath.QuiverHecke.SwappedAssembly
open CategoryTheory StringDiagrams OddMath.SKM
universe u uB v w
variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type uB} [BicategoryStruct.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}
namespace ProbeReservoir
variable {P : ProbeReservoir k B D Sc} {Gs Ys : ∀ s, P.H s}

/-- Inversion identities are required only on the retained inputs reached by whiskering. -/
theorem inversionRelations_on
    (Q : ∀ t, ObjectProperty (P.H t))
    (hpath : ∀ {w : List (Col I X)} {s t : Sector I} (p : SPath w s t) (Z : P.H t),
      Q t Z → Q s ((P.pathFunctor p).obj Z))
    (hYs : ∀ t, Q t (Ys t)) {c : P.CrossCoeff} {L : P.LeftwardData}
    (hσ : ∀ i j ν, i ≠ j → P.SigmaPermutation c i j ν) (hL : ∀ t (Z : P.H t), Q t Z → L.IsInverseAt c t Z) :
    InversionRelations Sc (P.layerRep Gs Ys (P.swappedGens c L)) := by
  classical
  intro r hr
  refine relHolds_of_compEval_wt_on Q hpath hYs _ r fun p q Z hZ hw => ?_
  cases r with
  | invNe₁ i j ν hij =>
    show compEval (P.swappedGens c L) (a := SKM.ob D ν [up j, dn i])
      (b := SKM.ob D ν [up j, dn i]) (SKM.relation D Sc (.invNe₁ i j ν hij)) p q Z = 0
    simp only [SKM.relation]
    rw [compEval_sub, compEval_dg_append _ ν (SKM.sigmaL i j) (SKM.lcrossL i j)
      (SKM.sChain_sigmaL i j) (SKM.sChain_lcrossL i j), compEval_of]
    have hs : ∀ m : SPath (wd D ν [dn i, up j]) _ _,
        compDiag (P.swappedGens c L) (SKM.mkD D ν (SKM.sigmaL i j) (SKM.sChain_sigmaL i j))
          p m Z ≫ compDiag (P.swappedGens c L)
            (SKM.mkD D ν (SKM.lcrossL i j) (SKM.sChain_lcrossL i j)) m q Z =
        P.sigmaEntry c i j ν p m Z ≫ P.lcrossNeImage c i j ν m q Z := fun m => by
      erw [compDiag_sigmaL_swappedGens, compDiag_lcrossL, P.swappedGens_lcross_of_ne c L hij]
    rw [sub_eq_zero]
    simp only [hs]
    let : ∀ a b, Fintype (SPath (wd D ν [dn i, up j]) a b) := fun _ _ => Fintype.ofFinite _
    erw [sigma_lcross_sum (hσ i j ν hij), compDiag_id]
  | invNe₂ i j ν hij =>
    show compEval (P.swappedGens c L) (a := SKM.ob D ν [dn i, up j])
      (b := SKM.ob D ν [dn i, up j]) (SKM.relation D Sc (.invNe₂ i j ν hij)) p q Z = 0
    simp only [SKM.relation]
    rw [compEval_sub, compEval_dg_append _ ν (SKM.lcrossL i j) (SKM.sigmaL i j)
      (SKM.sChain_lcrossL i j) (SKM.sChain_sigmaL i j), compEval_of]
    have hs : ∀ m : SPath (wd D ν [up j, dn i]) _ _,
        compDiag (P.swappedGens c L) (SKM.mkD D ν (SKM.lcrossL i j) (SKM.sChain_lcrossL i j))
          p m Z ≫ compDiag (P.swappedGens c L)
            (SKM.mkD D ν (SKM.sigmaL i j) (SKM.sChain_sigmaL i j)) m q Z =
        P.lcrossNeImage c i j ν p m Z ≫ P.sigmaEntry c i j ν m q Z := fun m => by
      erw [compDiag_sigmaL_swappedGens, compDiag_lcrossL, P.swappedGens_lcross_of_ne c L hij]
    rw [sub_eq_zero]
    simp only [hs]
    let : ∀ a b, Fintype (SPath (wd D ν [up j, dn i]) a b) := fun _ _ => Fintype.ofFinite _
    erw [lcross_sigma_sum (hσ i j ν hij), compDiag_id]
  | _ => exact (hL _ Z hZ) _ hr (by simp [IsInvNe]) p q hw

end ProbeReservoir

namespace SupportedSectors
open CyclotomicAction ELVOld
universe uS
local instance supportedInverseRelationHomPi {k : Type uS} [CommRing k]
    (A B : PiSCat.{uS,uS,uS+1} k) : PiSupercategory k (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B

/-- The exact native inversion obligation only needs inverse identities on supported inputs. -/
theorem inversionRelations_of_supportedInverse
    {I X k : Type uS} [AddCommGroup X] [CommRing k]
    (D : Datum I X) (Sc : Scalars D k) (m cutoff : I → ℕ) (bound : ℕ)
    (ΛP ΛR : X)
    (hP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
    (hR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)
    (Gs Ys : ∀ s, H D (parameterTwist D Sc) m cutoff bound ΛP ΛR s)
    (c : (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).CrossCoeff)
    (L : (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).LeftwardData)
    (hσ : ∀ i j ν, i ≠ j →
      (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).SigmaPermutation c i j ν)
    (hL : ∀ t (Z : H D (parameterTwist D Sc) m cutoff bound ΛP ΛR t),
      L.IsInverseAt c t Z.obj) :
    InversionRelations Sc ((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).layerRep
      (fun s => (Gs s).obj) (fun s => (Ys s).obj)
      ((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).swappedGens c L)) := by
  apply ProbeReservoir.inversionRelations_on
    (retainedInput D Sc m cutoff bound ΛP ΛR hP hR)
    (retainedInput_path D Sc m cutoff bound ΛP ΛR hP hR)
    (fun s => (Ys s).property) hσ
  intro t Z hZ
  exact hL t ⟨Z, hZ⟩

end SupportedSectors
end OddMath.QuiverHecke.SwappedAssembly
