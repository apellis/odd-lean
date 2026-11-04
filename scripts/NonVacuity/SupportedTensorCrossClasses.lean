import OddMath.QuiverHecke.SwappedAssembly.SupportedTensorCrossClasses
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeDenominatorUnits
import OddMath.QuiverHecke.HalfTurn.PowerWordCoordinates
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath OddMath.SKM OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction OddMath.QuiverHecke.SwappedAssembly
namespace NonVacuity.SupportedTensorCrossClasses
private theorem coordinate_ne_zero (D : SKM.Datum Bool (Bool → ℤ)) (Sc : SKM.Scalars D ℚ)
    (cutoff : Bool → ℕ) (L : Bool × ℕ → ℕ) (s t : List Bool)
    (v : (powerWordModule D (parameterTwist D Sc) cutoff L t.reverse).obj (OldCategory.mk s.reverse))
    (hv : v ≠ 0) : PowerWordQuotientCoordinates.coordinate D Sc cutoff L s t v ≠ 0 := by
  intro h
  let e := PowerWordQuotientCoordinates.quotientEquiv D Sc cutoff L s t
  have hh := congrArg e h
  change e (e.symm v) = e 0 at hh
  rw [LinearEquiv.apply_symm_apply,map_zero] at hh
  exact hv hh
local instance tensorHomPi (A C : PiSCat.{0,0,1} ℚ) : PiSupercategory ℚ (A ⟶ C) :=
  PiTwoSupercategory.homPiLeft A C
private def collisionDatum : SKM.Datum Bool (Bool → ℤ) where
  cd :=
    { root := fun j i => if i = j then 2 else -2
      coroot := fun i => LinearMap.proj i
      coroot_root_self := fun i => by simp }
  isGCM :=
    { diag := fun i => by simp [CartanDatum.cartanMatrix_apply]
      offDiag_nonpos := fun i j h => by simp [CartanDatum.cartanMatrix_apply, h]
      zero_comm := fun i j => by simp [CartanDatum.cartanMatrix_apply, eq_comm] }
  parity := fun _ => 1
  even_of_odd := by
    intro i j _
    change Even (if i = j then (2 : ℤ) else -2)
    split
    · exact ⟨1, by norm_num⟩
    · exact ⟨-1, by norm_num⟩

private def collisionScalars : SKM.Scalars collisionDatum ℚ where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := fun _ => isUnit_iff_ne_zero.mpr (by norm_num)


private abbrev D := collisionDatum
private abbrev originalSc := collisionScalars
private abbrev Sc := parameterTwist D originalSc
private def cutoff (_ : Bool) : ℕ := 40
private def L (_ : Bool × ℕ) : ℕ := 40
private def m (_ : Bool) : ℕ := 20
private def Λ : Bool → ℤ := fun _ => 40
private abbrev N := PowerWordContent.powerBound D cutoff L
local notation "R" => WeightTensorVacuum.regularProbe D (parameterTwist D originalSc) m Λ
private abbrev W := elvRouquierData D Sc cutoff N Λ
private def rightLabels : List (Col Bool (Bool → ℤ)) := wd D 0 [up true,up false]
private def leftLabels : List (Col Bool (Bool → ℤ)) := wd D 0 [up false]
private theorem right_up : ∀ a ∈ rightLabels, a.l.1 = true := by simp [rightLabels,wd]
private theorem left_up : ∀ a ∈ leftLabels, a.l.1 = true := by simp [leftLabels,wd]
private abbrev cR : Bool →₀ ℕ := SPath.wordContent rightLabels + 0
private def pR : SPath rightLabels (0,cR) (0,0) := SPath.reservoirPath rightLabels right_up 0
private def pL (cM : Bool →₀ ℕ) := SPath.reservoirPath leftLabels left_up cM
private abbrev ν : List Bool := [false,true]
private abbrev η : List Bool := [false]
private theorem weight_add (c : Bool →₀ ℕ) (i : Bool) :
    ReservoirWord.weight D Λ (c + Finsupp.single i 1) = ReservoirWord.weight D Λ c + D.α i := by
  simp only [ReservoirWord.weight,map_add,contentWeight,Finsupp.weight_single,one_nsmul]
  abel
private theorem powers_high (q : Bool × ℕ) : 32 ≤ L q * SKM.SYM.elementaryWeight D q := by
  have hw : 0 < SKM.SYM.elementaryWeight D q := by
    unfold SKM.SYM.elementaryWeight
    split_ifs <;> omega
  change 32 ≤ 40 * SKM.SYM.elementaryWeight D q
  omega
private def identityNF (s : List Bool) : NFIdx s s := by
  have hc : Categorification.TypeA.canWord s.length (1 : Equiv.Perm (Fin s.length)) = [] := by
    apply List.length_eq_zero_iff.mp
    rw [Categorification.TypeA.length_canWord,Categorification.TypeA.length_one]
  refine ⟨([],1),by simp,by simp,?_⟩
  simp only [List.map_nil,hc,cw,List.reverse_nil,List.nil_append,pl,QuiverHecke.SChain]
private def oddIndex : SKM.SYM.CoefficientIndex D := (0,{⟨false,rfl⟩,⟨true,rfl⟩})
private def occupied (s : List Bool) : ExtendedAtMost D originalSc s s 2 :=
  ⟨extensionBasis D originalSc s s (oddIndex,identityNF s),
    Submodule.subset_span ⟨(oddIndex,identityNF s),by
      change SKM.SYM.coefficientWeight D oddIndex + 0 ≤ 2
      decide,rfl⟩⟩
private def rawVector (s : List Bool) := powerWordHalfTurnCoordinate D originalSc cutoff L s s (occupied s).val
private theorem rawVector_ne_zero (s : List Bool) (hb : 2 + 2 * s.length.choose 2 < 32) : rawVector s ≠ 0 := by
  intro hz
  have hinj := powerWordHalfTurnCoordinate_injective_on_extendedAtMost D originalSc cutoff L (s := s) (t := s)
    (fun _ => (by decide : 32 ≤ 40)) powers_high hb
  have hh : occupied s = (0 : ExtendedAtMost D originalSc s s 2) := by
    apply hinj
    change powerWordHalfTurnCoordinate D originalSc cutoff L s s (occupied s).val =
      powerWordHalfTurnCoordinate D originalSc cutoff L s s 0
    exact hz.trans (map_zero _).symm
  exact (extensionBasis D originalSc s s).ne_zero (oddIndex,identityNF s) (congrArg Subtype.val hh)
private theorem probePairing (i : Bool) : (probeCutoff D m i : ℤ) = D.h i Λ := by
  cases i <;> norm_num [probeCutoff, probeDotExponent, m, D, collisionDatum, SKM.Datum.h, Λ]
private theorem reservoirPairing (i : Bool) : (cutoff i : ℤ) = D.h i Λ := rfl
private abbrev P := elvProbeReservoir D originalSc m cutoff N Λ Λ probePairing reservoirPairing
namespace Dot
private abbrev cM (i : Bool) := cR + Finsupp.single i 1
private abbrev h (i : Bool) := (weight_add cR i).symm
private abbrev τ (i : Bool) := (ν ++ [i]) ++ η
private abbrev σ (i : Bool) := (τ i).reverse
local notation "G" => (fun (i : Bool) =>
  TensorVacuumWords.wordHom D (parameterTwist D originalSc) m cutoff L Λ Λ ν ≫
    RouquierData.E (elvRouquierData D (parameterTwist D originalSc) cutoff
      (PowerWordContent.powerBound D cutoff L) Λ) i (PowerWordWeight.wordWeight_append D Λ ν i) ≫
    TensorHomContexts.context D (parameterTwist D originalSc) cutoff L Λ
      (PowerWordWeight.wordWeight D Λ (ν ++ [i])) η)
private def β (i : Bool) : WeightBlocks D Λ
    (PowerWordWeightContexts.contextWeight D (PowerWordWeight.wordWeight D Λ (ν ++ [i])) η) :=
  ⟨τ i,(PowerWordWeightContexts.context_weight_word D Λ (ν ++ [i]) η _ rfl).symm⟩
private def w (i : Bool) : ContentCategory D Sc cutoff N (β i).1 := ⟨⟨(σ i).reverse⟩,rfl⟩
private abbrev e (i : Bool) := moduleIsoLinearEquiv
  (Pi.isoApp (TensorHomContexts.dotChart D Sc m cutoff L Λ Λ ν η i) (β i)) (w i)
private def z (i : Bool) := (e i).symm (rawVector (σ i))
private theorem z_ne_zero (i : Bool) : z i ≠ 0 := by
  intro hz
  apply rawVector_ne_zero (σ i) (by change 2 + 2 * (4 : ℕ).choose 2 < 32; decide)
  have he := congrArg (e i) hz
  simpa only [z,LinearEquiv.apply_symm_apply,map_zero] using he
private theorem functorEq (i : Bool) :
    ReservoirLayerCells.dotHomAt D originalSc m cutoff L Λ Λ (pL (cM i)) left_up pR right_up i (h i) = G i :=
  ReservoirLayerCells.dotHomAt_eq D originalSc m cutoff L Λ Λ (pL (cM i)) left_up pR right_up i (h i)
private def entry (i : Bool) : G i ⟶
    ReservoirLayerCells.dotHomAt D originalSc m cutoff L Λ Λ (pL (cM i)) left_up pR right_up i (h i) :=
  eqToHom (functorEq i).symm
private def ident (i : Bool) : End (G i) := 𝟙 _
private theorem entry_chart (i : Bool) : entry i ≫ eqToHom (functorEq i) = ident i := by
  simp [entry,ident,eqToHom_trans]
private theorem evaluated_id (i : Bool) : ((((ident i).total R) (β i)).total (w i)) (z i) = z i := by
  change (((𝟙 ((G i).obj R) + 0) (β i)).total (w i)) (z i) = _
  rw [add_zero]
  change (𝟙 ((((G i).obj R) (β i)).obj (w i)) + 0) (z i) = _
  simp only [add_zero,SVec.id_apply]
private theorem hs (i : Bool) : ((σ i).reverse : Multiset Bool) = (β i).1 := by rfl
private def v (i : Bool) := TensorLayerClasses.dotVector D originalSc cutoff L m Λ Λ ν η i (G i)
  (entry i ≫ eqToHom (functorEq i)) (σ i) (β i) (hs i) (z i)
private theorem v_ne_zero (i : Bool) : v i ≠ 0 := by
  intro hv
  unfold v at hv
  rw [entry_chart] at hv
  have hz := (TensorLayerClasses.dotVector_eq_zero_iff D originalSc cutoff L m Λ Λ ν η i (G i)
    (ident i) (σ i) (β i) (hs i) (z i)).mp hv
  change ((((ident i).total R) (β i)).total (w i)) (z i) = 0 at hz
  rw [evaluated_id] at hz
  exact z_ne_zero i hz
private abbrev K (i : Bool) := PowerWordQuotientCoordinates.kernel D originalSc cutoff L (σ i)
  (PowerWordLayerClasses.domWord ν η (.dot i))
private def cls (i : Bool) := PowerWordQuotientCoordinates.coordinate D originalSc cutoff L (σ i)
  (PowerWordLayerClasses.domWord ν η (.dot i)) (v i)
private def rep (i : Bool) := Classical.choose ((Submodule.mkQ_surjective (K i)) (cls i))
private theorem rep_spec (i : Bool) : cls i = (K i).mkQ (rep i) :=
  (Classical.choose_spec ((Submodule.mkQ_surjective (K i)) (cls i))).symm
example (i : Bool) := ReservoirLayerCells.dot_square D originalSc m cutoff L Λ Λ (pL (cM i)) left_up pR right_up i (h i)
example (i : Bool) := ReservoirLayerCells.dot_class_square D originalSc m cutoff L Λ Λ (pL (cM i)) left_up pR right_up i (h i)
  (G i) (entry i) (σ i) (β i) (hs i) (z i) (rep i) (rep_spec i)
example (i : Bool) : z i ≠ 0 := z_ne_zero i
example (i : Bool) : v i ≠ 0 := v_ne_zero i
example (i : Bool) : cls i ≠ 0 := coordinate_ne_zero D originalSc cutoff L (σ i)
  (PowerWordLayerClasses.domWord ν η (.dot i)) (v i) (v_ne_zero i)
example (i : Bool) := SupportedSectors.tensorContextIso D originalSc m cutoff L Λ Λ
  probePairing reservoirPairing (pL (cM i)) left_up pR right_up ((P).W.E i (h i))
example (i : Bool) := SupportedSectors.tensorContext_square D originalSc m cutoff L Λ Λ
  probePairing reservoirPairing (pL (cM i)) left_up pR right_up ((P).W.dot i (h i))
example (i : Bool) : SupportedSectors.tensorContextHom D originalSc m cutoff L Λ Λ
    probePairing reservoirPairing (pL (cM i)) left_up pR right_up ((P).W.E i (h i)) =
  ReservoirLayerCells.dotRawHom D originalSc m cutoff L Λ Λ (pL (cM i)) left_up pR right_up i (h i) := rfl
end Dot
namespace Cross
private abbrev cM (i j : Bool) := (cR + Finsupp.single j 1) + Finsupp.single i 1
private abbrev h₁ (j : Bool) := (weight_add cR j).symm
private abbrev h₂ (i j : Bool) := (weight_add (cR + Finsupp.single j 1) i).symm
private abbrev h₃ (i : Bool) := (weight_add cR i).symm
private theorem h₄ (i j : Bool) : ReservoirWord.weight D Λ (cR + Finsupp.single i 1) + D.α j =
    ReservoirWord.weight D Λ (cM i j) := by
  have hc : (cR + Finsupp.single i 1) + Finsupp.single j 1 = cM i j := by dsimp [cM]; abel
  exact (weight_add (cR + Finsupp.single i 1) j).symm.trans (congrArg (ReservoirWord.weight D Λ) hc)
private theorem h₁c (j : Bool) : PowerWordWeight.wordWeight D Λ ν + D.α j = ReservoirWord.weight D Λ (cR + Finsupp.single j 1) :=
  (congrArg (fun x => x + D.α j) (TensorReservoirWords.path_weight D Λ pR right_up)).symm.trans (h₁ j)
private abbrev τ (i j : Bool) := ((ν ++ [j]) ++ [i]) ++ η
private abbrev σ (i j : Bool) := (τ i j).reverse
local notation "G" => (fun (i j : Bool) =>
  TensorVacuumWords.wordHom D (parameterTwist D originalSc) m cutoff L Λ Λ ν ≫
    RouquierData.E (elvRouquierData D (parameterTwist D originalSc) cutoff
      (PowerWordContent.powerBound D cutoff L) Λ) j (h₁c j) ≫
    RouquierData.E (elvRouquierData D (parameterTwist D originalSc) cutoff
      (PowerWordContent.powerBound D cutoff L) Λ) i (h₂ i j) ≫
    TensorHomContexts.context D (parameterTwist D originalSc) cutoff L Λ (ReservoirWord.weight D Λ (cM i j)) η)
private theorem midWeight (i j : Bool) : ReservoirWord.weight D Λ (cM i j) =
    PowerWordWeight.wordWeight D Λ ((ν ++ [j]) ++ [i]) :=
  (h₂ i j).symm.trans ((congrArg (fun x => x + D.α i)
    ((h₁c j).symm.trans (PowerWordWeight.wordWeight_append D Λ ν j))).trans
      (PowerWordWeight.wordWeight_append D Λ (ν ++ [j]) i))
private def β (i j : Bool) : WeightBlocks D Λ (PowerWordWeightContexts.contextWeight D
    (ReservoirWord.weight D Λ (cM i j)) η) :=
  ⟨τ i j,(PowerWordWeightContexts.context_weight_word D Λ ((ν ++ [j]) ++ [i]) η _ (midWeight i j)).symm⟩
private def w (i j : Bool) : ContentCategory D Sc cutoff N (β i j).1 := ⟨⟨(σ i j).reverse⟩,rfl⟩
private abbrev e (i j : Bool) := moduleIsoLinearEquiv
  (Pi.isoApp (TensorHomContexts.pairChart D Sc m cutoff L Λ Λ ν η i j (h₁c j) (h₂ i j)) (β i j)) (w i j)
private def z (i j : Bool) := (e i j).symm (rawVector (σ i j))
private theorem z_ne_zero (i j : Bool) : z i j ≠ 0 := by
  intro hz
  apply rawVector_ne_zero (σ i j) (by change 2 + 2 * (5 : ℕ).choose 2 < 32; decide)
  have he := congrArg (e i j) hz
  simpa only [z,LinearEquiv.apply_symm_apply,map_zero] using he
private theorem functorEq (i j : Bool) :
    ReservoirLayerCells.crossHomAt D originalSc m cutoff L Λ Λ (pL (cM i j)) left_up pR right_up i j (h₁ j) (h₂ i j) = G i j :=
  ReservoirLayerCells.crossHomAt_eq D originalSc m cutoff L Λ Λ (pL (cM i j)) left_up pR right_up i j (h₁ j) (h₂ i j)
private def entry (i j : Bool) : G i j ⟶
    ReservoirLayerCells.crossHomAt D originalSc m cutoff L Λ Λ (pL (cM i j)) left_up pR right_up i j (h₁ j) (h₂ i j) :=
  eqToHom (functorEq i j).symm
private def ident (i j : Bool) : End (G i j) := 𝟙 _
private theorem entry_chart (i j : Bool) : entry i j ≫ eqToHom (functorEq i j) = ident i j := by
  simp [entry,ident,eqToHom_trans]
private theorem evaluated_id (i j : Bool) : ((((ident i j).total R) (β i j)).total (w i j)) (z i j) = z i j := by
  change (((𝟙 ((G i j).obj R) + 0) (β i j)).total (w i j)) (z i j) = _
  rw [add_zero]
  change (𝟙 ((((G i j).obj R) (β i j)).obj (w i j)) + 0) (z i j) = _
  simp only [add_zero,SVec.id_apply]
private theorem hs (i j : Bool) : ((σ i j).reverse : Multiset Bool) = (β i j).1 := by rfl
private def v (i j : Bool) := TensorLayerClasses.crossVector D originalSc cutoff L m Λ Λ ν η i j (h₁c j) (h₂ i j) (G i j)
  (entry i j ≫ eqToHom (functorEq i j)) (σ i j) (β i j) (hs i j) (z i j)
private theorem v_ne_zero (i j : Bool) : v i j ≠ 0 := by
  intro hv
  unfold v at hv
  rw [entry_chart] at hv
  have hz := (TensorLayerClasses.crossVector_eq_zero_iff D originalSc cutoff L m Λ Λ ν η i j (h₁c j) (h₂ i j) (G i j)
    (ident i j) (σ i j) (β i j) (hs i j) (z i j)).mp hv
  change ((((ident i j).total R) (β i j)).total (w i j)) (z i j) = 0 at hz
  rw [evaluated_id] at hz
  exact z_ne_zero i j hz
private abbrev K (i j : Bool) := PowerWordQuotientCoordinates.kernel D originalSc cutoff L (σ i j)
  (PowerWordLayerClasses.domWord ν η (.cross i j))
private def cls (i j : Bool) := PowerWordQuotientCoordinates.coordinate D originalSc cutoff L (σ i j)
  (PowerWordLayerClasses.domWord ν η (.cross i j)) (v i j)
private def rep (i j : Bool) := Classical.choose ((Submodule.mkQ_surjective (K i j)) (cls i j))
private theorem rep_spec (i j : Bool) : cls i j = (K i j).mkQ (rep i j) :=
  (Classical.choose_spec ((Submodule.mkQ_surjective (K i j)) (cls i j))).symm
example (i j : Bool) := ReservoirLayerCells.cross_square D originalSc m cutoff L Λ Λ (pL (cM i j)) left_up pR right_up
  i j (h₁ j) (h₂ i j) (h₃ i) (h₄ i j)
example (i j : Bool) := ReservoirLayerCells.cross_class_square D originalSc m cutoff L Λ Λ (pL (cM i j)) left_up pR right_up
  i j (h₁ j) (h₂ i j) (h₃ i) (h₄ i j) (G i j) (entry i j) (σ i j) (β i j) (hs i j) (z i j) (rep i j) (rep_spec i j)
example (i j : Bool) : z i j ≠ 0 := z_ne_zero i j
example (i j : Bool) : v i j ≠ 0 := v_ne_zero i j
example (i j : Bool) : cls i j ≠ 0 := coordinate_ne_zero D originalSc cutoff L (σ i j)
  (PowerWordLayerClasses.domWord ν η (.cross i j)) (v i j) (v_ne_zero i j)
example (i j : Bool) := SupportedSectors.tensorContextIso D originalSc m cutoff L Λ Λ
  probePairing reservoirPairing (pL (cM i j)) left_up pR right_up
    ((P).W.E j (h₁ j) ≫ (P).W.E i (h₂ i j))
example (i j : Bool) := SupportedSectors.tensorContext_square D originalSc m cutoff L Λ Λ
  probePairing reservoirPairing (pL (cM i j)) left_up pR right_up
    ((P).W.cross i j (h₁ j) (h₂ i j) (h₃ i) (h₄ i j))
example (i j : Bool) : SupportedSectors.tensorContextHom D originalSc m cutoff L Λ Λ
    probePairing reservoirPairing (pL (cM i j)) left_up pR right_up
      ((P).W.E j (h₁ j) ≫ (P).W.E i (h₂ i j)) =
  ReservoirLayerCells.crossRawHom D originalSc m cutoff L Λ Λ (pL (cM i j)) left_up pR right_up
    i j (h₁ j) (h₂ i j) := rfl
end Cross

private def sy : SKM.Symmetrizer D where
  d := fun _ => 1
  pos := by intro _; norm_num
  symm := by intro i j; cases i <;> cases j <;> rfl
private theorem homogeneous : originalSc.Homogeneous := by
  intro _ _ _ _ _ _ _ _ h
  exact (h rfl).elim
private def coefficient :=
  elvProbeCrossCoeff D originalSc m cutoff N Λ Λ probePairing reservoirPairing sy homogeneous
private def dotLayer (i : Bool) := SKM.lay D 0 [up false] (.dot i) [up true,up false]
private abbrev dotContent (i : Bool) : Bool →₀ ℕ := cR + Finsupp.single i 1
private theorem dotValid (i : Bool) : StepValid (true,i) false (0,dotContent i) := by
  simp [StepValid,dotContent]
private theorem dotLeft_up (i : Bool) : ∀ a ∈ (dotLayer i).left, a.l.1 = true := by
  simp [dotLayer,SKM.lay,wd]
private theorem dotRight_up (i : Bool) : ∀ a ∈ (dotLayer i).right, a.l.1 = true := by
  simp [dotLayer,SKM.lay,wd]
private def dotLeft (i : Bool) :=
  SPath.reservoirPath (dotLayer i).left (dotLeft_up i) (dotContent i)
private def dotRight (i : Bool) : SPath (dotLayer i).right
    (0,dotContent i - Finsupp.single i 1) (0,0) := by
  simpa only [dotLayer,SKM.lay,dotContent,add_tsub_cancel_right,rightLabels] using pR
example (i : Bool) := SupportedSectors.tensorLayerDotIso D originalSc m cutoff L Λ Λ
  probePairing reservoirPairing 0 [up false] [up true,up false] i (dotValid i)
  (dotLeft i) (dotLeft_up i) (dotRight i) (dotRight_up i)
example (i : Bool) := SupportedSectors.tensorLayerDot_square D originalSc m cutoff L Λ Λ
  probePairing reservoirPairing 0 [up false] [up true,up false] i (dotValid i)
  (dotLeft i) (dotLeft_up i) (dotRight i) (dotRight_up i) coefficient

namespace LiteralCross
private def crossLayer (i j : Bool) := SKM.lay D 0 [up false] (.cross i j) [up true,up false]
private abbrev crossContent (i j : Bool) : Bool →₀ ℕ := cR + (Finsupp.single i 1 + Finsupp.single j 1)
private theorem firstValid (i j : Bool) : StepValid (true,i) false (0,crossContent i j) := by
  change 1 ≤ (crossContent i j) i
  simp only [crossContent,Finsupp.add_apply,Finsupp.single_eq_same]
  omega
private theorem secondValid (i j : Bool) :
    StepValid (true,j) false (nextSector (true,i) false (0,crossContent i j)) := by
  have hc : crossContent i j - Finsupp.single i 1 = cR + Finsupp.single j 1 := by
    dsimp [crossContent]
    rw [add_comm (Finsupp.single i 1), ← add_assoc, add_tsub_cancel_right]
  change 1 ≤ (crossContent i j - Finsupp.single i 1 : Bool →₀ ℕ) j
  rw [hc]
  simp
private theorem swapContent (i j : Bool) : crossContent i j = crossContent j i := by
  dsimp [crossContent]
  rw [add_comm (Finsupp.single i 1)]
private theorem targetFirst (i j : Bool) : StepValid (true,j) false (0,crossContent i j) := by
  rw [swapContent i j]
  exact firstValid j i
private theorem targetSecond (i j : Bool) :
    StepValid (true,i) false (nextSector (true,j) false (0,crossContent i j)) := by
  rw [swapContent i j]
  exact secondValid j i
private theorem endpoints (i j : Bool) :
    nextSector (true,j) false (nextSector (true,i) false (0,crossContent i j)) =
      nextSector (true,i) false (nextSector (true,j) false (0,crossContent i j)) := by
  change (0,crossContent i j - Finsupp.single i 1 - Finsupp.single j 1) =
    ((0,crossContent i j - Finsupp.single j 1 - Finsupp.single i 1) : Sector Bool)
  rw [tsub_tsub,tsub_tsub,add_comm (Finsupp.single i 1)]
private theorem crossLeft_up (i j : Bool) : ∀ a ∈ (crossLayer i j).left, a.l.1 = true := by
  simp [crossLayer,SKM.lay,wd]
private theorem crossRight_up (i j : Bool) : ∀ a ∈ (crossLayer i j).right, a.l.1 = true := by
  simp [crossLayer,SKM.lay,wd]
private def crossLeft (i j : Bool) :=
  SPath.reservoirPath (crossLayer i j).left (crossLeft_up i j) (crossContent i j)
private def crossRight (i j : Bool) : SPath (crossLayer i j).right
    (0,crossContent i j - Finsupp.single j 1 - Finsupp.single i 1) (0,0) := by
  simpa only [crossLayer,SKM.lay,crossContent,tsub_tsub,add_comm (Finsupp.single j 1),
    add_tsub_cancel_right,rightLabels] using pR
example (i : Bool) := SupportedSectors.tensorLayerSameCrossIso D originalSc m cutoff L Λ Λ
  probePairing reservoirPairing 0 [up false] [up true,up false] i (firstValid i i) (secondValid i i)
  (crossLeft i i) (crossLeft_up i i) (crossRight i i) (crossRight_up i i)
example (i : Bool) := SupportedSectors.tensorLayerSameCross_square D originalSc m cutoff L Λ Λ
  probePairing reservoirPairing 0 [up false] [up true,up false] i (firstValid i i) (secondValid i i)
  (crossLeft i i) (crossLeft_up i i) (crossRight i i) (crossRight_up i i) coefficient
example (i j : Bool) (hij : i ≠ j) := SupportedSectors.tensorLayerCross_square D originalSc m cutoff L Λ Λ
  probePairing reservoirPairing 0 [up false] [up true,up false] i j
  (firstValid i j) (secondValid i j) (targetFirst i j) (targetSecond i j) (endpoints i j)
  (crossLeft i j) (crossLeft_up i j) (crossRight i j) (crossRight_up i j) coefficient hij

private def reindexRight {r : List (Col Bool (Bool → ℤ))} {cR cR' : Bool →₀ ℕ}
    (h : cR = cR') (pR : SPath r (0,cR') (0,0)) : SPath r (0,cR) (0,0) := by
  subst cR'
  exact pR
private def sourceRight (i j : Bool) := reindexRight (congrArg Prod.snd (endpoints i j)) (crossRight i j)
private abbrev h₁ (i j : Bool) := (P).reservoirVacuumEdge j
  (crossContent i j - Finsupp.single i 1) (secondValid i j)
private abbrev h₂ (i j : Bool) := (P).reservoirVacuumEdge i (crossContent i j) (firstValid i j)
private theorem h₁c (i j : Bool) : PowerWordWeight.wordWeight D Λ ν + D.α j =
    ReservoirWord.weight D Λ (crossContent i j - Finsupp.single i 1) :=
  (congrArg (fun x => x + D.α j) (TensorReservoirWords.path_weight D Λ (sourceRight i j)
    (crossRight_up i j))).symm.trans (h₁ i j)
private abbrev τ (i j : Bool) := ((ν ++ [j]) ++ [i]) ++ η
private abbrev σ (i j : Bool) := (τ i j).reverse
local notation "G" => (fun (i j : Bool) =>
  TensorVacuumWords.wordHom D (parameterTwist D originalSc) m cutoff L Λ Λ ν ≫
    RouquierData.E (elvRouquierData D (parameterTwist D originalSc) cutoff
      (PowerWordContent.powerBound D cutoff L) Λ) j (h₁c i j) ≫
    RouquierData.E (elvRouquierData D (parameterTwist D originalSc) cutoff
      (PowerWordContent.powerBound D cutoff L) Λ) i (h₂ i j) ≫
    TensorHomContexts.context D (parameterTwist D originalSc) cutoff L Λ
      (ReservoirWord.weight D Λ (crossContent i j)) η)
private theorem midWeight (i j : Bool) : ReservoirWord.weight D Λ (crossContent i j) =
    PowerWordWeight.wordWeight D Λ ((ν ++ [j]) ++ [i]) :=
  (h₂ i j).symm.trans ((congrArg (fun x => x + D.α i)
    ((h₁c i j).symm.trans (PowerWordWeight.wordWeight_append D Λ ν j))).trans
      (PowerWordWeight.wordWeight_append D Λ (ν ++ [j]) i))
private def β (i j : Bool) : WeightBlocks D Λ (PowerWordWeightContexts.contextWeight D
    (ReservoirWord.weight D Λ (crossContent i j)) η) :=
  ⟨τ i j,(PowerWordWeightContexts.context_weight_word D Λ ((ν ++ [j]) ++ [i]) η _ (midWeight i j)).symm⟩
private def w (i j : Bool) : ContentCategory D Sc cutoff N (β i j).1 := ⟨⟨(σ i j).reverse⟩,rfl⟩
private abbrev e (i j : Bool) := moduleIsoLinearEquiv
  (Pi.isoApp (TensorHomContexts.pairChart D Sc m cutoff L Λ Λ ν η i j (h₁c i j) (h₂ i j)) (β i j)) (w i j)
private def z (i j : Bool) := (e i j).symm (rawVector (σ i j))
private theorem z_ne_zero (i j : Bool) : z i j ≠ 0 := by
  intro hz
  apply rawVector_ne_zero (σ i j) (by change 2 + 2 * (5 : ℕ).choose 2 < 32; decide)
  have he := congrArg (e i j) hz
  simpa only [z,LinearEquiv.apply_symm_apply,map_zero] using he
private theorem functorEq (i j : Bool) :
    ReservoirLayerCells.crossHomAt D originalSc m cutoff L Λ Λ
      (crossLeft i j) (crossLeft_up i j) (sourceRight i j) (crossRight_up i j) i j (h₁ i j) (h₂ i j) = G i j :=
  ReservoirLayerCells.crossHomAt_eq D originalSc m cutoff L Λ Λ
    (crossLeft i j) (crossLeft_up i j) (sourceRight i j) (crossRight_up i j) i j (h₁ i j) (h₂ i j)
private def entry (i j : Bool) : G i j ⟶
    ReservoirLayerCells.crossHomAt D originalSc m cutoff L Λ Λ
      (crossLeft i j) (crossLeft_up i j) (sourceRight i j) (crossRight_up i j) i j (h₁ i j) (h₂ i j) :=
  eqToHom (functorEq i j).symm
private def ident (i j : Bool) : End (G i j) := 𝟙 _
private theorem entry_chart (i j : Bool) : entry i j ≫ eqToHom (functorEq i j) = ident i j := by
  simp [entry,ident,eqToHom_trans]
private theorem evaluated_id (i j : Bool) : ((((ident i j).total R) (β i j)).total (w i j)) (z i j) = z i j := by
  change (((𝟙 ((G i j).obj R) + 0) (β i j)).total (w i j)) (z i j) = _
  rw [add_zero]
  change (𝟙 ((((G i j).obj R) (β i j)).obj (w i j)) + 0) (z i j) = _
  simp only [add_zero,SVec.id_apply]
private theorem hs (i j : Bool) : ((σ i j).reverse : Multiset Bool) = (β i j).1 := by rfl
private def v (i j : Bool) := TensorLayerClasses.crossVector D originalSc cutoff L m Λ Λ ν η i j
  (h₁c i j) (h₂ i j) (G i j) (entry i j ≫ eqToHom (functorEq i j)) (σ i j) (β i j) (hs i j) (z i j)
private theorem v_ne_zero (i j : Bool) : v i j ≠ 0 := by
  intro hv
  unfold v at hv
  rw [entry_chart] at hv
  have hz := (TensorLayerClasses.crossVector_eq_zero_iff D originalSc cutoff L m Λ Λ ν η i j
    (h₁c i j) (h₂ i j) (G i j) (ident i j) (σ i j) (β i j) (hs i j) (z i j)).mp hv
  change ((((ident i j).total R) (β i j)).total (w i j)) (z i j) = 0 at hz
  rw [evaluated_id] at hz
  exact z_ne_zero i j hz
private abbrev K (i j : Bool) := PowerWordQuotientCoordinates.kernel D originalSc cutoff L (σ i j)
  (PowerWordLayerClasses.domWord ν η (.cross i j))
private def cls (i j : Bool) := PowerWordQuotientCoordinates.coordinate D originalSc cutoff L (σ i j)
  (PowerWordLayerClasses.domWord ν η (.cross i j)) (v i j)
private def rep (i j : Bool) := Classical.choose ((Submodule.mkQ_surjective (K i j)) (cls i j))
private theorem rep_spec (i j : Bool) : cls i j = (K i j).mkQ (rep i j) :=
  (Classical.choose_spec ((Submodule.mkQ_surjective (K i j)) (cls i j))).symm
example (i j : Bool) : z i j ≠ 0 := z_ne_zero i j
example (i j : Bool) : cls i j ≠ 0 := coordinate_ne_zero D originalSc cutoff L (σ i j)
  (PowerWordLayerClasses.domWord ν η (.cross i j)) (v i j) (v_ne_zero i j)
example (i : Bool) := SupportedSectors.tensorLayerSameCross_class_square D originalSc m cutoff L Λ Λ
  probePairing reservoirPairing 0 [up false] [up true,up false] i (firstValid i i) (secondValid i i)
  (crossLeft i i) (crossLeft_up i i) (crossRight i i) (crossRight_up i i) coefficient
  (G i i) (entry i i) (σ i i) (β i i) (hs i i) (z i i) (rep i i) (rep_spec i i)
example (i j : Bool) (hij : i ≠ j) := SupportedSectors.tensorLayerCross_class_square D originalSc m cutoff L Λ Λ
  probePairing reservoirPairing 0 [up false] [up true,up false] i j
  (firstValid i j) (secondValid i j) (targetFirst i j) (targetSecond i j) (endpoints i j)
  (crossLeft i j) (crossLeft_up i j) (crossRight i j) (crossRight_up i j) coefficient hij
  (G i j) (entry i j) (σ i j) (β i j) (hs i j) (z i j) (rep i j) (rep_spec i j)
end LiteralCross
end NonVacuity.SupportedTensorCrossClasses
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.SwappedAssembly.SupportedTensorCrossClasses
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owned module"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"
