import OddMath.SKM.CupAttachmentReduced
import OddMath.SKM.TableIsotopy
import OddMath.SKM.CoveringDatum

/-!
# Literal left-cup attachment for the downward boundary

Supports BE2, arXiv:1701.04133v2, Theorem 10.3 Claim 3, using the generator
degree and parity table. This is literal attachment, not normalized-family
comparison. The degree is the sum of the actual extended-layer table. The
left cup is derived (`etaPDiagram`), not an ordinary `Shape.cup`.
-/
namespace OddMath.SKM
open StringDiagrams StringDiagrams.Chord DTMove
variable {I X : Type*} [AddCommGroup X]

/-- Attach the left cup to a downward left-cons source. -/
def leftCupAttachMatching (i : I) (R : List (TMove (Letter I))) :=
  CupAttachment.cupAttachMatching true i R

/-- Attach the left cup to the actual decorated move list. -/
def leftCupAttachMoves (i : I) (ds : List (DTMove I)) :=
  CupAttachment.cupAttachMoves true i ds

theorem leftCupAttach_matching_iso {i : I} {a b : List (Letter I)}
    {R : List (TMove (Letter I))} (hR : IsMatching₂ ((false, i) :: a) b R) :
    IsMatching₂ a ((true, i) :: b) (leftCupAttachMatching i R) ∧
      Iso (pairing₂ a (leftCupAttachMatching i R)) (pairing₂ ((false, i) :: a) R) :=
  CupAttachment.cupAttach_matching_iso hR

/-- The new layer is literally a left cup, followed by the whiskered old layers. -/
theorem dLay_leftCupAttach {i : I} {a b : List (Letter I)}
    {R : List (TMove (Letter I))} (hR : IsMatching₂ ((false, i) :: a) b R)
    {ds : List (DTMove I)} (hd : tmoves ds = R) :
    dLay a (leftCupAttachMoves i ds) =
      [([], XShape.lcup i, a)] ++
        (dLay ((false, i) :: a) ds).map (xwhL [(true, i)] []) := by
  have hs := dLay_shift_of_fits (length_dualW ((false, i) :: a)) [(true, i)] ds
    (tStart ((false, i) :: a)) ((false, i) :: a) (tStart_letters _)
    (by rw [hd]; exact hR.1)
  have hc : tLet a (.mv (.cup 0 (true, i))) = (true, i) :: (false, i) :: a := by
    simpa [tLet, flipL] using chStep_cup ([] : List (Letter I)) a (true, i)
  have hm : tmLay a (.mv (.cup 0 (true, i))) = [([], XShape.lcup i, a)] := by
    have h := moveLay_cup ([] : List (Letter I)) a (true, i)
    simpa [tmLay, xCupL, xwhL] using h
  simpa only [leftCupAttachMoves, CupAttachment.cupAttachMoves, dLay, hc, hm,
    List.length_singleton, List.singleton_append] using congrArg
      (fun z => [([], XShape.lcup i, a)] ++ z) hs

/-- Source table shift: degree `dᵢ(1−hᵢν)` and parity `|i,ν|`, with `ν = wt μ a`.
No hypothesis equates the left cup to a single ordinary generating layer. -/
theorem leftCupAttach_degree_parity (D : Datum I X) (sy : Symmetrizer D) (μ : X)
    {i : I} {a b : List (Letter I)} {R : List (TMove (Letter I))}
    (hR : IsMatching₂ ((false, i) :: a) b R)
    {ds : List (DTMove I)} (hd : tmoves ds = R) :
    tableDegree D sy μ (dLay a (leftCupAttachMoves i ds)) =
      tableDegree D sy μ (dLay ((false, i) :: a) ds) +
        sy.d i * (1 - D.h i (wt D μ a)) ∧
    xpar D μ (dLay a (leftCupAttachMoves i ds)) =
      xpar D μ (dLay ((false, i) :: a) ds) + ipar D i (wt D μ a) := by
  rw [dLay_leftCupAttach hR hd]
  constructor
  · rw [tableDegree_append, tableDegree_whisk]
    simp [tableDegree, add_comm]
  · rw [xpar_append, xpar_map_xwhL]
    simp [xpar, xlpar, ipar_wt, add_comm]

/-- The left-cup table entry agrees with the two ordinary source expressions defining
`etaPDiagram`. This is a numerical anchor, not equality of ordinary layer lists. -/
theorem leftCupAttach_etaP_source (D : Datum I X) (sy : Symmetrizer D) (μ : X)
    (i : I) (a : List (Letter I)) :
    tableDegree D sy μ [([], XShape.lcup i, a)] =
      if 0 < D.h i (wt D μ a) then
        gsum D sy (wt D μ a) (dcupL i (D.h i (wt D μ a) - 1).toNat)
      else gsum D sy (wt D μ a)
        (etaL i (-D.h i (wt D μ a)).toNat ++ lcrossL i i) := by
  convert tableDegree_etaP_source D sy (wt D μ a) i using 1
  simp [tableDegree]

@[simp] theorem ncr₂_leftCupAttachMatching (i : I) (R : List (TMove (Letter I))) :
    ncr₂ (leftCupAttachMatching i R) = ncr₂ R := by
  simp only [leftCupAttachMatching, CupAttachment.cupAttachMatching, ncr₂,
    List.countP_cons, List.countP_map, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
  congr 1
  funext m
  rcases m with (⟨g, x⟩ | p) | g <;> rfl

/-- Crossing-minimality is preserved; the stricter critical-point condition is not claimed. -/
theorem reduced₂_leftCupAttach {i : I} {a b : List (Letter I)}
    {R : List (TMove (Letter I))} (hR : IsMatching₂ ((false, i) :: a) b R)
    (hred : Reduced₂ ((false, i) :: a) R) :
    Reduced₂ a (leftCupAttachMatching i R) := by
  obtain ⟨hm, hi⟩ := leftCupAttach_matching_iso hR
  have hOld := (tInv_tStart ((false, i) :: a)).run hR.1
  have hNew := (tInv_tStart a).run hm.1
  have hup := Chord.length_xs_le_cr hOld hred.1 hred.2
  have hlo := Chord.cr_le_length_xs hNew
  have hcount :
      (tRun flipL a.length (tStart a) (leftCupAttachMatching i R)).xs.length =
        (tRun flipL ((false, i) :: a).length (tStart ((false, i) :: a)) R).xs.length := by
    simp only [Chord.length_xs_tRun, ncr₂_leftCupAttachMatching]
    rfl
  have hcr : cr (pairing₂ a (leftCupAttachMatching i R)) =
      cr (pairing₂ ((false, i) :: a) R) :=
    le_antisymm (Chord.cr_le_of_iso hi) (Chord.cr_le_of_iso hi.symm)
  apply Chord.reduced_of_length_xs_eq_cr hNew
  apply le_antisymm _ hlo
  rw [hcount]
  exact hup.trans (le_of_eq hcr.symm)

/-- Literal downward-left boundary bending with matching, endpoint strands, bounded
points, actual decorations and the source table shift. This does not assert a
bijection between normalized families or the bilinear-form comparison of Claim 3. -/
theorem cup_attach_down_decorated (D : Datum I X) (sy : Symmetrizer D) (μ : X)
    {i : I} {a b : List (Letter I)} {R : List (TMove (Letter I))}
    (hR : IsMatching₂ ((false, i) :: a) b R) :
    IsMatching₂ a ((true, i) :: b) (leftCupAttachMatching i R) ∧
    Iso (pairing₂ a (leftCupAttachMatching i R)) (pairing₂ ((false, i) :: a) R) ∧
    (Reduced₂ ((false, i) :: a) R → Reduced₂ a (leftCupAttachMatching i R)) ∧
    ∃ e : MatchingStrand ((false, i) :: a) R ≃ MatchingStrand a (leftCupAttachMatching i R),
      (∀ j, (e j).val = j.val) ∧
      ∀ (q : ℕ → ℕ × ℕ),
        (∀ j ∈ leftEnds₂ ((false, i) :: a) R,
          (q j).1 ≤ R.length ∧ OnStrand₂ ((false, i) :: a) R j (q j)) →
      ∀ (c : MatchingStrand ((false, i) :: a) R → ℕ) (ds : List (DTMove I)),
        Decorates₂ ((false, i) :: a) R q (strandCounts c) ds →
        (∀ j ∈ leftEnds₂ a (leftCupAttachMatching i R),
          (cupAttachPoint (q j)).1 ≤ (leftCupAttachMatching i R).length ∧
          OnStrand₂ a (leftCupAttachMatching i R) j (cupAttachPoint (q j))) ∧
        Decorates₂ a (leftCupAttachMatching i R) (cupAttachPoint ∘ q)
          (strandCounts (c ∘ e.symm)) (leftCupAttachMoves i ds) ∧
        tableDegree D sy μ (dLay a (leftCupAttachMoves i ds)) =
          tableDegree D sy μ (dLay ((false, i) :: a) ds) +
            sy.d i * (1 - D.h i (wt D μ a)) ∧
        xpar D μ (dLay a (leftCupAttachMoves i ds)) =
          xpar D μ (dLay ((false, i) :: a) ds) + ipar D i (wt D μ a) := by
  obtain ⟨hm, hi⟩ := leftCupAttach_matching_iso hR
  refine ⟨hm, hi, reduced₂_leftCupAttach hR,
    CupAttachment.cupAttachStrandEquiv (o := true) hR, fun _ => rfl, ?_⟩
  intro q hq c ds hd
  refine ⟨?_, CupAttachment.decorates₂_cupAttach (o := true) hR q c hd,
    leftCupAttach_degree_parity D sy μ hR hd.1⟩
  intro j hj
  change j ∈ leftEnds₂ a (CupAttachment.cupAttachMatching true i R) at hj
  rw [CupAttachment.leftEnds₂_cupAttach (o := true) hR] at hj
  exact CupAttachment.onStrand₂_cupAttach (o := true) hR (hq j hj).1 (hq j hj).2

/-- The same numerical shift in the covering-root-datum API used for the F-adjoint.
The region is the weight after removing the downward left-cons letter. -/
theorem leftCupAttach_root_degree_parity (Q : CoveringQuantum.RootDatum I X) (μ : X)
    {i : I} {a b : List (Letter I)} {R : List (TMove (Letter I))}
    (hR : IsMatching₂ ((false, i) :: a) b R)
    {ds : List (DTMove I)} (hd : tmoves ds = R) :
    tableDegree Q.toSKM Q.skmSymmetrizer μ (dLay a (leftCupAttachMoves i ds)) =
      tableDegree Q.toSKM Q.skmSymmetrizer μ (dLay ((false, i) :: a) ds) +
        (Q.d i : ℤ) * (1 - Q.h i (wt Q.toSKM μ a)) ∧
    xpar Q.toSKM μ (dLay a (leftCupAttachMoves i ds)) =
      xpar Q.toSKM μ (dLay ((false, i) :: a) ds) + Q.parl i (wt Q.toSKM μ a) := by
  simpa only [CoveringQuantum.RootDatum.skmSymmetrizer_d,
    CoveringQuantum.RootDatum.toSKM_h, ipar, CoveringQuantum.RootDatum.parl,
    CoveringQuantum.RootDatum.toSKM_parity] using
    leftCupAttach_degree_parity Q.toSKM Q.skmSymmetrizer μ hR hd

end OddMath.SKM
