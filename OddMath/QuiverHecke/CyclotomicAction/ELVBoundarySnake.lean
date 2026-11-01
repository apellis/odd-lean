import OddMath.QuiverHecke.CyclotomicAction.ELVCrossingHeight

/-! # The actual boundary-kernel map into the prescribed crossing source

The kernel arrow in the snake sequence of `DeformedRouquierMatrix.md` is
constructed from the existing source section, P map and short-cross decoder.
Its image is the kernel of the actual cyclotomic crossing. No exact-sequence
or faithful-action hypothesis is supplied.
-/
noncomputable section
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
open CategoryTheory StringDiagrams Supercategory
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

theorem shortCross_decode_of_mem (i : I) (v t : List I)
    (z : AppendTarget D Sc cutoff i v (t ++ [i]))
    (hz : z ∈ appendCrossingSpan D Sc cutoff i v t) :
    shortCross D Sc cutoff i v t (ShortCrossCoordinates.decode D Sc cutoff i v t z) = z := by
  rw [← ShortCrossCoordinates.range_shortCross] at hz
  obtain ⟨y, rfl⟩ := hz
  rw [ShortCrossCoordinates.decode_shortCross]

def boundarySnake (p : ZMod 2) (j : {j : I // D.parity j = 1}) (v : List I) :
    LinearMap.ker (outputPolynomialBoundary D Sc cutoff p j v) →ₗ[k]
      Source D Sc cutoff j.1 v v :=
  q D Sc cutoff j.1 v v ∘ₗ ShortCrossCoordinates.decode D Sc cutoff j.1 v v ∘ₗ
    pMap D Sc cutoff j.1 v (v ++ [j.1]) ∘ₗ sourceLongSection D Sc cutoff p j.1 v ∘ₗ
      (LinearMap.ker (outputPolynomialBoundary D Sc cutoff p j v)).subtype

theorem boundarySnake_lift (p : ZMod 2) (j : {j : I // D.parity j = 1}) (v : List I)
    (f : LinearMap.ker (outputPolynomialBoundary D Sc cutoff p j v)) :
    shortCross D Sc cutoff j.1 v v
      (ShortCrossCoordinates.decode D Sc cutoff j.1 v v
        (pMap D Sc cutoff j.1 v (v ++ [j.1]) (sourceLongSection D Sc cutoff p j.1 v f))) =
      pMap D Sc cutoff j.1 v (v ++ [j.1]) (sourceLongSection D Sc cutoff p j.1 v f) := by
  apply shortCross_decode_of_mem
  rw [← appendC0_ker, LinearMap.mem_ker, appendC0_pMap,
    outputLongExtraction_sourceLongSection]
  exact f.property

theorem toCyclotomic_boundarySnake (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I)
    (f : LinearMap.ker (outputPolynomialBoundary D Sc cutoff p j v)) :
    toCyclotomic D Sc cutoff j.1 v v (boundarySnake D Sc cutoff p j v f) = 0 := by
  have hs := LinearMap.congr_fun (shortColumn_quotient_square D Sc cutoff j.1 v v)
    (ShortCrossCoordinates.decode D Sc cutoff j.1 v v
      (pMap D Sc cutoff j.1 v (v ++ [j.1]) (sourceLongSection D Sc cutoff p j.1 v f)))
  change _ = toCyclotomic D Sc cutoff j.1 v v (boundarySnake D Sc cutoff p j v f) at hs
  rw [← hs, boundarySnake_lift]
  have hm : pMap D Sc cutoff j.1 v (v ++ [j.1]) (sourceLongSection D Sc cutoff p j.1 v f) ∈
      LinearMap.ker (canonicalAppendTarget D Sc cutoff j.1 v (v ++ [j.1])) := by
    rw [ker_canonicalAppendTarget]
    exact ⟨_, rfl⟩
  exact hm

theorem boundarySnake_injective (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I) :
    Function.Injective (boundarySnake D Sc cutoff p j v) := by
  apply LinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro f hf
  have hy : ShortCrossCoordinates.decode D Sc cutoff j.1 v v
      (pMap D Sc cutoff j.1 v (v ++ [j.1]) (sourceLongSection D Sc cutoff p j.1 v f)) ∈
      LinearMap.ker (q D Sc cutoff j.1 v v) := hf
  rw [← range_pprime_eq_ker_q] at hy
  obtain ⟨a, ha⟩ := hy
  have he : alpha D Sc cutoff j.1 v v a = sourceLongSection D Sc cutoff p j.1 v f := by
    apply pMap_injective D Sc cutoff j.1 v (v ++ [j.1])
    have hs := LinearMap.congr_fun (shortColumn_square D Sc cutoff j.1 v v) a
    exact hs.trans (by rw [ha, boundarySnake_lift])
  have hb := congrArg (outputLongExtraction D Sc cutoff p j.1 v) he
  rw [outputLongExtraction_alpha, outputLongExtraction_sourceLongSection] at hb
  exact Subtype.ext hb.symm

/-- Changing the source lift by its prescribed short coordinate does not
change the cyclotomic snake class. This permits using the original corrected
rho lifts in subsequent cap recurrences. -/
theorem boundarySnake_eq_lift (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I)
    (f : LinearMap.ker (outputPolynomialBoundary D Sc cutoff p j v))
    (z : Target D Sc cutoff j.1 v (v ++ [j.1]))
    (hz : outputLongExtraction D Sc cutoff p j.1 v z = f) :
    boundarySnake D Sc cutoff p j v f =
      q D Sc cutoff j.1 v v (ShortCrossCoordinates.decode D Sc cutoff j.1 v v
        (pMap D Sc cutoff j.1 v (v ++ [j.1]) z)) := by
  have he := source_reconstruction D Sc cutoff p j.1 v z
  rw [hz] at he
  rw [← he, map_add]
  have hs := LinearMap.congr_fun (shortColumn_square D Sc cutoff j.1 v v)
    (extract D Sc cutoff j.1 v v z)
  rw [hs, map_add, ShortCrossCoordinates.decode_shortCross, map_add]
  have hq : q D Sc cutoff j.1 v v
      (pprime D Sc cutoff j.1 v v (extract D Sc cutoff j.1 v v z)) = 0 := by
    have hm : pprime D Sc cutoff j.1 v v (extract D Sc cutoff j.1 v v z) ∈
        LinearMap.ker (q D Sc cutoff j.1 v v) := by
      rw [← range_pprime_eq_ker_q]
      exact ⟨_, rfl⟩
    exact hm
  rw [hq, zero_add]
  rfl

theorem range_boundarySnake (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I) :
    LinearMap.range (boundarySnake D Sc cutoff p j v) =
      LinearMap.ker (toCyclotomic D Sc cutoff j.1 v v) := by
  apply le_antisymm
  · rintro z ⟨f, rfl⟩
    exact toCyclotomic_boundarySnake D Sc cutoff p j v f
  · intro z hz
    obtain ⟨y, rfl⟩ := q_surjective D Sc cutoff j.1 v v z
    have hy : shortCross D Sc cutoff j.1 v v y ∈
        LinearMap.ker (canonicalAppendTarget D Sc cutoff j.1 v (v ++ [j.1])) := by
      rw [LinearMap.mem_ker]
      have he := LinearMap.congr_fun (shortColumn_quotient_square D Sc cutoff j.1 v v) y
      exact he.trans hz
    rw [ker_canonicalAppendTarget] at hy
    obtain ⟨x, hx⟩ := hy
    have hc : appendC0 D Sc cutoff j.1 v v (shortCross D Sc cutoff j.1 v v y) = 0 := by
      apply appendCrossingSpan_le_ker D Sc cutoff j.1 v v
      rw [← ShortCrossCoordinates.range_shortCross]
      exact ⟨y, rfl⟩
    let f : LinearMap.ker (outputPolynomialBoundary D Sc cutoff p j v) :=
      ⟨outputLongExtraction D Sc cutoff p j.1 v x, by
        rw [LinearMap.mem_ker, ← appendC0_pMap D Sc cutoff p j v, hx]
        exact hc⟩
    let a := extract D Sc cutoff j.1 v v x
    have he : y = pprime D Sc cutoff j.1 v v a +
        ShortCrossCoordinates.decode D Sc cutoff j.1 v v
          (pMap D Sc cutoff j.1 v (v ++ [j.1]) (sourceLongSection D Sc cutoff p j.1 v f)) := by
      apply ShortCrossCoordinates.shortCross_injective D Sc cutoff j.1 v v
      rw [map_add, boundarySnake_lift]
      have hs := LinearMap.congr_fun (shortColumn_square D Sc cutoff j.1 v v) a
      rw [← hs, ← map_add, source_reconstruction, hx]
    refine ⟨f, ?_⟩
    have hqa : q D Sc cutoff j.1 v v (pprime D Sc cutoff j.1 v v a) = 0 := by
      have hm : pprime D Sc cutoff j.1 v v a ∈ LinearMap.ker (q D Sc cutoff j.1 v v) := by
        rw [← range_pprime_eq_ker_q]
        exact ⟨a, rfl⟩
      exact hm
    rw [he, map_add, hqa, zero_add]
    rfl

/-- The actual kernel of the prescribed cyclotomic crossing is the boundary kernel. -/
def boundarySnakeKernelEquiv (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I) :
    LinearMap.ker (outputPolynomialBoundary D Sc cutoff p j v) ≃ₗ[k]
      LinearMap.ker (toCyclotomic D Sc cutoff j.1 v v) :=
  LinearEquiv.ofBijective
    ((boundarySnake D Sc cutoff p j v).codRestrict _
      (fun f => toCyclotomic_boundarySnake D Sc cutoff p j v f))
    ⟨fun f g hfg => boundarySnake_injective D Sc cutoff p j v (congrArg Subtype.val hfg),
      by
        intro z
        have hz : z.1 ∈ LinearMap.range (boundarySnake D Sc cutoff p j v) := by
          rw [range_boundarySnake]
          exact z.property
        obtain ⟨f, hf⟩ := hz
        exact ⟨f, Subtype.ext hf⟩⟩

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
