import OddMath.QuiverHecke.CyclotomicAction.ProbeMixedRelations
import OddMath.QuiverHecke.CyclotomicAction.ProbeFirstDot

/-! # Actual rectangular corner relations for mixed probe dots

The affine slides and positive-dot remainders are compared with the literal
word-corner maps. These comparisons use the existing cyclotomic algebra,
including its actual finite Hom-matrix multiplication.
-/
noncomputable section
open CategoryTheory StringDiagrams
open scoped Classical
namespace OddMath.QuiverHecke
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X]
  {k : Type w} [CommRing k] (D : SKM.Datum I X) (Sc : SKM.Scalars D k)
  [Fintype I] (a : I → Polynomial k)

theorem cyclotomicWordEntry_smul {n : ℕ} (s t : Word I (n+1)) (c : k)
    (f : wordObj D Sc s ⟶ wordObj D Sc t) :
    cyclotomicWordEntry D Sc a s t (c • f) =
      c • cyclotomicWordEntry D Sc a s t f := by
  unfold cyclotomicWordEntry
  rw [FiniteHomMatrix.single_smul, map_smul]

abbrev probeMixedCornerDot (pre post : List I) (i j : I) (r : ℕ) :=
  cyclotomicWordEnd D Sc a (probeMixedWord pre post i j)
    (dotE D Sc (pre ++ [i,j] ++ post) r)

def probeMixedEntry (pre post : List I) (i j : I) :
    CyclotomicAlgebra D Sc a (pre.length+post.length+1) :=
  cyclotomicWordEntry D Sc a (probeMixedWord pre post i j)
    (probeMixedWord pre post j i) (probeMixedCross D Sc pre post i j)

theorem probeMixedCorner_slide (pre post : List I) (i j : I) (hij : i ≠ j) :
    (probeMixedCornerDot D Sc a pre post j i pre.length).val *
        probeMixedEntry D Sc a pre post i j =
      SKM.zsign k (D.parity i * D.parity j) •
        (probeMixedEntry D Sc a pre post i j *
          (probeMixedCornerDot D Sc a pre post i j (pre.length+1)).val) := by
  change cyclotomicWordEntry D Sc a (probeMixedWord pre post j i)
      (probeMixedWord pre post j i) (dotE D Sc (pre ++ [j,i] ++ post) pre.length) *
      cyclotomicWordEntry D Sc a (probeMixedWord pre post i j)
        (probeMixedWord pre post j i) (probeMixedCross D Sc pre post i j) = _
  rw [← cyclotomicWordEntry_comp]
  change cyclotomicWordEntry D Sc a (probeMixedWord pre post i j)
      (probeMixedWord pre post j i) _ =
    SKM.zsign k (D.parity i * D.parity j) •
      (cyclotomicWordEntry D Sc a (probeMixedWord pre post i j)
        (probeMixedWord pre post j i) (probeMixedCross D Sc pre post i j) *
       cyclotomicWordEntry D Sc a (probeMixedWord pre post i j)
        (probeMixedWord pre post i j) (dotE D Sc (pre ++ [i,j] ++ post) (pre.length+1)))
  rw [← cyclotomicWordEntry_comp, ← cyclotomicWordEntry_smul]
  exact congrArg (cyclotomicWordEntry D Sc a (probeMixedWord pre post i j)
    (probeMixedWord pre post j i)) (probeMixedCross_slide D Sc pre post i j hij)

theorem probeMixedCorner_slide_reverse (pre post : List I) (i j : I) (hij : i ≠ j) :
    probeMixedEntry D Sc a pre post j i *
        (probeMixedCornerDot D Sc a pre post j i pre.length).val =
      SKM.zsign k (D.parity i * D.parity j) •
        ((probeMixedCornerDot D Sc a pre post i j (pre.length+1)).val *
          probeMixedEntry D Sc a pre post j i) := by
  change cyclotomicWordEntry D Sc a (probeMixedWord pre post j i)
      (probeMixedWord pre post i j) (probeMixedCross D Sc pre post j i) *
      cyclotomicWordEntry D Sc a (probeMixedWord pre post j i)
        (probeMixedWord pre post j i) (dotE D Sc (pre ++ [j,i] ++ post) pre.length) = _
  rw [← cyclotomicWordEntry_comp]
  change cyclotomicWordEntry D Sc a (probeMixedWord pre post j i)
      (probeMixedWord pre post i j) _ =
    SKM.zsign k (D.parity i * D.parity j) •
      (cyclotomicWordEntry D Sc a (probeMixedWord pre post i j)
        (probeMixedWord pre post i j) (dotE D Sc (pre ++ [i,j] ++ post) (pre.length+1)) *
       cyclotomicWordEntry D Sc a (probeMixedWord pre post j i)
        (probeMixedWord pre post i j) (probeMixedCross D Sc pre post j i))
  rw [← cyclotomicWordEntry_comp, ← cyclotomicWordEntry_smul]
  exact congrArg (cyclotomicWordEntry D Sc a (probeMixedWord pre post j i)
    (probeMixedWord pre post i j)) (probeMixedCross_slide_reverse D Sc pre post i j hij)

/-- Actual connected Q remainders in the source corner. The leading-term
unit follows from the preceding source dot and the given scalar unit. -/
theorem probeMixedCorner_remainders_connected (hn : Sc.NoPure) (pre post : List I) (i j : I)
    (hij : i ≠ j) (hd : D.d i j ≠ 0)
    (hu : IsUnit (probeMixedCornerDot D Sc a pre post i j pre.length)) :
    ∃ U Rright Rleft : CyclotomicWordCorner D Sc a (probeMixedWord pre post i j),
      IsUnit U ∧
      probeMixedEntry D Sc a pre post j i * probeMixedEntry D Sc a pre post i j =
        U.val + Rright.val * (probeMixedCornerDot D Sc a pre post i j (pre.length+1)).val ∧
      probeMixedEntry D Sc a pre post j i * probeMixedEntry D Sc a pre post i j =
        U.val + (probeMixedCornerDot D Sc a pre post i j (pre.length+1)).val * Rleft.val := by
  let s := probeMixedWord pre post i j
  let q : End ((pres D Sc).obj (ob D (pre ++ [i,j] ++ post))) →+* CyclotomicWordCorner D Sc a s :=
    cyclotomicWordEnd D Sc a s
  let u := dotE D Sc (pre ++ [i,j] ++ post) pre.length
  let v := dotE D Sc (pre ++ [i,j] ++ post) (pre.length+1)
  obtain ⟨Rright, hr⟩ := probeMixedCross_remainder_right D Sc hn pre post i j hij hd
  obtain ⟨Rleft, hl⟩ := probeMixedCross_remainder_left D Sc hn pre post i j hij hd
  refine ⟨q ((Sc.t i j : k) • u^(D.dn i j)), q Rright, q Rleft, ?_, ?_, ?_⟩
  · rw [Algebra.smul_def, map_mul, map_pow]
    exact (((Sc.t i j).isUnit.map
      (algebraMap k (End ((pres D Sc).obj (ob D (pre ++ [i,j] ++ post)))))).map q).mul (hu.pow _)
  · unfold probeMixedEntry
    rw [← cyclotomicWordEntry_comp]
    change (q (probeMixedCross D Sc pre post i j ≫
      probeMixedCross D Sc pre post j i)).val =
      (q ((Sc.t i j : k) • u^(D.dn i j))).val + (q Rright).val * (q v).val
    have hq : q (probeMixedCross D Sc pre post i j ≫
        probeMixedCross D Sc pre post j i) =
        q ((Sc.t i j : k) • u^(D.dn i j)) + q Rright * q v := by
      calc
        _ = q ((Sc.t i j : k) • u^(D.dn i j) + Rright*v) :=
          congrArg (fun f : End ((pres D Sc).obj (ob D (pre ++ [i,j] ++ post))) => q f) hr
        _ = q ((Sc.t i j : k) • u^(D.dn i j)) + q (Rright*v) := q.map_add' _ _
        _ = _ := congrArg (fun z : CyclotomicWordCorner D Sc a s =>
          q ((Sc.t i j : k) • u^(D.dn i j)) + z) (q.map_mul' Rright v)
    exact congrArg (fun z : CyclotomicWordCorner D Sc a s => z.val) hq
  · unfold probeMixedEntry
    rw [← cyclotomicWordEntry_comp]
    change (q (probeMixedCross D Sc pre post i j ≫
      probeMixedCross D Sc pre post j i)).val =
      (q ((Sc.t i j : k) • u^(D.dn i j))).val + (q v).val * (q Rleft).val
    have hq : q (probeMixedCross D Sc pre post i j ≫
        probeMixedCross D Sc pre post j i) =
        q ((Sc.t i j : k) • u^(D.dn i j)) + q v * q Rleft := by
      calc
        _ = q ((Sc.t i j : k) • u^(D.dn i j) + v*Rleft) :=
          congrArg (fun f : End ((pres D Sc).obj (ob D (pre ++ [i,j] ++ post))) => q f) hl
        _ = q ((Sc.t i j : k) • u^(D.dn i j)) + q (v*Rleft) := q.map_add' _ _
        _ = _ := congrArg (fun z : CyclotomicWordCorner D Sc a s =>
          q ((Sc.t i j : k) • u^(D.dn i j)) + z) (q.map_mul' v Rleft)
    exact congrArg (fun z : CyclotomicWordCorner D Sc a s => z.val) hq

/-- The disconnected quadratic supplies the same two remainder statements,
with zero remainders and its single scalar unit leading term. -/
theorem probeMixedCorner_remainders (pre post : List I) (i j : I)
    (hij : i ≠ j)
    (hu : IsUnit (probeMixedCornerDot D Sc a pre post i j pre.length)) :
    ∃ U Rright Rleft : CyclotomicWordCorner D Sc a (probeMixedWord pre post i j),
      IsUnit U ∧
      probeMixedEntry D Sc a pre post j i * probeMixedEntry D Sc a pre post i j =
        U.val + Rright.val * (probeMixedCornerDot D Sc a pre post i j (pre.length+1)).val ∧
      probeMixedEntry D Sc a pre post j i * probeMixedEntry D Sc a pre post i j =
        U.val + (probeMixedCornerDot D Sc a pre post i j (pre.length+1)).val * Rleft.val := by
  by_cases hd : D.d i j = 0
  · let s := probeMixedWord pre post i j
    let q : End ((pres D Sc).obj (ob D (pre ++ [i,j] ++ post))) →+* CyclotomicWordCorner D Sc a s :=
      cyclotomicWordEnd D Sc a s
    let c := algebraMap k (End ((pres D Sc).obj (ob D (pre ++ [i,j] ++ post)))) (Sc.t i j : k)
    have hBA : probeMixedEntry D Sc a pre post j i * probeMixedEntry D Sc a pre post i j =
        (q c).val := by
      unfold probeMixedEntry
      rw [← cyclotomicWordEntry_comp]
      change (q (probeMixedCross D Sc pre post i j ≫
        probeMixedCross D Sc pre post j i)).val = (q c).val
      rw [probeMixedCross_quadratic_zero D Sc pre post i j hij hd]
      change (q ((Sc.t i j : k) • (1 : End ((pres D Sc).obj (ob D (pre ++ [i,j] ++ post)))))).val =
        (q (algebraMap k (End ((pres D Sc).obj (ob D (pre ++ [i,j] ++ post)))) (Sc.t i j : k))).val
      rw [Algebra.algebraMap_eq_smul_one]
    refine ⟨q c, 0, 0,
      (((Sc.t i j).isUnit.map (algebraMap k (End ((pres D Sc).obj (ob D (pre ++ [i,j] ++ post)))))).map q), ?_, ?_⟩
    · change probeMixedEntry D Sc a pre post j i * probeMixedEntry D Sc a pre post i j =
        (q c).val + (0 : CyclotomicAlgebra D Sc a (pre.length+post.length+1)) *
          (probeMixedCornerDot D Sc a pre post i j (pre.length+1)).val
      rw [zero_mul, add_zero]
      exact hBA
    · change probeMixedEntry D Sc a pre post j i * probeMixedEntry D Sc a pre post i j =
        (q c).val + (probeMixedCornerDot D Sc a pre post i j (pre.length+1)).val *
          (0 : CyclotomicAlgebra D Sc a (pre.length+post.length+1))
      rw [mul_zero, add_zero]
      exact hBA
  · exact probeMixedCorner_remainders_connected D Sc a pre post i j hij hd hu

/-- The actual distinct-colour probe step: preceding dots in the source and
swapped target corners are units, hence so is the following source dot.
All signed slides and Q factorization premises are discharged internally. -/
theorem probeMixedCorner_dot_isUnit (pre post : List I) (i j : I) (hij : i ≠ j)
    (hu : IsUnit (probeMixedCornerDot D Sc a pre post i j pre.length))
    (hw : IsUnit (probeMixedCornerDot D Sc a pre post j i pre.length)) :
    IsUnit (probeMixedCornerDot D Sc a pre post i j (pre.length+1)) := by
  let s := probeMixedWord pre post i j
  let t := probeMixedWord pre post j i
  let q : End ((pres D Sc).obj (ob D (pre ++ [j,i] ++ post))) →+* CyclotomicWordCorner D Sc a t :=
    cyclotomicWordEnd D Sc a t
  let ε := SKM.zsign k (D.parity i * D.parity j)
  let v := probeMixedCornerDot D Sc a pre post i j (pre.length+1)
  let A := probeMixedEntry D Sc a pre post i j
  let B := probeMixedEntry D Sc a pre post j i
  let w := probeMixedCornerDot D Sc a pre post j i pre.length
  let W := q (ε • dotE D Sc (pre ++ [j,i] ++ post) pre.length)
  have he : ε * ε = 1 := zsign_mul_self _
  have hε : IsUnit ε := ⟨⟨ε, ε, he, he⟩, rfl⟩
  have hW : IsUnit W := by
    change IsUnit (q (ε • dotE D Sc (pre ++ [j,i] ++ post) pre.length))
    rw [Algebra.smul_def, map_mul]
    exact ((hε.map (algebraMap k (End ((pres D Sc).obj (ob D (pre ++ [j,i] ++ post)))))).map q).mul hw
  have hWval : W.val = ε • w.val := by
    change cyclotomicWordEntry D Sc a t t
      (ε • dotE D Sc (pre ++ [j,i] ++ post) pre.length) =
      ε • cyclotomicWordEntry D Sc a t t
        (dotE D Sc (pre ++ [j,i] ++ post) pre.length)
    exact cyclotomicWordEntry_smul D Sc a t t ε _
  have hs := probeMixedCorner_slide D Sc a pre post i j hij
  change w.val * A = ε • (A * v.val) at hs
  have hs' := probeMixedCorner_slide_reverse D Sc a pre post i j hij
  change B * w.val = ε • (v.val * B) at hs'
  have hslide : W.val * A = A * v.val := by
    rw [hWval, smul_mul_assoc, hs, smul_smul, he, one_smul]
  have hslide' : v.val * B = B * W.val := by
    symm
    rw [hWval, mul_smul_comm, hs', smul_smul, he, one_smul]
  obtain ⟨U, Rright, Rleft, hU, hr, hl⟩ :=
    probeMixedCorner_remainders D Sc a pre post i j hij hu
  exact cyclotomicWordEntry_distinct_isUnit_twoRemainders D Sc a s t
    (probeMixedCross D Sc pre post i j) (probeMixedCross D Sc pre post j i)
    v W U Rright Rleft hW hU hslide hslide' hr hl

end OddMath.QuiverHecke
