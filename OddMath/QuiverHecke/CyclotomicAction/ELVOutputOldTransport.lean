/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVOutputBalancedComparison
import OddMath.QuiverHecke.CyclotomicAction.ELVQDescent

/-!
# Output old action and the chronological short span

The relative-coset stability needed for `DeformedMackeyBoundary.md` (2).
Arbitrary full-ELV output old arrows preserve the chronological short span.
By its exact kernel identification, equal long extractions remain equal after
old output endomorphisms. Both generator types transport across the bare long chain with explicit signs
and sharp relative-short errors. Relative composition and PBW spanning extend
this to arbitrary scalar old arrows; full coefficient-parity cancellation then
proves transport for arbitrary full ELV old arrows and endpoints. Bare-long
rows descend to old quotient arrows.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- Output old arrows preserve the relative chronological short span, with full
ELV coefficients and arbitrary source and output words. -/
theorem act_appendInsert_chronologicalShortSpan (i : I) (v t w : List I)
    (g : hom D Sc cutoff t w) :
    (chronologicalShortSpan D Sc cutoff i v t).map
      (act D Sc cutoff i (appendInsert D Sc cutoff i t w g)) ≤
        chronologicalShortSpan D Sc cutoff i v w := by
  rw [Submodule.map_le_iff_le_comap]
  apply Submodule.span_le.mpr
  rintro _ ⟨s, r, h, rfl⟩
  change projection D Sc cutoff i v (w ++ [i])
    ((insert D Sc cutoff i v (s ++ [i]) r ≫
      rightContext D Sc cutoff [i] (i :: s) t h) ≫
      rightContext D Sc cutoff [i] t w g) ∈ chronologicalShortSpan D Sc cutoff i v w
  rw [Category.assoc, ← rightContext_comp]
  exact Submodule.subset_span ⟨s, r, h ≫ g, rfl⟩

/-- Equality of long output coordinates remains equality after an arbitrary
full old output endomorphism. This uses the exact relative kernel, not a bound
on the total crossing length. -/
theorem outputLongExtraction_act_appendInsert_congr (p : ZMod 2) (i : I) (v : List I)
    (g : hom D Sc cutoff v v) {x y : Target D Sc cutoff i v (v ++ [i])}
    (h : outputLongExtraction D Sc cutoff p i v x =
      outputLongExtraction D Sc cutoff p i v y) :
    outputLongExtraction D Sc cutoff p i v
      (act D Sc cutoff i (appendInsert D Sc cutoff i v v g) x) =
    outputLongExtraction D Sc cutoff p i v
      (act D Sc cutoff i (appendInsert D Sc cutoff i v v g) y) := by
  have hk : x - y ∈ chronologicalShortSpan D Sc cutoff i v v := by
    rw [← ker_outputLongExtraction_eq_chronologicalShortSpan D Sc cutoff p i v]
    change outputLongExtraction D Sc cutoff p i v (x - y) = 0
    rw [map_sub, h, sub_self]
  have hm := act_appendInsert_chronologicalShortSpan D Sc cutoff i v v v g
    (Submodule.mem_map_of_mem hk)
  rw [← ker_outputLongExtraction_eq_chronologicalShortSpan D Sc cutoff p i v] at hm
  change outputLongExtraction D Sc cutoff p i v
    (act D Sc cutoff i (appendInsert D Sc cutoff i v v g) (x - y)) = 0 at hm
  rwa [map_sub, map_sub, sub_eq_zero] at hm

end OddMath.QuiverHecke.ELVOld

noncomputable section
open CategoryTheory StringDiagrams MonoidalCategory
namespace OddMath.QuiverHecke.OutputOldCrossTransport
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k)

def run (p : ℕ) : List I → List PG
  | [] => []
  | _ :: v => .cross p :: run (p+1) v

private theorem run_count (p : ℕ) (v : List I) : crossCount (run p v) = v.length := by
  induction v generalizing p with
  | nil => rfl
  | cons a v ih =>
    change 1 + crossCount (run (p+1) v) = v.length + 1
    rw [ih, Nat.add_comm]

private theorem run_chain (l r : List I) (i : I) (v : List I) :
    SChain (l ++ i :: v ++ r) (pl (l ++ i :: v ++ r) (run l.length v)) (l ++ v ++ i :: r) := by
  induction v generalizing l with
  | nil => simp [run]
  | cons a v ih =>
    have hc : SChain (l ++ i :: (a :: v) ++ r)
        (pl (l ++ i :: (a :: v) ++ r) [.cross l.length])
        ((l ++ [a]) ++ i :: v ++ r) := by
      simpa [List.append_assoc] using sChain_crossAt l (v ++ r) i a
    have h := sChain_append_of hc (ih (l ++ [a]))
    simpa [run, List.append_assoc] using h

private theorem run_fits (l : List I) (i : I) (v r : List I) :
    Fits (l ++ i :: v ++ r).length (run l.length v) := by
  induction v generalizing l with
  | nil => intro g hg; simp [run] at hg
  | cons a v ih =>
    intro g hg
    simp only [run, List.mem_cons] at hg
    rcases hg with rfl | hg
    · simp [PG.pos, PG.width]
    · have h := ih (l ++ [a]) g (by simpa using hg)
      simpa [List.length_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

private theorem run_parity (l r : List I) (i : I) (v : List I) :
    chainParity D (l ++ i :: v ++ r) (run l.length v) =
      D.parity i * wordSumParity D v := by
  induction v generalizing l with
  | nil => simp [run, wordSumParity]
  | cons a v ih =>
    simp only [run, chainParity_cons]
    have ha : (PG.cross l.length).act (l ++ i :: (a :: v) ++ r) =
        (l ++ [a]) ++ i :: v ++ r := by simp [PG.act, List.append_assoc]
    rw [ha]
    have hp : (PG.cross l.length).par D (l ++ i :: (a :: v) ++ r) =
        D.parity i * D.parity a := by simp [PG.par]
    rw [hp]
    have he : l.length + 1 = (l ++ [a]).length := by simp
    rw [he, ih]
    simp [wordSumParity, mul_add]

private theorem run_shift (p q : ℕ) (v : List I) :
    (run q v).map (PG.shift p) = run (p+q) v := by
  induction v generalizing q with
  | nil => rfl
  | cons a v ih => simp [run, ih, Nat.add_assoc]

private theorem block_swap {s s' t t' : List I} (Q R : List PG)
    (hQ : SChain s (pl s Q) s') (hR : SChain t (pl t R) t')
    (fQ : Fits s.length Q) (fR : Fits t.length R)
    (hlen : s.length = s'.length)
    (h : SChain (s ++ t) (pl (s ++ t) (Q ++ R.map (PG.shift s.length))) (s' ++ t'))
    (h' : SChain (s ++ t) (pl (s ++ t) (R.map (PG.shift s.length) ++ Q)) (s' ++ t')) :
    cl D Sc _ _ (Q ++ R.map (PG.shift s.length)) h =
      SKM.zsign k (chainParity D s Q * chainParity D t R) •
        cl D Sc _ _ (R.map (PG.shift s.length) ++ Q) h' := by
  have he := MonoidalSupercategory.super_interchange (R := k)
    (cl_mem_chainParity D Sc Q hQ fQ) (cl_mem_chainParity D Sc R hR fR)
  rw [cl_whiskerRight D Sc Q hQ t fQ, cl_whiskerLeft,
    cl_whiskerLeft, cl_whiskerRight D Sc Q hQ t' fQ] at he
  erw [cl_comp, cl_comp] at he
  erw [Supercategory.koszulSign_smul (R := k)] at he
  change cl D Sc (s ++ t) (s' ++ t') (Q ++ R.map (PG.shift s'.length)) _ =
    Supercategory.sign k (chainParity D s Q * chainParity D t R) •
      cl D Sc (s ++ t) (s' ++ t') (R.map (PG.shift s.length) ++ Q) _ at he
  simpa only [hlen, sign_eq_zsign] using he

private theorem sweep_left (i a b : I) (l r : List I)
    (h : SChain ((i :: l) ++ a :: b :: r)
      (pl ((i :: l) ++ a :: b :: r) (run 0 l ++ [.cross (l.length+1)]))
      ((l ++ [i]) ++ b :: a :: r))
    (h' : SChain ((i :: l) ++ a :: b :: r)
      (pl ((i :: l) ++ a :: b :: r) ([.cross (l.length+1)] ++ run 0 l))
      ((l ++ [i]) ++ b :: a :: r)) :
    cl D Sc _ _ (run 0 l ++ [.cross (l.length+1)]) h =
      SKM.zsign k ((D.parity i * wordSumParity D l) * (D.parity a * D.parity b)) •
        cl D Sc _ _ ([.cross (l.length+1)] ++ run 0 l) h' := by
  have hQ : SChain (i :: l) (pl (i :: l) (run 0 l)) (l ++ [i]) := by
    simpa using run_chain [] [] i l
  have fQ : Fits (i :: l).length (run 0 l) := by simpa using run_fits [] i l []
  have hR : SChain (a :: b :: r) (pl (a :: b :: r) [.cross 0]) (b :: a :: r) := by
    simpa using sChain_crossAt [] r a b
  have fR : Fits (a :: b :: r).length [.cross 0] := by
    intro g hg; simp at hg; subst g; simp [PG.pos, PG.width]
  have he := block_swap D Sc (run 0 l) [.cross 0] hQ hR fQ fR (by simp)
  have hp : chainParity D (i :: l) (run 0 l) = D.parity i * wordSumParity D l := by
    simpa using run_parity D [] [] i l
  simpa only [List.map_cons, List.map_nil, PG.shift, Nat.add_zero, List.length_cons,
    hp, chainParity_cons, chainParity_nil, PG.par, List.getElem?_cons_zero,
    List.getElem?_cons_succ, zero_add, add_zero] using he
    (by simpa using h) (by simpa using h')

private theorem sweep_right (i a b : I) (l r : List I)
    (h : SChain ((l ++ [a,b]) ++ i :: r)
      (pl ((l ++ [a,b]) ++ i :: r) (run (l.length+2) r ++ [.cross l.length]))
      ((l ++ [b,a]) ++ (r ++ [i])))
    (h' : SChain ((l ++ [a,b]) ++ i :: r)
      (pl ((l ++ [a,b]) ++ i :: r) ([.cross l.length] ++ run (l.length+2) r))
      ((l ++ [b,a]) ++ (r ++ [i]))) :
    cl D Sc _ _ (run (l.length+2) r ++ [.cross l.length]) h =
      SKM.zsign k ((D.parity a * D.parity b) * (D.parity i * wordSumParity D r)) •
        cl D Sc _ _ ([.cross l.length] ++ run (l.length+2) r) h' := by
  have hQ : SChain (l ++ [a,b]) (pl (l ++ [a,b]) [.cross l.length]) (l ++ [b,a]) := by
    simpa using sChain_crossAt l [] a b
  have fQ : Fits (l ++ [a,b]).length [.cross l.length] := by
    intro g hg; simp at hg; subst g; simp [PG.pos, PG.width]
  have hR : SChain (i :: r) (pl (i :: r) (run 0 r)) (r ++ [i]) := by
    simpa using run_chain [] [] i r
  have fR : Fits (i :: r).length (run 0 r) := by simpa using run_fits [] i r []
  have he := block_swap D Sc [.cross l.length] (run 0 r) hQ hR fQ fR (by simp)
  have hp : chainParity D (i :: r) (run 0 r) = D.parity i * wordSumParity D r := by
    simpa using run_parity D [] [] i r
  have he' : cl D Sc _ _ ([.cross l.length] ++ run (l.length+2) r) h' =
      SKM.zsign k ((D.parity a * D.parity b) * (D.parity i * wordSumParity D r)) •
        cl D Sc _ _ (run (l.length+2) r ++ [.cross l.length]) h := by
    simpa [run_shift, hp, chainParity, PG.par] using he
      (by simpa [run_shift] using h') (by simpa [run_shift] using h)
  exact (eq_zsign_smul_iff _ _ _).mp he'

private theorem run_append (p : ℕ) (v w : List I) :
    run p (v ++ w) = run p v ++ run (p+v.length) w := by
  induction v generalizing p with
  | nil => simp [run]
  | cons a v ih => simp [run, ih, Nat.add_left_comm, Nat.add_comm]

private theorem cl_eq_transport {s s' t t' : List I} (es : s = s') (et : t = t')
    (Q R : List PG) (c : k)
    (hQ : SChain s (pl s Q) t) (hR : SChain s (pl s R) t)
    (hQ' : SChain s' (pl s' Q) t') (hR' : SChain s' (pl s' R) t')
    (he : cl D Sc s t Q hQ = c • cl D Sc s t R hR) :
    cl D Sc s' t' Q hQ' = c • cl D Sc s' t' R hR' := by
  subst s'; subst t'; exact he

private theorem cl_filt_transport {s s' t t' : List I} (es : s = s') (et : t = t')
    (Q R : List PG) (c : k) (n : ℕ)
    (hQ : SChain s (pl s Q) t) (hR : SChain s (pl s R) t)
    (hQ' : SChain s' (pl s' Q) t') (hR' : SChain s' (pl s' R) t')
    (he : cl D Sc s t Q hQ - c • cl D Sc s t R hR ∈ Filt D Sc s t n) :
    cl D Sc s' t' Q hQ' - c • cl D Sc s' t' R hR' ∈ Filt D Sc s' t' n := by
  subst s'; subst t'; exact he

private theorem sweep_right_normalized (i a b : I) (l r : List I)
    (h : SChain (l ++ a :: b :: i :: r)
      (pl (l ++ a :: b :: i :: r) (run (l.length+2) r ++ [.cross l.length]))
      (l ++ b :: a :: (r ++ [i])))
    (h' : SChain (l ++ a :: b :: i :: r)
      (pl (l ++ a :: b :: i :: r) ([.cross l.length] ++ run (l.length+2) r))
      (l ++ b :: a :: (r ++ [i]))) :
    cl D Sc _ _ (run (l.length+2) r ++ [.cross l.length]) h =
      SKM.zsign k ((D.parity a * D.parity b) * (D.parity i * wordSumParity D r)) •
        cl D Sc _ _ ([.cross l.length] ++ run (l.length+2) r) h' := by
  have hs := sweep_right D Sc i a b l r (by simpa using h) (by simpa using h')
  exact cl_eq_transport D Sc (s := (l ++ [a,b]) ++ i :: r)
    (t := (l ++ [b,a]) ++ (r ++ [i]))
    (s' := l ++ a :: b :: i :: r) (t' := l ++ b :: a :: (r ++ [i]))
    (by simp) (by simp) _ _ _ _ _ h h' hs

private theorem sweep_left_normalized (i a b : I) (l r : List I)
    (h : SChain (i :: (l ++ a :: b :: r))
      (pl (i :: (l ++ a :: b :: r)) (run 0 l ++ [.cross (l.length+1)]))
      (l ++ i :: b :: a :: r))
    (h' : SChain (i :: (l ++ a :: b :: r))
      (pl (i :: (l ++ a :: b :: r)) ([.cross (l.length+1)] ++ run 0 l))
      (l ++ i :: b :: a :: r)) :
    cl D Sc _ _ (run 0 l ++ [.cross (l.length+1)]) h =
      SKM.zsign k ((D.parity i * wordSumParity D l) * (D.parity a * D.parity b)) •
        cl D Sc _ _ ([.cross (l.length+1)] ++ run 0 l) h' := by
  have ht := sweep_left D Sc i a b l r (by simpa using h) (by simpa using h')
  exact cl_eq_transport D Sc (s := (i :: l) ++ a :: b :: r)
    (t := (l ++ [i]) ++ b :: a :: r)
    (s' := i :: (l ++ a :: b :: r)) (t' := l ++ i :: b :: a :: r)
    (by simp) (by simp) _ _ _ _ _ h h' ht

private theorem sweep_right_context (i a b : I) (l r : List I)
    (h : SChain (i :: (l ++ a :: b :: r))
      (pl (i :: (l ++ a :: b :: r)) (run 0 (l ++ a :: b :: r) ++ [.cross l.length]))
      (l ++ b :: a :: (r ++ [i])))
    (hA : SChain (i :: (l ++ a :: b :: r))
      (pl (i :: (l ++ a :: b :: r)) (run 0 l ++ [.cross l.length, .cross (l.length+1), .cross l.length] ++ run (l.length+2) r))
      (l ++ b :: a :: (r ++ [i]))) :
    cl D Sc _ _ (run 0 (l ++ a :: b :: r) ++ [.cross l.length]) h =
      SKM.zsign k ((D.parity a * D.parity b) * (D.parity i * wordSumParity D r)) •
      cl D Sc _ _ ((run 0 l) ++ [.cross l.length, .cross (l.length+1), .cross l.length] ++ (run (l.length+2) r)) hA := by
  let Q := run 0 l
  let R := run (l.length+2) r
  let j := l.length
  have hR : SChain (l ++ b :: a :: i :: r)
      (pl (l ++ b :: a :: i :: r) R) (l ++ b :: a :: (r ++ [i])) := by
    simpa [R, List.append_assoc] using run_chain (l ++ [b,a]) [] i r
  have hP : SChain (i :: (l ++ a :: b :: r))
      (pl (i :: (l ++ a :: b :: r)) (Q ++ [.cross j, .cross (j+1)]))
      (l ++ a :: b :: i :: r) := by
    simpa [Q, j, run_append, run, List.append_assoc] using run_chain [] r i (l ++ [a,b])
  have hSr : SChain (l ++ a :: b :: i :: r)
      (pl (l ++ a :: b :: i :: r) R) (l ++ a :: b :: (r ++ [i])) := by
    simpa [R, List.append_assoc] using run_chain (l ++ [a,b]) [] i r
  have hSc : SChain (l ++ a :: b :: (r ++ [i]))
      (pl (l ++ a :: b :: (r ++ [i])) [.cross j]) (l ++ b :: a :: (r ++ [i])) := by
    simpa [j] using sChain_crossAt l (r ++ [i]) a b
  have hSc' : SChain (l ++ a :: b :: i :: r)
      (pl (l ++ a :: b :: i :: r) [.cross j]) (l ++ b :: a :: i :: r) := by
    simpa [j] using sChain_crossAt l (i :: r) a b
  have hS₁ := sChain_append_of hSr hSc
  have hS₂ := sChain_append_of hSc' hR
  have hs := sweep_right_normalized D Sc i a b l r (by simpa [R, j] using hS₁)
    (by simpa [R, j] using hS₂)
  have he₁ : cl D Sc _ _ (run 0 (l ++ a :: b :: r) ++ [.cross l.length]) h =
      SKM.zsign k ((D.parity a * D.parity b) * (D.parity i * wordSumParity D r)) •
      cl D Sc _ _ (Q ++ [.cross j, .cross (j+1), .cross j] ++ R) hA := by
    have e := congrArg (fun f => cl D Sc _ _ (Q ++ [.cross j, .cross (j+1)]) hP ≫ f) hs
    rw [Linear.comp_smul, cl_comp, cl_comp] at e
    simpa only [Q, R, j, run_append, run, Nat.zero_add, List.cons_append,
      List.nil_append, List.append_assoc, Nat.add_assoc] using e
  exact he₁

private theorem sweep_left_context (i a b : I) (l r : List I)
    (h' : SChain (i :: (l ++ a :: b :: r))
      (pl (i :: (l ++ a :: b :: r)) ([.cross (l.length+1)] ++ run 0 (l ++ b :: a :: r)))
      (l ++ b :: a :: (r ++ [i])))
    (hB : SChain (i :: (l ++ a :: b :: r))
      (pl (i :: (l ++ a :: b :: r)) (run 0 l ++ [.cross (l.length+1), .cross l.length, .cross (l.length+1)] ++ run (l.length+2) r))
      (l ++ b :: a :: (r ++ [i]))) :
    cl D Sc _ _ ((run 0 l) ++ [.cross (l.length+1), .cross l.length, .cross (l.length+1)] ++ (run (l.length+2) r)) hB =
      SKM.zsign k ((D.parity i * wordSumParity D l) * (D.parity a * D.parity b)) •
      cl D Sc _ _ ([.cross (l.length+1)] ++ run 0 (l ++ b :: a :: r)) h' := by
  let Q := run 0 l
  let R := run (l.length+2) r
  let j := l.length
  have hQ : SChain (i :: (l ++ a :: b :: r))
      (pl (i :: (l ++ a :: b :: r)) Q) (l ++ i :: a :: b :: r) := by
    simpa [Q] using run_chain [] (a :: b :: r) i l
  have hTc : SChain (l ++ i :: a :: b :: r)
      (pl (l ++ i :: a :: b :: r) [.cross (j+1)]) (l ++ i :: b :: a :: r) := by
    simpa [j, List.append_assoc] using sChain_crossAt (l ++ [i]) r a b
  have hTc' : SChain (i :: (l ++ a :: b :: r))
      (pl (i :: (l ++ a :: b :: r)) [.cross (j+1)]) (i :: (l ++ b :: a :: r)) := by
    simpa [j] using sChain_crossAt (i :: l) r a b
  have hQt : SChain (i :: (l ++ b :: a :: r))
      (pl (i :: (l ++ b :: a :: r)) Q) (l ++ i :: b :: a :: r) := by
    simpa [Q] using run_chain [] (b :: a :: r) i l
  have hT₁ := sChain_append_of hQ hTc
  have hT₂ := sChain_append_of hTc' hQt
  have ht := sweep_left_normalized D Sc i a b l r (by simpa [Q, j] using hT₁)
    (by simpa [Q, j] using hT₂)
  have hTail : SChain (l ++ i :: b :: a :: r)
      (pl (l ++ i :: b :: a :: r) ([.cross j, .cross (j+1)] ++ R))
      (l ++ b :: a :: (r ++ [i])) := by
    simpa [R, j, run, Nat.add_assoc] using run_chain l [] i (b :: a :: r)
  have he₂ : cl D Sc _ _ (Q ++ [.cross (j+1), .cross j, .cross (j+1)] ++ R) hB =
      SKM.zsign k ((D.parity i * wordSumParity D l) * (D.parity a * D.parity b)) •
      cl D Sc _ _ ([.cross (l.length+1)] ++ run 0 (l ++ b :: a :: r)) h' := by
    have e := congrArg (fun f => f ≫ cl D Sc _ _ ([.cross j, .cross (j+1)] ++ R) hTail) ht
    rw [Linear.smul_comp, cl_comp, cl_comp] at e
    simpa only [Q, R, j, run_append, run, Nat.zero_add, List.cons_append,
      List.nil_append, List.append_assoc, Nat.add_assoc] using e
  exact he₂

theorem all_length_slide (i a b : I) (l r : List I)
    (h : SChain (i :: (l ++ a :: b :: r))
      (pl (i :: (l ++ a :: b :: r)) (run 0 (l ++ a :: b :: r) ++ [.cross l.length]))
      (l ++ b :: a :: (r ++ [i])))
    (h' : SChain (i :: (l ++ a :: b :: r))
      (pl (i :: (l ++ a :: b :: r)) ([.cross (l.length+1)] ++ run 0 (l ++ b :: a :: r)))
      (l ++ b :: a :: (r ++ [i]))) :
    cl D Sc _ _ (run 0 (l ++ a :: b :: r) ++ [.cross l.length]) h -
      SKM.zsign k (D.parity i * wordSumParity D (l ++ a :: b :: r) *
        D.parity a * D.parity b) •
      cl D Sc _ _ ([.cross (l.length+1)] ++ run 0 (l ++ b :: a :: r)) h' ∈
      Low D Sc _ _ (l ++ a :: b :: r).length := by
  let Q := run 0 l
  let R := run (l.length+2) r
  let j := l.length
  have hQ : SChain (i :: (l ++ a :: b :: r))
      (pl (i :: (l ++ a :: b :: r)) Q) (l ++ i :: a :: b :: r) := by
    simpa [Q] using run_chain [] (a :: b :: r) i l
  have hR : SChain (l ++ b :: a :: i :: r)
      (pl (l ++ b :: a :: i :: r) R) (l ++ b :: a :: (r ++ [i])) := by
    simpa [R, List.append_assoc] using run_chain (l ++ [b,a]) [] i r
  have hM : SChain (l ++ i :: a :: b :: r)
      (pl (l ++ i :: a :: b :: r) [.cross j, .cross (j+1), .cross j])
      (l ++ b :: a :: i :: r) := by
    simp [j, pl, PG.ld, PG.act, Shape.dom, Shape.cod, List.take_append, List.drop_append]
  have hM' : SChain (l ++ i :: a :: b :: r)
      (pl (l ++ i :: a :: b :: r) [.cross (j+1), .cross j, .cross (j+1)])
      (l ++ b :: a :: i :: r) := by
    simp [j, pl, PG.ld, PG.act, Shape.dom, Shape.cod, List.take_append, List.drop_append]
  have hA := sChain_append_of (sChain_append_of hQ hM) hR
  have hB := sChain_append_of (sChain_append_of hQ hM') hR
  have hm : cl D Sc _ _ [.cross j, .cross (j+1), .cross j] hM -
      (1 : k) • cl D Sc _ _ [.cross (j+1), .cross j, .cross (j+1)] hM' ∈
      Filt D Sc _ _ 0 := by
    apply cl_filt_transport D Sc (s := l ++ [i,a,b] ++ r) (t := l ++ [b,a,i] ++ r)
      (by simp) (by simp) _ _ _ _ (by simpa [j] using hM) (by simpa [j] using hM')
    simpa only [one_smul] using braid_mem D Sc l r i a b _ _
  have hc := move_ctx D Sc Q _ _ R (1 : k) hQ hR hM hM' hm hA hB
  have hlow : cl D Sc _ _ (Q ++ [.cross j, .cross (j+1), .cross j] ++ R) hA -
      cl D Sc _ _ (Q ++ [.cross (j+1), .cross j, .cross (j+1)] ++ R) hB ∈
      Low D Sc _ _ (l ++ a :: b :: r).length := by
    apply filt_le_low D Sc (m := l.length + r.length) (by simp)
    simpa only [Q, R, run_count, Nat.add_zero, one_smul] using hc
  have he₁ := sweep_right_context D Sc i a b l r h hA
  have he₂ := sweep_left_context D Sc i a b l r h' hB
  rw [he₁]
  have hz :
      SKM.zsign k ((D.parity a * D.parity b) * (D.parity i * wordSumParity D r)) *
      SKM.zsign k ((D.parity i * wordSumParity D l) * (D.parity a * D.parity b)) =
      SKM.zsign k (D.parity i * wordSumParity D (l ++ a :: b :: r) *
        D.parity a * D.parity b) := by
    rw [← zsign_add_aux]
    congr 1
    simp only [wordSumParity, List.map_append, List.map_cons, List.sum_append,
      List.sum_cons]
    have ha := SKM.zmod2_mul_self (D.parity a)
    have hb := SKM.zmod2_mul_self (D.parity b)
    have htwo : (2 : ZMod 2) = 0 := by decide
    linear_combination -D.parity i * D.parity b * ha -
      D.parity i * D.parity a * hb - D.parity i * D.parity a * D.parity b * htwo
  rw [← hz, mul_smul, ← he₂, ← smul_sub]
  exact Submodule.smul_mem _ _ hlow

theorem run_eq_leading (l v : List I) :
    cw (leadingMoveWord l v) = run l.length v := by
  induction v generalizing l with
  | nil => rfl
  | cons a v ih =>
    rw [leadingMoveWord, cw_append, ih]
    simp [cw, run]

end OddMath.QuiverHecke.OutputOldCrossTransport

open scoped TensorProduct
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- Arbitrary exterior coefficients lift relative scalar shortness into the
chronological short quotient span. -/
theorem tmul_shortSpan (i : I) (v t : List I)
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff)
    {f : (pres D Sc).obj (ob D (i :: v)) ⟶ (pres D Sc).obj (ob D (t ++ [i]))}
    (hf : f ∈ SmallerTailNormalization.shortSpan D Sc i v (t ++ [i])) :
    projection D Sc cutoff i v (t ++ [i]) (a ⊗ₜ[k] f) ∈
      chronologicalShortSpan D Sc cutoff i v t := by
  let L : ((pres D Sc).obj (ob D (i :: v)) ⟶
      (pres D Sc).obj (ob D (t ++ [i]))) →ₗ[k] Target D Sc cutoff i v (t ++ [i]) :=
    (projection D Sc cutoff i v (t ++ [i])).comp
      (TensorProduct.mk k (SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff)
        ((pres D Sc).obj (ob D (i :: v)) ⟶ (pres D Sc).obj (ob D (t ++ [i]))) a)
  change L f ∈ chronologicalShortSpan D Sc cutoff i v t
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨x, hx, rfl⟩ := hf
    rw [prependBasis_apply]
    change projection D Sc cutoff i v (t ++ [i])
      (a ⊗ₜ[k] prependElt D Sc x) ∈ chronologicalShortSpan D Sc cutoff i v t
    erw [← prepend_insert_twisted_coefficient D Sc cutoff x a]
    exact prepend_short_mem D Sc cutoff i v t x hx _
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add f g _ _ hf hg =>
    rw [map_add]
    exact Submodule.add_mem _ hf hg
  | smul c f _ hf =>
    rw [map_smul]
    exact Submodule.smul_mem _ c hf

/-- The actual old crossing slides across the bare long chain with its
specified super sign, modulo the exact chronological short span. Coefficients
are arbitrary in the full ELV coefficient algebra. -/
theorem bareLong_cross_chronologicalShort (i a b : I) (l r : List I)
    (c : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff)
    (h : SChain (i :: (l ++ a :: b :: r))
      (pl (i :: (l ++ a :: b :: r))
        (cw (leadingMoveWord [] (l ++ a :: b :: r)) ++ [.cross l.length]))
      ((l ++ b :: a :: r) ++ [i]))
    (h' : SChain (i :: (l ++ a :: b :: r))
      (pl (i :: (l ++ a :: b :: r))
        ([.cross (l.length+1)] ++ cw (leadingMoveWord [] (l ++ b :: a :: r))))
      ((l ++ b :: a :: r) ++ [i])) :
    projection D Sc cutoff i (l ++ a :: b :: r) ((l ++ b :: a :: r) ++ [i])
      (c ⊗ₜ[k] (cl D Sc _ _
        (cw (leadingMoveWord [] (l ++ a :: b :: r)) ++ [.cross l.length]) h -
        SKM.zsign k (D.parity i * wordSumParity D (l ++ a :: b :: r) *
          D.parity a * D.parity b) •
        cl D Sc _ _
          ([.cross (l.length+1)] ++ cw (leadingMoveWord [] (l ++ b :: a :: r))) h')) ∈
      chronologicalShortSpan D Sc cutoff i (l ++ a :: b :: r) (l ++ b :: a :: r) := by
  apply tmul_shortSpan D Sc cutoff
  apply SmallerTailNormalization.low_le_shortSpan D Sc
  have transport {s t t' : List I} (ht : t = t')
      (Q R : List PG) (z : k) (n : ℕ)
      (hQ : SChain s (pl s Q) t) (hR : SChain s (pl s R) t)
      (hQ' : SChain s (pl s Q) t') (hR' : SChain s (pl s R) t')
      (he : cl D Sc s t Q hQ - z • cl D Sc s t R hR ∈ Low D Sc s t n) :
      cl D Sc s t' Q hQ' - z • cl D Sc s t' R hR' ∈ Low D Sc s t' n := by
    subst t'; exact he
  apply transport (t := l ++ b :: a :: (r ++ [i])) (by simp) _ _ _ _
    (by simpa only [List.append_assoc, List.cons_append] using h)
    (by simpa only [List.append_assoc, List.cons_append] using h')
  have hh := OutputOldCrossTransport.all_length_slide D Sc i a b l r
    (by simpa only [OutputOldCrossTransport.run_eq_leading, List.length_nil,
      List.append_assoc, List.cons_append] using h)
    (by simpa only [OutputOldCrossTransport.run_eq_leading, List.length_nil,
      List.append_assoc, List.cons_append] using h')
  simpa only [OutputOldCrossTransport.run_eq_leading, List.length_nil,
    List.append_assoc, List.cons_append] using hh

end OddMath.QuiverHecke.ELVOld

noncomputable section
open CategoryTheory StringDiagrams Categorification.TypeA
namespace OddMath.QuiverHecke
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k] (D : SKM.Datum I X)

private theorem sourceDotPosition_leadingMoveWord_before (q s : List I) (p : ℕ) (hp : p < q.length) :
    sourceDotPosition (leadingMoveWord q s) p = p := by
  induction s generalizing q with
  | nil => rfl
  | cons j s ih =>
    rw [leadingMoveWord, sourceDotPosition_append, ih (q ++ [j]) (by simp; omega)]
    simp [sourceDotPosition, swapNat, show p ≠ q.length by omega,
      show p ≠ q.length + 1 by omega]

private theorem sourceDotSign_leadingMoveWord_before (i a : I) (q s : List I) (p : ℕ)
    (hp : p < q.length) (ha : q[p]? = some a) :
    sourceDotSign D (k := k) (q ++ i :: s) (leadingMoveWord q s) p =
      SKM.zsign k (D.parity i * wordSumParity D s * D.parity a) := by
  induction s generalizing q with
  | nil => simp [leadingMoveWord, sourceDotSign, wordSumParity, SKM.zsign]
  | cons j s ih =>
    rw [leadingMoveWord, sourceDotSign_append,
      sourceDotPosition_leadingMoveWord_before _ _ _ (by simp; omega)]
    have ht : tgt (q ++ i :: j :: s) (cw [q.length]) = (q ++ [j]) ++ i :: s := by
      simp [cw, PG.act, List.append_assoc]
    rw [ht, ih (q ++ [j]) (by simp; omega) (by simpa [List.getElem?_append_left hp])]
    have hd : (PG.dot p).par D (q ++ i :: j :: s) = D.parity a := by
      simp [PG.par, List.getElem?_append_left hp, ha]
    simp [sourceDotSign, crossDotExponent, show p ≠ q.length by omega,
      show p ≠ q.length + 1 by omega, PG.par, List.getElem?_append_left hp, ha,
      wordSumParity, mul_add, zsign_add_aux, mul_comm]

theorem sourceDotPosition_leadingMoveWord_old (q l r : List I) (a : I) :
    sourceDotPosition (leadingMoveWord q (l ++ a :: r)) (q.length + l.length) =
      q.length + l.length + 1 := by
  induction l generalizing q with
  | nil =>
    rw [List.nil_append, leadingMoveWord, sourceDotPosition_append,
      sourceDotPosition_leadingMoveWord_before _ _ _ (by simp)]
    simp [sourceDotPosition, swapNat]
  | cons b l ih =>
    rw [List.cons_append, leadingMoveWord, sourceDotPosition_append]
    have he : q.length + (b :: l).length = (q ++ [b]).length + l.length := by simp; omega
    rw [he, ih]
    simp only [sourceDotPosition, swapNat]
    split_ifs <;> simp_all only [List.length_append, List.length_cons] <;> omega

theorem sourceDotSign_leadingMoveWord_old (i a : I) (q l r : List I) :
    sourceDotSign D (k := k) (q ++ i :: (l ++ a :: r))
      (leadingMoveWord q (l ++ a :: r)) (q.length + l.length) =
      SKM.zsign k (D.parity i * wordSumParity D (l ++ a :: r) * D.parity a) := by
  induction l generalizing q with
  | nil =>
    simp only [List.nil_append, List.length_nil, Nat.add_zero]
    rw [leadingMoveWord, sourceDotSign_append,
      sourceDotPosition_leadingMoveWord_before _ _ _ (by simp)]
    have ht : tgt (q ++ i :: a :: r) (cw [q.length]) = (q ++ [a]) ++ i :: r := by
      simp [cw, PG.act, List.append_assoc]
    rw [ht, sourceDotSign_leadingMoveWord_before D i a (q ++ [a]) r q.length
      (by simp) (by simp)]
    have hs : sourceDotSign D (k := k) (q ++ i :: a :: r) [q.length] q.length =
        SKM.zsign k (D.parity i * D.parity a) := by
      simp [sourceDotSign, crossDotExponent, PG.par]
    rw [hs]
    rw [← zsign_add_aux]
    congr 1
    simp only [wordSumParity, List.map_cons, List.sum_cons]
    have ha := SKM.zmod2_mul_self (D.parity a)
    linear_combination -D.parity i * ha
  | cons b l ih =>
    rw [List.cons_append, leadingMoveWord, sourceDotSign_append]
    have he : q.length + (b :: l).length = (q ++ [b]).length + l.length := by simp; omega
    rw [he, sourceDotPosition_leadingMoveWord_old]
    have ht : tgt (q ++ i :: b :: (l ++ a :: r)) (cw [q.length]) =
        (q ++ [b]) ++ i :: (l ++ a :: r) := by simp [cw, PG.act, List.append_assoc]
    rw [ht, ih]
    have hd : (PG.dot ((q ++ [b]).length + l.length + 1)).par D
        (q ++ i :: b :: (l ++ a :: r)) = D.parity a := by
      have hh : (q ++ [b]).length + l.length + 1 = (q ++ [i,b] ++ l).length := by simp; omega
      rw [hh]
      have hw : q ++ i :: b :: (l ++ a :: r) = (q ++ [i,b] ++ l) ++ a :: r := by simp
      rw [hw]
      simp [PG.par]
    have hn : (q ++ [b]).length + l.length + 1 ≠ q.length := by simp; omega
    have hn' : (q ++ [b]).length + l.length + 1 ≠ q.length + 1 := by simp; omega
    simp only [sourceDotSign, crossDotExponent, hn, hn', false_or, ite_false, cw, List.reverse_nil, List.map_nil, tgt_nil, hd, mul_one]
    have hc : (PG.cross q.length).par D (q ++ i :: b :: (l ++ a :: r)) =
        D.parity i * D.parity b := by simp [PG.par]
    rw [hc, ← zsign_add_aux]
    congr 1
    simp [wordSumParity, mul_add, add_mul]
    ring

private theorem leadingMoveWord_length_oldDot (q s : List I) :
    (leadingMoveWord q s).length = s.length := by
  induction s generalizing q with
  | nil => rfl
  | cons a s ih => simp [leadingMoveWord, ih]

variable (Sc : SKM.Scalars D k)

/-- The old output dot crosses the bare long shuffle, with sharp old-length error. -/
theorem bareLong_dot_low (i a : I) (l r : List I)
    (h : SChain (i :: (l ++ a :: r))
      (pl (i :: (l ++ a :: r))
        (cw (leadingMoveWord [] (l ++ a :: r)) ++ [.dot l.length]))
      ((l ++ a :: r) ++ [i]))
    (h' : SChain (i :: (l ++ a :: r))
      (pl (i :: (l ++ a :: r))
        ([.dot (l.length+1)] ++ cw (leadingMoveWord [] (l ++ a :: r))))
      ((l ++ a :: r) ++ [i])) :
    cl D Sc _ _ (cw (leadingMoveWord [] (l ++ a :: r)) ++ [.dot l.length]) h -
      SKM.zsign k (D.parity i * wordSumParity D (l ++ a :: r) * D.parity a) •
        cl D Sc _ _ ([.dot (l.length+1)] ++ cw (leadingMoveWord [] (l ++ a :: r))) h' ∈
      Low D Sc _ _ (l ++ a :: r).length := by
  have hp : sourceDotPosition (leadingMoveWord [] (l ++ a :: r)) l.length =
      l.length + 1 := by simpa using sourceDotPosition_leadingMoveWord_old [] l r a
  have hs : sourceDotSign D (k := k) (i :: (l ++ a :: r))
      (leadingMoveWord [] (l ++ a :: r)) l.length =
      SKM.zsign k (D.parity i * wordSumParity D (l ++ a :: r) * D.parity a) := by
    simpa using sourceDotSign_leadingMoveWord_old D i a [] l r
  have hv : ValidWord ((i :: (l ++ a :: r)).length)
      (leadingMoveWord [] (l ++ a :: r)) := by
    simpa using leadingMoveWord_valid ([] : List I) (l ++ a :: r)
  have hh := dots_down_signed D Sc (t' := (l ++ a :: r) ++ [i]) [] rfl
    (leadingMoveWord [] (l ++ a :: r)) hv
    [l.length] (by intro p hp; simp only [List.mem_singleton] at hp; subst p; simp) []
    (by simpa using h)
  simp only [List.nil_append, List.append_nil, List.map_cons, List.map_nil,
    hp, sourceDotsSign, List.prod_cons, List.prod_nil, mul_one, tgt_nil, hs,
    crossCount_nil, Nat.zero_add, Nat.add_zero, leadingMoveWord_length_oldDot] at hh
  obtain ⟨_, hh⟩ := hh
  exact hh

open scoped TensorProduct
namespace ELVOld
variable (cutoff : I → ℕ)

/-- The generator slide modulo the exact chronological short span, with arbitrary
full exterior coefficients; no restriction on colours, parity, or old length. -/
theorem bareLong_dot_chronologicalShort (i a : I) (l r : List I)
    (c : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff)
    (h : SChain (i :: (l ++ a :: r))
      (pl (i :: (l ++ a :: r))
        (cw (leadingMoveWord [] (l ++ a :: r)) ++ [.dot l.length]))
      ((l ++ a :: r) ++ [i]))
    (h' : SChain (i :: (l ++ a :: r))
      (pl (i :: (l ++ a :: r))
        ([.dot (l.length+1)] ++ cw (leadingMoveWord [] (l ++ a :: r))))
      ((l ++ a :: r) ++ [i])) :
    projection D Sc cutoff i (l ++ a :: r) ((l ++ a :: r) ++ [i])
      (c ⊗ₜ[k] (cl D Sc _ _
        (cw (leadingMoveWord [] (l ++ a :: r)) ++ [.dot l.length]) h -
        SKM.zsign k (D.parity i * wordSumParity D (l ++ a :: r) * D.parity a) •
        cl D Sc _ _ ([.dot (l.length+1)] ++ cw (leadingMoveWord [] (l ++ a :: r))) h')) ∈
      chronologicalShortSpan D Sc cutoff i (l ++ a :: r) (l ++ a :: r) := by
  apply tmul_shortSpan D Sc cutoff
  apply SmallerTailNormalization.low_le_shortSpan D Sc
  exact bareLong_dot_low D Sc i a l r h h'

theorem bareLong_dot_chains (i a : I) (l r : List I) :
    SChain (i :: (l ++ a :: r))
      (pl (i :: (l ++ a :: r))
        (cw (leadingMoveWord [] (l ++ a :: r)) ++ [.dot l.length]))
      ((l ++ a :: r) ++ [i]) ∧
    SChain (i :: (l ++ a :: r))
      (pl (i :: (l ++ a :: r))
        ([.dot (l.length+1)] ++ cw (leadingMoveWord [] (l ++ a :: r))))
      ((l ++ a :: r) ++ [i]) := by
  have hU : SChain (i :: (l ++ a :: r))
      (pl (i :: (l ++ a :: r)) (cw (leadingMoveWord [] (l ++ a :: r))))
      ((l ++ a :: r) ++ [i]) := by
    simpa only [List.nil_append] using leadingMoveWord_sChain i [] (l ++ a :: r)
  exact ⟨sChain_append_of hU (sChain_dotAny _ _),
    sChain_append_of (sChain_dotAny _ _) hU⟩

end ELVOld
end OddMath.QuiverHecke

noncomputable section
open CategoryTheory StringDiagrams MonoidalCategory Categorification.TypeA
namespace OddMath.QuiverHecke.SmallerTailNormalization
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k)

private theorem prependTail_short_factor (i : I) (v t : List I)
    (x : PrependIdx i v (t ++ [i]))
    (hx : x.1.2.2.2 ≠ longPrependShuffle v.length) :
    ∃ (s : List I) (_hs : x.oldTarget = s ++ [i])
      (f : (pres D Sc).obj (ob D (i :: s)) ⟶ (pres D Sc).obj (ob D t)),
      HEq (ELVOld.prependTail D Sc x) (f ▷ (pres D Sc).obj (ob D [i])) := by
  have hv : 0 < v.length := by
    cases v with
    | nil =>
      apply False.elim
      apply hx
      apply Subtype.ext
      apply Equiv.ext
      intro z
      apply Fin.ext
      have h₁ := (x.1.2.2.2.1 z).isLt
      have h₂ := ((longPrependShuffle (([] : List I).length)).1 z).isLt
      simp only [List.length_nil] at h₁ h₂ ⊢
      omega
    | cons a v => simp
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hv)
  have hlen : x.oldTarget.length = n + 1 := by
    simp [PrependIdx.oldTarget, hn]
  obtain ⟨s, j, hs⟩ : ∃ s j, x.oldTarget = s ++ [j] := by
    generalize x.oldTarget = q at hlen ⊢
    induction q using List.reverseRecOn with
    | nil => simp at hlen
    | append_singleton q j ih => exact ⟨q, j, rfl⟩
  have hsl : s.length = n := by rw [hs] at hlen; simp only [List.length_append,
    List.length_singleton] at hlen; omega
  have hf : Fits (i :: s).length (cw (canWord (v.length + 1) x.1.2.2.2.1⁻¹)) := by
    apply fits_cw
    intro b hb
    have hb' : b < n := by
      have aux (m : ℕ) (u : PrependShuffle m) (hu : u ≠ longPrependShuffle m)
          (hm : m = n + 1) : ∀ b ∈ canWord (m + 1) u.1⁻¹, b < n := by
        subst m
        exact canWord_prependShort_lt n u hu
      exact aux v.length x.1.2.2.2 hx hn b hb
    simp only [List.length_cons, hsl]
    omega
  have he := x.moving_target
  rw [hs] at he
  change tgt ((i :: s) ++ [j]) _ = _ at he
  rw [tgt_append_right [j] hf] at he
  have hj : j = i := by
    have hh := congrArg List.getLast? he
    simpa using hh
  subst j
  have hfull : Fits (i :: s).length
      (((List.replicate x.1.1 0).map PG.dot) ++
        cw (canWord (v.length + 1) x.1.2.2.2.1⁻¹)) := by
    intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hg
      have hb0 := (List.mem_replicate.mp hb).2
      subst b
      simp [PG.pos, PG.width]
    · exact hf g hg
  refine ⟨s, hs, cl D Sc _ _ (((List.replicate x.1.1 0).map PG.dot) ++
      cw (canWord (v.length + 1) x.1.2.2.2.1⁻¹)) ?_, ?_⟩
  · have ht := x.moving_target
    rw [hs] at ht
    change tgt ((i :: s) ++ [i]) _ = _ at ht
    rw [tgt_append_right [i] hf] at ht
    have ht' := List.append_cancel_right ht
    have hd := sChain_pl (i :: s)
      (((List.replicate x.1.1 0).map PG.dot) ++
        cw (canWord (v.length + 1) x.1.2.2.2.1⁻¹))
    simpa only [tgt_append, tgt_map_dot, ht'] using hd
  · rw [cl_whiskerRight D Sc _ _ [i] hfull]
    unfold ELVOld.prependTail
    have aux {q q' t : List I} (e : q = q') (gs : List PG)
        (h : SChain q (pl q gs) t) (h' : SChain q' (pl q' gs) t) :
        HEq (cl D Sc q t gs h) (cl D Sc q' t gs h') := by
      subst q'; rfl
    exact aux (congrArg (List.cons i) hs) _ _ _

theorem short_comp_old {i : I} {v t w : List I}
    (f : (pres D Sc).obj (ob D (i :: v)) ⟶ (pres D Sc).obj (ob D (t ++ [i])))
    (g : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D w))
    (hf : f ∈ shortSpan D Sc i v (t ++ [i])) :
    f ≫ (g ▷ (pres D Sc).obj (ob D [i])) ∈ shortSpan D Sc i v (w ++ [i]) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨x, hx, rfl⟩ := hf
    rw [prependBasis_apply, ELVOld.prependElt_insert_tail]
    obtain ⟨s, hs, h, hh⟩ := prependTail_short_factor D Sc i v t x hx
    have aux {q : List I} (e : q = s ++ [i])
        (r : (pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D q))
        (z : (pres D Sc).obj (ob D (i :: q)) ⟶ (pres D Sc).obj (ob D (t ++ [i])))
        (hz : HEq z (h ▷ (pres D Sc).obj (ob D [i]))) :
        (ELVOld.affineInsert D Sc i v q r ≫ z) ≫
          (g ▷ (pres D Sc).obj (ob D [i])) ∈ shortSpan D Sc i v (w ++ [i]) := by
      subst q
      cases hz
      erw [Category.assoc, ← MonoidalSupercategory.comp_whiskerRight (R := k)]
      exact chronological_scalar_short D Sc r (h ≫ g)
    exact aux hs x.old.nf _ hh
  | zero =>
    erw [Limits.zero_comp]
    exact Submodule.zero_mem _
  | add f h _ _ hf hh =>
    erw [Preadditive.add_comp]
    exact Submodule.add_mem _ hf hh
  | smul a f _ hf =>
    erw [Linear.smul_comp]
    exact Submodule.smul_mem _ a hf

end OddMath.QuiverHecke.SmallerTailNormalization

namespace OddMath.QuiverHecke.OutputOldComposite
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k)
local notation "O[" t "]" => Presentation.obj (pres D Sc) (ob D t)
open SmallerTailNormalization Supercategory

def bareU (i : I) (v : List I) : O[i :: v] ⟶ O[v ++ [i]] :=
  cl D Sc _ _ (cw (leadingMoveWord [] v))
    (by simpa only [List.nil_append] using leadingMoveWord_sChain i [] v)

def error (i : I) (v w : List I) : (O[v] ⟶ O[w]) →ₗ[k] (O[i :: v] ⟶ O[w ++ [i]]) where
  toFun g := (bareU D Sc i v ≫ (g ▷ O[[i]]) : O[i :: v] ⟶ O[w ++ [i]]) -
    ((O[[i]] ◁ twist k (D.parity i * wordSumParity D v) g) ≫ bareU D Sc i w :
      O[i :: v] ⟶ O[w ++ [i]])
  map_add' g h := by
    erw [map_add, MonoidalSupercategory.add_whiskerRight (R := k),
      MonoidalSupercategory.whiskerLeft_add (R := k), Preadditive.comp_add,
      Preadditive.add_comp]
    abel
  map_smul' a g := by
    erw [map_smul, MonoidalSupercategory.smul_whiskerRight,
      MonoidalSupercategory.whiskerLeft_smul, Linear.comp_smul, Linear.smul_comp,
      smul_sub]
    rfl

 private theorem error_id (i : I) (v : List I) : error D Sc i v v (𝟙 _) = 0 := by
  change (bareU D Sc i v ≫ ((𝟙 O[v]) ▷ O[[i]]) : O[i :: v] ⟶ O[v ++ [i]]) -
    ((O[[i]] ◁ twist k (D.parity i * wordSumParity D v) (𝟙 O[v])) ≫ bareU D Sc i v :
      O[i :: v] ⟶ O[v ++ [i]]) = 0
  erw [twist_id, MonoidalSupercategory.id_whiskerRight (R := k),
    MonoidalSupercategory.whiskerLeft_id (R := k), Category.comp_id, Category.id_comp, sub_self]

private theorem error_comp_mem (i : I) {v w z : List I}
    (f : O[v] ⟶ O[w]) (g : O[w] ⟶ O[z])
    (hp : wordSumParity D v = wordSumParity D w)
    (hf : error D Sc i v w f ∈ shortSpan D Sc i v (w ++ [i]))
    (hg : error D Sc i w z g ∈ shortSpan D Sc i w (z ++ [i])) :
    error D Sc i v z (f ≫ g) ∈ shortSpan D Sc i v (z ++ [i]) := by
  have h₁ := short_comp_old D Sc _ g hf
  have h₂ := old_comp_short D Sc
    (twist k (D.parity i * wordSumParity D v) f) _ hg
  have he : error D Sc i v z (f ≫ g) =
      (error D Sc i v w f ≫ (g ▷ O[[i]]) : O[i :: v] ⟶ O[z ++ [i]]) +
      ELVOld.affineInsert D Sc i v w (twist k (D.parity i * wordSumParity D v) f) ≫
        error D Sc i w z g := by
    dsimp only [error, ELVOld.affineInsert, LinearMap.coe_mk, AddHom.coe_mk]
    erw [twist_comp, MonoidalSupercategory.comp_whiskerRight (R := k),
      MonoidalSupercategory.whiskerLeft_comp (R := k)]
    rw [hp]
    have aux {A B C E F G : (pres D Sc).Presented}
        (u : A ⟶ B) (u' : C ⟶ E) (u'' : F ⟶ G)
        (f : B ⟶ E) (g : E ⟶ G) (f' : A ⟶ C) (g' : C ⟶ F) :
        u ≫ (f ≫ g) - (f' ≫ g') ≫ u'' =
          (u ≫ f - f' ≫ u') ≫ g + f' ≫ (u' ≫ g - g' ≫ u'') := by
      simp only [Preadditive.sub_comp, Preadditive.comp_sub, Category.assoc]
      abel
    exact aux _ _ _ _ _ _ _
  rw [he]
  exact Submodule.add_mem _ h₁ h₂

private theorem error_cl (i : I) {v w : List I} (gs : List PG)
    (h : SChain v (pl v gs) w) (hf : Fits v.length gs) :
    error D Sc i v w (cl D Sc v w gs h) =
      cl D Sc _ _ (cw (leadingMoveWord [] v) ++ gs)
        (sChain_append_of (by simpa using leadingMoveWord_sChain i [] v)
          (by simpa using sChain_append_one i h hf)) -
      SKM.zsign k (D.parity i * wordSumParity D v * chainParity D v gs) •
        cl D Sc _ _ (gs.map (PG.shift 1) ++ cw (leadingMoveWord [] w))
          (sChain_append_of (by simpa using sChain_shift_one i h)
            (by simpa using leadingMoveWord_sChain i [] w)) := by
  dsimp only [error, LinearMap.coe_mk, AddHom.coe_mk]
  erw [twist_of_mem _ (cl_mem_chainParity D Sc gs h hf),
    MonoidalSupercategory.whiskerLeft_smul (R := k), Linear.smul_comp]
  rw [cl_whiskerRight D Sc gs h [i] hf, cl_whiskerLeft]
  unfold bareU
  erw [cl_comp, cl_comp]
  rw [sign_eq_zsign]
  rfl

private theorem error_dot_mem (i a : I) (l r : List I) :
    error D Sc i (l ++ a :: r) (l ++ a :: r)
      (cl D Sc _ _ [.dot l.length] (sChain_dotAny _ _)) ∈
        shortSpan D Sc i (l ++ a :: r) ((l ++ a :: r) ++ [i]) := by
  rw [error_cl D Sc i _ _ (by intro g hg; simp only [List.mem_singleton] at hg; subst g; simp [PG.pos, PG.width])]
  have hc := ELVOld.bareLong_dot_chains i a l r
  have h := low_le_shortSpan D Sc i (l ++ a :: r) ((l ++ a :: r) ++ [i])
    (bareLong_dot_low D Sc i a l r hc.1 hc.2)
  simpa [PG.shift, chainParity, PG.par, Nat.add_comm] using h

private theorem cross_short (i a b : I) (l r : List I)
    (h : SChain (i :: (l ++ a :: b :: r))
      (pl (i :: (l ++ a :: b :: r))
        (cw (leadingMoveWord [] (l ++ a :: b :: r)) ++ [.cross l.length]))
      ((l ++ b :: a :: r) ++ [i]))
    (h' : SChain (i :: (l ++ a :: b :: r))
      (pl (i :: (l ++ a :: b :: r))
        ([.cross (l.length+1)] ++ cw (leadingMoveWord [] (l ++ b :: a :: r))))
      ((l ++ b :: a :: r) ++ [i]))
    : cl D Sc _ _ (cw (leadingMoveWord [] (l ++ a :: b :: r)) ++ [.cross l.length]) h -
      SKM.zsign k (D.parity i * wordSumParity D (l ++ a :: b :: r) * D.parity a * D.parity b) •
        cl D Sc _ _ ([.cross (l.length+1)] ++ cw (leadingMoveWord [] (l ++ b :: a :: r))) h' ∈
      shortSpan D Sc i (l ++ a :: b :: r) ((l ++ b :: a :: r) ++ [i]) := by
  apply low_le_shortSpan
  have transport {s t t' : List I} (ht : t = t')
      (Q R : List PG) (z : k) (n : ℕ)
      (hQ : SChain s (pl s Q) t) (hR : SChain s (pl s R) t)
      (hQ' : SChain s (pl s Q) t') (hR' : SChain s (pl s R) t')
      (he : cl D Sc s t Q hQ - z • cl D Sc s t R hR ∈ Low D Sc s t n) :
      cl D Sc s t' Q hQ' - z • cl D Sc s t' R hR' ∈ Low D Sc s t' n := by
    subst t'; exact he
  apply transport (t := l ++ b :: a :: (r ++ [i])) (by simp) _ _ _ _
    (by simpa only [List.append_assoc, List.cons_append] using h)
    (by simpa only [List.append_assoc, List.cons_append] using h')
  have hh := OutputOldCrossTransport.all_length_slide D Sc i a b l r
    (by simpa only [OutputOldCrossTransport.run_eq_leading, List.length_nil,
      List.append_assoc, List.cons_append] using h)
    (by simpa only [OutputOldCrossTransport.run_eq_leading, List.length_nil,
      List.append_assoc, List.cons_append] using h')
  simpa only [OutputOldCrossTransport.run_eq_leading, List.length_nil,
    List.append_assoc, List.cons_append] using hh

private theorem error_cross_mem (i a b : I) (l r : List I) :
    error D Sc i (l ++ a :: b :: r) (l ++ b :: a :: r)
      (cl D Sc _ _ [.cross l.length] (by simpa using sChain_crossAt l r a b)) ∈
        shortSpan D Sc i (l ++ a :: b :: r) ((l ++ b :: a :: r) ++ [i]) := by
  rw [error_cl D Sc i _ _ (by intro g hg; simp only [List.mem_singleton] at hg; subst g; simp [PG.pos, PG.width])]
  have hU (s : List I) : SChain (i :: s) (pl (i :: s) (cw (leadingMoveWord [] s))) (s ++ [i]) :=
    by simpa using leadingMoveWord_sChain i [] s
  have hC : SChain (l ++ a :: b :: r) (pl (l ++ a :: b :: r) [.cross l.length]) (l ++ b :: a :: r) :=
    by simpa using sChain_crossAt l r a b
  have hf : Fits (l ++ a :: b :: r).length [.cross l.length] :=
    by intro g hg; simp only [List.mem_singleton] at hg; subst g; simp [PG.pos, PG.width]
  have hc := sChain_append_of (hU (l ++ a :: b :: r)) (sChain_append_one i hC hf)
  have hc' : SChain (i :: (l ++ a :: b :: r))
      (pl (i :: (l ++ a :: b :: r)) ([.cross (l.length+1)] ++ cw (leadingMoveWord [] (l ++ b :: a :: r))))
      ((l ++ b :: a :: r) ++ [i]) := by
    simpa [PG.shift, Nat.add_comm] using sChain_append_of (sChain_shift_one i hC) (hU (l ++ b :: a :: r))
  have h := cross_short D Sc i a b l r hc hc'
  simpa [PG.shift, chainParity, PG.par, Nat.add_comm, mul_assoc] using h

private theorem error_gen_mem (i : I) (g : PG) {v w : List I}
    (h : SChain v (pl v [g]) w) (hf : g.pos + g.width ≤ v.length) :
    error D Sc i v w (cl D Sc v w [g] h) ∈ shortSpan D Sc i v (w ++ [i]) := by
  cases g with
  | dot p =>
    have hp : p < v.length := by simpa [PG.pos, PG.width] using hf
    obtain ⟨l, a, r, hv, hl⟩ : ∃ l a r, v = l ++ a :: r ∧ l.length = p := by
      cases hd : v.drop p with
      | nil => have hh : (v.drop p).length = v.length - p := List.length_drop; rw [hd] at hh; simp at hh; omega
      | cons a r =>
        exact ⟨v.take p, a, r, (List.take_append_drop p v).symm.trans (by rw [hd]),
          List.length_take_of_le (by omega)⟩
    subst v
    subst p
    have hw : l ++ a :: r = w := sChain_target (sChain_dotAny _ _) h
    subst w
    exact error_dot_mem D Sc i a l r
  | cross p =>
    have hp : p + 2 ≤ v.length := hf
    obtain ⟨l, a, b, r, hv, hl⟩ : ∃ l a b r, v = l ++ a :: b :: r ∧ l.length = p := by
      cases hd : v.drop p with
      | nil => have hh : (v.drop p).length = v.length - p := List.length_drop; rw [hd] at hh; simp at hh; omega
      | cons a q =>
        cases q with
        | nil => have hh : (v.drop p).length = v.length - p := List.length_drop; rw [hd] at hh; simp at hh; omega
        | cons b r =>
          exact ⟨v.take p, a, b, r, (List.take_append_drop p v).symm.trans (by rw [hd]),
            List.length_take_of_le (by omega)⟩
    subst v
    subst p
    have hw : l ++ b :: a :: r = w := sChain_target (by simpa using sChain_crossAt l r a b) h
    subst w
    exact error_cross_mem D Sc i a b l r

private theorem error_word_mem (i : I) (gs : List PG) {v w : List I}
    (h : SChain v (pl v gs) w) (hf : Fits v.length gs) :
    error D Sc i v w (cl D Sc v w gs h) ∈ shortSpan D Sc i v (w ++ [i]) := by
  induction gs generalizing v with
  | nil =>
    obtain rfl : v = w := h
    erw [cl_nil, error_id]
    exact Submodule.zero_mem _
  | cons g gs ih =>
    have e := cl_append D Sc [g] gs h
    rw [show cl D Sc v w (g :: gs) h = _ from e]
    apply error_comp_mem D Sc i
    · exact (wordSumParity_tgt D v [g]).symm
    · exact error_gen_mem D Sc i g _ (hf g (by simp))
    · apply ih
      intro x hx
      simpa only [length_tgt] using hf x (List.mem_cons_of_mem g hx)

theorem error_mem (i : I) {v w : List I} (g : O[v] ⟶ O[w]) :
    error D Sc i v w g ∈ shortSpan D Sc i v (w ++ [i]) := by
  have hg : g ∈ Submodule.span k (Set.range (basisNF D Sc v w)) := by
    rw [Module.Basis.span_eq]
    trivial
  induction hg using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨x, rfl⟩ := hf
    rw [basisNF_apply]
    exact error_word_mem D Sc i _ _ (fits_append (fits_dots x.2.2.1)
      (fits_cw (isReduced_canWord v.length x.1.2).1))
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add f h _ _ hf hh => rw [map_add]; exact Submodule.add_mem _ hf hh
  | smul a f _ hf => rw [map_smul]; exact Submodule.smul_mem _ a hf

/-- Arbitrary scalar old arrows, with the total homogeneous super sign. -/
theorem bareU_homogeneous_transport (i : I) {v w : List I} {q : ZMod 2}
    (g : O[v] ⟶ O[w]) (hg : g ∈ Supercategory.parity (R := k) O[v] O[w] q) :
    (bareU D Sc i v ≫ (g ▷ O[[i]]) : O[i :: v] ⟶ O[w ++ [i]]) -
      SKM.zsign k (D.parity i * wordSumParity D v * q) •
        ((O[[i]] ◁ g) ≫ bareU D Sc i w : O[i :: v] ⟶ O[w ++ [i]]) ∈
      shortSpan D Sc i v (w ++ [i]) := by
  have h := error_mem D Sc i g
  dsimp only [error, LinearMap.coe_mk, AddHom.coe_mk] at h
  erw [twist_of_mem _ hg, MonoidalSupercategory.whiskerLeft_smul (R := k),
    Linear.smul_comp, sign_eq_zsign] at h
  exact h

end OddMath.QuiverHecke.OutputOldComposite

noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped TensorProduct
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
local notation "O[" t "]" => Presentation.obj (pres D Sc) (ob D t)

private theorem run_parity (i : I) (l r : List I) :
    chainParity D (l ++ i :: r) (OutputOldCrossTransport.run l.length r) =
      D.parity i * wordSumParity D r := by
  induction r generalizing l with
  | nil => simp [OutputOldCrossTransport.run, wordSumParity]
  | cons a r ih =>
    rw [OutputOldCrossTransport.run, chainParity_cons]
    have ht : (PG.cross l.length).act (l ++ i :: a :: r) = (l ++ [a]) ++ i :: r := by
      simp [PG.act, List.append_assoc]
    rw [ht]
    have hp : PG.par D (l ++ i :: a :: r) (.cross l.length) = D.parity i * D.parity a := by
      simp [PG.par]
    rw [hp, show l.length + 1 = (l ++ [a]).length by simp, ih]
    simp [wordSumParity, mul_add]

private theorem run_fits (l r : List I) :
    Fits (l.length + 1 + r.length) (OutputOldCrossTransport.run l.length r) := by
  induction r generalizing l with
  | nil => intro g hg; simp [OutputOldCrossTransport.run] at hg
  | cons a r ih =>
    intro g hg
    simp only [OutputOldCrossTransport.run, List.mem_cons] at hg
    rcases hg with rfl | hg
    · simp [PG.pos, PG.width]; omega
    · have hh := ih (l ++ [a]) g (by simpa using hg)
      simpa [List.length_append, List.length_cons, List.length_singleton, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using hh

theorem bareU_parity (i : I) (v : List I) :
    OutputOldComposite.bareU D Sc i v ∈ parity (R := k) _ _
      (D.parity i * wordSumParity D v) := by
  have hp := run_parity D i [] v
  have hf := run_fits ([] : List I) v
  rw [← OutputOldCrossTransport.run_eq_leading] at hp hf
  simpa only [List.nil_append, List.length_nil, zero_add] using
    (hp ▸ cl_mem_chainParity D Sc (cw (leadingMoveWord [] v))
      (by simpa using leadingMoveWord_sChain i [] v) (by simpa [Nat.add_comm] using hf))

-- The coefficient-parity contribution cancels against the box-product sign.
private theorem lift_twisted_error_tmul {v w a b c d : List I} {p r s : ZMod 2}
    (L : (O[v] ⟶ O[w]) →ₗ[k] (O[a] ⟶ O[b]))
    (R : (O[v] ⟶ O[w]) →ₗ[k] (O[c] ⟶ O[d]))
    (u : O[a] ⟶ O[c]) (z : O[b] ⟶ O[d])
    (hz : z ∈ parity (R := k) _ _ p)
    (aa : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff)
    (ha : aa ∈ SKM.SYM.elvCoefficientParity D cutoff r)
    (f : O[v] ⟶ O[w]) (hf : f ∈ parity (R := k) _ _ s)
    (hR : R f ∈ parity (R := k) _ _ s) :
    (affineUnit D Sc cutoff a c u ≫ TensorProduct.map LinearMap.id R (aa ⊗ₜ[k] f) -
      TensorProduct.map LinearMap.id L (twist k p (aa ⊗ₜ[k] f) : hom D Sc cutoff v w) ≫
        affineUnit D Sc cutoff b d z : hom D Sc cutoff a d) =
      aa ⊗ₜ[k] (u ≫ R f - L (twist k p f) ≫ z) := by
  have ht := BoxProd.tmul_mem_parity (X := obj D Sc cutoff v)
    (Y := obj D Sc cutoff w) ha hf
  erw [twist_of_mem p ht, ← koszulSign_smul, map_zsmul, Preadditive.zsmul_comp]
  change (BoxProd.tmulHom (X := obj D Sc cutoff a) (Y := obj D Sc cutoff c) (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) u ≫
      BoxProd.tmulHom (X := obj D Sc cutoff c) (Y := obj D Sc cutoff d) aa (R f)) -
    koszulSign p (r + s) •
      (BoxProd.tmulHom (X := obj D Sc cutoff a) (Y := obj D Sc cutoff b) aa (L f) ≫
        BoxProd.tmulHom (X := obj D Sc cutoff b) (Y := obj D Sc cutoff d) (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) z) = _
  rw [BoxProd.tmulHom_comp_tmulHom (X := obj D Sc cutoff a)
    (Y := obj D Sc cutoff c) (Z := obj D Sc cutoff d)
    (show (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ∈
      SKM.SYM.elvCoefficientParity D cutoff 0 from SetLike.GradedOne.one_mem) u aa hR,
    BoxProd.tmulHom_comp_tmulHom (X := obj D Sc cutoff a)
      (Y := obj D Sc cutoff b) (Z := obj D Sc cutoff d) ha (L f)
      (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) hz]
  simp only [koszulSign_zero_left, one_smul]
  change (aa * 1) ⊗ₜ[k] (u ≫ R f) -
    koszulSign p (r + s) • (koszulSign r p • ((1 * aa) ⊗ₜ[k] (L f ≫ z))) = _
  rw [mul_one, one_mul, twist_of_mem p hf, ← koszulSign_smul,
    map_zsmul, Preadditive.zsmul_comp, TensorProduct.tmul_sub, TensorProduct.tmul_smul,
    smul_smul, koszulSign_add_right, koszulSign_comm r p,
    mul_right_comm, koszulSign_mul_self, one_mul]

def bareUFull (i : I) (v : List I) : hom D Sc cutoff (i :: v) (v ++ [i]) :=
  affineUnit D Sc cutoff _ _ (OutputOldComposite.bareU D Sc i v)

def bareUFullError (i : I) (v w : List I) : hom D Sc cutoff v w →ₗ[k]
    hom D Sc cutoff (i :: v) (w ++ [i]) where
  toFun g := bareUFull D Sc cutoff i v ≫ appendInsert D Sc cutoff i v w g -
    insert D Sc cutoff i v w (twist k (D.parity i * wordSumParity D v) g) ≫
      bareUFull D Sc cutoff i w
  map_add' g h := by
    simp only [map_add, Preadditive.comp_add, Preadditive.add_comp]
    abel
  map_smul' a g := by
    simp only [map_smul, Linear.comp_smul, Linear.smul_comp, smul_sub]
    rfl

theorem bareUFull_transport (i : I) {v w : List I} (g : hom D Sc cutoff v w) :
    projection D Sc cutoff i v (w ++ [i])
      (bareUFull D Sc cutoff i v ≫ appendInsert D Sc cutoff i v w g -
        insert D Sc cutoff i v w (twist k (D.parity i * wordSumParity D v) g) ≫
          bareUFull D Sc cutoff i w) ∈ chronologicalShortSpan D Sc cutoff i v w := by
  change projection D Sc cutoff i v (w ++ [i]) (bareUFullError D Sc cutoff i v w g) ∈ _
  by_cases hp : wordSumParity D w = wordSumParity D v
  · induction g using BoxProd.induction_on_homogeneous with
    | zero =>
      erw [map_zero, map_zero]
      exact Submodule.zero_mem _
    | add g h hg hh =>
      erw [(bareUFullError D Sc cutoff i v w).map_add,
        (projection D Sc cutoff i v (w ++ [i])).map_add]
      exact Submodule.add_mem _ hg hh
    | tmul p q a f ha hf =>
      have hz := bareU_parity D Sc i w
      rw [hp] at hz
      have he := lift_twisted_error_tmul D Sc cutoff
        (affineInsert D Sc i v w) (affineRightContext D Sc [i] v w)
        (OutputOldComposite.bareU D Sc i v) (OutputOldComposite.bareU D Sc i w)
        hz a ha f hf
        (MonoidalSupercategory.whiskerRight_mem (R := k) O[[i]] hf)
      change bareUFullError D Sc cutoff i v w (BoxProd.tmulHom a f) =
        a ⊗ₜ[k] OutputOldComposite.error D Sc i v w f at he
      erw [he]
      exact tmul_shortSpan D Sc cutoff i v w a (OutputOldComposite.error_mem D Sc i f)
  · rw [hom_zero_of_wordParity_ne D Sc cutoff hp g, map_zero, map_zero]
    exact Submodule.zero_mem _

theorem bareUFull_ideal (i : I) {v w : List I} {g : hom D Sc cutoff v w}
    (hg : g ∈ ideal D Sc cutoff v w) :
    projection D Sc cutoff i v (w ++ [i])
      (bareUFull D Sc cutoff i v ≫ appendInsert D Sc cutoff i v w g) ∈
      chronologicalShortSpan D Sc cutoff i v w := by
  have h := bareUFull_transport D Sc cutoff i g
  rw [map_sub, projection_old_ideal D Sc cutoff i (twist_ideal D Sc cutoff _ hg),
    sub_zero] at h
  exact h

/-- The bare-long row does not depend on a representative of the old quotient arrow. -/
theorem bareUFull_old_representative_independent (i : I) {v w : List I}
    (g h : hom D Sc cutoff v w)
    (he : (ideal D Sc cutoff v w).mkQ g = (ideal D Sc cutoff v w).mkQ h) :
    (chronologicalShortSpan D Sc cutoff i v w).mkQ
      (projection D Sc cutoff i v (w ++ [i])
        (bareUFull D Sc cutoff i v ≫ appendInsert D Sc cutoff i v w g)) =
    (chronologicalShortSpan D Sc cutoff i v w).mkQ
      (projection D Sc cutoff i v (w ++ [i])
        (bareUFull D Sc cutoff i v ≫ appendInsert D Sc cutoff i v w h)) := by
  apply sub_eq_zero.mp
  rw [← map_sub, ← map_sub, ← Preadditive.comp_sub, ← map_sub]
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  apply bareUFull_ideal D Sc cutoff i
  apply (Submodule.Quotient.mk_eq_zero _).mp
  change (ideal D Sc cutoff v w).mkQ (g - h) = 0
  rw [map_sub, he, sub_self]

end OddMath.QuiverHecke.ELVOld
