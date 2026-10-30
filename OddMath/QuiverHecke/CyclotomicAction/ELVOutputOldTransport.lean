/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVOutputBalancedComparison

/-!
# Output old action and the chronological short span

The relative-coset stability needed for `DeformedMackeyBoundary.md` (2).
Arbitrary full-ELV output old arrows preserve the chronological short span.
By its exact kernel identification, equal long extractions remain equal after
old output endomorphisms. The crossing generator transports across the bare long chain with explicit
sign and sharp relative-short error, for arbitrary old words and full ELV
coefficients. Extension to arbitrary old arrows and balanced coefficients remains
a separate obligation.
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
