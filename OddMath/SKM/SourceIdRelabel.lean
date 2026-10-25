import OddMath.SKM.SourceFrozenSwap

/-! Injective strand-ID relabelling for source adaptation. Fresh IDs are fixed;
all cap renamings and critical IDs are transported exactly. -/
namespace OddMath.SKM.SourceIdRelabel
open StringDiagrams StringDiagrams.Chord
variable {α : Type*}

def idMap (f : ℕ → ℕ) (x : ℕ × α) : ℕ × α := (f x.1, x.2)

def rename (f : ℕ → ℕ) (T : TState α) : TState α :=
  ⟨T.nxt, T.st.map (idMap f), T.xs.map (Sym2.map f)⟩

private theorem idD_map (f : ℕ → ℕ) (s : List (ℕ × α)) (j : ℕ) (hj : j < s.length) :
    idD (s.map (idMap f)) j = f (idD s j) := by
  change (idAt (s.map (fun z => (f z.1, z.2))) j).getD 0 = f (idD s j)
  rw [idAt_map_fst s f j, idAt_eq_idD hj]
  rfl

private theorem rlId_map (f : ℕ → ℕ) (hf : Function.Injective f) (x y z : ℕ) :
    rlId (f x) (f y) (f z) = f (rlId x y z) := by
  simp only [rlId, hf.eq_iff]
  split_ifs <;> rfl

private theorem jn_map (f : ℕ → ℕ) (hf : Function.Injective f)
    (s : List (ℕ × α)) (r : ℕ) :
    jn (s.map (idMap f)) r = (jn s r).map (idMap f) := by
  simp only [jn, ← List.map_drop]
  cases s.drop r with
  | nil => rfl
  | cons A l =>
    cases l with
    | nil => rfl
    | cons B l =>
      simp only [List.map_cons, ← map_rmAt, List.map_map]
      apply List.map_congr_left
      intro z _
      exact Prod.ext (rlId_map f hf B.1 A.1 z.1) rfl

theorem ok (d : α → α) (f : ℕ → ℕ) (hf : Function.Injective f)
    (k : ℕ) (T : TState α) (m : TMove α) (hm : m.Ok d k T.st) :
    m.Ok d k (rename f T).st := by
  cases m with
  | mv m => cases m <;> simpa [TMove.Ok, rename] using hm
  | cap g =>
    obtain ⟨A, B, hA, hB, hl, hn⟩ := hm
    refine ⟨idMap f A, idMap f B, ?_, ?_, hl, hf.ne hn⟩
    · simp [rename, List.getElem?_map, hA]
    · simp [rename, List.getElem?_map, hB]

/-- Exact state transport, including the crossing-ID list. -/
theorem step (d : α → α) (f : ℕ → ℕ) (hf : Function.Injective f)
    (k : ℕ) (T : TState α) (hfix : f T.nxt = T.nxt)
    (m : TMove α) (hm : m.Ok d k T.st) :
    tStep d k (rename f T) m = rename f (tStep d k T m) := by
  cases m with
  | mv m =>
    cases m with
    | cup g a => simp [tStep, rename, map_insAt, idMap, hfix]
    | cross p =>
      have hp : k + p + 1 < T.st.length := hm
      simp only [tStep, rename, map_swapAt, List.map_append, List.map_cons, List.map_nil,
        idD_map f T.st (k + p) (by omega), idD_map f T.st (k + p + 1) hp]
      rfl
  | cap g =>
    obtain ⟨A, B, hA, hB, hl, hn⟩ := hm
    have hr : k + g + 1 < T.st.length := List.getElem?_eq_some_iff.mp hB |>.1
    simp only [tStep, rename, jn_map f hf,
      idD_map f T.st (k + g) (by omega), idD_map f T.st (k + g + 1) hr]
    congr 1
    simp only [List.map_map, ← Sym2.map_comp]
    congr 2
    funext z
    exact rlId_map f hf _ _ z

private theorem next_le (d : α → α) (k : ℕ) (T : TState α) (m : TMove α) :
    T.nxt ≤ (tStep d k T m).nxt := by
  cases m with
  | mv m => cases m <;> simp [tStep]
  | cap g => rfl

/-- Every active move remains valid after injective source-ID relabelling. -/
theorem fits (d : α → α) (f : ℕ → ℕ) (hf : Function.Injective f)
    (k : ℕ) (T : TState α) (hfix : ∀ n, T.nxt ≤ n → f n = n)
    (R : List (TMove α)) (hR : TFits d k T R) : TFits d k (rename f T) R := by
  induction R generalizing T with
  | nil => trivial
  | cons m R ih =>
    refine ⟨ok d f hf k T m hR.1, ?_⟩
    rw [step d f hf k T (hfix _ le_rfl) m hR.1]
    exact ih _ (fun n hn => hfix n ((next_le d k T m).trans hn)) hR.2

/-- All state data, not only the terminal pairing, commute with relabelling. -/
theorem run (d : α → α) (f : ℕ → ℕ) (hf : Function.Injective f)
    (k : ℕ) (T : TState α) (hfix : ∀ n, T.nxt ≤ n → f n = n)
    (R : List (TMove α)) (hR : TFits d k T R) :
    tRun d k (rename f T) R = rename f (tRun d k T R) := by
  induction R generalizing T with
  | nil => rfl
  | cons m R ih =>
    change tRun d k (tStep d k (rename f T) m) R = rename f (tRun d k (tStep d k T m) R)
    rw [step d f hf k T (hfix _ le_rfl) m hR.1]
    exact ih _ (fun n hn => hfix n ((next_le d k T m).trans hn)) hR.2

/-- Exact transport of the critical-ID list, needed for strict representatives. -/
theorem critStep_map (d : α → α) (f : ℕ → ℕ) (hf : Function.Injective f)
    (k : ℕ) (T : TState α) (hfix : f T.nxt = T.nxt)
    (cl : List ℕ) (m : TMove α) (hm : m.Ok d k T.st) :
    critStep k (rename f T) (cl.map f) m = (critStep k T cl m).map f := by
  cases m with
  | mv m => cases m <;> simp [critStep, rename, hfix]
  | cap g =>
    obtain ⟨A, B, hA, hB, hl, hn⟩ := hm
    have hr : k + g + 1 < T.st.length := List.getElem?_eq_some_iff.mp hB |>.1
    simp only [critStep, rename, List.map_append, List.map_cons, List.map_nil,
      idD_map f T.st (k + g) (by omega), idD_map f T.st (k + g + 1) hr, List.map_map]
    congr 2
    funext z
    exact rlId_map f hf _ _ z

theorem crit (d : α → α) (f : ℕ → ℕ) (hf : Function.Injective f)
    (k : ℕ) (T : TState α) (hfix : ∀ n, T.nxt ≤ n → f n = n)
    (R : List (TMove α)) (hR : TFits d k T R) (cl : List ℕ) :
    tCrit d k (rename f T) (cl.map f) R = (tCrit d k T cl R).map f := by
  induction R generalizing T cl with
  | nil => rfl
  | cons m R ih =>
    simp only [tCrit]
    rw [critStep_map d f hf k T (hfix _ le_rfl) cl m hR.1,
      step d f hf k T (hfix _ le_rfl) m hR.1]
    exact ih _ (fun n hn => hfix n ((next_le d k T m).trans hn)) hR.2 _

/-- Cap renaming commutes with an injective ID map at valid active positions. -/
theorem stepRen_map {I : Type*} (f : ℕ → ℕ) (hf : Function.Injective f)
    (k : ℕ) (T : TState (Letter I)) (m : TMove (Letter I))
    (hm : m.Ok flipL k T.st) (x : ℕ) :
    stepRen k (rename f T) m (f x) = f (stepRen k T m x) := by
  cases m with
  | mv m => rfl
  | cap g =>
    obtain ⟨A, B, hA, hB, hl, hn⟩ := hm
    have hr : k + g + 1 < T.st.length := List.getElem?_eq_some_iff.mp hB |>.1
    simp only [stepRen, rename, idD_map f T.st (k + g) (by omega),
      idD_map f T.st (k + g + 1) hr]
    exact rlId_map f hf _ _ x

/-- Full transport of distinguished-point strand IDs through subsequent caps. -/
theorem ren {I : Type*} (f : ℕ → ℕ) (hf : Function.Injective f)
    (k : ℕ) (T : TState (Letter I)) (hfix : ∀ n, T.nxt ≤ n → f n = n)
    (R : List (TMove (Letter I))) (hR : TFits flipL k T R) (x : ℕ) :
    tRen k (rename f T) R (f x) = f (tRen k T R x) := by
  induction R generalizing T x with
  | nil => rfl
  | cons m R ih =>
    simp only [tRen]
    rw [stepRen_map f hf k T m hR.1, step flipL f hf k T (hfix _ le_rfl) m hR.1]
    exact ih _ (fun n hn => hfix n ((next_le flipL k T m).trans hn)) hR.2 _

/-- Relabelling preserves the complete reducedness data at a valid state:
no repeated crossings, no diagonal crossings, and no repeated critical IDs. -/
theorem reducedData_iff (d : α → α) (f : ℕ → ℕ) (hf : Function.Injective f)
    (k : ℕ) (T : TState α) (hfix : ∀ n, T.nxt ≤ n → f n = n)
    (R : List (TMove α)) (hR : TFits d k T R) (cl : List ℕ) :
    ((tRun d k (rename f T) R).xs.Nodup ∧
      (∀ z ∈ (tRun d k (rename f T) R).xs, ¬ z.IsDiag) ∧
      (tCrit d k (rename f T) (cl.map f) R).Nodup) ↔
    ((tRun d k T R).xs.Nodup ∧
      (∀ z ∈ (tRun d k T R).xs, ¬ z.IsDiag) ∧
      (tCrit d k T cl R).Nodup) := by
  rw [run d f hf k T hfix R hR, crit d f hf k T hfix R hR cl]
  simp only [rename, List.nodup_map_iff (Sym2.map.injective hf),
    List.nodup_map_iff hf, List.mem_map, forall_exists_index, and_imp]
  constructor
  · rintro ⟨hn, hd, hc⟩
    refine ⟨hn, ?_, hc⟩
    intro z hz
    exact fun h => hd _ z hz rfl (h.map)
  · rintro ⟨hn, hd, hc⟩
    refine ⟨hn, ?_, hc⟩
    intro z x hx he
    subst z
    exact fun h => hd x hx ((Sym2.isDiag_map hf).mp h)

end OddMath.SKM.SourceIdRelabel
