import Ski.Circuit.CompDTraceRows

/-!
# What an honest DEC row sends

A DEC row's messages on the jet's chains (`decn`, `decb`, `decd`,
`decx`), in closed form over its columns (`DecT.sendN`, `sendB`,
`sendD`, `sendX`); on any other bus but `mem` it sends nothing
(`sendO`).
-/

namespace Circuit

open B Air

namespace DecT

set_option maxRecDepth 100000 in
theorem dec_nowOnly : NowOnly Dec.decAir := by
  have h : Dec.decAir.inters.all (fun I => I.count.onlyAtoms nowAtom && I.fields.all (·.onlyAtoms nowAtom)) = true := by
    decide
  intro I hI
  have := List.all_eq_true.1 h I hI
  rw [Bool.and_eq_true, List.all_eq_true] at this
  exact ⟨this.1, this.2⟩

theorem vec_env (A : List Cell) (d : DR) : ∀ a, nowAtom a = true → envOf (vec A d) a = (rowT A d).env 0 a := by
  intro a ha
  cases a with
  | main o c =>
    cases o with
    | zero =>
      show (vec A d).getD c 0 = d.col A c
      unfold vec
      rcases Nat.lt_or_ge c Dec.WIDTH with h | h
      · rw [getD_map_range _ _ h]
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega), col_wide A d h]; rfl
    | succ o => simp [nowAtom] at ha
  | _ => simp [nowAtom] at ha

/-- What a row sends, read on its one-row table. -/
def sendsT (A : List Cell) (d : DR) (B : String) (v : List F) : F :=
  Dec.decInters.foldr (fun I acc => (if I.bus = B ∧ I.fields.map (fun e => e.eval ((rowT A d).env 0)) = v
    then I.count.eval ((rowT A d).env 0) else 0) + acc) 0

theorem vec_sends (A : List Cell) (d : DR) (B : String) (v : List F) :
    rowSendsV Dec.decAir B v (vec A d) = sendsT A d B v := by
  unfold rowSendsV sendsT
  have cong := E.eval_congr (vec_env A d)
  have : ∀ (l : List Inter), (∀ I ∈ l, I ∈ Dec.decAir.inters) →
      l.foldr (fun I acc => (if I.bus = B ∧ I.fields.map (fun e => e.eval (envOf (vec A d))) = v
        then I.count.eval (envOf (vec A d)) else 0) + acc) 0 =
      l.foldr (fun I acc => (if I.bus = B ∧ I.fields.map (fun e => e.eval ((rowT A d).env 0)) = v
        then I.count.eval ((rowT A d).env 0) else 0) + acc) 0 := by
    intro l hl
    induction l with
    | nil => rfl
    | cons I l ih =>
      simp only [List.foldr_cons]
      obtain ⟨hc, hf⟩ := dec_nowOnly I (hl I List.mem_cons_self)
      rw [List.map_congr_left (fun e he => cong e (hf e he)), cong _ hc,
        ih (fun J hJ => hl J (List.mem_cons_of_mem _ hJ))]
  exact this _ (fun _ h => h)

theorem decInters_bus : ∀ I ∈ Dec.decInters, I.bus = "mem" ∨ I.bus = "decn" ∨ I.bus = "decb" ∨ I.bus = "decd" ∨
    I.bus = "decx" := by
  intro I hI
  have h : Dec.decInters.all (fun I => I.bus == "mem" || I.bus == "decn" || I.bus == "decb" || I.bus == "decd" ||
    I.bus == "decx") = true := by decide
  have := List.all_eq_true.1 h I hI
  simp only [Bool.or_eq_true, beq_iff_eq] at this
  rcases this with (((h | h) | h) | h) | h
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (.inl h))
  · exact .inr (.inr (.inr (.inl h)))
  · exact .inr (.inr (.inr (.inr h)))

section
variable (A : List Cell) (d : DR) (v : List F)

theorem sendO {B : String} (h1 : B ≠ "mem") (h2 : B ≠ "decn") (h3 : B ≠ "decb") (h4 : B ≠ "decd")
    (h5 : B ≠ "decx") : sendsT A d B v = 0 := by
  unfold sendsT
  apply fold_zero
  intro I hI
  rw [if_neg]
  intro ⟨hb, _⟩
  rcases decInters_bus I hI with h | h | h | h | h <;> rw [h] at hb <;> subst hb <;> contradiction

theorem sendN : sendsT A d "decn" v =
    (if [ofN d.key, ofN d.p, ofN d.ro] = v then -(kc d + ka d) else 0) +
    ((if [ofN d.key, ofN (sl A d 21).2.2.2, ofN 2 - h0 d] = v then kc d else 0) +
    ((if [ofN d.key, ofN (sl A d 23).2.2.2, ofN 2] = v then kc d else 0) + 0)) := by
  unfold sendsT
  rw [foldr_sends_filter, show Dec.decInters.filter (fun I => decide (I.bus = "decn")) =
    [⟨"decn", 1, .neg (.add (col Dec.KCELL) (col Dec.KATOM)), [col Dec.KEY, col Dec.PC, col Dec.RO]⟩,
     ⟨"decn", 1, col Dec.KCELL, [col Dec.KEY, Dec.f2 21, .sub (c 2) (col Dec.H0)]⟩,
     ⟨"decn", 1, col Dec.KCELL, [col Dec.KEY, Dec.f2 23, c 2]⟩] from rfl]
  simp only [List.foldr_cons, List.foldr_nil, List.map_cons, List.map_nil, true_and]
  rfl

theorem sendB : sendsT A d "decb" v =
    (if [ofN d.key, ofN (sl A d 22).2.2.2, 1 - h1 d, ofN 0, h1 d, ofN 0] = v then ka d else 0) +
    ((if [ofN d.key, ofN d.p, vM d, ofN d.lvl, vBW d, ofN d.wc] = v then -ks d else 0) +
    ((if [ofN d.key, ofN (sl A d 14).2.2.2, vM d, ofN d.lvl + 1, vBW d * (1 - vBIT d), ofN d.wc + ofN 6 * vWR d] = v
      then ks d * (1 - vL d) else 0) +
    ((if [ofN d.key, ofN d.p, vM d, ofN d.lvl, vBW d, ofN d.wc] = v then -kn d else 0) + 0))) := by
  unfold sendsT
  rw [foldr_sends_filter, show Dec.decInters.filter (fun I => decide (I.bus = "decb")) =
    [⟨"decb", 1, col Dec.KATOM, [col Dec.KEY, Dec.f2 22, .sub one (col Dec.H1), c 0, col Dec.H1, c 0]⟩,
     ⟨"decb", 1, .neg (col Dec.KCONS), [col Dec.KEY, col Dec.PC, col Dec.MODE, col Dec.LVL, col Dec.BW, col Dec.WC]⟩,
     ⟨"decb", 1, col Dec.CSEND, [col Dec.KEY, Dec.f2 14, col Dec.MODE, .add (col Dec.LVL) one, col Dec.NBW,
       col Dec.WCN]⟩,
     ⟨"decb", 1, .neg (col Dec.KNIL), [col Dec.KEY, col Dec.PC, col Dec.MODE, col Dec.LVL, col Dec.BW, col Dec.WC]⟩]
    from rfl]
  simp only [List.foldr_cons, List.foldr_nil, List.map_cons, List.map_nil, true_and]
  rfl

theorem sendD : sendsT A d "decd" v =
    (if [ofN d.key, bF d.err, ofN d.wc] = v then -vSUB d else 0) +
    ((if [ofN d.key, ofN 0, ofN d.wc + ofN 6 * vWR d] = v then ks d * vL d * (1 - vM d) else 0) +
    ((if [ofN d.key, ofN 1, ofN d.wc] = v then kn d * (1 - vM d) else 0) +
    ((if [ofN d.key, ofN 1, ofN 0] = v then kc d * h1 d else 0) + 0))) := by
  unfold sendsT
  rw [foldr_sends_filter, show Dec.decInters.filter (fun I => decide (I.bus = "decd")) =
    [⟨"decd", 1, .neg (col Dec.SUB), [col Dec.KEY, col Dec.ERR, col Dec.WC]⟩,
     ⟨"decd", 1, col Dec.DONE0, [col Dec.KEY, c 0, col Dec.WCN]⟩,
     ⟨"decd", 1, col Dec.DONE1, [col Dec.KEY, c 1, col Dec.WC]⟩,
     ⟨"decd", 1, col Dec.HC, [col Dec.KEY, c 1, c 0]⟩] from rfl]
  simp only [List.foldr_cons, List.foldr_nil, List.map_cons, List.map_nil, true_and]
  rfl

theorem sendX : sendsT A d "decx" v =
    (if [ofN d.key, ofN d.key + ofN 12 * bF d.err, ofN d.key + ofN 12 + ofN d.wc + ofN 3 * bF d.err] = v
      then vSUB d else 0) +
    ((if [ofN d.key, ofN d.key, ofN d.key + ofN 3] = v then ka d * h0 d else 0) + 0) := by
  unfold sendsT
  rw [foldr_sends_filter, show Dec.decInters.filter (fun I => decide (I.bus = "decx")) =
    [⟨"decx", 1, col Dec.SUB, [col Dec.KEY, .add (col Dec.KEY) (.mul (c 12) (col Dec.ERR)),
       .add (.add (.add (col Dec.KEY) (c 12)) (col Dec.WC)) (.mul (c 3) (col Dec.ERR))]⟩,
     ⟨"decx", 1, col Dec.ASUB, [col Dec.KEY, col Dec.KEY, .add (col Dec.KEY) (c 3)]⟩] from rfl]
  simp only [List.foldr_cons, List.foldr_nil, List.map_cons, List.map_nil, true_and]
  rfl

end

end DecT

end Circuit
