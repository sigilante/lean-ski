import Ski.ZK.LogUpSound
import Ski.Circuit.CompJAir

/-!
# LogUp is sound for the composed circuit with jets

`logup_accept` for the ten AIRs of `compJAirs`, any tables: every bus the
circuit uses is listed (`cjBuses`) and carries tuples of one width
(`cjBusWd`, at most 11, which is Plonky3's widest, `tmpl`'s), checked by
evaluation (`compJAirs_ok`).  For any numbering of the buses that is
injective and below `P - 1` -- Plonky3's, by first use, is one -- tables of
the circuit that do not balance pass the LogUp check for at most
`P^4 (11 M^2 + 2M)` of the challenge pairs (`compJ_logup_sound`).
-/

namespace Circuit

open ZKF Compose

/-- The buses of the composed circuit with jets. -/
def cjBuses : List String :=
  ["mem", "segs", "roots", "hdr", "tmpl", "popch", "wch", "arg",
   "blind_a", "blind_b", "blind_c", "blind_d", "blind_e", "blind_f", "blind_g"]

/-- Each bus's tuple width. -/
def cjBusWd : String → Nat
  | "segs" => 2 | "roots" => 2 | "hdr" => 7 | "tmpl" => 11 | "arg" => 3 | _ => 4

/-- Every message on a listed bus, of the bus's width. -/
def intersOK (l : List Inter) : Bool :=
  l.all (fun I => decide (I.bus ∈ cjBuses) && I.fields.length == cjBusWd I.bus)

theorem compJAirs_ok (shp : BT) (Ps : List Term) (W : Nat) (roots : List (Nat × Nat)) (jets : List Air.Jet) :
    ∀ A ∈ compJAirs shp Ps W roots jets, intersOK A.inters = true := by
  intro A hA
  simp only [compJAirs, List.mem_cons, List.not_mem_nil, or_false] at hA
  rcases hA with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem cjBusWd_le : ∀ a ∈ cjBuses, cjBusWd a ≤ 11 := by decide

/-- A message of zipped tables is one of an AIR's interactions. -/
theorem entries_of_zip {As : List AirD} {ts : List Table} {e : (String × List F) × F}
    (h : e ∈ allEntries (As.zip ts)) : ∃ A ∈ As, ∃ I ∈ A.inters, e.1.1 = I.bus ∧ e.1.2.length = I.fields.length := by
  obtain ⟨p, hp, he⟩ := List.mem_flatMap.1 h
  obtain ⟨r, _, he⟩ := List.mem_flatMap.1 he
  obtain ⟨I, hI, rfl⟩ := List.mem_map.1 he
  exact ⟨p.1, (List.of_mem_zip hp).1, I, hI, rfl, List.length_map _⟩

/-- **LogUp is sound for the composed circuit with jets**: its tables, if
    their buses do not balance, pass Plonky3's LogUp check for at most
    `P^4 (11 M^2 + 2M)` of the `P^8` challenge pairs, `M` the messages, for
    any injective numbering `idx` of its buses below `P - 1`. -/
theorem compJ_logup_sound (idx : String → Nat) (hinj : ∀ a ∈ cjBuses, ∀ b ∈ cjBuses, idx a = idx b → a = b)
    (hlt : ∀ a ∈ cjBuses, idx a + 1 < P)
    (shp : BT) (Ps : List Term) (W : Nat) (roots : List (Nat × Nat)) (jets : List Air.Jet)
    (ts : List Table) (hb : ¬ Balanced ((compJAirs shp Ps W roots jets).zip ts)) :
    sumTo Q4 (fun j => sumTo Q4 (fun i =>
      if Aborts (prefixOf (efOf i) (boff idx 11 (efOf j))) (efOf j) ((compJAirs shp Ps W roots jets).zip ts) ||
          decide (sumL (fun p => terminal (prefixOf (efOf i) (boff idx 11 (efOf j))) (efOf j) p.1 p.2)
            ((compJAirs shp Ps W roots jets).zip ts) = EF.zero)
      then 1 else 0)) ≤
      Q4 * ((allEntries ((compJAirs shp Ps W roots jets).zip ts)).length *
        (allEntries ((compJAirs shp Ps W roots jets).zip ts)).length * 11) +
      2 * (Q4 * (allEntries ((compJAirs shp Ps W roots jets).zip ts)).length) := by
  have hbus : ∀ e ∈ allEntries ((compJAirs shp Ps W roots jets).zip ts),
      e.1.1 ∈ cjBuses ∧ e.1.2.length = cjBusWd e.1.1 := by
    intro e he
    obtain ⟨A, hA, I, hI, hb1, hb2⟩ := entries_of_zip he
    have := List.all_eq_true.1 (compJAirs_ok shp Ps W roots jets A hA) I hI
    rw [Bool.and_eq_true, decide_eq_true_iff, beq_iff_eq] at this
    rw [hb1, hb2]
    exact this
  refine logup_accept idx 11 cjBusWd _ (fun e he => ⟨(hbus e he).2, cjBusWd_le _ (hbus e he).1⟩)
    (fun e he => hlt _ (hbus e he).1)
    (fun e he e' he' h => hinj _ (hbus e he).1 _ (hbus e' he').1 h) hb

end Circuit
