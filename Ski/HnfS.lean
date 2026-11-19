import Ski.Weak
open Term

/-!
# Head normal forms of pure S: the automaton half of *Dance of the Starlings*, Question 10

Barendregt, Endrullis, Klop and Waldmann (*Dance of the Starlings*, 2017, Question 10)
conjecture that the tree automaton of their Fig. 5.14 accepts exactly the closed S-terms
with a head normal form (`S`, `S X` or `S X Y`).  The answer in Murmuration I has two
directions.  This module proves, inside the axiom gate, everything except soundness of
the fold (an `h`-fold term has a head normal form), which is taken as a hypothesis:

* `fold_wsteps`: the 38-block fold is invariant under weak reduction of pure S-terms;
* `no_hnf_of_bot`: a term whose fold is the ⊥ block has no reduct in head normal form;
* `dance_fold`: the Fig. 5.14 automaton factors through the fold;
* `q10_rejecting`: every term the automaton rejects has no head normal form;
* `q10_of_soundness`: given soundness of the fold, the automaton accepts exactly the
  terms with a head normal form, which is Question 10.

The tables are data.  `blockTable` is the 38-block table of Murmuration I
(`FoldWalk.lean`, block 0 = `S`, block 36 = ⊥); `danceTable` is the transcription of
Fig. 5.14 (`dance_fig514.csv`, state 0 = `S`, state 34 = the rejecting state ⊛); and
`blockToDance` maps blocks to states.  Every fact used about them is a finite check by
`decide +kernel`, so no `native_decide` is involved.
-/

namespace HnfS

/-! ## Pure S-terms -/

/-- Closed pure-S terms. -/
inductive PureS : Term → Prop
  | S : PureS .S
  | app {f x : Term} : PureS f → PureS x → PureS (f ⬝ x)

theorem PureS.app_inv {f x : Term} (h : PureS (f ⬝ x)) : PureS f ∧ PureS x := by
  cases h with
  | app hf hx => exact ⟨hf, hx⟩

theorem PureS.not_K : ¬ PureS K := fun h => nomatch h
theorem PureS.not_I : ¬ PureS I := fun h => nomatch h

/-! ## The tables -/

def blockTable : List (List Nat) := [
  [1, 2, 4, 5, 8, 9, 10, 11, 17, 18, 9, 9, 10, 9, 18, 19, 20, 17, 27, 18, 27, 18, 28, 27, 18, 27, 20, 27, 18, 27, 27, 27, 18, 18, 27, 18, 27, 27],
  [3, 6, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12],
  [7, 13, 14, 21, 29, 29, 21, 30, 30, 30, 29, 30, 21, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30],
  [6, 14, 22, 23, 30, 31, 23, 25, 30, 31, 31, 31, 23, 31, 31, 34, 34, 30, 31, 31, 31, 31, 31, 31, 31, 31, 34, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31],
  [15, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22],
  [16, 24, 32, 33, 23, 23, 33, 25, 25, 25, 23, 25, 33, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25],
  [12, 21, 22, 33, 30, 31, 32, 25, 30, 31, 31, 31, 32, 31, 31, 34, 34, 30, 31, 31, 31, 31, 31, 31, 31, 31, 34, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31],
  [14, 22, 30, 31, 30, 31, 31, 31, 30, 31, 31, 31, 31, 31, 31, 31, 31, 30, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31],
  [14, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30],
  [25, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31],
  [26, 32, 32, 32, 23, 23, 32, 25, 25, 25, 23, 25, 32, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25],
  [25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25],
  [12, 30, 22, 25, 30, 31, 25, 25, 30, 31, 31, 31, 25, 31, 31, 34, 34, 30, 31, 31, 31, 31, 31, 31, 31, 31, 34, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31],
  [23, 32, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25],
  [25, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31],
  [22, 25, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31],
  [21, 31, 31, 36, 31, 36, 36, 36, 31, 36, 36, 36, 36, 36, 36, 36, 36, 31, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36],
  [30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30],
  [34, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31],
  [35, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34],
  [34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34],
  [23, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31],
  [31, 25, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31],
  [34, 31, 31, 36, 31, 36, 36, 36, 31, 36, 36, 36, 36, 36, 36, 36, 36, 31, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36],
  [33, 31, 31, 36, 31, 36, 36, 36, 31, 36, 36, 36, 36, 36, 36, 36, 36, 31, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36],
  [31, 31, 31, 36, 31, 36, 36, 36, 31, 36, 36, 36, 36, 36, 36, 36, 36, 31, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36],
  [30, 31, 31, 36, 31, 36, 36, 36, 31, 36, 36, 36, 36, 36, 36, 36, 36, 31, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36],
  [31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31],
  [37, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31],
  [34, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31],
  [31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31],
  [36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36],
  [25, 31, 31, 36, 31, 36, 36, 36, 31, 36, 36, 36, 36, 36, 36, 36, 36, 31, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36],
  [32, 31, 31, 36, 31, 36, 36, 36, 31, 36, 36, 36, 36, 36, 36, 36, 36, 31, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36],
  [31, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36],
  [25, 31, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36],
  [36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36],
  [36, 31, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36]]

def danceTable : List (List Nat) := [
  [1, 2, 3, 4, 5, 5, 7, 8, 9, 10, 10, 12, 8, 12, 15, 8, 8, 9, 19, 9, 21, 9, 10, 10, 10, 10, 27, 10, 9, 9, 9, 27, 9, 10, 10],
  [6, 11, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13],
  [14, 16, 8, 9, 10, 10, 17, 9, 10, 10, 10, 17, 9, 17, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10],
  [18, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20],
  [8, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10],
  [10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10],
  [11, 8, 20, 10, 10, 10, 22, 23, 23, 23, 23, 22, 23, 22, 24, 23, 23, 23, 25, 23, 23, 23, 23, 23, 23, 23, 25, 23, 23, 23, 23, 25, 23, 23, 23],
  [26, 28, 29, 22, 24, 24, 30, 22, 24, 24, 24, 30, 22, 30, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24],
  [24, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23],
  [25, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23],
  [23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23],
  [13, 17, 20, 10, 10, 10, 30, 23, 23, 23, 23, 29, 23, 29, 24, 23, 23, 23, 25, 23, 23, 23, 23, 23, 23, 23, 25, 23, 23, 23, 23, 25, 23, 23, 23],
  [31, 29, 29, 22, 24, 24, 29, 22, 24, 24, 24, 29, 22, 29, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24],
  [13, 10, 20, 10, 10, 10, 24, 23, 23, 23, 23, 24, 23, 24, 24, 23, 23, 23, 25, 23, 23, 23, 23, 23, 23, 23, 25, 23, 23, 23, 23, 25, 23, 23, 23],
  [8, 20, 10, 10, 10, 10, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23],
  [24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24],
  [22, 29, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24],
  [22, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23],
  [20, 24, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23],
  [32, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25],
  [23, 24, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23],
  [33, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23],
  [25, 23, 23, 23, 23, 23, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34],
  [34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34],
  [23, 23, 23, 23, 23, 23, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34],
  [23, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34],
  [17, 23, 23, 23, 23, 23, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34],
  [25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25],
  [30, 23, 23, 23, 23, 23, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34],
  [24, 23, 23, 23, 23, 23, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34],
  [29, 23, 23, 23, 23, 23, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34],
  [10, 23, 23, 23, 23, 23, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34],
  [24, 23, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34],
  [34, 23, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34],
  [34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34]]

def blockToDance : List Nat := [0, 1, 2, 6, 3, 7, 11, 14, 4, 8, 12, 15, 13, 16, 8, 18, 26, 5, 9, 19, 27, 17, 20, 22, 28, 24, 31, 10, 21, 9, 10, 23, 29, 30, 25, 32, 34, 33]

/-- The block algebra: block of `M N` from the blocks of `M` and `N`. -/
def β (a b : Nat) : Nat := (blockTable.getD a []).getD b 36

/-- The block fold of a term (`K` and `I` go to ⊥; only pure S-terms matter). -/
def fold : Term → Nat
  | .S => 0
  | .K => 36
  | .I => 36
  | .app f x => β (fold f) (fold x)

/-- Fig. 5.14's transition function. -/
def δ (a b : Nat) : Nat := (danceTable.getD a []).getD b 34

/-- Fig. 5.14's rejecting state ⊛. -/
def P : Nat := 34

/-- The state Fig. 5.14 assigns to a term. -/
def dance : Term → Nat
  | .S => 0
  | .K => P
  | .I => P
  | .app f x => δ (dance f) (dance x)

/-- The map from blocks to Fig. 5.14 states. -/
def φ (a : Nat) : Nat := blockToDance.getD a 34

/-! ## Finite checks -/

def r38 : List Nat := List.range 38

def closedB : Bool := r38.all fun a => r38.all fun b => decide (β a b < 38)
def compatB : Bool :=
  r38.all fun a => r38.all fun b => r38.all fun c => β (β (β 0 a) b) c == β (β a c) (β b c)
def hnfB : Bool :=
  r38.all fun a => (β 0 a != 36) && r38.all fun b => β (β 0 a) b != 36
def homB : Bool := r38.all fun a => r38.all fun b => φ (β a b) == δ (φ a) (φ b)
def rejectB : Bool := r38.all fun a => (φ a == P) == (a == 36)

theorem closedB_eq : closedB = true := by decide +kernel
theorem compatB_eq : compatB = true := by decide +kernel
theorem hnfB_eq : hnfB = true := by decide +kernel
theorem homB_eq : homB = true := by decide +kernel
theorem rejectB_eq : rejectB = true := by decide +kernel

theorem β_lt {a b : Nat} (ha : a < 38) (hb : b < 38) : β a b < 38 := by
  have h := closedB_eq
  simp only [closedB, r38, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  exact h a ha b hb

/-- The block table is an S-model: all 54,872 triples. -/
theorem compat {a b c : Nat} (ha : a < 38) (hb : b < 38) (hc : c < 38) :
    β (β (β 0 a) b) c = β (β a c) (β b c) := by
  have h := compatB_eq
  simp only [compatB, r38, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  exact h a ha b hb c hc

theorem hnf_blocks {a b : Nat} (ha : a < 38) (hb : b < 38) :
    β 0 a ≠ 36 ∧ β (β 0 a) b ≠ 36 := by
  have h := hnfB_eq
  simp only [hnfB, r38, List.all_eq_true, List.mem_range, Bool.and_eq_true, bne_iff_ne,
    ne_eq] at h
  exact ⟨(h a ha).1, (h a ha).2 b hb⟩

theorem hom {a b : Nat} (ha : a < 38) (hb : b < 38) : φ (β a b) = δ (φ a) (φ b) := by
  have h := homB_eq
  simp only [homB, r38, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  exact h a ha b hb

theorem reject {a : Nat} (ha : a < 38) : φ a = P ↔ a = 36 := by
  have h := rejectB_eq
  simp only [rejectB, r38, List.all_eq_true, List.mem_range] at h
  have := beq_iff_eq.mp (h a ha)
  constructor
  · intro hp
    rw [beq_iff_eq.mpr hp] at this
    exact beq_iff_eq.mp this.symm
  · intro h36
    rw [beq_iff_eq.mpr h36] at this
    exact beq_iff_eq.mp this

/-! ## The fold is a reduction invariant -/

theorem fold_lt {t : Term} (ht : PureS t) : fold t < 38 := by
  induction ht with
  | S => decide
  | app _ _ ihf ihx => exact β_lt ihf ihx

theorem wstep_pure {t t' : Term} (h : WStep t t') (ht : PureS t) :
    PureS t' ∧ fold t' = fold t := by
  induction h with
  | S f g x =>
    obtain ⟨h1, hx⟩ := ht.app_inv
    obtain ⟨h2, hg⟩ := h1.app_inv
    obtain ⟨_, hf⟩ := h2.app_inv
    refine ⟨.app (.app hf hx) (.app hg hx), ?_⟩
    simp only [fold]
    exact (compat (fold_lt hf) (fold_lt hg) (fold_lt hx)).symm
  | K x y => exact absurd ht.app_inv.1.app_inv.1 PureS.not_K
  | I x => exact absurd ht.app_inv.1 PureS.not_I
  | left x _ ih =>
    obtain ⟨hp, he⟩ := ih ht.app_inv.1
    exact ⟨.app hp ht.app_inv.2, by simp only [fold, he]⟩
  | right f _ ih =>
    obtain ⟨hp, he⟩ := ih ht.app_inv.2
    exact ⟨.app ht.app_inv.1 hp, by simp only [fold, he]⟩

/-- The block fold is invariant under weak reduction of pure S-terms. -/
theorem fold_wsteps {t u : Term} (h : WSteps t u) (ht : PureS t) :
    PureS u ∧ fold u = fold t := by
  induction h with
  | refl => exact ⟨ht, rfl⟩
  | step h1 _ ih =>
    obtain ⟨hp, he⟩ := wstep_pure h1 ht
    obtain ⟨hp', he'⟩ := ih hp
    exact ⟨hp', he'.trans he⟩

/-! ## Head normal forms -/

/-- *Dance*'s head normal forms of closed S-terms: `S`, `S X`, `S X Y`. -/
def IsHnf (t : Term) : Prop := t = S ∨ (∃ x, t = S ⬝ x) ∨ ∃ x y, t = S ⬝ x ⬝ y

/-- `t` reduces to a head normal form. -/
def HasHnf (t : Term) : Prop := ∃ u, WSteps t u ∧ IsHnf u

theorem fold_hnf {u : Term} (hu : PureS u) (h : IsHnf u) : fold u ≠ 36 := by
  rcases h with rfl | ⟨x, rfl⟩ | ⟨x, y, rfl⟩
  · decide
  · exact (hnf_blocks (fold_lt hu.app_inv.2) (by decide : 0 < 38)).1
  · exact (hnf_blocks (fold_lt hu.app_inv.1.app_inv.2) (fold_lt hu.app_inv.2)).2

/-- Completeness of the fold: a term whose fold is ⊥ has no head normal form. -/
theorem no_hnf_of_bot {t : Term} (ht : PureS t) (h : fold t = 36) : ¬ HasHnf t := by
  rintro ⟨u, hs, hu⟩
  obtain ⟨hp, he⟩ := fold_wsteps hs ht
  exact fold_hnf hp hu (he.trans h)

/-! ## Fig. 5.14 -/

/-- The Fig. 5.14 automaton factors through the block fold. -/
theorem dance_fold {t : Term} (ht : PureS t) : dance t = φ (fold t) := by
  induction ht with
  | S => decide
  | app hf hx ihf ihx =>
    simp only [dance, fold, ihf, ihx]
    exact (hom (fold_lt hf) (fold_lt hx)).symm

/-- Fig. 5.14 rejects a term exactly when its fold is ⊥. -/
theorem dance_rejects_iff {t : Term} (ht : PureS t) : dance t = P ↔ fold t = 36 := by
  rw [dance_fold ht]
  exact reject (fold_lt ht)

/-- Fig. 5.14's state is a reduction invariant of pure S-terms. -/
theorem dance_wsteps {t u : Term} (h : WSteps t u) (ht : PureS t) : dance u = dance t := by
  obtain ⟨hp, he⟩ := fold_wsteps h ht
  rw [dance_fold hp, dance_fold ht, he]

/-- The inclusion *Dance* expects to be easy: a term Fig. 5.14 rejects has no head
normal form. -/
theorem q10_rejecting {t : Term} (ht : PureS t) (h : dance t = P) : ¬ HasHnf t :=
  no_hnf_of_bot ht ((dance_rejects_iff ht).1 h)

/-- Question 10, given soundness of the fold (Murmuration I, `thm:soundness`): Fig. 5.14
accepts exactly the closed S-terms with a head normal form. -/
theorem q10_of_soundness
    (sound : ∀ t, PureS t → fold t ≠ 36 → HasHnf t) {t : Term} (ht : PureS t) :
    HasHnf t ↔ dance t ≠ P := by
  constructor
  · intro h hr
    exact q10_rejecting ht hr h
  · intro h
    exact sound t ht (fun hb => h ((dance_rejects_iff ht).2 hb))

end HnfS
