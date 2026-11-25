import Ski.S11Base
open Term

/-!
# S11: the set 𝔅 and Lemma 16

Paper S11, §5: the set `𝔅` (`InB`) and Lemma 16 (`lem:typing`), the two hypotheses of
Lemma 15 (`lem:closure`):

* (i) the function part and the argument of every member of `𝔅` that is an application are
  in `𝔅` (`InB.fun_arg`);
* (ii) for every `β ∈ 𝔅` and every frame `S x₀ y₀ z₀` with exactly three items on the head run
  of `β`, the terms `x₀ z₀` and `y₀ z₀` are in `𝔅` (`lemma16_ii`).

The paper proves (ii) by a narrated table ("and so on, no later frame has exactly three
items").  Here it is a step-closed invariant: `RunFrame` lists every frame shape on the head
run of a member, with its passive arguments `Us`; `RunFrame.mem` puts the members in it,
`RunFrame.step` shows it is closed under head steps, and `RunFrame.three` reads off the
three-item frames.  The shapes are those of the paper's table (members written with
`a = a_m`, `a' = a_{m+1}`, `b' = b_{m+1}`, `v = a (Q a)`):

| head                | frames after the head (`RunFrame` constructor)                         |
|---------------------|-----------------------------------------------------------------------|
| `a = Q c_j c_n`     | `S S c_n a'` (`a_ss`), `S a' b'` (`a_hnf`)                              |
| `a = G c_n`         | `Q c_n (Q c_n)` (`a_q`), `S S c_{n+1} a'` (`a_ss`), `S a' b'` (`a_hnf`) |
| `c_{j+1} a`         | `S S a (c_j a)` (`x_ss`), `S (c_j a) (a (c_j a))` (`x_hnf`)             |
| `G a = c_0 a`       | `Q a (Q a)` (`g_q`), `S S (Q a) v` (`g_ss`), `S v (Q a v)` (`g_hnf`)    |
| `Q a v`             | `S S v (a v)` (`q_ss`), `S (a v) (v (a v))` (`q_hnf`)                   |

each followed by the passive arguments.  A step from an `…_hnf` frame consumes the first
passive argument and lands in `𝔅` again (families (Fa) and (Fx)).
-/

namespace S11

/-! ## The set 𝔅 -/

/-- The set `𝔅` of the paper (§5).  Passive arguments are lists `Us` whose members are in
`𝔅`.  The pieces are `pS`, `pSS`, `pQ`, `pSQ`, `pc`; the families (Fa), (Fx), (FQa), (FQa2);
and (FSS), (FS) with one constructor for each listed `w`. -/
inductive InB : Term → Prop
  | pS : InB S
  | pSS : InB (S ⬝ S)
  | pQ : InB Q
  | pSQ : InB (S ⬝ Q)
  | pc (j : Nat) : InB (c j)
  /-- (Fa) `a_m U⃗`. -/
  | Fa (m : Nat) (Us : List Term) (hU : ∀ U ∈ Us, InB U) : InB (apps (am m) Us)
  /-- (Fx) `c_j a_m U⃗`. -/
  | Fx (j m : Nat) (Us : List Term) (hU : ∀ U ∈ Us, InB U) : InB (apps (c j ⬝ am m) Us)
  /-- (FQa) `Q a_m`. -/
  | FQa (m : Nat) : InB (Q ⬝ am m)
  /-- (FQa2) `Q a_m (a_m (Q a_m)) U⃗`. -/
  | FQa2 (m : Nat) (Us : List Term) (hU : ∀ U ∈ Us, InB U) : InB (apps (Q ⬝ am m ⬝ vm m) Us)
  /-- (FSS) `S S c_j`. -/
  | FSSc (j : Nat) : InB (S ⬝ S ⬝ c j)
  /-- (FSS) `S S a_m`. -/
  | FSSa (m : Nat) : InB (S ⬝ S ⬝ am m)
  /-- (FSS) `S S (Q a_m)`. -/
  | FSSQa (m : Nat) : InB (S ⬝ S ⬝ (Q ⬝ am m))
  /-- (FSS) `S S (a_m (Q a_m))`. -/
  | FSSv (m : Nat) : InB (S ⬝ S ⬝ vm m)
  /-- (FS) `S a_m`. -/
  | FSa (m : Nat) : InB (S ⬝ am m)
  /-- (FS) `S (c_j a_m)`. -/
  | FSca (j m : Nat) : InB (S ⬝ (c j ⬝ am m))
  /-- (FS) `S (a_m (Q a_m))`. -/
  | FSv (m : Nat) : InB (S ⬝ vm m)
  /-- (FS) `S (a_m (a_m (Q a_m)))`. -/
  | FSav (m : Nat) : InB (S ⬝ (am m ⬝ vm m))

theorem allB_nil : ∀ U ∈ ([] : List Term), InB U := fun _ h => nomatch h

theorem allB_cons {U : Term} {Us : List Term} (h : InB U) (hs : ∀ V ∈ Us, InB V) :
    ∀ V ∈ U :: Us, InB V := fun V hV => by
  cases hV with
  | head => exact h
  | tail _ hV => exact hs V hV

theorem InB.ofAm (m : Nat) : InB (am m) := .Fa m [] allB_nil

theorem InB.ofVm (m : Nat) : InB (vm m) := .Fa m [Q ⬝ am m] (allB_cons (.FQa m) allB_nil)

theorem InB.ofBm (m : Nat) : InB (bm m) := .Fx _ m [] allB_nil

/-- Every member of `𝔅` is a pure S-term. -/
theorem InB.pure {t : Term} (h : InB t) : HnfS.PureS t := by
  induction h with
  | pS => exact .S
  | pSS => exact .app .S .S
  | pQ => exact pure_Q
  | pSQ => exact .app .S pure_Q
  | pc j => exact pure_c j
  | Fa m Us _ ih => exact pure_apps (pure_am m) ih
  | Fx j m Us _ ih => exact pure_apps (.app (pure_c j) (pure_am m)) ih
  | FQa m => exact .app pure_Q (pure_am m)
  | FQa2 m Us _ ih =>
    exact pure_apps (.app (.app pure_Q (pure_am m)) (.app (pure_am m) (.app pure_Q (pure_am m)))) ih
  | FSSc j => exact .app (.app .S .S) (pure_c j)
  | FSSa m => exact .app (.app .S .S) (pure_am m)
  | FSSQa m => exact .app (.app .S .S) (.app pure_Q (pure_am m))
  | FSSv m => exact .app (.app .S .S) (.app (pure_am m) (.app pure_Q (pure_am m)))
  | FSa m => exact .app .S (pure_am m)
  | FSca j m => exact .app .S (.app (pure_c j) (pure_am m))
  | FSv m => exact .app .S (.app (pure_am m) (.app pure_Q (pure_am m)))
  | FSav m =>
    exact .app .S (.app (pure_am m) (.app (pure_am m) (.app pure_Q (pure_am m))))

/-! ## Lemma 16(i) -/

/-- Passive arguments of a prefix of a passive list. -/
theorem allB_append_left {Vs Ws : List Term} (h : ∀ U ∈ Vs ++ Ws, InB U) : ∀ U ∈ Vs, InB U :=
  fun U hU => h U (List.mem_append_left Ws hU)

theorem allB_append_last {Vs : List Term} {x : Term} (h : ∀ U ∈ Vs ++ [x], InB U) : InB x :=
  h x (List.mem_append_right Vs (.head _))

/-- **Lemma 16(i).** The function part and the argument of every member of `𝔅` that is an
application are in `𝔅`. -/
theorem InB.fun_arg {t : Term} (h : InB t) : ∀ {f x : Term}, t = f ⬝ x → InB f ∧ InB x := by
  intro f x he
  cases h with
  | pS => cases he
  | pSS => cases he; exact ⟨.pS, .pS⟩
  | pQ => have he : S ⬝ (S ⬝ S) = f ⬝ x := he; cases he; exact ⟨.pS, .pSS⟩
  | pSQ => cases he; exact ⟨.pS, .pQ⟩
  | pc j =>
    cases j with
    | zero => have he : S ⬝ Q ⬝ Q = f ⬝ x := he; cases he; exact ⟨.pSQ, .pQ⟩
    | succ j => have he : Q ⬝ c j = f ⬝ x := he; cases he; exact ⟨.pQ, .pc j⟩
  | Fa m Us hU =>
    rcases apps_eq_app he with ⟨rfl, he⟩ | ⟨Vs, rfl, rfl⟩
    · have he : c (st m).1 ⬝ c (st m).2 = f ⬝ x := he
      cases he; exact ⟨.pc _, .pc _⟩
    · exact ⟨.Fa m Vs (allB_append_left hU), allB_append_last hU⟩
  | Fx j m Us hU =>
    rcases apps_eq_app he with ⟨rfl, he⟩ | ⟨Vs, rfl, rfl⟩
    · cases he; exact ⟨.pc j, .ofAm m⟩
    · exact ⟨.Fx j m Vs (allB_append_left hU), allB_append_last hU⟩
  | FQa m => cases he; exact ⟨.pQ, .ofAm m⟩
  | FQa2 m Us hU =>
    rcases apps_eq_app he with ⟨rfl, he⟩ | ⟨Vs, rfl, rfl⟩
    · cases he; exact ⟨.FQa m, .ofVm m⟩
    · exact ⟨.FQa2 m Vs (allB_append_left hU), allB_append_last hU⟩
  | FSSc j => cases he; exact ⟨.pSS, .pc j⟩
  | FSSa m => cases he; exact ⟨.pSS, .ofAm m⟩
  | FSSQa m => cases he; exact ⟨.pSS, .FQa m⟩
  | FSSv m => cases he; exact ⟨.pSS, .ofVm m⟩
  | FSa m => cases he; exact ⟨.pS, .ofAm m⟩
  | FSca j m => cases he; exact ⟨.pS, .Fx j m [] allB_nil⟩
  | FSv m => cases he; exact ⟨.pS, .ofVm m⟩
  | FSav m => cases he; exact ⟨.pS, .Fa m [vm m] (allB_cons (.ofVm m) allB_nil)⟩

/-! ## The frames on the head runs of members -/

theorem am_succ_of_q {m j n : Nat} (hs : st m = (j + 1, n)) : am (m + 1) = c j ⬝ c n := by
  unfold am aT; rw [st_succ_q hs]

theorem am_succ_of_g {m n : Nat} (hs : st m = (0, n)) : am (m + 1) = c n ⬝ c (n + 1) := by
  unfold am aT; rw [st_succ_g hs]

theorem nargs_c (j : Nat) : nargs (c j) = 2 := by cases j <;> rfl

theorem nargs_am (m : Nat) : nargs (am m) = 3 := by
  show nargs (c _) + 1 = 3; rw [nargs_c]

theorem nargs_cam (j m : Nat) : nargs (c j ⬝ am m) = 3 := by
  show nargs (c j) + 1 = 3; rw [nargs_c]

/-- Every frame on the head run of a member of `𝔅`, with its passive arguments (Lemma 16(ii),
the paper's table as a step-closed invariant). -/
inductive RunFrame : Term → Prop
  | mem {t : Term} : InB t → RunFrame t
  /-- `G c_n ⬝ U⃗ → Q c_n (Q c_n) ⬝ U⃗`. -/
  | a_q (m n : Nat) (hs : st m = (0, n)) (Us : List Term) (hU : ∀ U ∈ Us, InB U) :
      RunFrame (apps (Q ⬝ c n ⬝ (Q ⬝ c n)) Us)
  /-- `S S c a_{m+1} ⬝ U⃗`, `c = c (st (m+1)).2`. -/
  | a_ss (m : Nat) (Us : List Term) (hU : ∀ U ∈ Us, InB U) :
      RunFrame (apps (S ⬝ S ⬝ c (st (m + 1)).2 ⬝ am (m + 1)) Us)
  /-- `S a_{m+1} b_{m+1} ⬝ U⃗`. -/
  | a_hnf (m : Nat) (Us : List Term) (hU : ∀ U ∈ Us, InB U) :
      RunFrame (apps (S ⬝ am (m + 1) ⬝ bm (m + 1)) Us)
  /-- `S S a (c_j a) ⬝ U⃗`, from `c_{j+1} a`. -/
  | x_ss (j m : Nat) (Us : List Term) (hU : ∀ U ∈ Us, InB U) :
      RunFrame (apps (S ⬝ S ⬝ am m ⬝ (c j ⬝ am m)) Us)
  /-- `S (c_j a) (a (c_j a)) ⬝ U⃗`. -/
  | x_hnf (j m : Nat) (Us : List Term) (hU : ∀ U ∈ Us, InB U) :
      RunFrame (apps (S ⬝ (c j ⬝ am m) ⬝ (am m ⬝ (c j ⬝ am m))) Us)
  /-- `Q a (Q a) ⬝ U⃗`, from `G a`. -/
  | g_q (m : Nat) (Us : List Term) (hU : ∀ U ∈ Us, InB U) :
      RunFrame (apps (Q ⬝ am m ⬝ (Q ⬝ am m)) Us)
  /-- `S S (Q a) v ⬝ U⃗`. -/
  | g_ss (m : Nat) (Us : List Term) (hU : ∀ U ∈ Us, InB U) :
      RunFrame (apps (S ⬝ S ⬝ (Q ⬝ am m) ⬝ vm m) Us)
  /-- `S v (Q a v) ⬝ U⃗`. -/
  | g_hnf (m : Nat) (Us : List Term) (hU : ∀ U ∈ Us, InB U) :
      RunFrame (apps (S ⬝ vm m ⬝ (Q ⬝ am m ⬝ vm m)) Us)
  /-- `S S v (a v) ⬝ U⃗`, from `Q a v`. -/
  | q_ss (m : Nat) (Us : List Term) (hU : ∀ U ∈ Us, InB U) :
      RunFrame (apps (S ⬝ S ⬝ vm m ⬝ (am m ⬝ vm m)) Us)
  /-- `S (a v) (v (a v)) ⬝ U⃗`. -/
  | q_hnf (m : Nat) (Us : List Term) (hU : ∀ U ∈ Us, InB U) :
      RunFrame (apps (S ⬝ (am m ⬝ vm m) ⬝ (vm m ⬝ (am m ⬝ vm m))) Us)

/-- Members of `𝔅` that are head normal forms take no head step. -/
theorem InB.step_mem {t t' : Term} (h : InB t) (hs : Step t t') : RunFrame t' := by
  cases h with
  | pS => exact absurd hs (Whnf.no_step .S)
  | pSS => exact absurd hs (Whnf.no_step (.S1 S))
  | pQ => exact absurd hs (Whnf.no_step (.S1 (S ⬝ S)))
  | pSQ => exact absurd hs (Whnf.no_step (.S1 Q))
  | pc j =>
    cases j with
    | zero => exact absurd hs (Whnf.no_step (.S2 Q Q))
    | succ j => exact absurd hs (Whnf.no_step (.S2 (S ⬝ S) (c j)))
  | FQa m => exact absurd hs (Whnf.no_step (.S2 (S ⬝ S) (am m)))
  | FSSc j => exact absurd hs (Whnf.no_step (.S2 S _))
  | FSSa m => exact absurd hs (Whnf.no_step (.S2 S _))
  | FSSQa m => exact absurd hs (Whnf.no_step (.S2 S _))
  | FSSv m => exact absurd hs (Whnf.no_step (.S2 S _))
  | FSa m => exact absurd hs (Whnf.no_step (.S1 _))
  | FSca j m => exact absurd hs (Whnf.no_step (.S1 _))
  | FSv m => exact absurd hs (Whnf.no_step (.S1 _))
  | FSav m => exact absurd hs (Whnf.no_step (.S1 _))
  | Fa m Us hU =>
    rcases hst : st m with ⟨i, n⟩
    cases i with
    | zero =>
      rw [am_of_g hst] at hs
      rw [step_apps_det (step_G (c n)) hs]
      exact .a_q m n hst Us hU
    | succ j =>
      rw [am_of_q hst] at hs
      rw [step_apps_det (step_Q (c j) (c n)) hs]
      have e : S ⬝ S ⬝ c n ⬝ (c j ⬝ c n) = S ⬝ S ⬝ c (st (m + 1)).2 ⬝ am (m + 1) := by
        rw [am_succ_of_q hst, st_succ_q hst]
      rw [e]
      exact .a_ss m Us hU
  | Fx j m Us hU =>
    cases j with
    | zero =>
      rw [step_apps_det (T := c 0 ⬝ am m) (step_G (am m)) hs]
      exact .g_q m Us hU
    | succ j =>
      rw [step_apps_det (T := c (j + 1) ⬝ am m) (step_Q (c j) (am m)) hs]
      exact .x_ss j m Us hU
  | FQa2 m Us hU =>
    rw [step_apps_det (step_Q (am m) (vm m)) hs]
    exact .q_ss m Us hU

/-- `RunFrame` is closed under head steps. -/
theorem RunFrame.step {t t' : Term} (h : RunFrame t) (hs : Step t t') : RunFrame t' := by
  cases h with
  | mem hb => exact hb.step_mem hs
  | a_q m n hst Us hU =>
    rw [step_apps_det (step_Q (c n) (Q ⬝ c n)) hs]
    have e : S ⬝ S ⬝ (Q ⬝ c n) ⬝ (c n ⬝ (Q ⬝ c n)) =
        S ⬝ S ⬝ c (st (m + 1)).2 ⬝ am (m + 1) := by
      rw [am_succ_of_g hst, st_succ_g hst]; rfl
    rw [e]
    exact .a_ss m Us hU
  | a_ss m Us hU =>
    rw [step_apps_det (step_SS _ _) hs]
    exact .a_hnf m Us hU
  | a_hnf m Us hU =>
    obtain ⟨U, Vs, rfl, rfl⟩ := step_apps_S2 hs
    exact .mem (.Fa (m + 1) (U :: bm (m + 1) ⬝ U :: Vs)
      (allB_cons (hU U (.head _)) (allB_cons (.Fx _ (m + 1) [U] (allB_cons (hU U (.head _))
        allB_nil)) (fun V hV => hU V (.tail _ hV)))))
  | x_ss j m Us hU =>
    rw [step_apps_det (step_SS _ _) hs]
    exact .x_hnf j m Us hU
  | x_hnf j m Us hU =>
    obtain ⟨U, Vs, rfl, rfl⟩ := step_apps_S2 hs
    have hU' : InB U := hU U (.head _)
    exact .mem (.Fx j m (U :: am m ⬝ (c j ⬝ am m) ⬝ U :: Vs)
      (allB_cons hU' (allB_cons (.Fa m [c j ⬝ am m, U]
        (allB_cons (.Fx j m [] allB_nil) (allB_cons hU' allB_nil)))
        (fun V hV => hU V (.tail _ hV)))))
  | g_q m Us hU =>
    rw [step_apps_det (step_Q (am m) (Q ⬝ am m)) hs]
    exact .g_ss m Us hU
  | g_ss m Us hU =>
    rw [step_apps_det (step_SS _ _) hs]
    exact .g_hnf m Us hU
  | g_hnf m Us hU =>
    obtain ⟨U, Vs, rfl, rfl⟩ := step_apps_S2 hs
    have hU' : InB U := hU U (.head _)
    exact .mem (.Fa m (Q ⬝ am m :: U :: Q ⬝ am m ⬝ vm m ⬝ U :: Vs)
      (allB_cons (.FQa m) (allB_cons hU' (allB_cons (.FQa2 m [U] (allB_cons hU' allB_nil))
        (fun V hV => hU V (.tail _ hV))))))
  | q_ss m Us hU =>
    rw [step_apps_det (step_SS _ _) hs]
    exact .q_hnf m Us hU
  | q_hnf m Us hU =>
    obtain ⟨U, Vs, rfl, rfl⟩ := step_apps_S2 hs
    have hU' : InB U := hU U (.head _)
    exact .mem (.Fa m (vm m :: U :: vm m ⬝ (am m ⬝ vm m) ⬝ U :: Vs)
      (allB_cons (.ofVm m) (allB_cons hU' (allB_cons
        (.Fa m [Q ⬝ am m, am m ⬝ vm m, U] (allB_cons (.FQa m)
          (allB_cons (.Fa m [vm m] (allB_cons (.ofVm m) allB_nil)) (allB_cons hU' allB_nil))))
        (fun V hV => hU V (.tail _ hV))))))

/-- `RunFrame` is closed under head runs. -/
theorem RunFrame.steps {t u : Term} (hr : Steps t u) (h : RunFrame t) : RunFrame u := by
  induction hr with
  | refl => exact h
  | step hs _ ih => exact ih (h.step hs)

theorem ne_S3_of_nargs {t x y z : Term} (hn : nargs t ≠ 3) : t ≠ S ⬝ x ⬝ y ⬝ z :=
  fun h => hn (h ▸ rfl)

/-- Three-item frames of members of `𝔅`. -/
theorem InB.three {t x y z : Term} (h : InB t) (he : t = S ⬝ x ⬝ y ⬝ z) :
    InB (x ⬝ z) ∧ InB (y ⬝ z) := by
  cases h with
  | pS => exact absurd he (ne_S3_of_nargs (by decide))
  | pSS => exact absurd he (ne_S3_of_nargs (by decide))
  | pQ => exact absurd he (ne_S3_of_nargs (by decide))
  | pSQ => exact absurd he (ne_S3_of_nargs (by decide))
  | pc j => exact absurd he (ne_S3_of_nargs (by rw [nargs_c]; decide))
  | FQa m => exact absurd he (ne_S3_of_nargs (show (2 : Nat) ≠ 3 by decide))
  | FSSc j => exact absurd he (ne_S3_of_nargs (show (2 : Nat) ≠ 3 by decide))
  | FSSa m => exact absurd he (ne_S3_of_nargs (show (2 : Nat) ≠ 3 by decide))
  | FSSQa m => exact absurd he (ne_S3_of_nargs (show (2 : Nat) ≠ 3 by decide))
  | FSSv m => exact absurd he (ne_S3_of_nargs (show (2 : Nat) ≠ 3 by decide))
  | FSa m => exact absurd he (ne_S3_of_nargs (show (1 : Nat) ≠ 3 by decide))
  | FSca j m => exact absurd he (ne_S3_of_nargs (show (1 : Nat) ≠ 3 by decide))
  | FSv m => exact absurd he (ne_S3_of_nargs (show (1 : Nat) ≠ 3 by decide))
  | FSav m => exact absurd he (ne_S3_of_nargs (show (1 : Nat) ≠ 3 by decide))
  | Fa m Us hU =>
    obtain ⟨rfl, he⟩ := apps_eq3 (nargs_am m) he
    rcases hst : st m with ⟨i, n⟩
    cases i with
    | zero =>
      rw [am_of_g hst] at he
      obtain ⟨rfl, rfl, rfl⟩ := S3_inj (p := Q) he
      exact ⟨.pc (n + 1), .pc (n + 1)⟩
    | succ j =>
      rw [am_of_q hst] at he
      obtain ⟨rfl, rfl, rfl⟩ := S3_inj (p := S ⬝ S) he
      refine ⟨.FSSc n, ?_⟩
      rw [← am_succ_of_q hst]; exact .ofAm (m + 1)
  | Fx j m Us hU =>
    obtain ⟨rfl, he⟩ := apps_eq3 (nargs_cam j m) he
    cases j with
    | zero =>
      obtain ⟨rfl, rfl, rfl⟩ := S3_inj (p := Q) he
      exact ⟨.FQa m, .FQa m⟩
    | succ j =>
      obtain ⟨rfl, rfl, rfl⟩ := S3_inj (p := S ⬝ S) he
      exact ⟨.FSSa m, .Fx j m [] allB_nil⟩
  | FQa2 m Us hU =>
    obtain ⟨rfl, he⟩ := apps_eq3 (T := Q ⬝ am m ⬝ vm m) rfl he
    obtain ⟨rfl, rfl, rfl⟩ := S3_inj (p := S ⬝ S) he
    exact ⟨.FSSv m, .Fa m [vm m] (allB_cons (.ofVm m) allB_nil)⟩

/-- Three-item frames on the head runs of members of `𝔅`. -/
theorem RunFrame.three {t x y z : Term} (h : RunFrame t) (he : t = S ⬝ x ⬝ y ⬝ z) :
    InB (x ⬝ z) ∧ InB (y ⬝ z) := by
  cases h with
  | mem hb => exact hb.three he
  | a_q m n hst Us hU =>
    obtain ⟨rfl, he⟩ := apps_eq3 (T := Q ⬝ c n ⬝ (Q ⬝ c n)) rfl he
    obtain ⟨rfl, rfl, rfl⟩ := S3_inj (p := S ⬝ S) he
    refine ⟨.FSSc (n + 1), ?_⟩
    have e : c n ⬝ (Q ⬝ c n) = am (m + 1) := (am_succ_of_g hst).symm
    rw [e]; exact .ofAm (m + 1)
  | a_ss m Us hU =>
    obtain ⟨rfl, he⟩ := apps_eq3 (T := S ⬝ S ⬝ c (st (m + 1)).2 ⬝ am (m + 1)) rfl he
    obtain ⟨rfl, rfl, rfl⟩ := S3_inj he
    exact ⟨.FSa (m + 1), .Fx _ (m + 1) [] allB_nil⟩
  | a_hnf m Us hU =>
    obtain ⟨rfl, rfl, rfl⟩ := apps_S2_eq3 he
    have hz : InB z := hU z (.head _)
    exact ⟨.Fa (m + 1) [z] (allB_cons hz allB_nil), .Fx _ (m + 1) [z] (allB_cons hz allB_nil)⟩
  | x_ss j m Us hU =>
    obtain ⟨rfl, he⟩ := apps_eq3 (T := S ⬝ S ⬝ am m ⬝ (c j ⬝ am m)) rfl he
    obtain ⟨rfl, rfl, rfl⟩ := S3_inj he
    exact ⟨.FSca j m, .Fa m [c j ⬝ am m] (allB_cons (.Fx j m [] allB_nil) allB_nil)⟩
  | x_hnf j m Us hU =>
    obtain ⟨rfl, rfl, rfl⟩ := apps_S2_eq3 he
    have hz : InB z := hU z (.head _)
    exact ⟨.Fx j m [z] (allB_cons hz allB_nil),
      .Fa m [c j ⬝ am m, z] (allB_cons (.Fx j m [] allB_nil) (allB_cons hz allB_nil))⟩
  | g_q m Us hU =>
    obtain ⟨rfl, he⟩ := apps_eq3 (T := Q ⬝ am m ⬝ (Q ⬝ am m)) rfl he
    obtain ⟨rfl, rfl, rfl⟩ := S3_inj (p := S ⬝ S) he
    exact ⟨.FSSQa m, .ofVm m⟩
  | g_ss m Us hU =>
    obtain ⟨rfl, he⟩ := apps_eq3 (T := S ⬝ S ⬝ (Q ⬝ am m) ⬝ vm m) rfl he
    obtain ⟨rfl, rfl, rfl⟩ := S3_inj he
    exact ⟨.FSv m, .FQa2 m [] allB_nil⟩
  | g_hnf m Us hU =>
    obtain ⟨rfl, rfl, rfl⟩ := apps_S2_eq3 he
    have hz : InB z := hU z (.head _)
    exact ⟨.Fa m [Q ⬝ am m, z] (allB_cons (.FQa m) (allB_cons hz allB_nil)),
      .FQa2 m [z] (allB_cons hz allB_nil)⟩
  | q_ss m Us hU =>
    obtain ⟨rfl, he⟩ := apps_eq3 (T := S ⬝ S ⬝ vm m ⬝ (am m ⬝ vm m)) rfl he
    obtain ⟨rfl, rfl, rfl⟩ := S3_inj he
    exact ⟨.FSav m, .Fa m [Q ⬝ am m, am m ⬝ vm m]
      (allB_cons (.FQa m) (allB_cons (.Fa m [vm m] (allB_cons (.ofVm m) allB_nil)) allB_nil))⟩
  | q_hnf m Us hU =>
    obtain ⟨rfl, rfl, rfl⟩ := apps_S2_eq3 he
    have hz : InB z := hU z (.head _)
    exact ⟨.Fa m [vm m, z] (allB_cons (.ofVm m) (allB_cons hz allB_nil)),
      .Fa m [Q ⬝ am m, am m ⬝ vm m, z] (allB_cons (.FQa m)
        (allB_cons (.Fa m [vm m] (allB_cons (.ofVm m) allB_nil)) (allB_cons hz allB_nil)))⟩

/-- **Lemma 16(ii).** For every `β ∈ 𝔅` and every frame `S x₀ y₀ z₀` with exactly three items
on the head run of `β`, the terms `x₀ z₀` and `y₀ z₀` are in `𝔅`. -/
theorem lemma16_ii {β x y z : Term} (hb : InB β) (hr : Steps β (S ⬝ x ⬝ y ⬝ z)) :
    InB (x ⬝ z) ∧ InB (y ⬝ z) :=
  (RunFrame.steps hr (.mem hb)).three rfl

/-- **Lemma 16(i)**, restated: `InB (f ⬝ x) → InB f ∧ InB x`. -/
theorem lemma16_i {f x : Term} (h : InB (f ⬝ x)) : InB f ∧ InB x := h.fun_arg rfl

end S11
