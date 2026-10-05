import Ski.Circuit.CompPred
import Ski.ComposedText
open Term

/-!
# A poke whose event is an entropy reply, its bits private

Avon's pier answers a kernel's request for entropy with the event
`[0 [id bits]]`, `bits` 128 Scott Booleans in a list (avon
`docs/DESIGN.md` §9.1, SKIjack `SPEC.md` §4.1).  Here that poke becomes a
predicate statement (`Ski/Predicate.lean`) whose private bits are the
reply's: the verifier `entropyV n` takes the public `x = [k [id chk]]` and
the circuit's `n` literal bits, builds the event, pokes the kernel `k` with
it, and hands the result `[effects k']` to the public check `chk`.

- **The encodings are Avon's** (`src/pier.c`, `reply_event`): pairs
  `S (S I (K a)) (K b)` (`pairT`), Booleans `K` and `K I` (`boolT`), the
  list `cons h t = K (pair h t)`, `nil = K` (`listT`), the tag `0` as `K`,
  and the poke `(4@k) k ev` with `4@k = hd (hd k)`, `hd = S I (K K)`
  (`pokeT`).
- **The circuit's bits are a comb** (`boolsT`); `convT n` turns a comb of
  `n` into Avon's list, one closed term per length, each built from the
  last, so that its size grows linearly (`convT_red`).
- **`entropyV_red`**: `entropyV n x (boolsT bs)` weakly reduces to
  `chk (pokeT k (replyT id (listT bs)))`, so by Church–Rosser one accepts
  exactly when the other does (`entropyV_iff`).
- **`entropyExport_sound`**: an accepted proof of the predicate circuit for
  `entropyV n` and `x` has `n` bits `bs` in its memory on which `chk`
  accepts the poke of `k` with the reply `[0 [id (listT bs)]]`.

The bits stay private as every composed statement's witness does: they are
the circuit's slot cells, and `Circuit.comp_zk` (with `transcript_zk`)
hides them for any statement, this one included.
-/

namespace Entropy

open CompM Compose

/-- `hd = S I (K K)`: `hd p = p K`, a pair's first. -/
def hdT : Term := S ⬝ I ⬝ (K ⬝ K)

/-- `tl = S I (K (K I))`: `tl p = p (K I)`, a pair's second. -/
def tlT : Term := S ⬝ I ⬝ (K ⬝ (K ⬝ I))

/-- `nil = K`. -/
def nilT : Term := K

/-- `cons h t = K (pair h t)`: `cons h t n c = c h t`. -/
def consT (h t : Term) : Term := K ⬝ pairT h t

/-- A list of Booleans, as Avon's pier builds a reply's bits. -/
def listT : List Bool → Term
  | [] => nilT
  | b :: r => consT (boolT b) (listT r)

/-- The reply event `[0 [id bits]]`, `0` the numeral `K`. -/
def replyT (id bits : Term) : Term := pairT K (pairT id bits)

/-- The poke: arm 4 of the kernel, pulled as Nock 9 does, `(4@k) k ev`. -/
def pokeT (k ev : Term) : Term := hdT ⬝ (hdT ⬝ k) ⬝ k ⬝ ev

theorem hd_red (a b : Term) : WSteps (hdT ⬝ pairT a b) a :=
  .step (.S _ _ _) <| .step (.left _ (.I _)) <| .step (.right _ (.K _ _)) <|
  .step (.S _ _ _) <| .step (.left _ (.S _ _ _)) <| .step (.left _ (.left _ (.I _))) <|
  .step (.K _ _) <| .step (.K _ _) (.refl _)

theorem tl_red (a b : Term) : WSteps (tlT ⬝ pairT a b) b :=
  .step (.S _ _ _) <| .step (.left _ (.I _)) <| .step (.right _ (.K _ _)) <|
  .step (.S _ _ _) <| .step (.left _ (.S _ _ _)) <| .step (.left _ (.left _ (.I _))) <|
  .step (.left _ (.K _ _)) <| .step (.I _) <| .step (.K _ _) (.refl _)

theorem pairT_cong {a a' b b' : Term} (ha : WSteps a a') (hb : WSteps b b') :
    WSteps (pairT a b) (pairT a' b') :=
  WSteps.app (WSteps.right _ (WSteps.right _ (WSteps.right _ ha))) (WSteps.right _ hb)

theorem consT_cong {h h' t t' : Term} (hh : WSteps h h') (ht : WSteps t t') :
    WSteps (consT h t) (consT h' t') :=
  WSteps.right _ (pairT_cong hh ht)

/-- `[a b]` as an open term. -/
def pairO (a b : OTerm) : OTerm := .S ⬝ₒ (.S ⬝ₒ .I ⬝ₒ (.K ⬝ₒ a)) ⬝ₒ (.K ⬝ₒ b)

theorem pairO_close (σ : Nat → Term) (a b : OTerm) : (pairO a b).close σ = pairT (a.close σ) (b.close σ) :=
  rfl

/-- **From the circuit's comb of `n` bits to Avon's list**: `convT 1 B =
    cons B nil`, `convT (n + 1) B = cons (hd B) (convT n (tl B))`. -/
def convT : Nat → Term
  | 0 => K
  | 1 => lam [0] (.K ⬝ₒ pairO (.var 0) .K)
  | n + 2 => lam [0] (.K ⬝ₒ pairO (hdT.toO ⬝ₒ .var 0) ((convT (n + 1)).toO ⬝ₒ (tlT.toO ⬝ₒ .var 0)))

theorem convT_one (B : Term) : WSteps (convT 1 ⬝ B) (consT B nilT) := by
  have h := lam_beta [0] (.K ⬝ₒ pairO (.var 0) .K) [B] rfl
  exact h

theorem convT_succ (n : Nat) (B : Term) :
    WSteps (convT (n + 2) ⬝ B) (consT (hdT ⬝ B) (convT (n + 1) ⬝ (tlT ⬝ B))) := by
  have h := lam_beta [0] (.K ⬝ₒ pairO (hdT.toO ⬝ₒ .var 0) ((convT (n + 1)).toO ⬝ₒ (tlT.toO ⬝ₒ .var 0))) [B] rfl
  have e : (OTerm.K ⬝ₒ pairO (hdT.toO ⬝ₒ .var 0) ((convT (n + 1)).toO ⬝ₒ (tlT.toO ⬝ₒ .var 0))).close
      (overrideC (fun _ => I) [0] [B]) = consT (hdT ⬝ B) (convT (n + 1) ⬝ (tlT ⬝ B)) := by
    show K ⬝ pairT (hdT.toO.close _ ⬝ B) ((convT (n + 1)).toO.close _ ⬝ (tlT.toO.close _ ⬝ B)) = _
    rw [close_toO, close_toO, close_toO]; rfl
  rw [e] at h
  exact h

/-- **The comb of `bs` becomes Avon's list of `bs`.** -/
theorem convT_red : ∀ (bs : List Bool), 0 < bs.length → WSteps (convT bs.length ⬝ boolsT bs) (listT bs)
  | [b], _ => convT_one (boolT b)
  | b :: c :: r, _ => by
    show WSteps (convT (r.length + 2) ⬝ pairT (boolT b) (boolsT (c :: r))) (consT (boolT b) (listT (c :: r)))
    refine (convT_succ r.length _).trans (consT_cong (hd_red _ _) ?_)
    exact (WSteps.right _ (tl_red _ _)).trans (convT_red (c :: r) (Nat.succ_pos _))

/-- The public input: `[k [id chk]]`. -/
def xOf (k id chk : Term) : Term := pairT k (pairT id chk)

/-- The verifier's body over `x` (0) and the bits (1). -/
def entropyBody (n : Nat) : OTerm :=
  (tlT.toO ⬝ₒ (tlT.toO ⬝ₒ .var 0)) ⬝ₒ
    (hdT.toO ⬝ₒ (hdT.toO ⬝ₒ (hdT.toO ⬝ₒ .var 0)) ⬝ₒ (hdT.toO ⬝ₒ .var 0) ⬝ₒ
      pairO .K (pairO (hdT.toO ⬝ₒ (tlT.toO ⬝ₒ .var 0)) ((convT n).toO ⬝ₒ .var 1)))

/-- **The verifier**: `λ x B. chk (poke k [0 [id (convT n B)]])`, the
    kernel, the request's id and the check read from `x`. -/
def entropyV (n : Nat) : Term := lam [0, 1] (entropyBody n)

/-- **The verifier pokes the kernel with the reply on the bits.** -/
theorem entropyV_red (k id chk : Term) (bs : List Bool) (hn : 0 < bs.length) :
    WSteps (entropyV bs.length ⬝ xOf k id chk ⬝ boolsT bs) (chk ⬝ pokeT k (replyT id (listT bs))) := by
  have h := lam_beta [0, 1] (entropyBody bs.length) [xOf k id chk, boolsT bs] rfl
  have e : (entropyBody bs.length).close (overrideC (fun _ => I) [0, 1] [xOf k id chk, boolsT bs]) =
      (tlT ⬝ (tlT ⬝ xOf k id chk)) ⬝
        (hdT ⬝ (hdT ⬝ (hdT ⬝ xOf k id chk)) ⬝ (hdT ⬝ xOf k id chk) ⬝
          pairT K (pairT (hdT ⬝ (tlT ⬝ xOf k id chk)) (convT bs.length ⬝ boolsT bs))) := by
    simp only [entropyBody, OTerm.close, pairO_close, close_toO]; rfl
  rw [e] at h
  refine h.trans ?_
  have hk : WSteps (hdT ⬝ xOf k id chk) k := hd_red _ _
  have hr : WSteps (tlT ⬝ xOf k id chk) (pairT id chk) := tl_red _ _
  have hid : WSteps (hdT ⬝ (tlT ⬝ xOf k id chk)) id := (WSteps.right _ hr).trans (hd_red _ _)
  have hc : WSteps (tlT ⬝ (tlT ⬝ xOf k id chk)) chk := (WSteps.right _ hr).trans (tl_red _ _)
  refine WSteps.app hc ?_
  refine WSteps.app (WSteps.app (WSteps.right _ (WSteps.right _ hk)) hk) ?_
  exact pairT_cong (.refl K) (pairT_cong hid (convT_red bs hn))

/-- **The verifier accepts exactly when the check accepts the poke.** -/
theorem entropyV_iff (k id chk : Term) (bs : List Bool) (hn : 0 < bs.length) :
    Eval (entropyV bs.length ⬝ xOf k id chk ⬝ boolsT bs) K ↔ Eval (chk ⬝ pokeT k (replyT id (listT bs))) K := by
  rw [eval_K_iff, eval_K_iff, wsteps_K_iff (entropyV_red k id chk bs hn)]

theorem entropyV_iff' (k id chk : Term) (bs : List Bool) {n : Nat} (hl : bs.length = n) (hn : 0 < n) :
    Eval (entropyV n ⬝ xOf k id chk ⬝ boolsT bs) K ↔ Eval (chk ⬝ pokeT k (replyT id (listT bs))) K := by
  subst hl; exact entropyV_iff k id chk bs hn

/-- The statement: `n` literal bits make `entropyV n` accept `x`. -/
def entropyStmt (k id chk : Term) (n : Nat) : ComposedText.CStmt := .pred (entropyV n) (xOf k id chk) n

end Entropy

namespace Circuit

open B Air Compose CompM Stmt Mach Wit Entropy

/-- **Soundness of a proved entropy poke**: an accepted proof of the
    predicate circuit for `entropyV n` and `[k [id chk]]` has `n` bits
    `bs` in its memory, literal Booleans, on which `chk` accepts the poke
    of the kernel `k` with the reply `[0 [id (listT bs)]]`. -/
theorem entropyExport_sound {k id chk : Term} {n W : Nat} (hn : 0 < n) {Rs : List AirD} {ts : List Table}
    (hs : sameAirsB Rs (predAirs (entropyV n) (xOf k id chk) n W) = true) (h : AcceptedP Rs ts) :
    ∃ bs : List Bool, bs.length = n ∧ Eval (chk ⬝ pokeT k (replyT id (listT bs))) K := by
  obtain ⟨_, _, _, _, _, _, hl, hP⟩ := predExport_sound hn hs h
  exact ⟨_, hl, (entropyV_iff' k id chk _ hl hn).1 hP⟩

/-- **A checked table proves the entropy poke**, as `checkPred_sound`. -/
theorem checkEntropy_sound {k id chk : Term} {n W : Nat} (hn : 0 < n) {A : Array Cell} {ends : Array Nat}
    {R : Array Air.Row} (h : checkC (combBT n) W [predStmt (entropyV n) (xOf k id chk)] A ends R = true) :
    ∃ bs : List Bool, bs.length = n ∧ Eval (chk ⬝ pokeT k (replyT id (listT bs))) K := by
  have hP := checkPred_sound hn h
  have hl := slotBits_length (bitsOf A) 0 n
  exact ⟨_, hl, (entropyV_iff' k id chk _ hl hn).1 hP⟩

end Circuit
