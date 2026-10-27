-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordLiftFlat
import BeaconcryptCore.Computational.PqxdhRecordLiftHiding

/-!
# Left-or-right secrecy of the record-ideal world: `LorStatement` (items 4 and 5, world facts)

**Statement.** `idealRecords_lor` proves `PqxdhRecordLiftIdeal.LorStatement` as defined: in mode P, for every environment, adversary, public decision and public eligibility on `PublicHiding` (no `Frame` or budget premise), the probability in `idealRecords` that the run is eligible, every admitted test was on a handle holding a hidden slot and the decision equals the test bit is exactly half the probability that the run is eligible and every admitted test was on a hidden handle.

**Proof.** First (`law_zeros`), both events depend on a view only through its hiding projection (`lorGuess_hiding`, `lorEligible_hiding`, from `testsHidden_hiding`, `testBit_hidingView` and `PqxdhRecordLiftIdeal.admittedTest_view`), so by `PqxdhRecordLiftHiding.hiding_replace` their laws in `idealRecords` equal their laws in the random-ciphertext world with every hidden seal plaintext zeroed. Second (`world_couple`), the zeroed world is coupled with itself by a `PqxdhRecordLiftSwap.Swap` coupling on the flattened world of `PqxdhRecordLiftFlat`: the native coin that draws the first admitted test's bit is relabelled by `Fin.rev`, so the bit is negated (`fullImpl_test_first`, `decide_rev`), and every other coin is drawn equally. Queries that send no test message commute with negating the ledger's bit (`ledger_flip_forward`, `ledger_flip_fresh`, `ledger_flip_refused`, `commute_couple`); a test that sends the other message on a handle without a caller-known kernel is the same computation (`send_couple`, from `PqxdhRecordLiftFlat.nativeImpl_send_zeros`); a test on a caller-known handle is an escape (`Escaped`), kept by every later query (`escaped_keep`) because the transcript only grows and caller-known kernels persist, and in an escaped run not every admitted test was hidden (`lorGuess_escaped`). On related final states the win of the decision on one side equals the win of the negated decision on the other (`lorGuess_flip`). Hence the two wins have the same law (`PqxdhRecordLiftSwap.Swap.evalDist_map`); they exclude each other and their disjunction is eligibility with all tests hidden (`lorEligible_split`, `evalDist_or`), so each is half of it (`lor_zeros`).

**Contracts.** No theorem of this module has an assumption or contract hypothesis, and no security game enters; contracts reached are listed per theorem in `doc/impl/record-lift-facts.md`. New Claude work.
-/

open OracleComp OracleSpec ENNReal CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhRecordLiftLor
open PqxdhRecordLiftInterface PqxdhRecordLiftIdeal PqxdhRecordLiftFlat PqxdhRecordLiftSwap
open PqxdhDeploymentInterface (Mode ModeSpec FreshBounds Spec FullSpec Handle asModeO)
open PqxdhDeploymentSecrecy (Ledger)
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftWorldCompiler (Label)
variable {n : Nat} {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response E X : Type}

/-! ### The bit swap on ledgers -/

/-- The ledger with its test bit negated. -/
def flipLedger (ledger : Ledger) : Ledger :=
  { ledger with test := ledger.test.map fun test => { test with bit := !test.bit } }

/-- Recording an entry commutes with the bit swap. -/
theorem flipLedger_record (ledger : Ledger) (query : PqxdhDeploymentInterface.Query)
    (reply : FullSpec.Range query) : flipLedger (ledger.record query reply) = (flipLedger ledger).record query reply :=
  rfl

/-- A forwarded query commutes with the bit swap. -/
theorem ledger_flip_forward (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKid : Std.U64)
    (bounds : FreshBounds) (query : Spec.Domain) (ledger : Ledger) :
    (PqxdhDeploymentSecrecy.ledgerImpl crypto codec serverKid bounds (.inl query)).run (flipLedger ledger) =
      (fun p => (p.1, flipLedger p.2)) <$>
        (PqxdhDeploymentSecrecy.ledgerImpl crypto codec serverKid bounds (.inl query)).run ledger := by
  rw [PqxdhDeploymentSecrecy.ledgerImpl_forward, PqxdhDeploymentSecrecy.ledgerImpl_forward, Functor.map_map]
  rfl

/-- A fresh message commutes with the bit swap. -/
theorem ledger_flip_fresh (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKid : Std.U64)
    (bounds : FreshBounds) (handle : Handle) (length : Nat) (ledger : Ledger) :
    (PqxdhDeploymentSecrecy.ledgerImpl crypto codec serverKid bounds (.inr (.fresh handle length))).run
        (flipLedger ledger) =
      (fun p => (p.1, flipLedger p.2)) <$>
        (PqxdhDeploymentSecrecy.ledgerImpl crypto codec serverKid bounds (.inr (.fresh handle length))).run ledger := by
  simp only [PqxdhDeploymentSecrecy.ledgerImpl, StateT.run]
  split
  · simp only [map_bind, map_pure]
    rfl
  · simp only [map_pure]
    rfl


/-- A test the ledger refuses commutes with the bit swap: inadmissible messages, or a handle outside the test session. -/
theorem ledger_flip_refused (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKid : Std.U64)
    (bounds : FreshBounds) (handle : Handle) (left right : Pqxdh.Bytes) (ledger : Ledger)
    (refused : ¬PqxdhDeploymentSecrecy.Admissible left right ∨ ∃ session, ledger.test = some session ∧
      ¬PqxdhDeploymentSecrecy.SameSession crypto codec serverKid ledger.transcript session.first handle) :
    (PqxdhDeploymentSecrecy.ledgerImpl crypto codec serverKid bounds (.inr (.test handle left right))).run
        (flipLedger ledger) =
      (fun p => (p.1, flipLedger p.2)) <$>
        (PqxdhDeploymentSecrecy.ledgerImpl crypto codec serverKid bounds (.inr (.test handle left right))).run
          ledger := by
  simp only [PqxdhDeploymentSecrecy.ledgerImpl, StateT.run]
  rcases refused with inadmissible | ⟨session, hsession, other⟩
  · simp only [inadmissible, ↓reduceIte, map_pure]
    rfl
  · have flipped : (flipLedger ledger).test = some { session with bit := !session.bit } := by
      simp only [flipLedger, hsession, Option.map_some]
    by_cases admissible : PqxdhDeploymentSecrecy.Admissible left right
    · simp only [admissible, ↓reduceIte, hsession, flipped, other, map_pure]
      have other' : ¬PqxdhDeploymentSecrecy.SameSession crypto codec serverKid (flipLedger ledger).transcript
          { session with bit := !session.bit }.first handle := other
      simp only [other', ↓reduceIte]
      rfl
    · simp only [admissible, ↓reduceIte, map_pure]
      rfl

/-! ### Related and escaped states -/

/-- Full states of the two coupled runs: the same native state, ledgers that differ only in the test bit, and the ledger invariant. -/
def Related (s t : Ledger × NativeState n E) : Prop :=
  t.2 = s.2 ∧ t.1 = flipLedger s.1 ∧ LedgerInv s.1

/-- The run has escaped: the transcript holds a test that the ledger admitted on a handle that now holds a caller-known kernel. -/
def Escaped (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKid : Std.U64)
    (s : Ledger × NativeState n E) : Prop :=
  ∃ before entry after handle left right, s.1.transcript = before ++ entry :: after ∧
    entry.query = .inr (.test handle left right) ∧ AdmittedTest crypto codec serverKid before handle left right ∧
    KnownAt s.2.1.2 handle

/-- Every adversary query keeps an escape: the transcript only grows and caller-known kernels persist. -/
theorem escaped_keep (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (query : FullSpec.Domain)
    (s : Ledger × NativeState n E) (escaped : Escaped setup.source.crypto codec serverKid s) :
    ∀ p ∈ support ((fullImpl modes replace setup codec route env serverKid bounds query).run s),
      Escaped setup.source.crypto codec serverKid p.2 := by
  obtain ⟨ledger, state⟩ := s
  obtain ⟨before, entry, after, handle, left, right, htranscript, hquery, hadmitted, hknown⟩ := escaped
  intro p hp
  rw [fullImpl_run, support_map] at hp
  obtain ⟨z, hz, rfl⟩ := hp
  obtain ⟨reply, happend⟩ := ledger_append setup.source.crypto codec serverKid bounds query ledger z.1
    (support_run_fst _ _ _ z hz)
  refine ⟨before, entry, after ++ [⟨query, reply⟩], handle, left, right, ?_, hquery, hadmitted, ?_⟩
  · dsimp only at htranscript ⊢
    rw [happend, htranscript]
    simp only [List.append_assoc, List.cons_append]
  · exact support_keep_oracle (nativeImpl modes replace setup codec route env) (fun ns => KnownAt ns.1.2 handle)
      (fun q ns known => nativeImpl_known modes replace setup codec route env handle q ns known) _ state hknown z hz


/-! ### One coupled adversary query -/

/-- A query whose ledger step commutes with the bit swap is coupled with itself, with related states. -/
theorem commute_couple (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (query : FullSpec.Domain) (ledger : Ledger)
    (state : NativeState n E) (inv : LedgerInv ledger)
    (commute : (PqxdhDeploymentSecrecy.ledgerImpl setup.source.crypto codec serverKid bounds query).run
        (flipLedger ledger) = (fun p => (p.1, flipLedger p.2)) <$>
          (PqxdhDeploymentSecrecy.ledgerImpl setup.source.crypto codec serverKid bounds query).run ledger) :
    Swap (SimRel Related (Escaped setup.source.crypto codec serverKid) (Escaped setup.source.crypto codec serverKid))
      ((fullImpl modes replace setup codec route env serverKid bounds query).run (ledger, state))
      ((fullImpl modes replace setup codec route env serverKid bounds query).run (flipLedger ledger, state)) := by
  rw [fullImpl_run, fullImpl_run, commute, simulateQ_map, StateT.run_map, Functor.map_map]
  refine (Swap.refl_support ((simulateQ (nativeImpl modes replace setup codec route env)
    ((PqxdhDeploymentSecrecy.ledgerImpl setup.source.crypto codec serverKid bounds query).run ledger)).run state)
    (R := fun a b => a = b ∧ a ∈ support ((simulateQ (nativeImpl modes replace setup codec route env)
      ((PqxdhDeploymentSecrecy.ledgerImpl setup.source.crypto codec serverKid bounds query).run ledger)).run state))
    fun a ha => ⟨rfl, ha⟩).map ?_
  rintro a b ⟨rfl, ha⟩
  exact Or.inl ⟨rfl, rfl, rfl,
    ledger_inv setup.source.crypto codec serverKid bounds query ledger inv a.1 (support_run_fst _ _ _ a ha)⟩

/-- The transcript of a ledger holds a test that the ledger admitted on the handle. -/
def TestLogged (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKid : Std.U64) (ledger : Ledger)
    (handle : Handle) : Prop :=
  ∃ before entry after left right, ledger.transcript = before ++ entry :: after ∧
    entry.query = .inr (.test handle left right) ∧ AdmittedTest crypto codec serverKid before handle left right

/-- Two test sends of plaintexts of equal length, followed by ledger updates that differ only in the test bit, are coupled: with equal replies and related states when the handle holds no caller-known kernel (the zeroed sends are the same computation), and as an escape otherwise. -/
theorem send_couple (modes : Label n → KeyMode) (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Std.U64) (handle : Handle)
    (first second : Pqxdh.Bytes) (length : first.length = second.length) (state : NativeState n E)
    (update₁ update₂ : Option RawCtxSourceSend.Encrypted → Ledger) (flip : ∀ r, update₂ r = flipLedger (update₁ r))
    (inv : ∀ r, LedgerInv (update₁ r))
    (logged : ∀ r, TestLogged setup.source.crypto codec serverKid (update₁ r) handle ∧
      TestLogged setup.source.crypto codec serverKid (update₂ r) handle) :
    Swap (SimRel Related (Escaped setup.source.crypto codec serverKid) (Escaped setup.source.crypto codec serverKid))
      ((fun p => (p.1, (update₁ p.1, p.2))) <$> (simulateQ (nativeImpl modes zeros setup codec route env)
        (PqxdhDeploymentSecrecy.send handle first)).run state)
      ((fun p => (p.1, (update₂ p.1, p.2))) <$> (simulateQ (nativeImpl modes zeros setup codec route env)
        (PqxdhDeploymentSecrecy.send handle second)).run state) := by
  by_cases known : KnownAt state.1.2 handle
  · have keep : ∀ (message : Pqxdh.Bytes),
        ∀ p ∈ support ((simulateQ (nativeImpl modes zeros setup codec route env)
          (PqxdhDeploymentSecrecy.send handle message)).run state), KnownAt p.2.1.2 handle := fun message =>
      support_keep_oracle (nativeImpl modes zeros setup codec route env) (fun ns => KnownAt ns.1.2 handle)
        (fun q ns hk => nativeImpl_known modes zeros setup codec route env handle q ns hk) _ state known
    refine Swap.escape _ _ fun a ha b hb => Or.inr ⟨?_, ?_⟩
    · rw [support_map] at ha
      obtain ⟨z, hz, rfl⟩ := ha
      obtain ⟨before, entry, after, left, right, h₁, h₂, h₃⟩ := (logged z.1).1
      exact ⟨before, entry, after, handle, left, right, h₁, h₂, h₃, keep first z hz⟩
    · rw [support_map] at hb
      obtain ⟨z, hz, rfl⟩ := hb
      obtain ⟨before, entry, after, left, right, h₁, h₂, h₃⟩ := (logged z.1).2
      exact ⟨before, entry, after, handle, left, right, h₁, h₂, h₃, keep second z hz⟩
  · rw [← nativeImpl_send_zeros modes setup codec route env handle first second length state known]
    refine (Swap.refl _ (R := Eq) fun _ => rfl).map ?_
    rintro a b rfl
    exact Or.inl ⟨rfl, rfl, flip a.1, inv a.1⟩


/-- A later test on the test session's handle class is one send of the session's message, then the count update. -/
theorem fullImpl_test_session (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (handle : Handle) (left right : Pqxdh.Bytes)
    (ledger : Ledger) (state : NativeState n E) (admissible : PqxdhDeploymentSecrecy.Admissible left right)
    (session : PqxdhDeploymentSecrecy.TestState) (hsession : ledger.test = some session)
    (same : PqxdhDeploymentSecrecy.SameSession setup.source.crypto codec serverKid ledger.transcript session.first
      handle) :
    (fullImpl modes replace setup codec route env serverKid bounds (.inr (.test handle left right))).run
        (ledger, state) =
      (fun p => (p.1, ({ ledger.record (.inr (.test handle left right)) p.1 with
          test := some { session with count := session.count + 1 } }, p.2))) <$>
        (simulateQ (nativeImpl modes replace setup codec route env)
          (PqxdhDeploymentSecrecy.send handle (if session.bit then right else left))).run state := by
  have step : (PqxdhDeploymentSecrecy.ledgerImpl setup.source.crypto codec serverKid bounds
      (.inr (.test handle left right))).run ledger =
        PqxdhDeploymentSecrecy.send handle (if session.bit then right else left) >>= fun reply =>
          pure (reply, { ledger.record (.inr (.test handle left right)) reply with
            test := some { session with count := session.count + 1 } }) := by
    simp only [PqxdhDeploymentSecrecy.ledgerImpl, StateT.run, admissible, ↓reduceIte, hsession, same]
  rw [fullImpl_run, step, simulateQ_bind, StateT.run_bind, map_bind]
  simp only [simulateQ_pure, StateT.run_pure, map_eq_bind_pure_comp, Function.comp_apply, pure_bind]
  rfl


/-- The first admitted test draws the bit with one native coin, then sends the chosen message and opens the test session. -/
theorem fullImpl_test_first (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (handle : Handle) (left right : Pqxdh.Bytes)
    (ledger : Ledger) (state : NativeState n E) (admissible : PqxdhDeploymentSecrecy.Admissible left right)
    (hsession : ledger.test = none) :
    (fullImpl modes replace setup codec route env serverKid bounds (.inr (.test handle left right))).run
        (ledger, state) =
      (unifSpec.query 1 : ProbComp _) >>= fun coin =>
        (fun p => (p.1, ({ ledger.record (.inr (.test handle left right)) p.1 with
            test := some ⟨decide (coin = 1), handle, 1⟩ }, p.2))) <$>
          (simulateQ (nativeImpl modes replace setup codec route env)
            (PqxdhDeploymentSecrecy.send handle (if decide (coin = 1) then right else left))).run
            (state.1, coinStep state.2) := by
  have step : (PqxdhDeploymentSecrecy.ledgerImpl setup.source.crypto codec serverKid bounds
      (.inr (.test handle left right))).run ledger =
        PqxdhDeploymentSecrecy.drawBit >>= fun bit =>
          PqxdhDeploymentSecrecy.send handle (if bit then right else left) >>= fun reply =>
            pure (reply, { ledger.record (.inr (.test handle left right)) reply with
              test := some ⟨bit, handle, 1⟩ }) := by
    simp only [PqxdhDeploymentSecrecy.ledgerImpl, StateT.run, admissible, ↓reduceIte, hsession]
  rw [fullImpl_run, step, simulateQ_bind, StateT.run_bind, PqxdhDeploymentSecrecy.drawBit, simulateQ_map,
    StateT.run_map, PqxdhDeploymentSecrecy.coin, simulateQ_spec_query, nativeImpl_coin]
  simp only [simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure, map_eq_bind_pure_comp,
    Function.comp_apply, pure_bind, bind_assoc]
  rfl


/-- The test bit as a function of the native coin, and its relabelling. -/
theorem decide_rev (coin : Fin 2) : decide (Fin.rev coin = 1) = !decide (coin = 1) := by
  fin_cases coin <;> rfl

/-- **One coupled query.** In the zeroed-plaintext world, every adversary query from related states is coupled: with the native coin of the first admitted test relabelled (the bit negated), the replies are equal and the states related, or both runs escape. -/
theorem step_couple (modes : Label n → KeyMode) (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds)
    (query : FullSpec.Domain) (s t : Ledger × NativeState n E) (related : Related s t) :
    Swap (SimRel Related (Escaped setup.source.crypto codec serverKid) (Escaped setup.source.crypto codec serverKid))
      ((fullImpl modes zeros setup codec route env serverKid bounds query).run s)
      ((fullImpl modes zeros setup codec route env serverKid bounds query).run t) := by
  obtain ⟨ledger, state⟩ := s
  obtain ⟨ledger', state'⟩ := t
  obtain ⟨hstate, hledger, inv⟩ := related
  dsimp only at hstate hledger inv
  subst state' ledger'
  rcases query with forwarded | (⟨handle, left, right⟩ | ⟨handle, length⟩)
  · exact commute_couple modes zeros setup codec route env serverKid bounds _ ledger state inv
      (ledger_flip_forward _ codec serverKid bounds forwarded ledger)
  · by_cases admissible : PqxdhDeploymentSecrecy.Admissible left right
    · cases hsession : ledger.test with
      | none =>
          have unflipped : flipLedger ledger = ledger := by
            rcases ledger with ⟨transcript, test, fresh⟩
            dsimp only at hsession
            subst hsession
            rfl
          have none : firstTest ledger.transcript = none := by
            unfold LedgerInv at inv
            rw [← inv, hsession]
            rfl
          rw [unflipped, fullImpl_test_first modes zeros setup codec route env serverKid bounds handle left right ledger
            state admissible hsession]
          refine .query_bind 1 Fin.rev Fin.rev_bijective _ _ fun coin => ?_
          rw [decide_rev]
          refine send_couple modes setup codec route env serverKid handle
            (if decide (coin = 1) then right else left) (if !decide (coin = 1) then right else left) ?_ _
            (fun r => { ledger.record (.inr (.test handle left right)) r with test := some ⟨decide (coin = 1), handle, 1⟩ })
            (fun r => { ledger.record (.inr (.test handle left right)) r with test := some ⟨!decide (coin = 1), handle, 1⟩ })
            (fun r => rfl) (fun r => ?_) (fun r => ⟨?_, ?_⟩)
          · cases decide (coin = 1) <;> simp [admissible.1]
          · unfold LedgerInv
            dsimp only [PqxdhDeploymentSecrecy.Ledger.record]
            rw [firstTest_append, admissibleTest_test, ite_eq_left admissible, none]
            rfl
          · exact ⟨ledger.transcript, ⟨.inr (.test handle left right), r⟩, [], left, right, rfl, rfl, admissible,
              fun first hfirst => by
                rw [none] at hfirst
                exact absurd hfirst (by simp)⟩
          · exact ⟨ledger.transcript, ⟨.inr (.test handle left right), r⟩, [], left, right, rfl, rfl, admissible,
              fun first hfirst => by
                rw [none] at hfirst
                exact absurd hfirst (by simp)⟩
      | some session =>
          have first : firstTest ledger.transcript = some session.first := by
            unfold LedgerInv at inv
            rw [← inv, hsession]
            rfl
          by_cases same : PqxdhDeploymentSecrecy.SameSession setup.source.crypto codec serverKid ledger.transcript
            session.first handle
          · have flipped : (flipLedger ledger).test = some { session with bit := !session.bit } := by
              simp only [flipLedger, hsession, Option.map_some]
            rw [fullImpl_test_session modes zeros setup codec route env serverKid bounds handle left right ledger state
              admissible session hsession same,
              fullImpl_test_session modes zeros setup codec route env serverKid bounds handle left right
                (flipLedger ledger) state admissible _ flipped same]
            have logged : ∀ (target : Ledger), target.transcript = ledger.transcript →
                ∀ r, TestLogged setup.source.crypto codec serverKid
                  (target.record (.inr (.test handle left right)) r) handle := fun target htarget r =>
              ⟨ledger.transcript, ⟨.inr (.test handle left right), r⟩, [], left, right,
                by simp [PqxdhDeploymentSecrecy.Ledger.record, htarget], rfl,
                admissible, fun first' hfirst => by
                  rw [first] at hfirst
                  cases hfirst
                  exact same⟩
            refine send_couple modes setup codec route env serverKid handle
              (if session.bit then right else left) (if !session.bit then right else left) ?_ _
              (fun r => { ledger.record (.inr (.test handle left right)) r with
                test := some { session with count := session.count + 1 } })
              (fun r => { (flipLedger ledger).record (.inr (.test handle left right)) r with
                test := some { { session with bit := !session.bit } with count := session.count + 1 } })
              (fun r => rfl) (fun r => ?_) (fun r => ⟨?_, ?_⟩)
            · cases session.bit <;> simp [admissible.1]
            · unfold LedgerInv
              dsimp only [PqxdhDeploymentSecrecy.Ledger.record]
              rw [firstTest_append, first]
              rfl
            · exact logged ledger rfl r
            · exact logged (flipLedger ledger) rfl r
          · exact commute_couple modes zeros setup codec route env serverKid bounds _ ledger state inv
              (ledger_flip_refused _ codec serverKid bounds handle left right ledger
                (Or.inr ⟨session, hsession, same⟩))
    · exact commute_couple modes zeros setup codec route env serverKid bounds _ ledger state inv
        (ledger_flip_refused _ codec serverKid bounds handle left right ledger (Or.inl admissible))
  · exact commute_couple modes zeros setup codec route env serverKid bounds _ ledger state inv
      (ledger_flip_fresh _ codec serverKid bounds handle length ledger)


/-! ### The final observations -/

/-- With the test bit negated in the ledger, the negated decision wins exactly when the original decision wins: the public hiding projection, the eligibility and the hidden-test condition ignore the bit. -/
theorem lorGuess_flip (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKid : Std.U64)
    (decision eligible : PublicHiding n E X → Bool) (x : X) (ledger : Ledger) (environment : E)
    (produced : List (PqxdhDeploymentInterface.FrameTag × PqxdhDeploymentNative.Frame))
    (raw : PqxdhRecordLiftWorld.RawCounters) (slots : Handle → Option (Slot n)) :
    lorGuess crypto codec serverKid (fun projection => !decision projection) eligible
        ⟨some (x, flipLedger ledger, environment), produced, raw, slots⟩ =
      lorGuess crypto codec serverKid decision eligible ⟨some (x, ledger, environment), produced, raw, slots⟩ := by
  have hidden : TestsHidden crypto codec serverKid
      (⟨some (x, flipLedger ledger, environment), produced, raw, slots⟩ : View n E X) ↔
        TestsHidden crypto codec serverKid ⟨some (x, ledger, environment), produced, raw, slots⟩ := by
    rcases ledger with ⟨transcript, test, fresh⟩
    cases test <;> simp [TestsHidden, flipLedger]
  have publicView : publicHiding (⟨some (x, flipLedger ledger, environment), produced, raw, slots⟩ : View n E X) =
      publicHiding ⟨some (x, ledger, environment), produced, raw, slots⟩ := by
    rcases ledger with ⟨transcript, test, fresh⟩
    cases test <;> rfl
  have bit : testBit (⟨some (x, flipLedger ledger, environment), produced, raw, slots⟩ : View n E X) =
      (testBit (⟨some (x, ledger, environment), produced, raw, slots⟩ : View n E X)).map not := by
    rcases ledger with ⟨transcript, test, fresh⟩
    cases test <;> rfl
  unfold lorGuess
  rw [publicView, bit, propext hidden]
  cases testBit (⟨some (x, ledger, environment), produced, raw, slots⟩ : View n E X) <;> simp

/-- An escaped run has no hidden-test win: its admitted test on a caller-known handle maps to no slot. -/
theorem lorGuess_escaped (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKid : Std.U64)
    (decision eligible : PublicHiding n E X → Bool) (x : X) (ledger : Ledger) (state : NativeState n E)
    (produced : List (PqxdhDeploymentInterface.FrameTag × PqxdhDeploymentNative.Frame))
    (raw : PqxdhRecordLiftWorld.RawCounters) (escaped : Escaped crypto codec serverKid (ledger, state)) :
    lorGuess crypto codec serverKid decision eligible
      ⟨some (x, ledger, state.1.1), produced, raw, handleSlot state.1.2⟩ = false := by
  obtain ⟨before, entry, after, handle, left, right, htranscript, hquery, hadmitted, hknown⟩ := escaped
  dsimp only at htranscript hknown
  have noSlot : handleSlot state.1.2 handle = none := by
    cases handle with
    | peer keyId =>
        obtain ⟨server, peer, kernel, hs, hp, hk⟩ := hknown
        simp [handleSlot, peerSlot, hs, hp, hk, PqxdhRecordLiftWorldCompiler.StoredKernel.origin]
    | owner owner =>
        obtain ⟨shell, kernel, ho⟩ := hknown
        simp [handleSlot, ownerSlot, ho, PqxdhRecordLiftWorldCompiler.Phase.origin,
          PqxdhRecordLiftWorldCompiler.StoredKernel.origin]
  simp only [lorGuess, decide_eq_false_iff_not]
  rintro ⟨_, ⟨value, hvalue, _, hall⟩, _⟩
  simp only [Option.mem_def, Option.some.injEq] at hvalue
  subst hvalue
  have hit := hall before entry after handle left right htranscript hquery hadmitted
  dsimp only at hit
  rw [noSlot] at hit
  exact absurd hit (by simp)


/-! ### The coupled world -/

/-- **World coupling.** The mode-P CTX world with zeroed hidden plaintexts is coupled with itself so that the left-or-right win of a decision on one side equals the win of the negated decision on the other: the native coin of the first admitted test is relabelled, so the test bit is negated while every reply, the transcript and every non-bit state agree, unless an admitted test went to a caller-known handle, in which case neither side has all tests hidden. -/
theorem world_couple (modes : Label n → KeyMode) (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds)
    (adversary : OracleComp (ModeSpec .P) X) (decision eligible : PublicHiding n E X → Bool) :
    Swap (fun r₁ r₂ => lorGuess setup.source.crypto codec serverKid decision eligible (ctxView r₁) =
        lorGuess setup.source.crypto codec serverKid (fun projection => !decision projection) eligible (ctxView r₂))
      (ctxRun modes zeros setup codec route env serverKid bounds .P adversary)
      (ctxRun modes zeros setup codec route env serverKid bounds .P adversary) := by
  rw [ctxRun_flat]
  refine (Swap.refl (startup modes zeros setup codec route env) (R := Eq) fun _ => rfl).bind fun born _ hborn => ?_
  subst hborn
  rcases born with ⟨⟨_ | ⟨created, initial⟩, control⟩, secret⟩
  · exact .pure _ _ (by simp [ctxView, viewOf, lorGuess, TestsHidden])
  · refine (Swap.refl (install modes zeros setup codec route created control secret) (R := Eq) fun _ => rfl).bind
      fun installed _ hinstalled => ?_
    subst hinstalled
    refine (Swap.simulateQ_run (fullImpl modes zeros setup codec route env serverKid bounds)
      (fullImpl modes zeros setup codec route env serverKid bounds) Related
      (Escaped setup.source.crypto codec serverKid) (Escaped setup.source.crypto codec serverKid)
      (escaped_keep modes zeros setup codec route env serverKid bounds)
      (escaped_keep modes zeros setup codec route env serverKid bounds)
      (step_couple modes setup codec route env serverKid bounds) (asModeO .P adversary) _ _
      ⟨rfl, rfl, ledgerInv_empty⟩).map ?_
    rintro ⟨x₁, ledger₁, state₁⟩ ⟨x₂, ledger₂, state₂⟩ (⟨hx, hstate, hledger, _⟩ | ⟨escaped₁, escaped₂⟩)
    · dsimp only at hx hstate hledger
      subst x₂ state₂ ledger₂
      exact (lorGuess_flip setup.source.crypto codec serverKid decision eligible x₁ ledger₁ state₁.1.1 _ _ _).symm
    · exact (lorGuess_escaped setup.source.crypto codec serverKid decision eligible x₁ ledger₁ state₁ _ _
        escaped₁).trans (lorGuess_escaped setup.source.crypto codec serverKid _ eligible x₂ ledger₂ state₂ _ _
          escaped₂).symm


/-! ### Halving -/

/-- The probability of a disjoint disjunction of two Boolean observations is the sum of their probabilities. -/
theorem evalDist_or {α : Type} (work : ProbComp α) (first second : α → Bool)
    (disjoint : ∀ a, ¬(first a = true ∧ second a = true)) :
    𝒟[(fun a => first a || second a) <$> work] {true} = 𝒟[first <$> work] {true} + 𝒟[second <$> work] {true} := by
  let _ : MeasurableSpace α := ⊤
  have _ : DiscreteMeasurableSpace α := ⟨fun _ => trivial⟩
  rw [evalDist_map_of_discrete, evalDist_map_of_discrete, evalDist_map_of_discrete,
    MeasureTheory.Measure.map_apply .of_discrete (measurableSet_singleton _),
    MeasureTheory.Measure.map_apply .of_discrete (measurableSet_singleton _),
    MeasureTheory.Measure.map_apply .of_discrete (measurableSet_singleton _)]
  have split : (fun a => first a || second a) ⁻¹' {true} = first ⁻¹' {true} ∪ second ⁻¹' {true} := by
    ext a
    simp [Bool.or_eq_true]
  rw [split]
  exact MeasureTheory.measure_union (Set.disjoint_left.mpr fun a h₁ h₂ => disjoint a ⟨h₁, h₂⟩) .of_discrete

/-- Eligibility splits into the win of the decision and the win of its negation, which exclude each other. -/
theorem lorEligible_split (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKid : Std.U64)
    (decision eligible : PublicHiding n E X → Bool) (view : View n E X) :
    lorEligible crypto codec serverKid eligible view =
      (lorGuess crypto codec serverKid decision eligible view ||
        lorGuess crypto codec serverKid (fun projection => !decision projection) eligible view) ∧
    ¬(lorGuess crypto codec serverKid decision eligible view = true ∧
      lorGuess crypto codec serverKid (fun projection => !decision projection) eligible view = true) := by
  have someBit : TestsHidden crypto codec serverKid view → ∃ bit, testBit view = some bit := by
    rintro ⟨value, hvalue, test, _⟩
    obtain ⟨session, hsession⟩ := Option.isSome_iff_exists.mp test
    exact ⟨session.bit, by simp [testBit, Option.mem_def.mp hvalue, hsession]⟩
  constructor
  · unfold lorEligible lorGuess
    by_cases th : TestsHidden crypto codec serverKid view
    · obtain ⟨bit, hbit⟩ := someBit th
      rw [hbit]
      rcases Bool.eq_false_or_eq_true (decision (publicHiding view)) with chosen | chosen <;>
        cases bit <;> simp [th, chosen]
    · simp [th]
  · unfold lorGuess
    rintro ⟨first, second⟩
    simp only [decide_eq_true_eq] at first second
    rw [first.2.2] at second
    rcases Bool.eq_false_or_eq_true (decision (publicHiding view)) with chosen | chosen <;> simp [chosen] at second


/-- **Left-or-right secrecy with zeroed hidden plaintexts.** In the mode-P CTX world with zeroed hidden plaintexts (any key modes), a public decision wins with exactly half the probability of eligibility with all admitted tests hidden. -/
theorem lor_zeros (modes : Label n → KeyMode) (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds)
    (adversary : OracleComp (ModeSpec .P) X) (decision eligible : PublicHiding n E X → Bool) :
    𝒟[(fun result => lorGuess setup.source.crypto codec serverKid decision eligible (ctxView result)) <$>
        ctxRun modes zeros setup codec route env serverKid bounds .P adversary] {true} =
      2⁻¹ * 𝒟[(fun result => lorEligible setup.source.crypto codec serverKid eligible (ctxView result)) <$>
        ctxRun modes zeros setup codec route env serverKid bounds .P adversary] {true} := by
  have same := (world_couple modes setup codec route env serverKid bounds adversary decision eligible).evalDist_map
    (fun result => lorGuess setup.source.crypto codec serverKid decision eligible (ctxView result))
    (fun result => lorGuess setup.source.crypto codec serverKid (fun projection => !decision projection) eligible
      (ctxView result)) fun _ _ related => related
  have split : (fun result : Client n E X × CtxPrivate n =>
      lorEligible setup.source.crypto codec serverKid eligible (ctxView result)) =
      fun result => lorGuess setup.source.crypto codec serverKid decision eligible (ctxView result) ||
        lorGuess setup.source.crypto codec serverKid (fun projection => !decision projection) eligible (ctxView result) :=
    funext fun result => (lorEligible_split setup.source.crypto codec serverKid decision eligible (ctxView result)).1
  rw [split, evalDist_or _ _ _ fun result =>
    (lorEligible_split setup.source.crypto codec serverKid decision eligible (ctxView result)).2, ← same, ← two_mul,
    ← mul_assoc, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]


/-! ### Transfer to the record-ideal world -/

/-- A split of a list transfers to every list with the same image. -/
theorem map_split {α β : Type} (f : α → β) (first second : List α) (same : first.map f = second.map f)
    (before : List α) (entry : α) (after : List α) (hsecond : second = before ++ entry :: after) :
    ∃ before' entry' after', first = before' ++ entry' :: after' ∧ before'.map f = before.map f ∧ f entry' = f entry := by
  subst hsecond
  rw [List.map_append, List.map_cons] at same
  obtain ⟨front, back, hfirst, hfront, hback⟩ := List.map_eq_append_iff.mp same
  obtain ⟨entry', after', hback', hentry, _⟩ := List.map_eq_cons_iff.mp hback
  exact ⟨front, entry', after', by rw [hfirst, hback'], hfront, hentry⟩

/-- Whether all admitted tests were hidden depends on a view only through its hiding projection. -/
theorem testsHidden_hiding (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKid : Std.U64)
    (first second : View n E X) (same : hidingView first = hidingView second)
    (hidden : TestsHidden crypto codec serverKid first) : TestsHidden crypto codec serverKid second := by
  obtain ⟨value, hvalue, test, all⟩ := hidden
  simp only [hidingView, Prod.mk.injEq] at same
  obtain ⟨results, _, _, slots⟩ := same
  rw [Option.mem_def] at hvalue
  rw [hvalue, Option.map_some] at results
  obtain ⟨value', hvalue', hmap⟩ := Option.map_eq_some_iff.mp results.symm
  simp only [Prod.mk.injEq] at hmap
  obtain ⟨_, transcripts, tests, _, _⟩ := hmap
  refine ⟨value', hvalue', by rw [tests]; exact test, ?_⟩
  intro before entry after handle left right htranscript hquery hadmitted
  obtain ⟨before', entry', after', hsplit, hbefore, hentry⟩ := map_split (PqxdhDeploymentInterface.Entry.view .P)
    value.2.1.transcript value'.2.1.transcript transcripts.symm before entry after htranscript
  have query : entry'.query = entry.query := congrArg PqxdhDeploymentInterface.PublicEntry.query hentry
  have admitted := (admittedTest_view crypto codec serverKid before' before hbefore handle left right).mpr hadmitted
  have hit := all before' entry' after' handle left right hsplit (query.trans hquery) admitted
  rw [← slots]
  exact hit

/-- The test bit of a view is read from its hiding projection. -/
theorem testBit_hidingView (view : View n E X) :
    testBit view = (hidingView view).1.bind fun value => value.2.2.1.map PqxdhDeploymentSecrecy.TestState.bit := by
  rcases view with ⟨_ | value, produced, raw, slots⟩ <;> rfl

/-- The left-or-right win depends on a view only through its hiding projection. -/
theorem lorGuess_hiding (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKid : Std.U64)
    (decision eligible : PublicHiding n E X → Bool) (first second : View n E X)
    (same : hidingView first = hidingView second) :
    lorGuess crypto codec serverKid decision eligible first = lorGuess crypto codec serverKid decision eligible second := by
  unfold lorGuess
  rw [publicHiding_hidingView, publicHiding_hidingView, testBit_hidingView, testBit_hidingView, same,
    propext ⟨testsHidden_hiding crypto codec serverKid first second same,
      testsHidden_hiding crypto codec serverKid second first same.symm⟩]

/-- Eligibility with all admitted tests hidden depends on a view only through its hiding projection. -/
theorem lorEligible_hiding (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKid : Std.U64)
    (eligible : PublicHiding n E X → Bool) (first second : View n E X) (same : hidingView first = hidingView second) :
    lorEligible crypto codec serverKid eligible first = lorEligible crypto codec serverKid eligible second := by
  unfold lorEligible
  rw [publicHiding_hidingView, publicHiding_hidingView, same,
    propext ⟨testsHidden_hiding crypto codec serverKid first second same,
      testsHidden_hiding crypto codec serverKid second first same.symm⟩]

/-- A Boolean observation that depends on views only through their hiding projection has the same law in `idealRecords` (mode P) and in the random-ciphertext world with zeroed hidden plaintexts (`PqxdhRecordLiftHiding.hiding_replace`). -/
theorem law_zeros (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds)
    (adversary : OracleComp (ModeSpec .P) X) (observe : View n E X → Bool)
    (invariant : ∀ first second, hidingView first = hidingView second → observe first = observe second) :
    (fun result => observe (ctxView result)) <$> idealRecords setup codec route env serverKid bounds .P adversary =
      (fun result => observe (ctxView result)) <$>
        ctxRun (fun _ => .random) zeros setup codec route env serverKid bounds .P adversary := by
  let factor : HidingView n E X → Bool := fun projection =>
    @dite _ (∃ view, hidingView view = projection) (Classical.propDecidable _) (fun h => observe h.choose)
      (fun _ => false)
  have factored : ∀ view, observe view = factor (hidingView view) := fun view => by
    have h : ∃ other, hidingView other = hidingView view := ⟨view, rfl⟩
    simp only [factor, h]
    exact invariant _ _ (Eq.symm (Exists.choose_spec (p := fun other => hidingView other = hidingView view) _))
  have replaced := PqxdhRecordLiftHiding.hiding_replace setup codec route serverKid bounds env adversary id zeros
    fun message => (zeros_length message).symm
  calc (fun result => observe (ctxView result)) <$> idealRecords setup codec route env serverKid bounds .P adversary
      = factor <$> ((fun result => hidingView (ctxView result)) <$>
          ctxRun (fun _ => .random) id setup codec route env serverKid bounds .P adversary) := by
        rw [Functor.map_map]
        exact congrArg (fun f => f <$> idealRecords setup codec route env serverKid bounds .P adversary)
          (funext fun result => factored (ctxView result))
    _ = factor <$> ((fun result => hidingView (ctxView result)) <$>
          ctxRun (fun _ => .random) zeros setup codec route env serverKid bounds .P adversary) := by
        rw [replaced]
    _ = _ := by
        rw [Functor.map_map]
        exact congrArg (fun f => f <$> ctxRun (fun _ => .random) zeros setup codec route env serverKid bounds .P
          adversary) (funext fun result => (factored (ctxView result)).symm)

/-- **`LorStatement` (H-5 `idealRecords_hiding`, left-or-right form for CE-LOR), delivered.** In mode P, for every environment, adversary, public decision and public eligibility, the probability in `idealRecords` that the run is eligible, every admitted test was on a hidden handle and the decision equals the test bit is exactly half the probability that the run is eligible and every admitted test was on a hidden handle. No contract. -/
theorem idealRecords_lor (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (serverKid : Std.U64) (bounds : FreshBounds) (n : Nat) :
    LorStatement setup codec route serverKid bounds n := by
  intro E X env adversary decision eligible
  rw [law_zeros setup codec route env serverKid bounds adversary _
      (lorGuess_hiding setup.source.crypto codec serverKid decision eligible),
    law_zeros setup codec route env serverKid bounds adversary _
      (lorEligible_hiding setup.source.crypto codec serverKid eligible)]
  exact lor_zeros (fun _ => .random) setup codec route env serverKid bounds adversary decision eligible

end BeaconcryptCore.Computational.PqxdhRecordLiftLor

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLor.flipLedger_record' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLor.flipLedger_record

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLor.ledger_flip_forward' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLor.ledger_flip_forward

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLor.ledger_flip_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLor.ledger_flip_fresh

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLor.ledger_flip_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLor.ledger_flip_refused

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLor.escaped_keep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLor.escaped_keep

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLor.commute_couple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLor.commute_couple

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLor.send_couple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLor.send_couple

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLor.fullImpl_test_session' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLor.fullImpl_test_session

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLor.fullImpl_test_first' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLor.fullImpl_test_first

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLor.decide_rev' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLor.decide_rev

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLor.step_couple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLor.step_couple

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLor.lorGuess_flip' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLor.lorGuess_flip

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLor.lorGuess_escaped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLor.lorGuess_escaped

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLor.world_couple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLor.world_couple

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLor.evalDist_or' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLor.evalDist_or

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLor.lorEligible_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLor.lorEligible_split

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLor.lor_zeros' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLor.lor_zeros

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLor.map_split' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLor.map_split

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLor.testsHidden_hiding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLor.testsHidden_hiding

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLor.testBit_hidingView' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLor.testBit_hidingView

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLor.lorGuess_hiding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLor.lorGuess_hiding

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLor.lorEligible_hiding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLor.lorEligible_hiding

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLor.law_zeros' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLor.law_zeros

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLor.idealRecords_lor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLor.idealRecords_lor
