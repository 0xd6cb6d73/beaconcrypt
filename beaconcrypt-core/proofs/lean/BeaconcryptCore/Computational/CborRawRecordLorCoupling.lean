-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawRecordFlatSemantics

/-! The actual first eligible test bit is swapped inside the original secrecy ledger. Cursor refusal and advancement agree for both equal-length alternatives; all non-test queries and every later cursor update retain the bit-swap relation. Caller-known-handle escapes remain explicit rather than granting them hidden-message secrecy. -/
open OracleComp OracleSpec ENNReal CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawRecordLorCoupling
open PqxdhRecordLiftInterface PqxdhRecordLiftIdeal PqxdhRecordLiftSwap
open PqxdhDeploymentInterface (Mode ModeSpec FreshBounds Spec FullSpec Handle asModeO)
open PqxdhDeploymentSecrecy (Ledger)
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftFlat (KnownAt zeros coinStep support_keep_oracle support_run_fst LedgerInv ledger_append ledger_inv firstTest_append admissibleTest_test)
open PqxdhRecordLiftLor
open CborRawRecordFlat (NativeState fullImpl nativeImpl nativeImpl_known fullImpl_run)
open CborRawRecordFlatSemantics (nativeImpl_coin nativeImpl_send_zeros)
variable {n : Nat} {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response E X : Type}

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


end BeaconcryptCore.Computational.CborRawRecordLorCoupling

/-- info: 'BeaconcryptCore.Computational.CborRawRecordLorCoupling.escaped_keep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordLorCoupling.escaped_keep

/-- info: 'BeaconcryptCore.Computational.CborRawRecordLorCoupling.commute_couple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordLorCoupling.commute_couple

/-- info: 'BeaconcryptCore.Computational.CborRawRecordLorCoupling.send_couple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordLorCoupling.send_couple

/-- info: 'BeaconcryptCore.Computational.CborRawRecordLorCoupling.fullImpl_test_session' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordLorCoupling.fullImpl_test_session

/-- info: 'BeaconcryptCore.Computational.CborRawRecordLorCoupling.fullImpl_test_first' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordLorCoupling.fullImpl_test_first

/-- info: 'BeaconcryptCore.Computational.CborRawRecordLorCoupling.decide_rev' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordLorCoupling.decide_rev

/-- info: 'BeaconcryptCore.Computational.CborRawRecordLorCoupling.step_couple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordLorCoupling.step_couple
