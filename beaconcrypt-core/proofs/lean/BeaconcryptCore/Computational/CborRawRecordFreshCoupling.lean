-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawRecordFlatSemantics

/-! Fresh-message byte shifts run through the actual cursor-aware native interpreter. The ledger retains its original byte draws and fresh-message records even when the underlying send is refused. Equal-length shifts take identical cursor branches and updates; caller-known-handle escapes remain explicit and persistent. -/
open OracleComp OracleSpec ENNReal CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawRecordFreshCoupling
open PqxdhRecordLiftInterface PqxdhRecordLiftIdeal PqxdhRecordLiftSwap
open PqxdhDeploymentInterface (Mode ModeSpec FreshBounds Spec FullSpec Handle asModeO)
open PqxdhDeploymentSecrecy (Ledger FreshEntry)
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftFlat (KnownAt zeros coinStep support_keep_oracle support_run_fst)
open PqxdhRecordLiftFresh
open CborRawRecordFlat (NativeState fullImpl nativeImpl nativeImpl_known fullImpl_run)
open CborRawRecordFlatSemantics (nativeImpl_coin nativeImpl_send_zeros)
variable {n : Nat} {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response E X : Type}

def FreshRelated (bounds : FreshBounds) (index : ℕ) (offsets : ℕ → Fin 256) (s t : Ledger × NativeState n E) :
    Prop :=
  t.2 = s.2 ∧ t.1 = shiftLedger index offsets s.1 ∧ FreshLong bounds s.1

/-- The run has escaped: the `index`-th fresh message went to a handle that now holds a caller-known kernel. -/
def FreshEscaped (index : ℕ) (s : Ledger × NativeState n E) : Prop :=
  ∃ entry, s.1.fresh[index]? = some entry ∧ KnownAt s.2.1.2 entry.handle

/-- Every adversary query keeps an escape: fresh entries are only appended and caller-known kernels persist. -/
theorem freshEscaped_keep (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (index : ℕ) (query : FullSpec.Domain)
    (s : Ledger × NativeState n E) (escaped : FreshEscaped index s) :
    ∀ p ∈ support ((fullImpl modes replace setup codec route env serverKid bounds query).run s),
      FreshEscaped index p.2 := by
  obtain ⟨ledger, state⟩ := s
  obtain ⟨entry, hentry, hknown⟩ := escaped
  intro p hp
  rw [fullImpl_run, support_map] at hp
  obtain ⟨z, hz, rfl⟩ := hp
  obtain ⟨extra, hextra⟩ := ledger_fresh_prefix setup.source.crypto codec serverKid bounds query ledger z.1
    (support_run_fst _ _ _ z hz)
  dsimp only at hentry hknown
  obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp hentry
  refine ⟨entry, ?_, ?_⟩
  · dsimp only
    rw [hextra, List.getElem?_append_left hlt]
    exact hentry
  · exact support_keep_oracle (nativeImpl modes replace setup codec route env)
      (fun ns => KnownAt ns.1.2 entry.handle)
      (fun q ns known => nativeImpl_known modes replace setup codec route env entry.handle q ns known) _ state hknown
      z hz

/-! ### One coupled adversary query -/

/-- A query whose ledger step commutes with the shift is coupled with itself, with related states. -/
theorem commute_couple (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (index : ℕ) (offsets : ℕ → Fin 256)
    (query : FullSpec.Domain) (ledger : Ledger) (state : NativeState n E) (long : FreshLong bounds ledger)
    (commute : (PqxdhDeploymentSecrecy.ledgerImpl setup.source.crypto codec serverKid bounds query).run
        (shiftLedger index offsets ledger) = (fun p => (p.1, shiftLedger index offsets p.2)) <$>
          (PqxdhDeploymentSecrecy.ledgerImpl setup.source.crypto codec serverKid bounds query).run ledger) :
    Swap (SimRel (FreshRelated bounds index offsets) (FreshEscaped index) (FreshEscaped index))
      ((fullImpl modes replace setup codec route env serverKid bounds query).run (ledger, state))
      ((fullImpl modes replace setup codec route env serverKid bounds query).run
        (shiftLedger index offsets ledger, state)) := by
  rw [fullImpl_run, fullImpl_run, commute, simulateQ_map, StateT.run_map, Functor.map_map]
  refine (Swap.refl_support ((simulateQ (nativeImpl modes replace setup codec route env)
    ((PqxdhDeploymentSecrecy.ledgerImpl setup.source.crypto codec serverKid bounds query).run ledger)).run state)
    (R := fun a b => a = b ∧ a ∈ support ((simulateQ (nativeImpl modes replace setup codec route env)
      ((PqxdhDeploymentSecrecy.ledgerImpl setup.source.crypto codec serverKid bounds query).run ledger)).run state))
    fun a ha => ⟨rfl, ha⟩).map ?_
  rintro a b ⟨rfl, ha⟩
  exact Or.inl ⟨rfl, rfl, rfl,
    ledger_freshLong setup.source.crypto codec serverKid bounds query ledger long a.1 (support_run_fst _ _ _ a ha)⟩

/-- The sends of a message and of its shift, followed by ledger updates related by the shift, are coupled: with equal replies and related states when the handle holds no caller-known kernel (the zeroed sends are the same computation), and as an escape otherwise. -/
theorem send_couple (modes : Label n → KeyMode) (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (bounds : FreshBounds) (index : ℕ)
    (offsets : ℕ → Fin 256) (handle : Handle) (first second : Pqxdh.Bytes) (length : first.length = second.length)
    (state : NativeState n E) (update₁ update₂ : Option RawCtxSourceSend.Encrypted → Ledger)
    (shift : ∀ r, update₂ r = shiftLedger index offsets (update₁ r)) (long : ∀ r, FreshLong bounds (update₁ r))
    (logged : ∀ r, (∃ entry, (update₁ r).fresh[index]? = some entry ∧ entry.handle = handle) ∧
      ∃ entry, (update₂ r).fresh[index]? = some entry ∧ entry.handle = handle) :
    Swap (SimRel (FreshRelated bounds index offsets) (FreshEscaped index) (FreshEscaped index))
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
      obtain ⟨entry, hentry, hhandle⟩ := (logged z.1).1
      exact ⟨entry, hentry, hhandle ▸ keep first z hz⟩
    · rw [support_map] at hb
      obtain ⟨z, hz, rfl⟩ := hb
      obtain ⟨entry, hentry, hhandle⟩ := (logged z.1).2
      exact ⟨entry, hentry, hhandle ▸ keep second z hz⟩
  · rw [← nativeImpl_send_zeros modes setup codec route env handle first second length state known]
    refine (Swap.refl _ (R := Eq) fun _ => rfl).map ?_
    rintro a b rfl
    exact Or.inl ⟨rfl, rfl, shift a.1, long a.1⟩

/-- **Relabelled message coins.** The native coins of a uniform message, the coin of byte `j` relabelled by adding `offsets (start + j)`, couple two continuations that are coupled on a message and its shift. -/
theorem bytes_couple {α β : Type} {R : α → β → Prop} (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (offsets : ℕ → Fin 256) (length : ℕ) :
    ∀ (start : ℕ) (state : NativeState n E) (f : Pqxdh.Bytes × NativeState n E → ProbComp α)
      (g : Pqxdh.Bytes × NativeState n E → ProbComp β),
      (∀ message st, message.length = length → Swap R (f (message, st)) (g (shiftFrom offsets start message, st))) →
      Swap R ((simulateQ (nativeImpl modes replace setup codec route env)
          (PqxdhDeploymentSecrecy.uniformBytes length)).run state >>= f)
        ((simulateQ (nativeImpl modes replace setup codec route env)
          (PqxdhDeploymentSecrecy.uniformBytes length)).run state >>= g) := by
  induction length with
  | zero =>
      intro start state f g next
      simp only [PqxdhDeploymentSecrecy.uniformBytes, simulateQ_pure, StateT.run_pure, pure_bind]
      exact next [] state rfl
  | succ length ih =>
      intro start state f g next
      simp only [PqxdhDeploymentSecrecy.uniformBytes, simulateQ_bind, StateT.run_bind, PqxdhDeploymentSecrecy.coin,
        simulateQ_spec_query, bind_assoc, simulateQ_pure, StateT.run_pure, pure_bind]
      rw [nativeImpl_coin]
      simp only [bind_map_left]
      refine .query_bind 255 (fun r => r + offsets start)
        ⟨add_left_injective _, fun y => ⟨y - offsets start, sub_add_cancel y _⟩⟩ _ _ fun coin => ?_
      refine ih (start + 1) (state.1, coinStep state.2) _ _ fun message st hlength => ?_
      have h := next (UInt8.ofNat coin.val :: message) st (by simp only [List.length_cons, hlength])
      simp only [shiftFrom, shiftByte_coin] at h
      exact h

/-- The admitted fresh query: the native coins of a uniform message, then its send and the ledger update. -/
theorem fullImpl_fresh (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (handle : Handle) (length : ℕ)
    (ledger : Ledger) (state : NativeState n E) (admitted : bounds.min ≤ length ∧ length ≤ bounds.max) :
    (fullImpl modes replace setup codec route env serverKid bounds (.inr (.fresh handle length))).run
        (ledger, state) =
      (simulateQ (nativeImpl modes replace setup codec route env)
          (PqxdhDeploymentSecrecy.uniformBytes length)).run state >>= fun p =>
        (fun q => (q.1, ({ ledger.record (.inr (.fresh handle length)) q.1 with
            fresh := ledger.fresh ++ [⟨handle, p.1, q.1⟩] }, q.2))) <$>
          (simulateQ (nativeImpl modes replace setup codec route env)
            (PqxdhDeploymentSecrecy.send handle p.1)).run p.2 := by
  have step : (PqxdhDeploymentSecrecy.ledgerImpl setup.source.crypto codec serverKid bounds
      (.inr (.fresh handle length))).run ledger =
        PqxdhDeploymentSecrecy.uniformBytes length >>= fun message =>
          PqxdhDeploymentSecrecy.send handle message >>= fun reply =>
            pure (reply, { ledger.record (.inr (.fresh handle length)) reply with
              fresh := ledger.fresh ++ [⟨handle, message, reply⟩] }) := by
    simp only [PqxdhDeploymentSecrecy.ledgerImpl, StateT.run, admitted, and_self, ↓reduceIte]
  rw [fullImpl_run, step, simulateQ_bind, StateT.run_bind, map_bind]
  simp only [simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure, map_eq_bind_pure_comp,
    Function.comp_apply, pure_bind, bind_assoc]
  rfl

/-- The admitted `index`-th fresh query is coupled with itself, its message coins relabelled by the shift. -/
theorem target_couple (modes : Label n → KeyMode) (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds)
    (offsets : ℕ → Fin 256) (handle : Handle) (length : ℕ) (ledger : Ledger) (state : NativeState n E)
    (admitted : bounds.min ≤ length ∧ length ≤ bounds.max) (long : FreshLong bounds ledger) :
    Swap (SimRel (FreshRelated bounds ledger.fresh.length offsets) (FreshEscaped ledger.fresh.length)
        (FreshEscaped ledger.fresh.length))
      ((fullImpl modes zeros setup codec route env serverKid bounds (.inr (.fresh handle length))).run
        (ledger, state))
      ((fullImpl modes zeros setup codec route env serverKid bounds (.inr (.fresh handle length))).run
        (shiftLedger ledger.fresh.length offsets ledger, state)) := by
  rw [fullImpl_fresh modes zeros setup codec route env serverKid bounds handle length ledger state admitted,
    fullImpl_fresh modes zeros setup codec route env serverKid bounds handle length _ state admitted]
  refine bytes_couple modes zeros setup codec route env offsets length 0 state _ _ fun message st hlength => ?_
  refine send_couple modes setup codec route env bounds ledger.fresh.length offsets handle message
    (shiftFrom offsets 0 message) (shiftFrom_length offsets 0 message).symm st
    (fun r => { ledger.record (.inr (.fresh handle length)) r with fresh := ledger.fresh ++ [⟨handle, message, r⟩] })
    (fun r => { (shiftLedger ledger.fresh.length offsets ledger).record (.inr (.fresh handle length)) r with
      fresh := (shiftLedger ledger.fresh.length offsets ledger).fresh ++ [⟨handle, shiftFrom offsets 0 message, r⟩] })
    (fun r => shiftLedger_target offsets ledger (.inr (.fresh handle length)) r handle message r) (fun r => ?_) (fun r => ⟨?_, ?_⟩)
  · intro entry hentry
    rcases List.mem_append.mp hentry with hentry | hentry
    · exact long entry hentry
    · rw [List.mem_singleton.mp hentry, hlength]
      exact admitted.1
  · exact ⟨_, List.getElem?_concat_length, rfl⟩
  · refine ⟨⟨handle, shiftFrom offsets 0 message, r⟩, ?_, rfl⟩
    simp [shiftLedger]

/-- **One coupled query.** In the zeroed-plaintext world, every adversary query from related states is coupled: with the native coins of the `index`-th admitted fresh message relabelled by the shift, the replies are equal and the states related, or both runs escape. -/
theorem step_couple (modes : Label n → KeyMode) (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds)
    (index : ℕ) (offsets : ℕ → Fin 256) (query : FullSpec.Domain) (s t : Ledger × NativeState n E)
    (related : FreshRelated bounds index offsets s t) :
    Swap (SimRel (FreshRelated bounds index offsets) (FreshEscaped index) (FreshEscaped index))
      ((fullImpl modes zeros setup codec route env serverKid bounds query).run s)
      ((fullImpl modes zeros setup codec route env serverKid bounds query).run t) := by
  obtain ⟨ledger, state⟩ := s
  obtain ⟨ledger', state'⟩ := t
  obtain ⟨hstate, hledger, long⟩ := related
  dsimp only at hstate hledger long
  subst state' ledger'
  rcases query with forwarded | (⟨handle, left, right⟩ | ⟨handle, length⟩)
  · exact commute_couple modes zeros setup codec route env serverKid bounds index offsets _ ledger state long
      (ledger_shift_forward _ codec serverKid bounds index offsets forwarded ledger)
  · exact commute_couple modes zeros setup codec route env serverKid bounds index offsets _ ledger state long
      (ledger_shift_test _ codec serverKid bounds index offsets handle left right ledger)
  · by_cases target : (bounds.min ≤ length ∧ length ≤ bounds.max) ∧ ledger.fresh.length = index
    · obtain ⟨admitted, rfl⟩ := target
      exact target_couple modes setup codec route env serverKid bounds offsets handle length ledger state admitted
        long
    · exact commute_couple modes zeros setup codec route env serverKid bounds index offsets _ ledger state long
        (ledger_shift_fresh _ codec serverKid bounds index offsets handle length ledger target)


end BeaconcryptCore.Computational.CborRawRecordFreshCoupling

/-- info: 'BeaconcryptCore.Computational.CborRawRecordFreshCoupling.freshEscaped_keep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordFreshCoupling.freshEscaped_keep

/-- info: 'BeaconcryptCore.Computational.CborRawRecordFreshCoupling.commute_couple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordFreshCoupling.commute_couple

/-- info: 'BeaconcryptCore.Computational.CborRawRecordFreshCoupling.send_couple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordFreshCoupling.send_couple

/-- info: 'BeaconcryptCore.Computational.CborRawRecordFreshCoupling.bytes_couple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordFreshCoupling.bytes_couple

/-- info: 'BeaconcryptCore.Computational.CborRawRecordFreshCoupling.fullImpl_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordFreshCoupling.fullImpl_fresh

/-- info: 'BeaconcryptCore.Computational.CborRawRecordFreshCoupling.target_couple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordFreshCoupling.target_couple

/-- info: 'BeaconcryptCore.Computational.CborRawRecordFreshCoupling.step_couple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordFreshCoupling.step_couple
