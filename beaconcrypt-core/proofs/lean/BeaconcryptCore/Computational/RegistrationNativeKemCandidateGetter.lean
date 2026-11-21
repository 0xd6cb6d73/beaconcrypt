-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemOpenTarget
import BeaconcryptCore.Computational.RegistrationNativeKemCandidateLinkedCall
import BeaconcryptCore.Computational.RegistrationNativeKemOpenGetterReceipt

/-! The original broad canonical native APP target in the actual candidate source has its retained born owner, successful parsed SDK call and exact getter-zero ciphertext/candidate reply in one operational receipt. There is no unchanged-bundle, no-prior-finish, current-birth-at-getter or source-simulation premise. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemCandidateGetter
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhDeploymentInterface (Budget FreshBounds Mode)
open RegistrationNativeWire (Wire)
open RegistrationNativeKemOpenProvider (State counter)
open RegistrationNativeKemCut (Cut scan)
open PqxdhKemIndCca
variable {ι KemSK Value : Type} {base : OracleSpec ι} {n : Nat} {mlSource : RegistrationNativeMldsa.Source}

/-- The complete original-ledger and selected-provider receipt, before any later root or record reduction. -/
def Receipt (setup : Setup base KemSK) (checks : Checks) (wire : Wire) (serverKeyId : U64)
    (budget : Budget) (target : Fin budget.accept × Fin budget.capacity) (claim : Value → Option (Nat × Pqxdh.Bytes))
    (provider : QueryImpl (RegistrationNativeKemParsedRouting.Spec n mlSource KemSK) (OptionT (StateT (State n mlSource KemSK) ProbComp)))
    (publicKey : MlKem768PublicKey) (challenge : MlKem768Ciphertext) (candidate : MlKemSharedSecret)
    (finalState : RegistrationNativeKemServerState.State n mlSource) (value : Value) (ledger : RegistrationNativeLedger.State) : Prop :=
    ∃ index guess entry session owner pre raw packet post,
      ∃ first last : State n mlSource KemSK, ∃ next reached replied,
      claim value = some (index, guess) ∧ ledger.ledger.fresh[index]? = some entry ∧ entry.message = guess ∧
      PqxdhDeploymentTranscript.designateIn setup.source.crypto (RegistrationNativeWire.ledgerCodec wire)
        serverKeyId budget ledger.ledger.transcript entry.handle = some (session, target.2) ∧
      finalState.beacons[target.2.val]? = some owner ∧ owner.kemHandle = target.2.val ∧ owner.kemPublic = publicKey ∧
      ledger.transcript = pre ++ (RegistrationNativeInterface.Entry.mk (.inl (.inr (.accept raw))) (some session.val)) :: post ∧
      RegistrationNativeEvents.parsedAcceptCount wire pre = target.1.val ∧ RegistrationNativeWire.readInit wire raw = some packet ∧
      counter first = target.1.val ∧ first.2 = none ∧
      (some (.ok (some session.val)), last) ∈ support
        (((simulateQ (provider)
          (simulateQ (RegistrationNativeKemOpenFrame.lower true) (RegistrationNativeKemServerInterface.typedAccept setup checks packet))).run).run first) ∧
      (some (Cut.pending publicKey next), reached) ∈ support
        (((scan (provider)
          (simulateQ (RegistrationNativeKemOpenFrame.lower true) (RegistrationNativeKemServerInterface.typedAccept setup checks packet)) 0).run).run first) ∧
      (some (challenge, candidate), replied) ∈ support
        (((provider (.inr (.inr publicKey))).run).run reached) ∧
      (some (.ok (some session.val)), last) ∈ support
        (((simulateQ (provider)
          (next (challenge, candidate))).run).run replied)


/-- Actual canonical broad APP success in the candidate observation supplies the original session and its literal selected SDK getter receiving that same observation's candidate. -/
theorem selected_getter (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential mlSource)
    (readback : RegistrationNativeWire.InitReadBack wire) (bounds : FreshBounds) (mode : Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (budget : Budget)
    (target : Fin budget.accept × Fin budget.capacity) (claim : Value → Option (Nat × Pqxdh.Bytes))
    (chosen : MlKem768PublicKey × KemSK) (others : Fin budget.create → MlKem768PublicKey × KemSK) (real : Bool)
    (localState : RegistrationNativeKemServerState.State n mlSource) (zero : localState.parsedAccepts = 0) (empty : localState.beacons = [])
    (record : RegistrationNativeKemCandidateObservation.Record (RegistrationNativeKemParsedRouting.Ambient n mlSource)
      KemSK (RegistrationNativeKemServerState.State n mlSource) (Value × RegistrationNativeLedger.State))
    (supported : record ∈ support (RegistrationNativeKemCandidateObservation.run setup.baseImpl setup.kem
      (RegistrationNativeKemParsedRouting.other setup checks wire route representation created credential) target.2 chosen others
      (RegistrationNativeKemFullSource.program setup checks wire created.server.server.metadata.sender bounds mode work target.1.val)
      (localState, PqxdhDynamicKemRouter.empty) 0 real))
    (value : Value) (ledger : RegistrationNativeLedger.State) (returned : record.value = some (value, ledger))
    (winning : RegistrationNativeParsedTargetCanonical.CEAppAt setup.source.crypto wire created.server.server.metadata.sender budget target claim
      (value, (ledger, ()))) :
    ∃ index guess entry session owner pre raw packet post,
      ∃ first last : State n mlSource KemSK, ∃ next reached replied,
      claim value = some (index, guess) ∧ ledger.ledger.fresh[index]? = some entry ∧ entry.message = guess ∧
      PqxdhDeploymentTranscript.designateIn setup.source.crypto (RegistrationNativeWire.ledgerCodec wire)
        created.server.server.metadata.sender budget ledger.ledger.transcript entry.handle = some (session, target.2) ∧
      record.finalState.1.beacons[target.2.val]? = some owner ∧ owner.kemHandle = target.2.val ∧ owner.kemPublic = chosen.1 ∧
      ledger.transcript = pre ++ (RegistrationNativeInterface.Entry.mk (.inl (.inr (.accept raw))) (some session.val)) :: post ∧
      RegistrationNativeEvents.parsedAcceptCount wire pre = target.1.val ∧ RegistrationNativeWire.readInit wire raw = some packet ∧
      counter first = target.1.val ∧ first.2 = none ∧
      (some (.ok (some session.val)), last) ∈ support
        (((simulateQ (RegistrationNativeKemOpenProvider.implementation setup checks wire route representation created credential
          target.2.val (List.ofFn (target.2.insertNth chosen others)) chosen.1 real)
          (simulateQ (RegistrationNativeKemOpenFrame.lower true) (RegistrationNativeKemServerInterface.typedAccept setup checks packet))).run).run first) ∧
      (some (Cut.pending chosen.1 next), reached) ∈ support
        (((scan (RegistrationNativeKemOpenProvider.implementation setup checks wire route representation created credential
          target.2.val (List.ofFn (target.2.insertNth chosen others)) chosen.1 real)
          (simulateQ (RegistrationNativeKemOpenFrame.lower true) (RegistrationNativeKemServerInterface.typedAccept setup checks packet)) 0).run).run first) ∧
      (some (record.encapsulation.1, record.candidate real), replied) ∈ support
        (((RegistrationNativeKemOpenProvider.implementation setup checks wire route representation created credential
          target.2.val (List.ofFn (target.2.insertNth chosen others)) chosen.1 real (.inr (.inr chosen.1))).run).run reached) ∧
      (some (.ok (some session.val)), last) ∈ support
        (((simulateQ (RegistrationNativeKemOpenProvider.implementation setup checks wire route representation created credential
          target.2.val (List.ofFn (target.2.insertNth chosen others)) chosen.1 real)
          (next (record.encapsulation.1, record.candidate real))).run).run replied) := by
  obtain ⟨index, guess, entry, session, claimed, fresh, designated, accepted, guessed⟩ := winning
  have actual := RegistrationNativeKemSwitchObservation.observation_support setup.baseImpl setup.kem
    (RegistrationNativeKemParsedRouting.other setup checks wire route representation created credential) real target.2 chosen others
    (RegistrationNativeKemFullSource.program setup checks wire created.server.server.metadata.sender bounds mode work target.1.val)
    (localState, PqxdhDynamicKemRouter.empty) record supported
  rw [RegistrationNativeKemSwitchObservation.observe, returned] at actual
  have prior := RegistrationNativeKemOpenRosterRun.empty_holds (List.ofFn (target.2.insertNth chosen others)) localState empty none
  obtain ⟨owner, canonicalRaw, canonicalPacket, keys, ownerAt, ownerHandle, ownerKey, canonicalFirst, canonicalRead, verified, selectedKey⟩ :=
    RegistrationNativeKemOpenTarget.designated_selected setup checks wire route representation created credential real target.1.val
      readback bounds mode work budget target.2 chosen others ((localState, PqxdhDynamicKemRouter.empty), none) _ prior value ledger actual
        entry.handle session designated
  obtain ⟨pre, raw, packet, post, first, last, trace, firstAccept, count, read, counted, inactive, linked, success⟩ :=
    RegistrationNativeKemCandidateLinkedCall.accepted_call setup checks wire route representation created credential real target.1.val
      bounds mode work target.2 chosen others localState zero record supported value ledger returned session.val accepted
  have consistent := RegistrationNativeKemOpenPublicationRun.program_consistent setup checks wire route representation created credential
    target.2.val (List.ofFn (target.2.insertNth chosen others)) chosen.1 real target.1.val bounds mode work
    ((localState, PqxdhDynamicKemRouter.empty), none) _ value ledger actual
  have firstOriginal : PqxdhDeploymentTranscript.acceptOf ledger.ledger.transcript session.val = some raw := by
    simpa only [consistent] using firstAccept
  have rawEq : canonicalRaw = raw := Option.some.inj (canonicalFirst.symm.trans firstOriginal)
  subst canonicalRaw
  have packetEq : canonicalPacket = packet := Option.some.inj (canonicalRead.symm.trans read)
  subst canonicalPacket
  obtain ⟨label, active⟩ := RegistrationNativeKemOpenGetterReceipt.sdk_active setup checks wire route representation created credential
    target.2.val (List.ofFn (target.2.insertNth chosen others)) chosen.1 real packet session.val first last inactive success
  have assigned : ∃ label, RegistrationNativeKemSwitchObservation.phase record.cut (record.encapsulation.1, record.candidate real) = some label := by
    rcases linked with impossible | same
    · rw [active] at impossible
      cases impossible
    · exact ⟨label, same.trans active⟩
  have finalPhase : RegistrationNativeKemSwitchObservation.phase record.cut
      (record.encapsulation.1, record.candidate real) = some (record.encapsulation.1, record.candidate real) := by
    cases cutEq : record.cut with
    | none => simp only [cutEq, RegistrationNativeKemSwitchObservation.phase, reduceCtorEq, exists_const] at assigned
    | some suspended =>
        cases suspended with
        | complete completed => simp only [cutEq, RegistrationNativeKemSwitchObservation.phase, reduceCtorEq, exists_const] at assigned
        | pending key next => rfl
  have linkedCandidate : RegistrationNativeKemOpenPhaseOrder.Extends last.2 (some (record.encapsulation.1, record.candidate real)) := by
    simpa only [finalPhase] using linked
  obtain ⟨next, reached, replied, _noPhase, prefixSupport, called, continued⟩ :=
    RegistrationNativeKemOpenGetterReceipt.sdk_reply setup checks wire route representation created credential
      target.2.val (List.ofFn (target.2.insertNth chosen others)) chosen.1 real packet keys verified selectedKey session.val
        first last inactive record.encapsulation.1 (record.candidate real) linkedCandidate success
  exact ⟨index, guess, entry, session, owner, pre, raw, packet, post, first, last, next, reached, replied,
    claimed, fresh, guessed, designated, ownerAt, ownerHandle, ownerKey, trace, count, read, counted, inactive,
    success, prefixSupport, called, continued⟩

end BeaconcryptCore.Computational.RegistrationNativeKemCandidateGetter

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCandidateGetter.selected_getter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCandidateGetter.selected_getter
