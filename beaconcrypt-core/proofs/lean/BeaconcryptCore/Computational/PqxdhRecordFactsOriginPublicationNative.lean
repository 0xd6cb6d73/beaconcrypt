-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationDispatch

/-! Exact native-command history for the temporal publication invariant. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationNative
open CtxRomAuth AdaptiveCtxReceive
open PqxdhRecordLiftIdeal PqxdhRecordLiftInterface PqxdhRecordLiftFlat
open PqxdhRecordFactsOriginReplay PqxdhRecordFactsOriginServices PqxdhRecordFactsOriginAmbient
open PqxdhRecordFactsOriginHandles PqxdhRecordFactsOriginReceive
open PqxdhRecordFactsOriginPublicationStep PqxdhRecordFactsOriginPublicationDispatch
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhDeploymentInterface (Handle Entry Spec)
variable {n : Nat} {ι KemSK Reader Response E X : Type} {baseSpec : OracleSpec ι}

/-- Every adaptive restricted environment program retains the complete coordinate states and writer logs. -/
theorem effects_program_kept (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (client : OracleComp (EnvEffects n) X) (control : PqxdhRecordLiftProtocol.Control n)
    (before : CtxPrivate n) (result : (X × PqxdhRecordLiftProtocol.Control n) × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (ctxInterpreter modes replace setup codec)
      ((simulateQ PqxdhRecordLiftProtocol.effects client).run control)).run before)) :
    Kept before result.2 := by
  induction client using OracleComp.inductionOn generalizing control before result with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    subst result
    exact Kept.refl before
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨inner, reached, continued⟩ := supported
    exact Kept.trans before inner.2 result.2
      (effects_kept modes replace setup codec query control before inner reached)
      (ih inner.1.1 inner.1.2 inner.2 result continued)

/-- The restricted environment embedding dispatches every callback through the literal source effects. -/
theorem effect_lift (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (client : OracleComp (EnvEffects n) X) :
    simulateQ (PqxdhRecordLiftProtocol.handler codec.frameRead route) (simulateQ effectLift client) =
      simulateQ PqxdhRecordLiftProtocol.effects client := by
  induction client using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure]
  | query_bind query next ih =>
    simp only [simulateQ_bind, effectLift, simulateQ_spec_query, PqxdhRecordLiftProtocol.handler, ih]

/-- Native calls other than the two honest-record request constructors. -/
def NonSending : Spec.Domain → Prop
  | .inr (.serverSend _ _) | .inr (.beaconSend _ _) => False
  | _ => True

/-- Every non-send native call preserves the exact hidden seal dictionaries, with all other effects retained. -/
theorem native_nonSend_seals (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (query : Spec.Domain) (nonsending : NonSending query)
    (before : NativeState n E) (result : Spec.Range query × NativeState n E)
    (supported : result ∈ support ((nativeImpl modes replace setup codec route env query).run before)) :
    ∀ label, (result.2.2.keys label).1.successfulSeals = (before.2.keys label).1.successfulSeals := by
  rcases query with coin | command
  · rw [nativeImpl_coin, support_map] at supported
    obtain ⟨reply, reached, rfl⟩ := supported
    exact fun _ => rfl
  · cases command
    case serverSend keyId plaintext => exact False.elim nonsending
    case beaconSend owner plaintext => exact False.elim nonsending
    case serverRaw raw =>
      simp only [nativeImpl_run, PqxdhRecordFactsOriginNative.native_serverRaw_run, simulateQ_map,
        StateT.run_map, Functor.map_map, support_map] at supported
      obtain ⟨inner, reached, rfl⟩ := supported
      exact serverReceive_seals modes ideal replace setup codec route before.1.2 raw before.2 inner reached
    case beaconRaw owner raw =>
      simp only [nativeImpl_run, PqxdhRecordFactsOriginNative.native_beaconRaw_run, simulateQ_map,
        StateT.run_map, Functor.map_map, support_map] at supported
      obtain ⟨inner, reached, rfl⟩ := supported
      exact beaconReceive_seals modes ideal replace setup codec before.1.2 owner raw before.2 inner reached
    all_goals
      rw [nativeImpl_run, support_map] at supported
      obtain ⟨inner, reached, rfl⟩ := supported
    case hash bytes =>
      simp only [native, StateT.lift, StateT.run, effectLift, simulateQ_spec_query,
        PqxdhRecordLiftProtocol.handler, bind_pure_comp, simulateQ_map] at reached
      change inner ∈ support ((simulateQ (ctxInterpreter modes replace setup codec)
        ((fun reply => ((reply.1, before.1.1), reply.2)) <$>
          (PqxdhRecordLiftProtocol.effects (.inr (.hash bytes))).run before.1.2)).run before.2) at reached
      simp only [simulateQ_map, StateT.run_map, support_map] at reached
      obtain ⟨effect, effectReached, rfl⟩ := reached
      exact fun label => congrArg (fun keys => (keys label).1.successfulSeals)
        (effects_kept modes replace setup codec _ before.1.2 before.2 effect effectReached).keys
    all_goals
      simp only [native, environmentStep, StateT.run, effect_lift] at reached
      exact fun label => congrArg (fun keys => (keys label).1.successfulSeals)
        (effects_program_kept modes replace setup codec _ before.1.2 before.2 inner reached).keys

/-- The current transcript entry either publishes the generated hidden frame or its literal writer failed. -/
def CreatedAt (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (control : PqxdhRecordLiftProtocol.Control n) (event : Entry) (label : Label n)
    (entry : CtxSuccessfulSeal) : Prop :=
  ∃ handle frame, OwnsLabel control label handle ∧ Matches frame entry ∧
    (codec.frameWrite frame = none ∨ ∃ encrypted, event.published = some (handle, encrypted) ∧
      codec.frameRead encrypted.ciphertext = some frame)

/-- A native reply creates no hidden entry except an actual send with its literal writer outcome. -/
theorem native_entry (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : Environment n E) (query : Spec.Domain) (before : NativeState n E)
    (safe : PqxdhRecordLiftProtocolHistory.Safe before.1.2)
    (result : Spec.Range query × NativeState n E)
    (supported : result ∈ support ((nativeImpl modes replace setup codec route env query).run before))
    (label : Label n) (entry : CtxSuccessfulSeal)
    (member : entry ∈ (result.2.2.keys label).1.successfulSeals) :
    entry ∈ (before.2.keys label).1.successfulSeals ∨
      CreatedAt codec before.1.2 ⟨.inl query, result.1⟩ label entry := by
  rcases query with coin | command
  · exact Or.inl ((native_nonSend_seals modes ideal replace setup codec route env _ (by trivial) before result supported label) ▸ member)
  · cases command
    case serverSend keyId plaintext =>
      simp only [nativeImpl_run, native_serverSend_run, simulateQ_map, StateT.run_map,
        Functor.map_map, support_map] at supported
      obtain ⟨inner, reached, rfl⟩ := supported
      rcases serverSend_entry modes ideal replace setup codec route readback before.1.2 safe keyId plaintext
        before.2 inner reached label entry member with prior | ⟨owned, frame, matched, outcome⟩
      · exact Or.inl prior
      · refine Or.inr ⟨.peer keyId, frame, owned, matched, ?_⟩
        rcases outcome with failed | ⟨encrypted, returned, decoded⟩
        · exact Or.inl failed
        · exact Or.inr ⟨encrypted, by simp only [Entry.published, returned], decoded⟩
    case beaconSend owner plaintext =>
      simp only [nativeImpl_run, native_beaconSend_run, simulateQ_map, StateT.run_map,
        Functor.map_map, support_map] at supported
      obtain ⟨inner, reached, rfl⟩ := supported
      rcases beaconSend_entry modes ideal replace setup codec readback before.1.2 safe owner plaintext
        before.2 inner reached label entry member with prior | ⟨owned, frame, matched, outcome⟩
      · exact Or.inl prior
      · refine Or.inr ⟨.owner owner, frame, owned, matched, ?_⟩
        rcases outcome with failed | ⟨encrypted, returned, decoded⟩
        · exact Or.inl failed
        · exact Or.inr ⟨encrypted, by simp only [Entry.published, returned], decoded⟩
    all_goals exact Or.inl ((native_nonSend_seals modes ideal replace setup codec route env _ (by trivial)
      before result supported label) ▸ member)

/-- A literal accepted native record uses a dictionary entry already present before that receive. -/
theorem native_received_before (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : Environment n E) (query : Spec.Domain) (before : NativeState n E)
    (safe : PqxdhRecordLiftProtocolHistory.Safe before.1.2)
    (result : Spec.Range query × NativeState n E)
    (supported : result ∈ support ((nativeImpl modes replace setup codec route env query).run before))
    (receiver : PqxdhDeploymentInterface.Receiver) (raw : Pqxdh.Bytes)
    (opened : RawCtxWholeOwner.Decrypted)
    (received : (⟨.inl query, result.1⟩ : Entry).received = some (receiver, raw, .Some opened)) :
    ∃ handle, receivingHandle route receiver raw = some handle ∧
      PqxdhRecordFactsOriginAccepted.Accepted codec before.1.2 before.2 handle raw opened := by
  have nonsending : NonSending query := by
    rcases query with coin | command
    · trivial
    · cases command <;> simp_all only [NonSending, Entry.received, reduceCtorEq]
  have kept := native_nonSend_seals modes ideal replace setup codec route env query nonsending before result supported
  obtain ⟨handle, routed, accepted⟩ :=
    (PqxdhRecordFactsOriginNative.native_entryFacts_before modes ideal replace setup codec route readback env
      query before safe result supported).2 receiver raw opened received
  refine ⟨handle, routed, ?_⟩
  simpa only [PqxdhRecordFactsOriginAccepted.Accepted, kept] using accepted

end BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationNative

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationNative.effects_program_kept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationNative.effects_program_kept

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationNative.effect_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationNative.effect_lift

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationNative.native_nonSend_seals' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationNative.native_nonSend_seals

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationNative.native_entry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationNative.native_entry

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationNative.native_received_before' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationNative.native_received_before
