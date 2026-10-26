-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginGlobal

/-!
# AG lift R2, send side: every CE production has a seal with its plaintext (CE-12 P4 step 3, design-v2 section 7.6)

The send-side counterpart of `PqxdhDeploymentHeadlineAgreeReceive`: the frozen record-origin route for returned records (`PqxdhRecordFactsOriginPublished.Published`, `PqxdhRecordFactsOriginNative.EntryFacts`, `PqxdhRecordFactsOriginLedger`) with the sealed plaintext kept.

- `PublishedPlain codec control secret handle encrypted plaintext`: the handle is caller-known, or a successful seal with plaintext `plaintext`, at a label the handle owns, matches the decoded frame of the returned ciphertext. The send chain `sealing_plain`, `kernelSend_plain`, `ownerSend_plain`, `ownerRun_plain`, `serverSend_plain`, `beaconSend_plain`, `native_serverSend_plain`, `native_beaconSend_plain` and `native_send_plain` (the experiment's own sends for `test` and `fresh`), with persistence `publishedPlain_mono` and `native_final`.
- The CE productions with their plaintexts, read on the secrecy ledger (`PqxdhDeploymentSecrecy.Ledger`, part of the CE observation): `entryPlain` (an explicit Server or Beacon send returns its handle, ciphertext and query plaintext; an admitted test returns its handle, ciphertext and the message the ledger's hidden bit chose) and `Sent` (a production of a transcript entry, or an admitted fresh message with its reply in the ledger's fresh list). `TestFree`: before the first admitted test no production depends on the bit.
- The ledger invariant `InvariantPlain` (`ledger_plain`, `full_invariant_plain`, `full_program_invariant_plain`) and `ctxRun_sentPlain`: on every supported outcome of every ideal CTX world, every CE production of the final ledger has its witness with the (replaced) produced plaintext at the final control and private state.

Premise: `FrameReadBack codec`, the frozen codec premise that reads a written frame back, as for `PqxdhRecordFactsOriginNative.EntryFacts`. No assumption or contract, and no probability. No `PqxdhBoundary*` module is imported.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlainSend
open CtxRomAuth AdaptiveCtxReceive
open PqxdhRecordLiftInterface PqxdhRecordLiftIdeal PqxdhRecordLiftFlat
open PqxdhRecordFactsOriginReplay PqxdhRecordFactsOriginServices
open PqxdhRecordFactsOriginHandles PqxdhRecordFactsOriginSend
open PqxdhRecordLiftProtocolHistory (Safe Step)
open PqxdhRecordLiftWorldCompiler (Label StoredKernel LabeledKernel)
open PqxdhDeploymentInterface (Handle Entry Spec FullSpec FreshBounds Mode ModeSpec asModeO)
variable {n : Nat} {ι KemSK Reader Response E X : Type} {baseSpec : OracleSpec ι}

/-! ### The send chain with the sealed plaintext -/

/-- A returned record with a plaintext: its handle is caller-known, or a successful seal with that plaintext, at a label the handle owns, matches the record's decoded frame. -/
def PublishedPlain (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (control : PqxdhRecordLiftProtocol.Control n) (secret : CtxPrivate n)
    (handle : Handle) (encrypted : RawCtxSourceSend.Encrypted) (plaintext : Pqxdh.Bytes) : Prop :=
  KnownAt control handle ∨
    ∃ label, OwnsLabel control label handle ∧ ∃ frame, codec.frameRead encrypted.ciphertext = some frame ∧
      ∃ entry ∈ (secret.keys label).1.successfulSeals, Matches frame entry ∧ entry.input.plaintext = plaintext

/-- A successful hidden writer decodes to the frame of a seal in its post-seal dictionary whose plaintext is the sealing request's (replaced) plaintext. -/
theorem sealing_plain (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (pending : PqxdhRecordLiftProtocol.Sealing n) (before after : CtxPrivate n)
    (encrypted : RawCtxSourceSend.Encrypted)
    (supported : (some encrypted, after) ∈ support
      ((ctxInterpreter modes replace setup codec (.sealing pending)).run before)) :
    ∃ frame, codec.frameRead encrypted.ciphertext = some frame ∧
      ∃ entry ∈ (after.keys pending.material).1.successfulSeals, Matches frame entry ∧
        entry.input.plaintext = replace pending.context.plaintext := by
  have traced := (sealing_trace modes ideal replace setup codec pending before (some encrypted, after) supported).2
  obtain ⟨width, record, dictionary, _, reply⟩ := traced.resolve_left (by simp)
  obtain ⟨ciphertext, written, equal⟩ := Option.map_eq_some_iff.mp reply.symm
  subst encrypted
  refine ⟨_, (readback _ _ written).2, ⟨RawCtxSelectedMessageSealing.selectedInput
    (materialAt before.base.chain pending.material).2 pending.sequence (replaceContext replace pending.context) width,
    record⟩, ?_, ⟨rfl, rfl, rfl⟩, rfl⟩
  rw [dictionary]
  exact List.mem_cons_self

/-- A successful opaque hidden send leaves the returned frame in its sending-coordinate dictionary, with the send context's (replaced) plaintext. -/
theorem kernelSend_plain (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (slot : PqxdhRecordLiftInterface.Slot n) (entry : LabeledKernel n)
    (context : RawCtxSourceSend.SealContext) (before : CtxPrivate n)
    (result : (StoredKernel n × Option RawCtxSourceSend.Encrypted) × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (ctxInterpreter modes replace setup codec)
      (PqxdhRecordLiftProtocol.kernelSend (.hidden slot entry) context)).run before))
    (encrypted : RawCtxSourceSend.Encrypted) (returned : result.1.2 = some encrypted) :
    ∃ frame, codec.frameRead encrypted.ciphertext = some frame ∧
      ∃ sealedEntry ∈ (result.2.keys entry.send_chain).1.successfulSeals, Matches frame sealedEntry ∧
        sealedEntry.input.plaintext = replace context.plaintext := by
  have tracked := PqxdhRecordLiftChainState.send_begin_tracked entry context
  cases admitted : RawCtxChainSend.normalBegin entry context with
  | exhausted original prior =>
    simp only [PqxdhRecordLiftProtocol.kernelSend, PqxdhRecordLiftOpaqueDrivers.admittedSend,
      admitted, PqxdhRecordLiftOpaqueDrivers.sendProgram, simulateQ_pure,
      StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at supported
    simp only [supported, reduceCtorEq] at returned
  | requested pending =>
    simp only [PqxdhRecordLiftProtocol.kernelSend, PqxdhRecordLiftOpaqueDrivers.admittedSend,
      admitted, PqxdhRecordLiftOpaqueDrivers.sendProgram, simulateQ_bind, simulateQ_spec_query,
      simulateQ_pure, PqxdhRecordLiftProtocol.localLift, StateT.run_bind, StateT.run_pure,
      bind_assoc, pure_bind, mem_support_bind_iff] at supported
    obtain ⟨looked, lookupSupported, sealed, sealSupported, finished⟩ := supported
    obtain rfl := (mem_support_pure_iff _ _).mp finished
    rw [admitted] at tracked
    simpa only [RawCtxChainSend.ready, tracked.2.2.1, tracked.2.1] using
      sealing_plain modes ideal replace setup codec readback
        (RawCtxChainSend.ready pending (PqxdhRecordLiftChainState.advance pending.request 1, pending.request))
        looked.2 sealed.2 encrypted (by simpa only [← returned, Prod.eta] using sealSupported)

/-- The complete owner send classifies each successful writer by its stored kernel and sending handle, with the requested (replaced) plaintext. -/
theorem ownerSend_plain (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (control : PqxdhRecordLiftProtocol.Control n) (safe : Safe control)
    (handle : Handle) (owner : PqxdhRecordLiftWorldCompiler.Owner n)
    (stored : handleKernel control handle = some owner.kernel) (sender : Std.U64) (plaintext : Pqxdh.Bytes)
    (before : CtxPrivate n)
    (result : (Option RawCtxSourceSend.Encrypted × PqxdhRecordLiftWorldCompiler.Owner n) × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (ctxInterpreter modes replace setup codec)
      (PqxdhRecordLiftProtocol.ownerSend sender plaintext owner)).run before))
    (encrypted : RawCtxSourceSend.Encrypted) (returned : result.1.1 = some encrypted) :
    PublishedPlain codec control result.2 handle encrypted (replace plaintext) := by
  cases storedKind : owner.kernel with
  | known kernel =>
    exact Or.inl (PqxdhRecordFactsOriginPublished.known_of_handleKernel control handle kernel
      (by simpa only [storedKind] using stored))
  | hidden slot entry =>
    simp only [PqxdhRecordLiftProtocol.ownerSend] at supported
    split at supported
    · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      simp only [supported, reduceCtorEq] at returned
    · simp only [storedKind, bind_pure_comp, simulateQ_map, StateT.run_map, support_map] at supported
      obtain ⟨inner, reached, rfl⟩ := supported
      refine Or.inr ⟨entry.send_chain, ?_, kernelSend_plain modes ideal replace setup codec readback
        slot entry _ before inner reached encrypted returned⟩
      simpa [Claims] using sending_claim control safe handle slot entry (by simpa only [storedKind] using stored)

/-- The owner command keeps the send's plaintext witness through its tagged publication callback. -/
theorem ownerRun_plain (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (control : PqxdhRecordLiftProtocol.Control n) (safe : Safe control)
    (handle : Handle) (owner : PqxdhRecordLiftWorldCompiler.Owner n)
    (stored : handleKernel control handle = some owner.kernel) (sender : Std.U64) (plaintext : Pqxdh.Bytes)
    (before : CtxPrivate n)
    (result : (Option RawCtxSourceSend.Encrypted × PqxdhRecordLiftWorldCompiler.Owner n) × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (ctxInterpreter modes replace setup codec)
      (PqxdhRecordLiftProtocol.ownerRun (some handle) sender codec.frameRead (.inl plaintext) owner)).run before))
    (encrypted : RawCtxSourceSend.Encrypted) (returned : result.1.1 = some encrypted) :
    PublishedPlain codec control result.2 handle encrypted (replace plaintext) := by
  simp only [PqxdhRecordLiftProtocol.ownerRun, PqxdhRecordLiftProtocol.ownerStep,
    simulateQ_bind, simulateQ_spec_query, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    mem_support_bind_iff] at supported
  obtain ⟨sent, sendSupported, published, publishSupported, finished⟩ := supported
  rw [PqxdhRecordFactsOriginBuffers.publish_callback, support_pure, Set.mem_singleton_iff] at publishSupported
  subst published
  obtain rfl := (mem_support_pure_iff _ _).mp finished
  exact ownerSend_plain modes ideal replace setup codec readback control safe handle owner stored
    sender plaintext before sent sendSupported encrypted returned

/-- A returned Server ciphertext keeps the requested peer and plaintext. -/
theorem serverSend_plain (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (control : PqxdhRecordLiftProtocol.Control n) (safe : Safe control)
    (keyId : Std.U64) (plaintext : Pqxdh.Bytes) (before : CtxPrivate n)
    (result : (Option RawCtxSourceSend.Encrypted × PqxdhRecordLiftProtocol.Control n) × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (ctxInterpreter modes replace setup codec)
      (PqxdhRecordLiftProtocol.serverStep codec.frameRead route (.inl (plaintext, keyId)) control)).run before))
    (encrypted : RawCtxSourceSend.Encrypted) (returned : result.1.1 = some encrypted) :
    PublishedPlain codec control result.2 (.peer keyId) encrypted (replace plaintext) := by
  rcases existing : control.server with _ | server
  · simp_all only [PqxdhRecordLiftProtocol.serverStep, simulateQ_pure, StateT.run_pure,
      support_pure, Set.mem_singleton_iff, reduceCtorEq]
  · rcases found : server.peers keyId with _ | peer
    · simp_all only [PqxdhRecordLiftProtocol.serverStep, simulateQ_pure, StateT.run_pure,
        support_pure, Set.mem_singleton_iff, reduceCtorEq]
    · simp only [PqxdhRecordLiftProtocol.serverStep, existing, found, bind_pure_comp,
        simulateQ_map, StateT.run_map, support_map] at supported
      obtain ⟨inner, reached, rfl⟩ := supported
      apply ownerRun_plain modes ideal replace setup codec readback control safe (.peer keyId)
        (PqxdhRecordLiftWorldCompiler.serverOwner server keyId peer) _ server.sender plaintext
        before inner reached encrypted returned
      simp only [handleKernel, existing, Option.bind_some, found, Option.map_some,
        PqxdhRecordLiftWorldCompiler.serverOwner]

/-- A returned Beacon ciphertext keeps the requested owner and plaintext. -/
theorem beaconSend_plain (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (control : PqxdhRecordLiftProtocol.Control n) (safe : Safe control)
    (owner : Nat) (plaintext : Pqxdh.Bytes) (before : CtxPrivate n)
    (result : (Option RawCtxSourceSend.Encrypted × PqxdhRecordLiftProtocol.Control n) × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (ctxInterpreter modes replace setup codec)
      (PqxdhRecordLiftProtocol.beaconStep codec.frameRead owner (.inl plaintext) control)).run before))
    (encrypted : RawCtxSourceSend.Encrypted) (returned : result.1.1 = some encrypted) :
    PublishedPlain codec control result.2 (.owner owner) encrypted (replace plaintext) := by
  rcases found : control.owners[owner]? with _ | (phase | ⟨shell, kernel⟩)
  · simp_all only [PqxdhRecordLiftProtocol.beaconStep, PqxdhDeploymentNative.absent,
      simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, reduceCtorEq]
  · simp_all only [PqxdhRecordLiftProtocol.beaconStep, simulateQ_pure, StateT.run_pure,
      support_pure, Set.mem_singleton_iff, reduceCtorEq]
  · simp only [PqxdhRecordLiftProtocol.beaconStep, found, bind_pure_comp,
      simulateQ_map, StateT.run_map, support_map] at supported
    obtain ⟨inner, reached, rfl⟩ := supported
    apply ownerRun_plain modes ideal replace setup codec readback control safe (.owner owner)
      (PqxdhRecordLiftWorldCompiler.beaconOwner shell kernel (control.ownerRaw owner))
      _ shell.identityKeyId plaintext before inner reached encrypted returned
    simp only [handleKernel, found, Option.bind_some, PqxdhRecordLiftWorldCompiler.beaconOwner]

/-- The plaintext witness survives control steps that keep caller-known handles and seal-dictionary growth. -/
theorem publishedPlain_mono (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (control next : PqxdhRecordLiftProtocol.Control n) (before after : CtxPrivate n)
    (progress : Step control next) (known : ∀ handle, KnownAt control handle → KnownAt next handle)
    (seals : ∀ label entry, entry ∈ (before.keys label).1.successfulSeals → entry ∈ (after.keys label).1.successfulSeals)
    (handle : Handle) (encrypted : RawCtxSourceSend.Encrypted) (plaintext : Pqxdh.Bytes)
    (good : PublishedPlain codec control before handle encrypted plaintext) :
    PublishedPlain codec next after handle encrypted plaintext := by
  rcases good with good | ⟨label, owned, frame, decoded, entry, member, matched, plain⟩
  · exact Or.inl (known handle good)
  · exact Or.inr ⟨label, ownsLabel_step control next progress label handle owned, frame,
      decoded, entry, seals label entry member, matched, plain⟩

/-- A successful native Server send keeps its peer and plaintext witness, at the control before the command. -/
theorem native_serverSend_plain (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : Environment n E) (keyId : Std.U64) (plaintext : Pqxdh.Bytes)
    (before : NativeState n E) (safe : Safe before.1.2)
    (result : Option RawCtxSourceSend.Encrypted × NativeState n E)
    (supported : result ∈ support ((nativeImpl modes replace setup codec route env (.inr (.serverSend keyId plaintext))).run before))
    (encrypted : RawCtxSourceSend.Encrypted) (returned : result.1 = some encrypted) :
    PublishedPlain codec before.1.2 result.2.2 (.peer keyId) encrypted (replace plaintext) := by
  simp only [nativeImpl_run, native_serverSend_run, simulateQ_map, StateT.run_map,
    Functor.map_map, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact serverSend_plain modes ideal replace setup codec route readback before.1.2 safe
    keyId plaintext before.2 inner reached encrypted returned

/-- A successful native Beacon send keeps its owner and plaintext witness, at the control before the command. -/
theorem native_beaconSend_plain (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : Environment n E) (owner : Nat) (plaintext : Pqxdh.Bytes)
    (before : NativeState n E) (safe : Safe before.1.2)
    (result : Option RawCtxSourceSend.Encrypted × NativeState n E)
    (supported : result ∈ support ((nativeImpl modes replace setup codec route env (.inr (.beaconSend owner plaintext))).run before))
    (encrypted : RawCtxSourceSend.Encrypted) (returned : result.1 = some encrypted) :
    PublishedPlain codec before.1.2 result.2.2 (.owner owner) encrypted (replace plaintext) := by
  simp only [nativeImpl_run, native_beaconSend_run, simulateQ_map, StateT.run_map,
    Functor.map_map, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact beaconSend_plain modes ideal replace setup codec readback before.1.2 safe
    owner plaintext before.2 inner reached encrypted returned

/-- A native command's witness, valid at the control before it, holds at its final control and private state. -/
theorem native_final (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (query : Spec.Domain) (before : NativeState n E) (safe : Safe before.1.2)
    (result : Spec.Range query × NativeState n E)
    (supported : result ∈ support ((nativeImpl modes replace setup codec route env query).run before))
    (handle : Handle) (encrypted : RawCtxSourceSend.Encrypted) (plaintext : Pqxdh.Bytes)
    (good : PublishedPlain codec before.1.2 result.2.2 handle encrypted plaintext) :
    PublishedPlain codec result.2.1.2 result.2.2 handle encrypted plaintext :=
  publishedPlain_mono codec before.1.2 result.2.1.2 result.2.2 result.2.2
    (PqxdhRecordFactsOriginControl.native_step modes replace setup codec route env query before safe result supported)
    (fun handle known => nativeImpl_known modes replace setup codec route env handle query before known result supported)
    (fun _ _ member => member) handle encrypted plaintext good

/-- An experiment-generated native send keeps the handle and the sent plaintext, at the final control and private state. -/
theorem native_send_plain (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : Environment n E) (handle : Handle) (plaintext : Pqxdh.Bytes)
    (before : NativeState n E) (safe : Safe before.1.2)
    (result : Option RawCtxSourceSend.Encrypted × NativeState n E)
    (supported : result ∈ support ((simulateQ (nativeImpl modes replace setup codec route env)
      (PqxdhDeploymentSecrecy.send handle plaintext)).run before))
    (encrypted : RawCtxSourceSend.Encrypted) (returned : result.1 = some encrypted) :
    PublishedPlain codec result.2.1.2 result.2.2 handle encrypted (replace plaintext) := by
  cases handle with
  | peer keyId =>
    simp only [PqxdhDeploymentSecrecy.send, simulateQ_spec_query] at supported
    exact native_final modes replace setup codec route env (.inr (.serverSend keyId plaintext)) before safe result
      supported _ _ _ (native_serverSend_plain modes ideal replace setup codec route readback env keyId plaintext before
        safe result supported encrypted returned)
  | owner owner =>
    simp only [PqxdhDeploymentSecrecy.send, simulateQ_spec_query] at supported
    exact native_final modes replace setup codec route env (.inr (.beaconSend owner plaintext)) before safe result
      supported _ _ _ (native_beaconSend_plain modes ideal replace setup codec route readback env owner plaintext before
        safe result supported encrypted returned)

/-! ### The CE productions with their plaintexts -/

/-- The production of a transcript entry, with the experiment's test bit if a test session exists: an explicit Server or Beacon send returns its handle, its ciphertext and its query plaintext; an admitted test returns its handle, its ciphertext and the message chosen by the bit; every other entry, a failed send, a rejected secrecy command and every `fresh` entry (whose message is recorded in the ledger's fresh list instead) produce nothing. -/
def entryPlain (bit : Option Bool) : Entry → Option (Handle × RawCtxSourceSend.Encrypted × Pqxdh.Bytes)
  | ⟨.inl (.inr (.serverSend keyId plaintext)), some encrypted⟩ => some (.peer keyId, encrypted, plaintext)
  | ⟨.inl (.inr (.beaconSend owner plaintext)), some encrypted⟩ => some (.owner owner, encrypted, plaintext)
  | ⟨.inr (.test handle left right), some encrypted⟩ =>
      bit.map fun value => (handle, encrypted, if value then right else left)
  | _ => none

/-- A forwarded command's production does not depend on the test bit. -/
theorem entryPlain_forward (bit other : Option Bool) (query : Spec.Domain) (reply : Spec.Range query) :
    entryPlain bit ⟨.inl query, reply⟩ = entryPlain other ⟨.inl query, reply⟩ := by
  rcases query with coin | command
  · rfl
  · cases command <;> first | rfl | (cases reply <;> rfl)

/-- `Sent ledger handle encrypted plaintext`: the CE production of a record ciphertext with a plaintext, read on the ledger: a transcript entry produced it (`entryPlain` with the ledger's test bit), or an admitted `fresh` command sent its message and returned it. -/
def Sent (ledger : PqxdhDeploymentSecrecy.Ledger) (handle : Handle) (encrypted : RawCtxSourceSend.Encrypted)
    (plaintext : Pqxdh.Bytes) : Prop :=
  (∃ entry ∈ ledger.transcript,
      entryPlain (ledger.test.map PqxdhDeploymentSecrecy.TestState.bit) entry = some (handle, encrypted, plaintext)) ∨
    (⟨handle, plaintext, some encrypted⟩ : PqxdhDeploymentSecrecy.FreshEntry) ∈ ledger.fresh

/-- Before the first admitted test, the transcript has no production that depends on the test bit. -/
def TestFree (ledger : PqxdhDeploymentSecrecy.Ledger) : Prop :=
  ledger.test = none → ∀ entry ∈ ledger.transcript, ∀ value, entryPlain (some value) entry = entryPlain none entry

/-- Every native reply's forwarded entry has the plaintext witness of its production, at the final control and private state. -/
theorem native_entryPlain (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : Environment n E) (query : Spec.Domain) (before : NativeState n E) (safe : Safe before.1.2)
    (result : Spec.Range query × NativeState n E)
    (supported : result ∈ support ((nativeImpl modes replace setup codec route env query).run before))
    (bit : Option Bool) (handle : Handle) (encrypted : RawCtxSourceSend.Encrypted) (plaintext : Pqxdh.Bytes)
    (found : entryPlain bit ⟨.inl query, result.1⟩ = some (handle, encrypted, plaintext)) :
    PublishedPlain codec result.2.1.2 result.2.2 handle encrypted (replace plaintext) := by
  apply native_final modes replace setup codec route env query before safe result supported
  rcases query with coin | command
  · simp [entryPlain] at found
  · cases command
    case serverSend keyId message =>
      rcases returned : result.1 with _ | sent
      · simp [entryPlain, returned] at found
      · simp only [entryPlain, returned, Option.some.injEq, Prod.mk.injEq] at found
        obtain ⟨rfl, rfl, rfl⟩ := found
        exact native_serverSend_plain modes ideal replace setup codec route readback env keyId message before safe
          result supported sent returned
    case beaconSend owner message =>
      rcases returned : result.1 with _ | sent
      · simp [entryPlain, returned] at found
      · simp only [entryPlain, returned, Option.some.injEq, Prod.mk.injEq] at found
        obtain ⟨rfl, rfl, rfl⟩ := found
        exact native_beaconSend_plain modes ideal replace setup codec route readback env owner message before safe
          result supported sent returned
    all_goals simp [entryPlain] at found

/-- One secrecy-ledger command keeps `TestFree`, and each production of its new ledger is a production of the old ledger or has its plaintext witness at the final control and private state. -/
theorem ledger_plain (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (query : FullSpec.Domain)
    (ledger : PqxdhDeploymentSecrecy.Ledger) (before : NativeState n E) (safe : Safe before.1.2)
    (free : TestFree ledger)
    (result : (FullSpec.Range query × PqxdhDeploymentSecrecy.Ledger) × NativeState n E)
    (supported : result ∈ support ((simulateQ (nativeImpl modes replace setup codec route env)
      ((PqxdhDeploymentSecrecy.ledgerImpl setup.source.crypto codec serverKid bounds query).run ledger)).run before)) :
    TestFree result.1.2 ∧ ∀ handle encrypted plaintext, Sent result.1.2 handle encrypted plaintext →
      Sent ledger handle encrypted plaintext ∨
        PublishedPlain codec result.2.1.2 result.2.2 handle encrypted (replace plaintext) := by
  rcases query with forwarded | (⟨handle, left, right⟩ | ⟨handle, length⟩)
  · rw [PqxdhDeploymentSecrecy.ledgerImpl_forward, simulateQ_map, simulateQ_spec_query,
      StateT.run_map, support_map] at supported
    obtain ⟨inner, reached, rfl⟩ := supported
    refine ⟨?_, ?_⟩
    · intro none entry member value
      simp only [PqxdhDeploymentSecrecy.Ledger.record, List.mem_append, List.mem_singleton] at none member
      rcases member with prior | rfl
      · exact free none entry prior value
      · exact entryPlain_forward _ _ forwarded inner.1
    · rintro sentHandle sentCipher sentPlain (⟨entry, member, found⟩ | fresh)
      · simp only [PqxdhDeploymentSecrecy.Ledger.record, List.mem_append, List.mem_singleton] at member found
        rcases member with prior | rfl
        · exact Or.inl (Or.inl ⟨entry, prior, found⟩)
        · exact Or.inr (native_entryPlain modes ideal replace setup codec route readback env forwarded before safe inner
            reached _ sentHandle sentCipher sentPlain found)
      · exact Or.inl (Or.inr fresh)
  · simp only [PqxdhDeploymentSecrecy.ledgerImpl, StateT.run] at supported
    by_cases admissible : PqxdhDeploymentSecrecy.Admissible left right
    · simp only [admissible, ↓reduceIte] at supported
      cases testEq : ledger.test with
      | none =>
        simp only [testEq] at supported
        simp only [simulateQ_bind, simulateQ_pure] at supported
        change result ∈ support ((_ : StateT (NativeState n E) ProbComp _).run before) at supported
        simp only [StateT.run_bind, StateT.run_pure, mem_support_bind_iff] at supported
        obtain ⟨drawn, drawReached, sent, sendReached, finished⟩ := supported
        obtain rfl := (mem_support_pure_iff _ _).mp finished
        have drawnSafe := (PqxdhRecordFactsOriginControl.native_program_step modes replace setup codec route env _
          before safe drawn drawReached).1
        refine ⟨fun none => by simp at none, ?_⟩
        rintro sentHandle sentCipher sentPlain (⟨entry, member, found⟩ | fresh)
        · simp only [PqxdhDeploymentSecrecy.Ledger.record, List.mem_append, List.mem_singleton,
            Option.map_some] at member found
          rcases member with prior | rfl
          · refine Or.inl (Or.inl ⟨entry, prior, ?_⟩)
            rw [testEq, Option.map_none, ← free testEq entry prior drawn.1]
            exact found
          · rcases returned : sent.1 with _ | cipher
            · simp [entryPlain, returned] at found
            · simp only [entryPlain, returned, Option.map_some, Option.some.injEq, Prod.mk.injEq] at found
              obtain ⟨rfl, rfl, rfl⟩ := found
              exact Or.inr (native_send_plain modes ideal replace setup codec route readback env handle
                (if drawn.1 then right else left) drawn.2 drawnSafe sent sendReached cipher returned)
        · exact Or.inl (Or.inr (by simpa [PqxdhDeploymentSecrecy.Ledger.record] using fresh))
      | some session =>
        simp only [testEq] at supported
        by_cases same : PqxdhDeploymentSecrecy.SameSession setup.source.crypto codec serverKid ledger.transcript
          session.first handle
        · simp only [same, ↓reduceIte] at supported
          simp only [simulateQ_bind, simulateQ_pure] at supported
          change result ∈ support ((_ : StateT (NativeState n E) ProbComp _).run before) at supported
          simp only [StateT.run_bind, StateT.run_pure, mem_support_bind_iff] at supported
          obtain ⟨sent, sendReached, finished⟩ := supported
          obtain rfl := (mem_support_pure_iff _ _).mp finished
          refine ⟨fun none => by simp at none, ?_⟩
          rintro sentHandle sentCipher sentPlain (⟨entry, member, found⟩ | fresh)
          · simp only [PqxdhDeploymentSecrecy.Ledger.record, List.mem_append, List.mem_singleton,
              Option.map_some] at member found
            rcases member with prior | rfl
            · refine Or.inl (Or.inl ⟨entry, prior, ?_⟩)
              rw [testEq, Option.map_some]
              exact found
            · rcases returned : sent.1 with _ | cipher
              · simp [entryPlain, returned] at found
              · simp only [entryPlain, returned, Option.map_some, Option.some.injEq, Prod.mk.injEq] at found
                obtain ⟨rfl, rfl, rfl⟩ := found
                exact Or.inr (native_send_plain modes ideal replace setup codec route readback env handle
                  (if session.bit then right else left) before safe sent sendReached cipher returned)
          · exact Or.inl (Or.inr (by simpa [PqxdhDeploymentSecrecy.Ledger.record] using fresh))
        · simp only [same, ↓reduceIte] at supported
          obtain rfl := (mem_support_pure_iff _ _).mp supported
          refine ⟨fun none => by simp [PqxdhDeploymentSecrecy.Ledger.record, testEq] at none, ?_⟩
          rintro sentHandle sentCipher sentPlain (⟨entry, member, found⟩ | fresh)
          · simp only [PqxdhDeploymentSecrecy.Ledger.record, List.mem_append, List.mem_singleton] at member found
            rcases member with prior | rfl
            · exact Or.inl (Or.inl ⟨entry, prior, found⟩)
            · simp [entryPlain] at found
          · exact Or.inl (Or.inr fresh)
    · simp only [admissible, ↓reduceIte] at supported
      obtain rfl := (mem_support_pure_iff _ _).mp supported
      refine ⟨?_, ?_⟩
      · intro none entry member value
        simp only [PqxdhDeploymentSecrecy.Ledger.record, List.mem_append, List.mem_singleton] at none member
        rcases member with prior | rfl
        · exact free none entry prior value
        · rfl
      · rintro sentHandle sentCipher sentPlain (⟨entry, member, found⟩ | fresh)
        · simp only [PqxdhDeploymentSecrecy.Ledger.record, List.mem_append, List.mem_singleton] at member found
          rcases member with prior | rfl
          · exact Or.inl (Or.inl ⟨entry, prior, found⟩)
          · simp [entryPlain] at found
        · exact Or.inl (Or.inr fresh)
  · simp only [PqxdhDeploymentSecrecy.ledgerImpl, StateT.run] at supported
    by_cases admitted : bounds.min ≤ length ∧ length ≤ bounds.max
    · simp only [admitted.1, admitted.2, and_self, ↓reduceIte] at supported
      simp only [simulateQ_bind, simulateQ_pure] at supported
      change result ∈ support ((_ : StateT (NativeState n E) ProbComp _).run before) at supported
      simp only [StateT.run_bind, StateT.run_pure, mem_support_bind_iff] at supported
      obtain ⟨drawn, drawReached, sent, sendReached, finished⟩ := supported
      obtain rfl := (mem_support_pure_iff _ _).mp finished
      have drawnSafe := (PqxdhRecordFactsOriginControl.native_program_step modes replace setup codec route env _
        before safe drawn drawReached).1
      refine ⟨?_, ?_⟩
      · intro none entry member value
        simp only [PqxdhDeploymentSecrecy.Ledger.record, List.mem_append, List.mem_singleton] at none member
        rcases member with prior | rfl
        · exact free none entry prior value
        · rfl
      · rintro sentHandle sentCipher sentPlain (⟨entry, member, found⟩ | fresh)
        · simp only [PqxdhDeploymentSecrecy.Ledger.record, List.mem_append, List.mem_singleton] at member found
          rcases member with prior | rfl
          · exact Or.inl (Or.inl ⟨entry, prior, found⟩)
          · simp [entryPlain] at found
        · simp only [List.mem_append, List.mem_singleton, PqxdhDeploymentSecrecy.FreshEntry.mk.injEq] at fresh
          rcases fresh with prior | ⟨rfl, rfl, returned⟩
          · exact Or.inl (Or.inr prior)
          · exact Or.inr (native_send_plain modes ideal replace setup codec route readback env sentHandle drawn.1
              drawn.2 drawnSafe sent sendReached sentCipher returned.symm)
    · simp only [admitted, ↓reduceIte] at supported
      obtain rfl := (mem_support_pure_iff _ _).mp supported
      refine ⟨?_, ?_⟩
      · intro none entry member value
        simp only [PqxdhDeploymentSecrecy.Ledger.record, List.mem_append, List.mem_singleton] at none member
        rcases member with prior | rfl
        · exact free none entry prior value
        · rfl
      · rintro sentHandle sentCipher sentPlain (⟨entry, member, found⟩ | fresh)
        · simp only [PqxdhDeploymentSecrecy.Ledger.record, List.mem_append, List.mem_singleton] at member found
          rcases member with prior | rfl
          · exact Or.inl (Or.inl ⟨entry, prior, found⟩)
          · simp [entryPlain] at found
        · exact Or.inl (Or.inr fresh)

/-- The plaintext ledger invariant: source control safety, `TestFree`, and the plaintext witness of every CE production of the ledger at the current control and private state. -/
def InvariantPlain (codec : PqxdhServerAuthExperiment.Codec Reader Response) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (state : PqxdhDeploymentSecrecy.Ledger × NativeState n E) : Prop :=
  Safe state.2.1.2 ∧ TestFree state.1 ∧ ∀ handle encrypted plaintext, Sent state.1 handle encrypted plaintext →
    PublishedPlain codec state.2.1.2 state.2.2 handle encrypted (replace plaintext)

/-- One secrecy-ledger command keeps the plaintext ledger invariant. -/
theorem full_invariant_plain (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (query : FullSpec.Domain)
    (before : PqxdhDeploymentSecrecy.Ledger × NativeState n E) (good : InvariantPlain codec replace before)
    (result : FullSpec.Range query × (PqxdhDeploymentSecrecy.Ledger × NativeState n E))
    (supported : result ∈ support ((fullImpl modes replace setup codec route env serverKid bounds query).run before)) :
    InvariantPlain codec replace result.2 := by
  have progress := PqxdhRecordFactsOriginControl.full_step modes replace setup codec route env serverKid bounds query
    before good.1 result supported
  have grows := PqxdhRecordFactsOriginMonotone.full_grows modes ideal replace setup codec route env serverKid bounds
    query before result supported
  have known := fun handle present => PqxdhRecordFactsOriginControl.full_known modes replace setup codec route env
    serverKid bounds query before handle present result supported
  rcases before with ⟨ledger, state⟩
  rw [fullImpl_run, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  obtain ⟨free, fresh⟩ := ledger_plain modes ideal replace setup codec route readback env serverKid bounds query ledger
    state good.1 good.2.1 inner reached
  refine ⟨progress.1, free, ?_⟩
  intro handle encrypted plaintext sent
  rcases fresh handle encrypted plaintext sent with prior | final
  · exact publishedPlain_mono codec state.1.2 inner.2.1.2 state.2 inner.2.2 progress known grows.seals handle
      encrypted _ (good.2.2 handle encrypted plaintext prior)
  · exact final

/-- Every adaptive full continuation keeps the plaintext ledger invariant. -/
theorem full_program_invariant_plain (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (client : OracleComp FullSpec X)
    (before : PqxdhDeploymentSecrecy.Ledger × NativeState n E) (good : InvariantPlain codec replace before)
    (result : X × (PqxdhDeploymentSecrecy.Ledger × NativeState n E))
    (supported : result ∈ support ((simulateQ (fullImpl modes replace setup codec route env serverKid bounds) client).run before)) :
    InvariantPlain codec replace result.2 :=
  support_keep_oracle (fullImpl modes replace setup codec route env serverKid bounds)
    (InvariantPlain codec replace)
    (fun query state invariant => full_invariant_plain modes ideal replace setup codec route readback env serverKid
      bounds query state invariant)
    client before good result supported

/-- **Seal source with plaintext.** On every supported outcome of every ideal CTX world, every CE production of the final ledger (an explicit send, an admitted test with the ledger's bit, an admitted fresh message) has its plaintext witness at the final control and private state: its handle is caller-known, or a successful seal with the (replaced) produced plaintext, at a label the handle owns, matches the returned record's decoded frame. -/
theorem ctxRun_sentPlain (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (result : Client n E X × CtxPrivate n)
    (supported : result ∈ support (ctxRun modes replace setup codec route env serverKid bounds mode adversary)) :
    ∀ value ∈ result.1.1, ∀ handle encrypted plaintext, Sent value.2.1.2 handle encrypted plaintext →
      PublishedPlain codec result.1.2 result.2 handle encrypted (replace plaintext) := by
  rw [ctxRun_flat] at supported
  rw [mem_support_bind_iff] at supported
  obtain ⟨born, bornSupported, continued⟩ := supported
  have bornSafe := PqxdhRecordFactsOriginGlobal.startup_safe modes replace setup codec route env born bornSupported
  cases bornEq : born.1.1 with
  | none =>
    simp only [bornEq] at continued
    obtain rfl := (mem_support_pure_iff _ _).mp continued
    simp
  | some initial =>
    rcases initial with ⟨created, initial⟩
    simp only [bornEq] at continued
    rw [mem_support_bind_iff] at continued
    obtain ⟨installed, installSupported, continued⟩ := continued
    have installedSafe := PqxdhRecordFactsOriginGlobal.install_safe modes replace setup codec route created born.1.2
      bornSafe born.2 installed installSupported
    rw [support_map] at continued
    obtain ⟨final, finalSupported, rfl⟩ := continued
    have complete := full_program_invariant_plain modes ideal replace setup codec route readback env serverKid bounds
      (asModeO mode adversary) _ ⟨installedSafe, fun _ entry member => by simp [PqxdhDeploymentSecrecy.Ledger.empty] at member,
        fun handle encrypted plaintext sent => by simp [Sent, PqxdhDeploymentSecrecy.Ledger.empty] at sent⟩
      final finalSupported
    intro value member
    have equal := Option.some.inj member
    subst value
    exact complete.2.2

end BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlainSend

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlainSend.sealing_plain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlainSend.sealing_plain

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlainSend.kernelSend_plain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlainSend.kernelSend_plain

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlainSend.ownerSend_plain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlainSend.ownerSend_plain

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlainSend.ownerRun_plain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlainSend.ownerRun_plain

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlainSend.serverSend_plain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlainSend.serverSend_plain

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlainSend.beaconSend_plain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlainSend.beaconSend_plain

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlainSend.publishedPlain_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlainSend.publishedPlain_mono

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlainSend.native_serverSend_plain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlainSend.native_serverSend_plain

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlainSend.native_beaconSend_plain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlainSend.native_beaconSend_plain

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlainSend.native_final' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlainSend.native_final

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlainSend.native_send_plain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlainSend.native_send_plain

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlainSend.entryPlain_forward' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlainSend.entryPlain_forward

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlainSend.native_entryPlain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlainSend.native_entryPlain

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlainSend.ledger_plain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlainSend.ledger_plain

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlainSend.full_invariant_plain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlainSend.full_invariant_plain

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlainSend.full_program_invariant_plain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlainSend.full_program_invariant_plain

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlainSend.ctxRun_sentPlain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlainSend.ctxRun_sentPlain
