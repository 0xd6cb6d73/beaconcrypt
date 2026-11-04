-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeRecordOriginInitialized
import BeaconcryptCore.Computational.RegistrationNativeRecordOriginStartup
import BeaconcryptCore.Computational.RegistrationNativeRecordBindingEvent
import BeaconcryptCore.Computational.RegistrationNativeSelectiveEntropyStartup
import BeaconcryptCore.Computational.RegistrationNativeRecordHandleSlots
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationEvent

/-! Every actual ordinary native acceptance without an earlier opposite-handle publication has a literal failed-writer witness in that same execution. Effectful startup and ML-pin hashes retain the initial empty record dictionaries, and later publications cannot replace the earlier receive prefix. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeRecordOriginEvent
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhRecordLiftIdeal (CtxPrivate KeyMode)
open PqxdhRecordLiftWorldCompiler (Label)
open RegistrationNativeHiddenInterpreter (Provider)
open RegistrationNativeSelectiveEntropyEnvironment (State)
variable {n : Nat} {ι KemSK ProviderState Value E : Type} {base : OracleSpec ι}

open RegistrationNativeRecordBindingEvent (view)

section Startup
variable (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
  (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (route : RawCtxServerRouting.SenderDecoder) (readback : PqxdhServerAuthNegativeControl.FrameReadBack (RegistrationNativeWire.ledgerCodec wire))
  (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKid : U64)
  (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
  (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState) (providerState : ProviderState)
  (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
  (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)

include ideal readback in
/-- Every supported complete native selective execution derives record witnesses after its actual startup cache and original typed ledger. -/
theorem prefixes (result : RegistrationNativeEntropyRun.Result n (State n KemSK ProviderState source) Value)
    (supported : result ∈ support (RegistrationNativeSelectiveEntropyStartup.run modes replace setup checks wire route source ensureInit identityIndex serverKid
      seed scalar candidate provider providerState selectedOwner selectedAccept bounds mode adversary CtxPrivate.initial)) :
    ∀ born ∈ result.1.1, PqxdhRecordFactsOriginPublicationPrefixes.Prefixes (RegistrationNativeWire.ledgerCodec wire) route
      result.1.2 result.2 born.2.1.2.ledger.transcript := by
  rw [RegistrationNativeSelectiveEntropyStartup.run_start, mem_support_bind_iff] at supported
  obtain ⟨started, startSupported, continued⟩ := supported
  rcases started with ⟨⟨⟨initialized, shell⟩, control⟩, reached⟩
  cases initialized with
  | none =>
      simp only [RegistrationNativeSelectiveEntropyStartup.after, mem_support_pure_iff] at continued
      subst result
      simp
  | some born =>
      dsimp only [RegistrationNativeSelectiveEntropyStartup.after] at continued
      have valid := RegistrationNativeHiddenAllocationStartup.initialized setup ensureInit identityIndex serverKid
        (setup.joint.publicKeys seed) providerState (PqxdhRecordLiftIdeal.ctxInterpreter modes replace setup (RegistrationNativeWire.ledgerCodec wire))
        (RegistrationNativeWire.ledgerCodec wire) route CtxPrivate.initial born shell control reached startSupported
      have safe := (RegistrationNativeRecordHandleSlots.interpreted
        (PqxdhRecordLiftIdeal.ctxInterpreter modes replace setup (RegistrationNativeWire.ledgerCodec wire))
        (RegistrationNativeWire.ledgerCodec wire) route _ _ _ PqxdhRecordLiftProtocolHistory.initial_safe _ _ startSupported).1
      rw [RegistrationNativeSelectiveEntropyRun.run_source modes replace setup checks wire route source born.native.credential
        seed scalar candidate provider selectedOwner selectedAccept serverKid bounds mode _ born.created
        (born.native.frontend, RegistrationNativeSelectiveHiddenInterpreter.initial providerState) shell control reached valid] at continued
      have empty := RegistrationNativeRecordOriginStartup.empty modes replace setup (RegistrationNativeWire.ledgerCodec wire) route
        source ensureInit identityIndex serverKid (setup.joint.publicKeys seed) _ startSupported
      exact RegistrationNativeRecordOriginInitialized.initialized_prefixes modes ideal replace setup (RegistrationNativeWire.ledgerCodec wire) route readback
        _ serverKid bounds mode _ born.created _ shell control safe reached empty result continued

include ideal readback in
/-- Exact temporal native origin failure supplies an accepted dictionary seal whose original writer failed, in either record direction. -/
theorem unpublished_failed (result : RegistrationNativeEntropyRun.Result n (State n KemSK ProviderState source) Value)
    (supported : result ∈ support (RegistrationNativeSelectiveEntropyStartup.run modes replace setup checks wire route source ensureInit identityIndex serverKid
      seed scalar candidate provider providerState selectedOwner selectedAccept bounds mode adversary CtxPrivate.initial))
    (unpublished : PqxdhRecordLiftIdeal.UnpublishedAccept (RegistrationNativeWire.ledgerCodec wire) route (view result)) :
    ∃ value ∈ (view result).result, ∃ before event after, value.2.1.transcript = before ++ event :: after ∧
      PqxdhRecordFactsOriginPublicationEvent.FailedWriterAt (RegistrationNativeWire.ledgerCodec wire) route result.1.2 result.2 event := by
  obtain ⟨value, valueMember, before, event, after, split, forged⟩ := unpublished
  have retained : PqxdhRecordFactsOriginPublicationPrefixes.Prefixes (RegistrationNativeWire.ledgerCodec wire) route
      result.1.2 result.2 value.2.1.transcript := by
    change value ∈ result.1.1.map _ at valueMember
    rw [Option.mem_def, Option.map_eq_some_iff] at valueMember
    obtain ⟨born, bornMember, rfl⟩ := valueMember
    exact prefixes modes ideal replace setup checks wire route readback source ensureInit identityIndex serverKid seed scalar candidate provider providerState
      selectedOwner selectedAccept bounds mode adversary result supported born bornMember
  exact ⟨value, valueMember, before, event, after, split,
    PqxdhRecordFactsOriginPublicationEvent.forged_failed (RegistrationNativeWire.ledgerCodec wire) route result.1.2 result.2
      before event (retained before event after split) forged⟩

end Startup
end BeaconcryptCore.Computational.RegistrationNativeRecordOriginEvent
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRecordOriginEvent.prefixes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRecordOriginEvent.prefixes

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRecordOriginEvent.unpublished_failed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRecordOriginEvent.unpublished_failed
