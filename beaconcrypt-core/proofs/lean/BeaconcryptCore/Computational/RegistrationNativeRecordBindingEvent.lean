-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeRecordLedger
import BeaconcryptCore.Computational.RegistrationNativeSelectiveEntropyStartup
import BeaconcryptCore.Computational.RegistrationNativeRecordHandleSlots
import BeaconcryptCore.Computational.PqxdhRecordFactsBindingEvent

/-! Actual native cross-handle binding reads the original native analysis ledger, including all later publications, and the literal installed record slots. Its same-execution evidence is derived through the actual effectful startup and native initialized run. This slot-partnership statement does not assert completed source peer/root agreement. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeRecordBindingEvent
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhRecordLiftIdeal (CtxPrivate KeyMode)
open PqxdhRecordLiftWorldCompiler (Label)
open RegistrationNativeHiddenInterpreter (Provider)
open RegistrationNativeSelectiveEntropyEnvironment (State)
variable {n : Nat} {ι KemSK ProviderState Value E : Type} {base : OracleSpec ι}

/-- Record analysis retains the literal original ledger; private native state is carried but not inspected by the binding event. -/
def view (result : RegistrationNativeEntropyRun.Result n E Value) : PqxdhRecordLiftIdeal.View n E Value :=
  ⟨result.1.1.map (fun born => (born.2.1.1, born.2.1.2.ledger, born.2.2)), result.2.base.produced,
    PqxdhRecordLiftProtocol.rawCounters result.1.2, PqxdhRecordLiftIdeal.handleSlot result.1.2⟩

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
theorem ledger (result : RegistrationNativeEntropyRun.Result n (State n KemSK ProviderState source) Value)
    (supported : result ∈ support (RegistrationNativeSelectiveEntropyStartup.run modes replace setup checks wire route source ensureInit identityIndex serverKid
      seed scalar candidate provider providerState selectedOwner selectedAccept bounds mode adversary CtxPrivate.initial)) :
    ∀ born ∈ result.1.1, PqxdhRecordFactsBindingLedger.LedgerEvidence (RegistrationNativeWire.ledgerCodec wire) route
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
      exact RegistrationNativeRecordLedger.initialized modes ideal replace setup (RegistrationNativeWire.ledgerCodec wire) route readback
        _ serverKid bounds mode _ born.created _ shell control safe reached result continued

include ideal readback in
/-- Every actual native cross-handle acceptance forces a retained same-run commitment conflict, with no caller ledger-evidence premise. -/
theorem cross_conflict (result : RegistrationNativeEntropyRun.Result n (State n KemSK ProviderState source) Value)
    (supported : result ∈ support (RegistrationNativeSelectiveEntropyStartup.run modes replace setup checks wire route source ensureInit identityIndex serverKid
      seed scalar candidate provider providerState selectedOwner selectedAccept bounds mode adversary CtxPrivate.initial))
    (crossed : PqxdhRecordLiftIdeal.CrossAccept (RegistrationNativeWire.ledgerCodec wire) route (view result)) :
    PqxdhRecordFactsBindingEvent.DigestConflict result.2 := by
  apply PqxdhRecordFactsBindingEvent.cross_accept_conflict (RegistrationNativeWire.ledgerCodec wire) route
    (view result) result.1.2 result.2 rfl _ crossed
  intro actual member
  change actual ∈ result.1.1.map _ at member
  rw [Option.mem_def, Option.map_eq_some_iff] at member
  obtain ⟨born, bornMember, rfl⟩ := member
  exact ledger modes ideal replace setup checks wire route readback source ensureInit identityIndex serverKid seed scalar candidate provider providerState
    selectedOwner selectedAccept bounds mode adversary result supported born bornMember

end Startup
end BeaconcryptCore.Computational.RegistrationNativeRecordBindingEvent
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRecordBindingEvent.ledger' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRecordBindingEvent.ledger

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRecordBindingEvent.cross_conflict' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRecordBindingEvent.cross_conflict
