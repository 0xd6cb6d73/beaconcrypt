-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomTraceOrder
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomTracedSource

/-! Actual concrete callback interpretation preserves the chronological attempt-before-install order through every adaptive original typed and raw-ledger execution. The source may have arbitrary private state and reply kernels; no lifecycle or event-shape premise is imposed on the initialized result. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomTraceOrderSource
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordInterpreter (Provider)
open RegistrationNativeSecretWordAtomTracedSource (State)
open RegistrationNativeSecretWordAtomTraceOrder (Good)
open PqxdhRecordLiftInterface (Role)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}
/-- Any actual stateful private interpretation and subsequent outer closure retain the literal observer's attempt-before-install order. -/
theorem interpreted_good {κ Private : Type} {target : OracleSpec κ} (role : Role)
    (implementation : QueryImpl (RegistrationNativeSecretWordInterface.Spec n KemSK) (StateT Private (OracleComp target)))
    (outer : QueryImpl target ProbComp) (work : OracleComp (RegistrationNativeSecretWordInterface.Spec n KemSK) Value)
    (before : Private) (result : (Value × RegistrationNativeSecretWordFrontendTrace.State) × Private)
    (supported : result ∈ support (simulateQ outer ((simulateQ implementation
      (RegistrationNativeSecretWordFrontendTrace.program work)).run before))) : Good role result.1.2.events := by
  have opened := PqxdhDeploymentEnvironment.support_simulateQ_subset outer _ supported
  have observed : result.1 ∈ support (RegistrationNativeSecretWordFrontendTrace.program work) := by
    apply OracleComp.support_simulateQ_run'_subset implementation _ before
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem Prod.fst opened
  exact RegistrationNativeSecretWordAtomTraceOrder.program_good role work RegistrationNativeSecretWordFrontendTrace.initial
    (by simp [Good, RegistrationNativeSecretWordAtomTraceOrder.stream, RegistrationNativeSecretWordFrontendTrace.initial]) result.1 observed

variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (route : RawCtxServerRouting.SenderDecoder)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
  (provider : Provider KemSK) (outer : QueryImpl Combined ProbComp)
  (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
local notation "typed" => RegistrationNativeSecretWordAtomTracedSource.typed (n := n)
  setup wire route sign input inside provider outer checks selectedOwner selectedAccept publicPrekey

/-- Every supported actual typed callback retains the same ordered-event invariant as its exact pure observer. -/
theorem query_good (role : Role) (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State n KemSK source)
    (valid : Good role before.2.1.events) (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State n KemSK source)
    (supported : result ∈ support ((typed query).run before)) : Good role result.2.2.1.events :=
  RegistrationNativeSecretWordAtomTraceOrder.program_good role _ before.2.1 valid _
    (RegistrationNativeSecretWordAtomTracedSource.typed_support setup wire route sign input inside provider outer checks
      selectedOwner selectedAccept publicPrekey query before result supported)

/-- The exact chronological invariant holds on every actual adaptive typed prefix. -/
theorem program_good (role : Role) (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value) (before : State n KemSK source)
    (valid : Good role before.2.1.events) (result : Value × State n KemSK source)
    (supported : result ∈ support ((simulateQ typed work).run before)) : Good role result.2.2.1.events := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      cases supported
      exact valid
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨middle, called, continued⟩ := supported
      exact ih middle.1 middle.2 (query_good setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey
        role query before valid middle called) continued

/-- The complete original ledger has actual attempt-before-install ordering from its empty chronological observer, without an invariant premise. -/
theorem run_initialized (role : Role) (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (front : RegistrationNativeSecretWordMessage.State source) (privateState : RegistrationNativeSecretWordInterpreter.State n KemSK)
    (result : Value × (RegistrationNativeLedger.State × State n KemSK source))
    (supported : result ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds typed mode work
      (front, RegistrationNativeSecretWordFrontendTrace.initial, privateState))) : Good role result.2.2.2.1.events := by
  rw [RegistrationNativeFullCompiler.compile_run, support_map] at supported
  obtain ⟨reached, called, equal⟩ := supported
  cases equal
  exact program_good setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey role _
    (front, RegistrationNativeSecretWordFrontendTrace.initial, privateState)
    (by simp [Good, RegistrationNativeSecretWordAtomTraceOrder.stream, RegistrationNativeSecretWordFrontendTrace.initial]) reached called

end BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomTraceOrderSource
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomTraceOrderSource.query_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomTraceOrderSource.query_good
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomTraceOrderSource.program_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomTraceOrderSource.program_good
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomTraceOrderSource.run_initialized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomTraceOrderSource.run_initialized

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomTraceOrderSource.interpreted_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomTraceOrderSource.interpreted_good
