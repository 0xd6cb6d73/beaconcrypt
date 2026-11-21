-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedProtocolLazy
import BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordStartupActual

/-! The materialized known108 to actual selective material44 bound is averaged over the literal guarded native startup. Every successful continuation receives the reached World, including the shared ML-pin hash cache. Startup failure is identical on both sides. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3MaterializedStartup
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhRecordLiftInterface (Slot)
open PqxdhDeploymentHiddenLayout (Material)
open RegistrationNativeHiddenInterpreter (Provider)
variable {n : Nat} {ι KemSK ProviderState Value Extra : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

def publicOutcome (native : RegistrationNativeEntropyRun.Outcome
    (RegistrationNativePublicFrontend.State source × Extra) Value) :
    RegistrationNativeEntropyRun.Outcome (RegistrationNativePublicFrontend.State source) Value :=
  native.map (fun result => (result.1, result.2.1, result.2.2.1))

variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
  (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
  (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
  (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState) (providerState : ProviderState)
  (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
  (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)

noncomputable def startup : ProbComp (Option (RegistrationNativeHiddenStartup.Started source) × PqxdhRecordLiftWorld.State n) :=
  (simulateQ (CborRecordWorldSimulation.guarded setup (RegistrationNativeWire.ledgerCodec wire) route)
    (RegistrationNativeHiddenStartup.start setup source ensureInit identityIndex serverKeyId (setup.joint.publicKeys seed))).run
      PqxdhRecordLiftWorld.initial

noncomputable def typedWork (born : RegistrationNativeHiddenStartup.Started source) :=
  RegistrationNativeFullCompiler.compile setup.source.crypto wire serverKeyId bounds mode
    (adversary ⟨setup.joint.publicKeys seed, born.native.credential.publicKey, serverKeyId⟩)

noncomputable def fullAfter (initialized : Option (RegistrationNativeHiddenStartup.Started source) × PqxdhRecordLiftWorld.State n) :
    ProbComp (RegistrationNativeEntropyRun.Outcome (RegistrationNativePublicFrontend.State source) Value) :=
  match initialized.1 with
  | none => pure none
  | some born =>
      (fun result => some (PqxdhRegistrationJointServerBirth.encode born.created, result.1, result.2)) <$>
        RegistrationNativeG3MaterializedProtocolLazy.fullGame setup (RegistrationNativeWire.ledgerCodec wire) route wire
          (RegistrationNativeMldsa.owned source born.native.credential) seed scalar candidate provider source checks selectedOwner selectedAccept
          (setup.dh.publicKey scalar) (typedWork (setup := setup) (wire := wire) (source := source) (serverKeyId := serverKeyId) (seed := seed) (bounds := bounds) (mode := mode) (adversary := adversary) born) born.native.frontend
          (RegistrationNativeSelectiveHiddenInterpreter.initial providerState, initialized.2)

noncomputable def actualAfter (initialized : Option (RegistrationNativeHiddenStartup.Started source) × PqxdhRecordLiftWorld.State n) :
    ProbComp (RegistrationNativeEntropyRun.Outcome (RegistrationNativePublicFrontend.State source) Value) :=
  match initialized.1 with
  | none => pure none
  | some born =>
      (fun result => some (PqxdhRegistrationJointServerBirth.encode born.created, result.1, result.2)) <$>
        RegistrationNativeG3MaterializedProtocolLazy.actual setup (RegistrationNativeWire.ledgerCodec wire) route wire
          (RegistrationNativeMldsa.owned source born.native.credential) seed scalar candidate provider source checks selectedOwner selectedAccept
          (setup.dh.publicKey scalar) (typedWork (setup := setup) (wire := wire) (source := source) (serverKeyId := serverKeyId) (seed := seed) (bounds := bounds) (mode := mode) (adversary := adversary) born) born.native.frontend
          (RegistrationNativeSelectiveHiddenInterpreter.initial providerState, initialized.2)

noncomputable def auditAfter (initialized : Option (RegistrationNativeHiddenStartup.Started source) × PqxdhRecordLiftWorld.State n) : ProbComp Bool :=
  match initialized.1 with
  | none => pure false
  | some born => do
      let table ← $ᵗ (Slot n → Material)
      let result ← RegistrationNativeG3MaterializedProtocolLazy.auditRun setup (RegistrationNativeWire.ledgerCodec wire) route wire
        (RegistrationNativeMldsa.owned source born.native.credential) seed scalar candidate provider source checks selectedOwner selectedAccept
        (setup.dh.publicKey scalar) (typedWork (setup := setup) (wire := wire) (source := source) (serverKeyId := serverKeyId) (seed := seed) (bounds := bounds) (mode := mode) (adversary := adversary) born) born.native.frontend
        (RegistrationNativeSelectiveHiddenInterpreter.initial providerState, initialized.2)
        (OracleComp.completeTable (RegistrationNativeSelectiveHiddenInterpreter.initial (n := n) (KemSK := KemSK) providerState).1.keys.materials table)
      pure result.2.2.2

noncomputable def fullGame := startup (n := n) setup wire route source ensureInit identityIndex serverKeyId seed >>=
  fullAfter (n := n) (setup := setup) (checks := checks) (wire := wire) (route := route) (source := source) (serverKeyId := serverKeyId) (seed := seed) (scalar := scalar) (candidate := candidate) (provider := provider) (providerState := providerState) (selectedOwner := selectedOwner) (selectedAccept := selectedAccept) (bounds := bounds) (mode := mode) (adversary := adversary)

noncomputable def actual := startup (n := n) setup wire route source ensureInit identityIndex serverKeyId seed >>=
  actualAfter (n := n) (setup := setup) (checks := checks) (wire := wire) (route := route) (source := source) (serverKeyId := serverKeyId) (seed := seed) (scalar := scalar) (candidate := candidate) (provider := provider) (providerState := providerState) (selectedOwner := selectedOwner) (selectedAccept := selectedAccept) (bounds := bounds) (mode := mode) (adversary := adversary)

noncomputable def audit := startup (n := n) setup wire route source ensureInit identityIndex serverKeyId seed >>=
  auditAfter (n := n) (setup := setup) (checks := checks) (wire := wire) (route := route) (source := source) (serverKeyId := serverKeyId) (seed := seed) (scalar := scalar) (candidate := candidate) (provider := provider) (providerState := providerState) (selectedOwner := selectedOwner) (selectedAccept := selectedAccept) (bounds := bounds) (mode := mode) (adversary := adversary)

/-- The cold selective endpoint is the literal actual guarded record source after forgetting only its private interpreter output. -/
theorem actual_source :
    actual (n := n) setup checks wire route source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState
      selectedOwner selectedAccept bounds mode adversary =
      publicOutcome <$>
        RegistrationNativeRecordPackage.actual setup (RegistrationNativeWire.ledgerCodec wire) route
          (RegistrationNativeSelectiveRecordStartup.program (n := n) setup checks wire source ensureInit identityIndex serverKeyId
            seed scalar candidate provider providerState selectedOwner selectedAccept bounds mode adversary) := by
  rw [RegistrationNativeSelectiveRecordStartupActual.actual_start]
  simp only [actual, startup, map_bind]
  apply bind_congr
  rintro ⟨_ | born, reached⟩
  · simp only [actualAfter, map_pure, publicOutcome, Option.map_none]
  · simp only [actualAfter, RegistrationNativeG3MaterializedProtocolLazy.actual,
      RegistrationNativeG3MaterializedProtocol.publicProgram, RegistrationNativeSelectiveHiddenInterpreter.run,
      RegistrationNativePublicFrontend.run, typedWork, Functor.map_map]
    rfl

end BeaconcryptCore.Computational.RegistrationNativeG3MaterializedStartup

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedStartup.actual_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedStartup.actual_source
