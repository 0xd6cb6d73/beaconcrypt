-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedStartup

/-! The concrete preinitialized materialized protocol bound is averaged over the actual effectful cold startup. The loss is precisely the startup-averaged actual repeat audit, with no reset of the reached World and no extra resource or source-equality premise. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedStartupBound
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeHiddenInterpreter (Provider)
variable {n : Nat} {ι KemSK ProviderState Value : Type} {base : OracleSpec ι}
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
  (serverKeyId : U64) (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
  (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState) (providerState : ProviderState)
  (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
  (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
local notation "fullContinuation" => RegistrationNativeG3MaterializedTracedStartup.fullAfter (n := n)
  (setup := setup) (checks := checks) (wire := wire) (route := route) (source := source) (serverKeyId := serverKeyId)
  (seed := seed) (scalar := scalar) (candidate := candidate) (provider := provider) (providerState := providerState)
  (selectedOwner := selectedOwner) (selectedAccept := selectedAccept) (bounds := bounds) (mode := mode) (adversary := adversary)
local notation "actualContinuation" => RegistrationNativeG3MaterializedTracedStartup.actualAfter (n := n)
  (setup := setup) (checks := checks) (wire := wire) (route := route) (source := source) (serverKeyId := serverKeyId)
  (seed := seed) (scalar := scalar) (candidate := candidate) (provider := provider) (providerState := providerState)
  (selectedOwner := selectedOwner) (selectedAccept := selectedAccept) (bounds := bounds) (mode := mode) (adversary := adversary)
local notation "auditContinuation" => RegistrationNativeG3MaterializedTracedStartup.auditAfter (n := n)
  (setup := setup) (checks := checks) (wire := wire) (route := route) (source := source) (serverKeyId := serverKeyId)
  (seed := seed) (scalar := scalar) (candidate := candidate) (provider := provider) (providerState := providerState)
  (selectedOwner := selectedOwner) (selectedAccept := selectedAccept) (bounds := bounds) (mode := mode) (adversary := adversary)

/-- Every actual reached startup branch obeys the concrete materialization bound with its full reached World state. -/
theorem after (initialized : Option (RegistrationNativeHiddenStartup.Started source) × PqxdhRecordLiftWorld.State n) :
    ENNReal.ofReal (discreteDistance (fullContinuation initialized) (actualContinuation initialized)) ≤
      Pr{let bad ← auditContinuation initialized}[bad = true] := by
  rcases initialized with ⟨_ | born, reached⟩
  · simp [RegistrationNativeG3MaterializedTracedStartup.fullAfter, RegistrationNativeG3MaterializedTracedStartup.actualAfter,
      RegistrationNativeG3MaterializedTracedStartup.auditAfter]
  · have pointwise := RegistrationNativeG3MaterializedTracedBound.bound setup (RegistrationNativeWire.ledgerCodec wire) route wire
      (RegistrationNativeMldsa.owned source born.native.credential) seed scalar candidate provider source checks selectedOwner selectedAccept
      (setup.dh.publicKey scalar)
      (RegistrationNativeG3MaterializedTracedStartup.typedWork (setup := setup) (wire := wire) (source := source)
        (serverKeyId := serverKeyId) (seed := seed) (bounds := bounds) (mode := mode) (adversary := adversary) born)
      born.native.frontend (RegistrationNativeSelectiveHiddenInterpreter.initial providerState, reached)
    have projected := (ENNReal.ofReal_le_ofReal (discreteDistance_map_le
      (fun result => some (PqxdhRegistrationJointServerBirth.encode born.created, result.1.1, (result.1.2, result.2))) _ _)).trans pointwise
    simpa only [RegistrationNativeG3MaterializedTracedStartup.fullAfter, RegistrationNativeG3MaterializedTracedStartup.actualAfter,
      RegistrationNativeG3MaterializedTracedStartup.auditAfter, OracleComp.prEvent_bind_eq_tsum,
      bind_pure_comp, prEvent_map] using projected

variable (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat)

/-- Cold known108 and actual selective native execution differ by the actual startup-averaged repeat audit alone. -/
theorem bound :
    ENNReal.ofReal (discreteDistance
      (RegistrationNativeG3MaterializedTracedStartup.fullGame (n := n) setup checks wire route source ensureInit identityIndex serverKeyId
        seed scalar candidate provider providerState selectedOwner selectedAccept bounds mode adversary)
      (RegistrationNativeG3MaterializedTracedStartup.actual (n := n) setup checks wire route source ensureInit identityIndex serverKeyId
        seed scalar candidate provider providerState selectedOwner selectedAccept bounds mode adversary)) ≤
      Pr{let bad ← (RegistrationNativeG3MaterializedTracedStartup.audit (n := n) setup checks wire route source ensureInit identityIndex serverKeyId
        seed scalar candidate provider providerState selectedOwner selectedAccept bounds mode adversary)}[bad = true] := by
  have compared := PqxdhExtractRomHiddenSuffix.tvDist_bind_le_probEvent
    (RegistrationNativeG3MaterializedTracedStartup.startup (n := n) setup wire route source ensureInit identityIndex serverKeyId seed)
    fullContinuation actualContinuation auditContinuation (fun _ bad => bad = true) (fun initialized _ => by
      have pointwise := ENNReal.toReal_mono (prEvent_ne_top _)
        (after setup checks wire route source serverKeyId seed scalar candidate provider providerState selectedOwner selectedAccept
          bounds mode adversary initialized)
      simpa only [ENNReal.toReal_ofReal (discreteDistance_nonneg _ _)] using pointwise)
  have lifted := (ENNReal.ofReal_le_ofReal compared).trans (ENNReal.ofReal_toReal (prEvent_ne_top _)).le
  simpa only [RegistrationNativeG3MaterializedTracedStartup.fullGame, RegistrationNativeG3MaterializedTracedStartup.actual,
    RegistrationNativeG3MaterializedTracedStartup.audit, OracleComp.prEvent_bind_eq_tsum, bind_pure_comp, prEvent_map] using lifted

end BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedStartupBound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedStartupBound.after' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedStartupBound.after
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedStartupBound.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedStartupBound.bound
