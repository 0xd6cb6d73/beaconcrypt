-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedAuditErase

/-! The materialization distance retains the whole original installation trace, while its loss is exactly the already quantified original audit bit. Both genuine cache-overlay samplings stay in the source; the observer erasure changes no bad-event probability. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedBound
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhRecordLiftInterface (Slot)
open PqxdhDeploymentHiddenLayout (Material)
open RegistrationNativeG3LocalKeys (State)
variable {n : Nat} {ι KemSK ProviderState Reader Response Value : Type} {base : OracleSpec ι}
variable (setup : Setup base KemSK) (codec : Codec Reader Response)
  (route : RawCtxServerRouting.SenderDecoder) (wire : RegistrationNativeWire.Wire)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
  (candidate : PqxdhKemIndCca.MlKemSharedSecret)
  (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)
  (source : RegistrationNativeMldsa.Source) (checks : Checks)
  (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
  (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value)
  (frontend : RegistrationNativePublicFrontend.State source) (before : State n KemSK ProviderState)
attribute [local irreducible] uniformSample RegistrationNativeG3MaterializedTracedProtocolLazy.auditRun RegistrationNativeG3MaterializedProtocolLazy.auditRun

/-- Full trace-retaining known108 and actual selective protocol outcomes differ by the original exact repeat-audit probability alone. -/
theorem bound :
    ENNReal.ofReal (discreteDistance
      (RegistrationNativeG3MaterializedTracedProtocolLazy.fullGame setup codec route wire sign seed scalar candidate provider source checks selectedOwner selectedAccept publicPrekey work frontend before)
      (RegistrationNativeG3MaterializedTracedProtocolLazy.actual setup codec route wire sign seed scalar candidate provider source checks selectedOwner selectedAccept publicPrekey work frontend before)) ≤
      Pr{let bad ← (do
        let table ← $ᵗ (Slot n → Material)
        let result ← RegistrationNativeG3MaterializedProtocolLazy.auditRun setup codec route wire sign seed scalar candidate provider source checks selectedOwner selectedAccept publicPrekey work frontend before
          (OracleComp.completeTable before.1.1.keys.materials table)
        pure result.2.2.2)}[bad = true] := by
  have compared := RegistrationNativeG3MaterializedTracedProtocolLazy.bound setup codec route wire sign seed scalar candidate provider source checks selectedOwner selectedAccept publicPrekey work frontend before
  have mapped :
      (fun pair => pair.2.2.2.2) <$> (do
        let table ← $ᵗ (Slot n → Material)
        let result ← RegistrationNativeG3MaterializedTracedProtocolLazy.auditRun setup codec route wire sign seed scalar candidate provider source checks selectedOwner selectedAccept publicPrekey work frontend before
          (OracleComp.completeTable before.1.1.keys.materials table)
        pure (table, result)) =
      (do let table ← $ᵗ (Slot n → Material)
          let result ← RegistrationNativeG3MaterializedTracedProtocolLazy.auditRun setup codec route wire sign seed scalar candidate provider source checks selectedOwner selectedAccept publicPrekey work frontend before
            (OracleComp.completeTable before.1.1.keys.materials table)
          pure result.2.2.2) := by
    simp only [map_bind, map_pure]
  have sourceEq := mapped.trans
    (RegistrationNativeG3MaterializedTracedAuditErase.audit_source setup wire sign source checks selectedOwner selectedAccept publicPrekey work frontend codec route seed scalar candidate provider before)
  have chance := congrArg (fun program : ProbComp Bool => Pr{let bad ← program}[bad = true]) sourceEq
  simp only [prEvent_map] at chance
  exact compared.trans chance.le

end BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedBound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedBound.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedBound.bound
