-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedProtocolLazy
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedProtocolLazy

/-! Erasing only the same original G2 observer leaves the literal prior materialization audit. No independent bad-event source is supplied: the exact trace erasure commutes through the actual selective service and marked World interpreter. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedAuditErase
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhRecordLiftInterface (Slot)
open PqxdhDeploymentHiddenLayout (Material)
open RegistrationNativeG3LocalKeys (State)
open RegistrationNativeG3LocalMaterialCompletion (put)
open RegistrationNativeG3LocalMaterialCompletedSource (cache)
variable {n : Nat} {ι KemSK ProviderState Reader Response Value : Type} {base : OracleSpec ι}
variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (source : RegistrationNativeMldsa.Source) (checks : Checks)
  (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
  (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value)
  (frontend : RegistrationNativePublicFrontend.State source)

/-- The complete original frontend and same chronological observer erase to exactly the original frontend AST. -/
theorem public_erase :
    Prod.fst <$> RegistrationNativeG3MaterializedTracedProtocol.publicProgram (n := n) setup wire sign source checks selectedOwner selectedAccept publicPrekey work frontend =
      RegistrationNativeG3MaterializedProtocol.publicProgram (n := n) setup wire sign source checks selectedOwner selectedAccept publicPrekey work frontend :=
  RegistrationNativeG2Trace.program_erase _ RegistrationNativeG2Trace.initial

/-- The actual completed selective World program retains its full thin poststate when only the analysis trace is erased. -/
theorem world_erase (table : Slot n → Material) (seed : PqxdhJointIdentity.IdentitySeed)
    (scalar : PqxdhJointGapDh.ScalarBytes) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState) (before : State n KemSK ProviderState) :
    Prod.map Prod.fst id <$>
      RegistrationNativeG3MaterializedTracedProtocol.worldProgram table setup wire sign seed scalar candidate provider source checks selectedOwner selectedAccept publicPrekey work frontend before =
      RegistrationNativeG3MaterializedProtocol.worldProgram table setup wire sign seed scalar candidate provider source checks selectedOwner selectedAccept publicPrekey work frontend before := by
  have erased := congrArg (fun program =>
    (simulateQ (RegistrationNativeSelectiveHiddenInterpreter.handler setup wire sign seed scalar candidate provider) program).run
      (put before (cache table)).1)
    (public_erase (n := n) (KemSK := KemSK) setup wire sign source checks selectedOwner selectedAccept publicPrekey work frontend)
  simpa only [RegistrationNativeG3MaterializedTracedProtocol.worldProgram, RegistrationNativeG3MaterializedProtocol.worldProgram,
    simulateQ_map, StateT.run_map, Prod.map_def, id_eq] using erased

/-- The same actual marked World audit keeps its literal private state and bad bit when only the original G2 trace is erased. -/
theorem audit_erase (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (table : Slot n → Material) (seed : PqxdhJointIdentity.IdentitySeed)
    (scalar : PqxdhJointGapDh.ScalarBytes) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState) (before : State n KemSK ProviderState)
    (seeds : RegistrationNativeG3AuditedWorld.Seeds n) :
    Prod.map (Prod.map Prod.fst id) id <$>
      RegistrationNativeG3GuardedCoupling.audit setup codec route seeds
        (RegistrationNativeG3MaterializedTracedProtocol.worldProgram table setup wire sign seed scalar candidate provider source checks selectedOwner selectedAccept publicPrekey work frontend before) before.2 =
      RegistrationNativeG3GuardedCoupling.audit setup codec route seeds
        (RegistrationNativeG3MaterializedProtocol.worldProgram table setup wire sign seed scalar candidate provider source checks selectedOwner selectedAccept publicPrekey work frontend before) before.2 := by
  have erased := congrArg (fun program => RegistrationNativeG3GuardedCoupling.audit setup codec route seeds program before.2)
    (world_erase setup wire sign source checks selectedOwner selectedAccept publicPrekey work frontend table seed scalar candidate provider before)
  simpa only [RegistrationNativeG3GuardedCoupling.audit, simulateQ_map, StateT.run_map, Prod.map_def, id_eq] using erased

/-- The actual marked audit's Boolean bad event is unchanged by dropping only the same execution's trace. -/
theorem audit_bad (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (table : Slot n → Material) (seed : PqxdhJointIdentity.IdentitySeed)
    (scalar : PqxdhJointGapDh.ScalarBytes) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState) (before : State n KemSK ProviderState)
    (seeds : RegistrationNativeG3AuditedWorld.Seeds n) :
    (fun result => result.2.2) <$>
      RegistrationNativeG3GuardedCoupling.audit setup codec route seeds
        (RegistrationNativeG3MaterializedTracedProtocol.worldProgram table setup wire sign seed scalar candidate provider source checks selectedOwner selectedAccept publicPrekey work frontend before) before.2 =
      (fun result => result.2.2) <$>
      RegistrationNativeG3GuardedCoupling.audit setup codec route seeds
        (RegistrationNativeG3MaterializedProtocol.worldProgram table setup wire sign seed scalar candidate provider source checks selectedOwner selectedAccept publicPrekey work frontend before) before.2 := by
  have erased := congrArg (Functor.map (fun result => result.2.2))
    (audit_erase setup wire sign source checks selectedOwner selectedAccept publicPrekey work frontend codec route table seed scalar candidate provider before seeds)
  simpa only [Functor.map_map, Prod.map_def, id_eq, Function.comp_def] using erased

attribute [local irreducible] RegistrationNativeG3GuardedCoupling.audit

/-- Sampling the same genuine overlaid seed table leaves exactly the original protocol audit bit. -/
theorem auditRun_bad (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (table : Slot n → Material) (seed : PqxdhJointIdentity.IdentitySeed)
    (scalar : PqxdhJointGapDh.ScalarBytes) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState) (before : State n KemSK ProviderState) :
    (fun result => result.2.2.2) <$>
      RegistrationNativeG3MaterializedTracedProtocolLazy.auditRun setup codec route wire sign seed scalar candidate provider source checks selectedOwner selectedAccept publicPrekey work frontend before table =
      (fun result => result.2.2.2) <$>
      RegistrationNativeG3MaterializedProtocolLazy.auditRun setup codec route wire sign seed scalar candidate provider source checks selectedOwner selectedAccept publicPrekey work frontend before table := by
  simp only [RegistrationNativeG3MaterializedTracedProtocolLazy.auditRun, RegistrationNativeG3MaterializedProtocolLazy.auditRun,
    map_bind, bind_pure_comp]
  apply bind_congr
  intro seeds
  simpa only [Functor.map_map] using
    audit_bad setup wire sign source checks selectedOwner selectedAccept publicPrekey work frontend codec route table seed scalar candidate provider before
      (RegistrationNativeG3GuardedCoupling.overlay before.2 seeds)

attribute [local irreducible] RegistrationNativeG3MaterializedTracedProtocolLazy.auditRun RegistrationNativeG3MaterializedProtocolLazy.auditRun

/-- Both full table samplings retain exactly the original bad-bit source, with the literal reached material cache overlaid. -/
theorem audit_source (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState) (before : State n KemSK ProviderState) :
    (do let table ← $ᵗ (Slot n → Material)
        let result ← RegistrationNativeG3MaterializedTracedProtocolLazy.auditRun setup codec route wire sign seed scalar candidate provider source checks selectedOwner selectedAccept publicPrekey work frontend before
          (OracleComp.completeTable before.1.1.keys.materials table)
        pure result.2.2.2) =
      (do let table ← $ᵗ (Slot n → Material)
          let result ← RegistrationNativeG3MaterializedProtocolLazy.auditRun setup codec route wire sign seed scalar candidate provider source checks selectedOwner selectedAccept publicPrekey work frontend before
            (OracleComp.completeTable before.1.1.keys.materials table)
          pure result.2.2.2) := by
  apply bind_congr
  intro table
  simpa only [bind_pure_comp] using
    auditRun_bad setup wire sign source checks selectedOwner selectedAccept publicPrekey work frontend codec route
      (OracleComp.completeTable before.1.1.keys.materials table) seed scalar candidate provider before

end BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedAuditErase
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedAuditErase.public_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedAuditErase.public_erase
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedAuditErase.world_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedAuditErase.world_erase

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedAuditErase.audit_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedAuditErase.audit_erase

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedAuditErase.audit_bad' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedAuditErase.audit_bad
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedAuditErase.auditRun_bad' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedAuditErase.auditRun_bad

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedAuditErase.audit_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedAuditErase.audit_source
