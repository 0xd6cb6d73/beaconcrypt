-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedProgram
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedSelectivePullback
import BeaconcryptCore.Computational.RegistrationNativeG3LocalMaterialCompletedSource
import BeaconcryptCore.Computational.RegistrationNativeG3GuardedCoupling

/-! The concrete known108 frontend and the selective material44 interpreter share one actual open World program, retaining their same complete G2 chronology. The fixed hidden seed table occurs only in the outer materializing World interpreter; it is absent from that program. This source bridge consumes the entire typed frontend equation, the completed private material cache and the exact pullback of hidden installation references. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedProtocol
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhRecordLiftInterface (Slot)
open PqxdhDeploymentHiddenLayout (Material)
open RegistrationNativeG3AuditedWorld (Seeds)
open RegistrationNativeG3LocalKeys (State)
open RegistrationNativeG3LocalMaterialCompletedSource (cache)
open RegistrationNativeG3LocalMaterialCompletion (put)
variable {n : Nat} {ι KemSK ProviderState Reader Response Value : Type} {base : OracleSpec ι}
variable (table : Slot n → Material) (setup : Setup base KemSK) (codec : Codec Reader Response)
  (route : RawCtxServerRouting.SenderDecoder) (wire : RegistrationNativeWire.Wire)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
  (candidate : PqxdhKemIndCca.MlKemSharedSecret)
  (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)
  (source : RegistrationNativeMldsa.Source) (checks : Checks)
  (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
  (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value)
  (frontend : RegistrationNativePublicFrontend.State source) (before : State n KemSK ProviderState)

noncomputable def publicProgram : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK)
    ((Value × RegistrationNativePublicFrontend.State source) × RegistrationNativeG2Trace.State) :=
  RegistrationNativeG2Trace.program
    ((simulateQ (RegistrationNativePublicFrontend.handler setup checks wire source sign selectedOwner selectedAccept publicPrekey) work).run frontend)

noncomputable def worldProgram :=
  (simulateQ (RegistrationNativeSelectiveHiddenInterpreter.handler setup wire sign seed scalar candidate provider)
    (publicProgram setup wire sign source checks selectedOwner selectedAccept publicPrekey work frontend)).run
      (put before (cache table)).1

noncomputable def full (seeds : Seeds n) :=
  Prod.fst <$> (simulateQ (RegistrationNativeG3MaterializedLocal.handler true table seeds setup codec route wire sign seed scalar candidate provider)
    (publicProgram setup wire sign source checks selectedOwner selectedAccept publicPrekey work frontend)).run before

/-- The actual complete known108 frontend equals the materializing guarded World interpretation of the same seed-independent selective program, with all public outcomes retained. -/
theorem known_source (seeds : Seeds n) :
    full table setup codec route wire sign seed scalar candidate provider source checks selectedOwner selectedAccept publicPrekey work frontend before seeds =
      Prod.fst <$> RegistrationNativeG3GuardedCoupling.known setup codec route seeds
        (worldProgram table setup wire sign seed scalar candidate provider source checks selectedOwner selectedAccept publicPrekey work frontend before) before.2 := by
  have mixed := congrArg (Functor.map Prod.fst)
    (RegistrationNativeG3MaterializedTracedProgram.frontend_source table setup codec route wire sign seed scalar candidate provider
      source checks selectedOwner selectedAccept publicPrekey seeds work frontend RegistrationNativeG2Trace.initial before)
  have actual := congrArg (Functor.map Prod.fst)
    (RegistrationNativeG3LocalMaterialCompletedSource.world_source table setup codec route wire sign seed scalar candidate provider
      (simulateQ (RegistrationNativeG3MaterializedLocal.translate false seeds)
        (publicProgram setup wire sign source checks selectedOwner selectedAccept publicPrekey work frontend)) before)
  have pulled := congrArg (fun program =>
    (fun result => result.1.1) <$> (simulateQ (CborRecordWorldSimulation.guarded setup codec route) program).run before.2)
    (RegistrationNativeG3MaterializedSelectivePullback.program_source setup wire sign seed scalar candidate provider seeds
      (publicProgram setup wire sign source checks selectedOwner selectedAccept publicPrekey work frontend)
      (put before (cache table)).1)
  simp only [RegistrationNativeG3MaterializedLocal.handler, QueryImpl.simulateQ_compose,
    Functor.map_map, Prod.map_def, id_eq, publicProgram] at mixed actual
  have sameRealize : RegistrationNativeG3GuardedMaterializedWorld.realize seeds =
      RegistrationNativeG3MaterializedWorld.realize seeds := rfl
  have combined := mixed.trans (actual.symm.trans pulled.symm)
  simpa only [full, worldProgram, publicProgram, RegistrationNativeG3GuardedCoupling.known,
    RegistrationNativeG3GuardedMaterializedWorld.source, RegistrationNativeG3MaterializedLocal.handler,
    sameRealize, QueryImpl.simulateQ_compose,
    Functor.map_map, Prod.map_def, id_eq, Function.comp_def, RegistrationNativeG2Trace.program] using combined

noncomputable def fullGame := do
  let seeds ← $ᵗ (Seeds n)
  full table setup codec route wire sign seed scalar candidate provider source checks selectedOwner selectedAccept publicPrekey
    work frontend before (RegistrationNativeG3GuardedCoupling.overlay before.2 seeds)

noncomputable def hiddenGame :=
  Prod.fst <$> RegistrationNativeG3GuardedCoupling.hidden setup codec route
    (worldProgram table setup wire sign seed scalar candidate provider source checks selectedOwner selectedAccept publicPrekey work frontend before) before.2

/-- The actual entire known108 frontend and the actual guarded selective material44 program differ by at most their concrete known-side repeated-role audit probability. All materialized source and hidden seed completion equations are discharged internally. -/
theorem bound :
    ENNReal.ofReal (discreteDistance
      (fullGame table setup codec route wire sign seed scalar candidate provider source checks selectedOwner selectedAccept publicPrekey work frontend before)
      (hiddenGame table setup codec route wire sign seed scalar candidate provider source checks selectedOwner selectedAccept publicPrekey work frontend before)) ≤
      Pr{let pair ← (do
        let seeds ← $ᵗ (Seeds n)
        let result ← RegistrationNativeG3GuardedCoupling.audit setup codec route
          (RegistrationNativeG3GuardedCoupling.overlay before.2 seeds)
          (worldProgram table setup wire sign seed scalar candidate provider source checks selectedOwner selectedAccept publicPrekey work frontend before) before.2
        pure (seeds, result))}[pair.2.2.2 = true] := by
  have sourceEq : fullGame table setup codec route wire sign seed scalar candidate provider source checks selectedOwner selectedAccept publicPrekey work frontend before =
      Prod.fst <$> RegistrationNativeG3GuardedCoupling.knownGame setup codec route
        (worldProgram table setup wire sign seed scalar candidate provider source checks selectedOwner selectedAccept publicPrekey work frontend before) before.2 := by
    simp only [fullGame, RegistrationNativeG3GuardedCoupling.knownGame, map_bind,
      known_source table setup codec route wire sign seed scalar candidate provider source checks selectedOwner selectedAccept publicPrekey work frontend before]
  rw [sourceEq]
  exact (ENNReal.ofReal_le_ofReal (discreteDistance_map_le Prod.fst _ _)).trans
    (RegistrationNativeG3GuardedCoupling.bound setup codec route
      (worldProgram table setup wire sign seed scalar candidate provider source checks selectedOwner selectedAccept publicPrekey work frontend before) before.2)

end BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedProtocol
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedProtocol.known_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedProtocol.known_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedProtocol.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedProtocol.bound
