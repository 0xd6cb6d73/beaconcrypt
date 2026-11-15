-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePublicSourceFinishLocal
import BeaconcryptCore.Computational.RegistrationNativeBeaconCoherence

/-! The finite source join restores every owner's own scalar at its original public roster index. The selected owner uses the private scalar; ordinary owners retain their supplied scalar. World-owner and opaque KEM handles remain the stored separate fields. The actual native roster controller supplies the complete reached owner rather than a fabricated phase update. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceRoster
open PqxdhServerAuthExperiment (Setup)
open PqxdhJointIdentity (IdentitySeed)
open PqxdhJointGapDh (ScalarBytes)
open RegistrationNativePublicSourceEffects (Private)
open RegistrationNativePublicSourceCallbacks (implementation)
open RegistrationNativeOrdinaryFinishSourceNative (trusted)
open RegistrationNativeOrdinaryFinishSourceFrame (drop)
open RegistrationNativeOrdinaryFinishSourcePhase (adapt)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationNativePublicSourceState (owners)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι}
variable {mlSource : RegistrationNativeMldsa.Source}

def publicView (scalar : ScalarBytes)
    (result : (RustM (Option Pqxdh.Bytes) × RegistrationNativePublicOwners.State mlSource) ×
      EnvState RegistrationServerRoleBackend.State) :=
  ((result.1.1, owners scalar result.1.2), result.2)

def nativeView (result : (RustM (Option Pqxdh.Bytes) × RegistrationNativeBeaconFrontend.State mlSource) ×
    EnvState RegistrationServerRoleBackend.State) :=
  ((result.1.1, result.1.2), RegistrationBeaconReferenceNativeRecord.erase result.2)

private theorem public_run (setup : Setup base KemSK) (index : Nat) (packet : Option registration.ResponsePacket)
    (roster : RegistrationNativePublicOwners.State mlSource) (current : RegistrationNativePublicOwners.Owner mlSource)
    (found : roster[index]? = some current) (env : EnvState RegistrationServerRoleBackend.State) :
    ((RegistrationNativePublicOwners.finish (n := n) setup mlSource index packet).run roster).run env =
      (fun result => ((result.1.1, roster.set index { current with view := result.1.2 }), result.2)) <$>
        simulateQ (adapt setup current.scalar)
          (((RegistrationBeaconReferenceFinish.finish setup mlSource packet :
            RegistrationBeaconReferenceCompletion.M (target := RegistrationBeaconReferenceCompiler.Spec n KemSK)
              (Auxiliary := RegistrationServerRoleBackend.State) mlSource (RustM (Option Pqxdh.Bytes))).run current.view).run env) := by
  cases scalar : current.scalar <;>
    simp only [RegistrationNativePublicOwners.finish, StateT.run, found, scalar, adapt, simulateQ_id']

private def rebuild (roster : RegistrationNativeBeaconFrontend.State mlSource) (index : Nat)
    (result : (RustM (Option Pqxdh.Bytes) × RegistrationNativeBeaconFrontend.Owner mlSource) ×
      EnvState RegistrationServerRoleBackend.State) :=
  ((result.1.1, roster.set index result.1.2), result.2)

/-- The complete public-owner finishing command is the actual native roster finishing command on the same source World and private generated-key pool. -/
theorem finish_source (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : IdentitySeed) (selectedScalar : ScalarBytes) (index : Nat) (packet : Option registration.ResponsePacket)
    (roster : RegistrationNativePublicOwners.State mlSource)
    (coherent : RegistrationNativeBeaconCoherence.Holds (owners selectedScalar roster))
    (env : EnvState RegistrationServerRoleBackend.State) (empty : env.recordRequests = [])
    (erased : Std.Array U8 227#usize) (before : Private n KemSK) :
    Prod.map (publicView selectedScalar) drop <$>
      (simulateQ (implementation setup wire route sign seed selectedScalar)
        (((RegistrationNativePublicOwners.finish setup mlSource index packet).run roster).run env)).run before =
      Prod.map nativeView drop <$>
        (simulateQ (trusted setup wire route sign seed selectedScalar)
          (((RegistrationNativeBeaconFrontend.finish setup mlSource wire index packet).run
            (owners selectedScalar roster)).run env)).run before := by
  cases found : roster[index]? with
  | none =>
      have sameEnv : RegistrationBeaconReferenceNativeRecord.erase env = env := by
        cases env
        simp_all only [RegistrationBeaconReferenceNativeRecord.erase]
      have emptyRun : ((RegistrationNativePublicOwners.finish (n := n) (KemSK := KemSK)
          setup mlSource index packet).run roster).run env = pure ((.ok none, roster), env) := by
        simp only [RegistrationNativePublicOwners.finish, StateT.run, found]
      rw [emptyRun]
      simp only [RegistrationNativeBeaconFrontend.finish,
        StateT.run_bind, StateT.run_get, pure_bind, owners, List.getElem?_map, found,
        Option.map_none, StateT.run_pure, simulateQ_pure, map_pure, publicView, nativeView,
        Prod.map_def, sameEnv]
  | some current =>
      let native := RegistrationNativePublicSourceState.owner selectedScalar current
      have nativeFound : (owners selectedScalar roster)[index]? = some native := by
        simp only [owners, List.getElem?_map, found, Option.map_some]
        rfl
      have pendingCoherent : ∀ pending oneTime, native.phase = .initSent pending oneTime →
          pending.control.expected_server_binding = pending.binding.server_pin.binding := by
        intro pending oneTime sent
        have currentCoherent := coherent native (List.mem_of_getElem? nativeFound)
        simpa only [sent, RegistrationNativeBeaconCoherence.PhaseCoherent] using currentCoherent
      have single := RegistrationNativePublicSourceFinishLocal.finish_source setup wire route sign seed selectedScalar current.scalar
        native packet rfl pendingCoherent env empty erased before
      have mapped := congrArg (fun distribution => Prod.map (rebuild (owners selectedScalar roster) index) id <$> distribution) single
      have sameScalar : native.prekeyScalar = current.scalar.getD selectedScalar := rfl
      rw [sameScalar] at mapped
      rw [public_run setup index packet roster current found env,
        RegistrationBeaconReferenceNativeOwner.finish_source setup wire index packet
          (owners selectedScalar roster) native nativeFound env]
      simpa only [simulateQ_map, StateT.run_map, Functor.map_map, Prod.map_def, id_eq,
        publicView, nativeView, rebuild, owners, List.map_set,
        RegistrationNativePublicSourceFinishLocal.restorePublic, RegistrationNativePublicSourceFinishLocal.recordView,
        RegistrationNativePublicSourceState.owner, RegistrationBeaconReferenceCompiler.erase_restore,
        native] using mapped

end BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceRoster

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceRoster.finish_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceRoster.finish_source
