-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborProductionBoundary

/-! Empty-message substitutions implement rejected CBOR commands without executing a record primitive. A build still consumes its moved registration token. These are exact operational equalities, not cryptographic headline transfers. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborAdmissionSubstitution
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhServerAuthNative
variable {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}

def consumeRegistration (session : Nat) (state : NativeState KemSK) : NativeState KemSK :=
  (state.1, { state.2 with pending := Function.update state.2.pending session none })

theorem candidate_empty (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (candidate : pqxdh.ServerRegistrationCandidate)
    (root : PqxdhSecretInputKdf.RootOutput)
    (server : PqxdhServerRegistrationPublication.State Unit Unit (List Pqxdh.Bytes))
    (state : RawCtxSharedPrimitive.SharedState (List RawCtxSourceSend.SealContext)) :
    (fun result => (PqxdhServerAuthExperiment.settle server result.1, result.2)) <$>
      ((simulateQ (PqxdhServerAuthExperiment.tailImpl setup codec checks)
        (PqxdhServerRegistrationPublication.candidateTail setup.source candidate root (some []) () server)).run state) =
      pure ((none, server), state) := by
  simp only [PqxdhServerRegistrationPublication.candidateTail, simulateQ_bind, simulateQ_spec_query,
    StateT.run_bind, PqxdhServerAuthNegativeControl.tailImpl_aux, PqxdhServerAuthExperiment.tailAux,
    StateT.run_pure, pure_bind]
  cases checks.beaconIdentity candidate.beacon_identity_public_key <;>
    simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_true, ite_false,
      simulateQ_bind, simulateQ_spec_query, simulateQ_pure, StateT.run_bind,
      PqxdhServerAuthNegativeControl.tailImpl_aux, PqxdhServerAuthExperiment.tailAux,
      StateT.run_pure, pure_bind, map_pure, PqxdhServerAuthExperiment.settle]
  cases checks.reservePeer <;>
    simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_true, ite_false,
      simulateQ_pure, StateT.run_pure, map_pure, Option.getD_some, List.isEmpty_nil]
  cases Refinement.ServerTransactionRefinement.initializeCandidate candidate
      (PqxdhRootTableInitialization.rootArray root)
      (PqxdhRootTableInitialization.initialResponse setup.source.crypto) <;>
    simp only [PqxdhServerRegistrationPublication.continueRust, simulateQ_pure, StateT.run_pure, map_pure]

theorem build_empty (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (pending : pqxdh.PendingServerRegistration)
    (root : PqxdhSecretInputKdf.RootOutput)
    (server : PqxdhServerRegistrationPublication.State Unit Unit (List Pqxdh.Bytes))
    (state : RawCtxSharedPrimitive.SharedState (List RawCtxSourceSend.SealContext)) :
    (fun result => (PqxdhServerAuthExperiment.settle server result.1, result.2)) <$>
      ((simulateQ (PqxdhServerAuthExperiment.tailImpl setup codec checks)
        (PqxdhServerRegistrationPublication.build setup.source pending root (some []) () server)).run state) =
      pure ((none, server), state) := by
  unfold PqxdhServerRegistrationPublication.build
  cases next : pqxdh.server_next_key_id server.control <;>
    simp only [PqxdhServerRegistrationPublication.continueRust, simulateQ_pure, StateT.run_pure,
      map_pure, PqxdhServerAuthExperiment.settle]
  rename_i result
  cases result <;> simp only [simulateQ_pure, StateT.run_pure, map_pure]
  rename_i key
  cases pqxdh.server_prepare_commit server.control pending
      ⟨server.server.identity, server.identityKeyId⟩
      (if (server.server.peers key).isSome then .Occupied else .Available) <;>
    simp only [simulateQ_pure, StateT.run_pure, map_pure]
  rename_i prepared
  cases prepared <;> simp only [simulateQ_pure, StateT.run_pure, map_pure]
  exact candidate_empty setup codec checks _ root server state

/-- An empty build consumes exactly its addressed token and leaves the complete primitive state unchanged. -/
theorem native_build_empty (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (session : Nat) (state : NativeState KemSK) :
    nativeBuild setup codec checks session (some []) state =
      pure (none, consumeRegistration session state) := by
  simp only [nativeBuild, nativeGet_bind]
  cases found : state.2.pending session
  case none =>
    simp only [native_pure_run, consumeRegistration, ← found, Function.update_eq_self]
  case some token =>
    simp only [native_bind_run, nativeCoins, nativeSet, bind_pure_comp]
    simp only [native_map_run, PqxdhServerAuthNative.localState, map_pure,
      bind_pure_comp, Functor.map_map]
    let complete := fun result :
        ((Option PqxdhServerRegistrationPublication.Response ×
          PqxdhServerRegistrationPublication.State Unit Unit (List Pqxdh.Bytes)) ×
          RawCtxSharedPrimitive.SharedState (List RawCtxSourceSend.SealContext)) =>
      (result.1.1, (state.1, { state.2 with
        ctx := result.2.2
        server := result.1.2
        pending := Function.update state.2.pending session none
        ghost := { state.2.ghost with
          seals := state.2.ghost.seals ++ (result.2.1.map fun context => (session, context)) } }))
    simpa only [complete, Functor.map_map, Function.comp_def, Prod.map_apply, id_eq,
      map_pure, List.map_nil, List.append_nil, consumeRegistration] using
      congrArg (fun work => complete <$> work)
        (build_empty setup codec checks token.pending token.root state.2.server ([], state.2.ctx))

/-- The deployment lift preserves owners, raw counters and produced frames while consuming the moved token. -/
theorem deployment_build_empty (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (seed : PqxdhJointIdentity.IdentitySeed) (session : Nat)
    (state : PqxdhDeploymentNative.State KemSK) :
    (PqxdhDeploymentNative.handler setup codec checks route seed (.inr (.build session (some [])))).run state =
      pure (none, CborProductionBoundary.consumePending session state) := by
  change (fun result => (result.1, { state with native := result.2 })) <$>
    (PqxdhRegistrationSchedule.onShared (nativeBuild setup codec checks session (some []))).run state.native = _
  rw [PqxdhRegistrationSchedule.onShared_run, native_build_empty]
  simp only [map_pure, consumeRegistration, CborProductionBoundary.consumePending]

end BeaconcryptCore.Computational.CborAdmissionSubstitution

/-- info: 'BeaconcryptCore.Computational.CborAdmissionSubstitution.candidate_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborAdmissionSubstitution.candidate_empty
/-- info: 'BeaconcryptCore.Computational.CborAdmissionSubstitution.build_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborAdmissionSubstitution.build_empty
/-- info: 'BeaconcryptCore.Computational.CborAdmissionSubstitution.native_build_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborAdmissionSubstitution.native_build_empty
/-- info: 'BeaconcryptCore.Computational.CborAdmissionSubstitution.deployment_build_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborAdmissionSubstitution.deployment_build_empty
