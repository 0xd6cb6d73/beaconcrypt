-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhBoundaryRegistrationAccept
import BeaconcryptCore.Computational.PqxdhDeploymentLaterServerGame

/-! Complete source acceptance with the actual private LQ-F ephemeral log. No ghost is projected away. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhBoundaryLoggedAccept
open PqxdhServerAuthExperiment PqxdhJointIdentity PqxdhJointGapDh PqxdhServerAuthNative
open PqxdhServerRootPreparation (Inputs Verified Ephemeral)
open PqxdhBeaconPhase2Preparation (Word32)
open PqxdhDeploymentLaterServerSource (Log)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result : Type}

/-- The source verifier feeds the real pre-encapsulation collector. The entry survives later rejection, including rejected KEM parsing after scalar generation. -/
def collection {E Shared : Type} (raw : Pqxdh.Bytes) :
    OracleComp (PqxdhServerRootPreparation.Spec Reader E Shared) (Option (Inputs Reader E Shared) × Option E) := do
  let verified ← PqxdhBoundaryRegistrationAccept.verification raw
  match verified with
  | none => pure (none, none)
  | some verified => do
      let before ← PqxdhDeploymentLaterServerSource.beforeLogged verified
      match before.1 with
      | none => pure (none, before.2)
      | some ephemeral => do
          let reply ← (PqxdhServerRootPreparation.Spec Reader E Shared).query (.encapsulate verified.keys.pqKey)
          let input ← PqxdhRegistrationJointKemCollected.afterEncapsulation verified ephemeral reply
          pure (input, some ephemeral.secret)

/-- Exact callback program equality keeps both the collected input and generated scalar under every subsequent interpretation. -/
theorem collection_exact {E Shared : Type} (raw : Pqxdh.Bytes) :
    collection (Reader := Reader) (E := E) (Shared := Shared) raw =
      PqxdhDeploymentLaterServerSource.collectLogged raw := by
  simp only [collection, PqxdhDeploymentLaterServerSource.collectLogged, PqxdhBoundaryRegistrationAccept.verification_source]
  rfl

/-- The original native callbacks interpret the exact logged source program, retaining the consumed-ID state beside both returned values. -/
noncomputable def preparation (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (seed : IdentitySeed) (raw : Pqxdh.Bytes) :
    StateT (List Pqxdh.Bytes) ProbComp (Option (Inputs Reader ScalarBytes Word32) × Option ScalarBytes) :=
  simulateQ (PqxdhServerStaticDhSource.nativeImpl setup.joint seed (serverAux setup codec checks)
    (fun _ => pure ())) (collection raw)

/-- Exact native prefix law includes the generated scalar and the consumed set, with no success or honesty premise. -/
theorem preparation_exact (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (seed : IdentitySeed) (raw : Pqxdh.Bytes) :
    preparation setup codec checks seed raw =
      PqxdhDeploymentLaterServerNative.prefixLogged setup codec checks seed raw := by
  simp only [preparation, PqxdhDeploymentLaterServerNative.prefixLogged, collection_exact]

/-- The original acceptance tail is run on the very source-collected input and consumed state, retaining both the scalar and every native effect. -/
noncomputable def accept (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (seed : IdentitySeed) (raw : Pqxdh.Bytes) :
    NativeGame KemSK (Option Nat × Option ScalarBytes) := fun shared => do
  let collected ← (preparation setup codec checks seed raw).run shared.2.server.consumed
  let answer ← (PqxdhRegistrationJointServerAccept.tail setup (setup.joint.publicKeys seed) shared.2
    (collected.1.1, collected.2)).run shared
  pure ((answer.1, collected.1.2), answer.2)

/-- Full logged acceptance equality, not its scalar-forgetting projection. -/
theorem accept_exact (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (seed : IdentitySeed) (raw : Pqxdh.Bytes) (shared : NativeState KemSK) :
    (accept setup codec checks seed raw).run shared =
      (PqxdhDeploymentLaterServerNative.acceptLogged setup codec checks seed raw).run shared := by
  rw [PqxdhDeploymentLaterServerNative.acceptLogged_run]
  simp only [accept, StateT.run, preparation_exact]

/-- The exact source-collected accept is reinstalled in the deployment state and appends one optional scalar entry for this actual attempt. -/
noncomputable def deployment (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (seed : IdentitySeed) (raw : Pqxdh.Bytes) :
    StateT (PqxdhDeploymentNative.State KemSK × Log) ProbComp (Option Nat) := fun state =>
  (fun result => (result.1.1, ({ state.1 with native := { state.1.native with shared := result.2 } },
    state.2 ++ [result.1.2]))) <$> (accept setup codec checks seed raw).run state.1.native.shared

/-- CE's actual logged acceptance is the same full source execution and log append, for arbitrary previous state and log. -/
theorem deployment_exact (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (route : RawCtxServerRouting.SenderDecoder) (seed : IdentitySeed)
    (raw : Pqxdh.Bytes) (state : PqxdhDeploymentNative.State KemSK × Log) :
    (deployment setup codec checks seed raw).run state =
      (PqxdhDeploymentLaterServerGame.handler setup codec checks route seed (.inr (.accept raw))).run state := by
  have same := accept_exact setup codec checks seed raw state.1.native.shared
  simp only [StateT.run] at same
  simp only [deployment, PqxdhDeploymentLaterServerGame.handler,
    PqxdhDeploymentLaterServerNative.native, PqxdhRegistrationSchedule.onShared, StateT.run, Functor.map_map, same]

/-- Every adaptive continuation receives the exact joint optional reply, live deployment state and appended private log. -/
theorem deployment_complete (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (route : RawCtxServerRouting.SenderDecoder) (seed : IdentitySeed)
    (raw : Pqxdh.Bytes) (state : PqxdhDeploymentNative.State KemSK × Log)
    (next : Option Nat × (PqxdhDeploymentNative.State KemSK × Log) → ProbComp Result) :
    (deployment setup codec checks seed raw).run state >>= next =
      (PqxdhDeploymentLaterServerGame.handler setup codec checks route seed (.inr (.accept raw))).run state >>= next := by
  rw [deployment_exact setup codec checks route seed raw state]

/-- Forgetting the log of the exact source-collected accept gives the published PB-03 adapter operation on the complete deployment state, so the logged and the classical acceptance boundaries agree on every reply and state field. -/
theorem deployment_erase (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (seed : IdentitySeed) (raw : Pqxdh.Bytes)
    (state : PqxdhDeploymentNative.State KemSK) (log : Log) :
    Prod.map id Prod.fst <$> (deployment setup codec checks seed raw).run (state, log) =
      (PqxdhBoundaryRegistrationAccept.deploymentAccept setup codec checks seed raw).run state := by
  rw [deployment_exact setup codec checks (fun _ => none) seed raw (state, log),
    PqxdhDeploymentLaterServerGame.handler_erase setup codec checks (fun _ => none) seed (.inr (.accept raw)) state log,
    PqxdhBoundaryRegistrationAccept.deployment_accept]

/-- The logged source collector keeps the callback cap of the unlogged collector (`PqxdhServerRootPreparation.collect_bound`, the cap that `PqxdhBoundaryRegistrationAccept.source_callback_caps` states for the published PB-03 collector): at most twenty-two source callbacks before interpretation. Logging the generated scalar adds no callback. -/
theorem logged_caps {E Shared : Type} (raw : Pqxdh.Bytes) :
    (collection (Reader := Reader) (E := E) (Shared := Shared) raw).IsTotalQueryBound 22 := by
  have unlogged := PqxdhServerRootPreparation.collect_bound (Reader := Reader) (E := E) (Shared := Shared) raw
  rw [← PqxdhDeploymentLaterServerSource.collectLogged_fst] at unlogged
  rw [collection_exact]
  exact (isQueryBound_map_iff _ _ _ _ _).mp unlogged

/-- Every supported logged acceptance appends exactly one optional scalar entry to the private log and changes no earlier entry. -/
theorem deployment_log (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (seed : IdentitySeed) (raw : Pqxdh.Bytes)
    (state : PqxdhDeploymentNative.State KemSK × Log)
    (result : Option Nat × (PqxdhDeploymentNative.State KemSK × Log))
    (supported : result ∈ support ((deployment setup codec checks seed raw).run state)) :
    ∃ entry : Option ScalarBytes, result.2.2 = state.2 ++ [entry] := by
  change result ∈ support (deployment setup codec checks seed raw state) at supported
  simp only [deployment, support_map, Set.mem_image] at supported
  obtain ⟨accepted, _, rfl⟩ := supported
  exact ⟨accepted.1.2, rfl⟩

end BeaconcryptCore.Computational.PqxdhBoundaryLoggedAccept

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhBoundaryLoggedAccept.collection_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryLoggedAccept.collection_exact

/--
info: 'BeaconcryptCore.Computational.PqxdhBoundaryLoggedAccept.preparation_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryLoggedAccept.preparation_exact

/--
info: 'BeaconcryptCore.Computational.PqxdhBoundaryLoggedAccept.accept_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryLoggedAccept.accept_exact

/--
info: 'BeaconcryptCore.Computational.PqxdhBoundaryLoggedAccept.deployment_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryLoggedAccept.deployment_exact

/--
info: 'BeaconcryptCore.Computational.PqxdhBoundaryLoggedAccept.deployment_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryLoggedAccept.deployment_complete

/--
info: 'BeaconcryptCore.Computational.PqxdhBoundaryLoggedAccept.deployment_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryLoggedAccept.deployment_erase

/--
info: 'BeaconcryptCore.Computational.PqxdhBoundaryLoggedAccept.logged_caps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryLoggedAccept.logged_caps

/--
info: 'BeaconcryptCore.Computational.PqxdhBoundaryLoggedAccept.deployment_log' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryLoggedAccept.deployment_log
