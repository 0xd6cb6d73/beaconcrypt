-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePublicSourceCreate
import BeaconcryptCore.Computational.RegistrationNativePublicSourceBundle
import BeaconcryptCore.Computational.RegistrationNativePublicSourceOtherQueries
import BeaconcryptCore.Computational.RegistrationNativePublicSourceServerQueries
import BeaconcryptCore.Computational.RegistrationNativePublicSourceFinish
import BeaconcryptCore.Computational.RegistrationNativePublicMaskInvariant
import BeaconcryptCore.Computational.RegistrationNativeScalarEagerView
import BeaconcryptCore.Computational.RegistrationNativePublicInvariantRun

/-! Internal source invariants and adaptive sequencing for the complete mixed native client. These are derived execution properties, not additions to the original secrecy event or to the cryptographic assumptions. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePublicSourceProgram
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePublicSourceServer (State)
open RegistrationNativePublicSourceState (Live MemoCorrect owners)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

/-- Internal state tracks live source roots, the selected-owner mask and controller metadata. -/
structure Good (setup : Setup base KemSK) (seed : PqxdhJointIdentity.IdentitySeed)
    (scalar : PqxdhJointGapDh.ScalarBytes) (selected : Nat) (before : State n KemSK source) : Prop where
  live : Live before.1 before.2
  memo : MemoCorrect setup seed scalar before.2.roots
  mask : RegistrationNativePublicOwnerMask.Canonical selected (setup.dh.publicKey scalar) before.1.beacons
  coherent : RegistrationNativeBeaconCoherence.Holds (owners scalar before.1.beacons)
  empty : before.1.environment.recordRequests = []

/-- Each actual typed query executes the complete native eager command on its restored source state. The metadata and memo conditions are the initialized execution invariant. -/
theorem query_source (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (correct : PqxdhSecretInputKdf.SourceRootCorrect setup.source setup.hmac)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (scalar : PqxdhJointGapDh.ScalarBytes)
    (credential : RegistrationNativeMldsa.Credential source) (selectedOwner selectedAccept : Nat)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State n KemSK source)
    (good : Good setup created.seed scalar selectedOwner before) :
    Prod.map id (fun after => RegistrationNativePublicSourceState.project
      (RegistrationNativePublicSourceState.roots setup created.seed scalar) scalar after.1 after.2) <$>
      (RegistrationNativePublicSourceExecution.execute setup wire route (RegistrationNativeMldsa.owned source credential) created.seed scalar
        (RegistrationNativePublicFrontend.handler setup checks wire source (RegistrationNativeMldsa.owned source credential)
          selectedOwner selectedAccept (setup.dh.publicKey scalar) query)).run before =
      Prod.map id RegistrationNativePublicSourceState.nativeView <$>
        (RegistrationNativeScalarEager.handler setup checks wire route representation created source credential selectedOwner scalar query).run
          (RegistrationNativePublicSourceState.restore (RegistrationNativePublicSourceState.roots setup created.seed scalar)
            scalar before.1 before.2) := by
  cases query with
  | inl coin =>
      exact RegistrationNativePublicSourceOtherQueries.query_source setup checks wire route representation created scalar credential
        selectedOwner selectedAccept (setup.dh.publicKey scalar) _ (.inl coin) trivial before
  | inr command => cases command with
    | create edPin mlPin keyId =>
        exact RegistrationNativePublicSourceCreate.create_source setup checks wire route representation created scalar credential
          selectedOwner selectedAccept _ edPin mlPin keyId before good.mask
    | bundle index =>
        exact RegistrationNativePublicSourceBundle.bundle_source setup checks wire route representation created scalar credential
          selectedOwner selectedAccept _ index before good.mask
    | accept packet =>
        exact RegistrationNativePublicSourceServerQueries.accept_source setup checks wire route representation correct created scalar credential
          selectedOwner selectedAccept (setup.dh.publicKey scalar) packet before
    | build handle application =>
        exact RegistrationNativePublicSourceServerQueries.build_source setup checks wire route representation created scalar credential
          selectedOwner selectedAccept (setup.dh.publicKey scalar) handle application before good.live good.memo
    | finish index packet =>
        exact RegistrationNativePublicSourceFinish.finish_source setup checks wire route representation created scalar credential
          selectedOwner selectedAccept (setup.dh.publicKey scalar) _ index packet before good.coherent good.empty
    | hmac key bytes =>
        exact RegistrationNativePublicSourceOtherQueries.query_source setup checks wire route representation created scalar credential
          selectedOwner selectedAccept (setup.dh.publicKey scalar) _ (.inr (.hmac key bytes)) trivial before
    | hash bytes =>
        exact RegistrationNativePublicSourceOtherQueries.query_source setup checks wire route representation created scalar credential
          selectedOwner selectedAccept (setup.dh.publicKey scalar) _ (.inr (.hash bytes)) trivial before
    | serverSend keyId plaintext =>
        exact RegistrationNativePublicSourceOtherQueries.query_source setup checks wire route representation created scalar credential
          selectedOwner selectedAccept (setup.dh.publicKey scalar) _ (.inr (.serverSend keyId plaintext)) trivial before
    | serverRaw raw =>
        exact RegistrationNativePublicSourceOtherQueries.query_source setup checks wire route representation created scalar credential
          selectedOwner selectedAccept (setup.dh.publicKey scalar) _ (.inr (.serverRaw raw)) trivial before
    | beaconSend index plaintext =>
        exact RegistrationNativePublicSourceOtherQueries.query_source setup checks wire route representation created scalar credential
          selectedOwner selectedAccept (setup.dh.publicKey scalar) _ (.inr (.beaconSend index plaintext)) trivial before
    | beaconRaw index raw =>
        exact RegistrationNativePublicSourceOtherQueries.query_source setup checks wire route representation created scalar credential
          selectedOwner selectedAccept (setup.dh.publicKey scalar) _ (.inr (.beaconRaw index raw)) trivial before

/-- Every actual source query preserves all internal invariants needed by the complete native correspondence. -/
theorem query_good (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (scalar : PqxdhJointGapDh.ScalarBytes)
    (credential : RegistrationNativeMldsa.Credential source) (selectedOwner selectedAccept : Nat)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State n KemSK source)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State n KemSK source)
    (good : Good setup created.seed scalar selectedOwner before)
    (supported : result ∈ support
      ((RegistrationNativePublicSourceExecution.execute setup wire route (RegistrationNativeMldsa.owned source credential) created.seed scalar
        (RegistrationNativePublicFrontend.handler setup checks wire source (RegistrationNativeMldsa.owned source credential)
          selectedOwner selectedAccept (setup.dh.publicKey scalar) query)).run before)) :
    Good setup created.seed scalar selectedOwner result.2 := by
  have roots := RegistrationNativePublicSourceInvariant.query_live setup checks wire route
    (RegistrationNativeMldsa.owned source credential) created.seed scalar selectedOwner selectedAccept
    (setup.dh.publicKey scalar) query before result good.live good.memo supported
  have raw := RegistrationNativePublicSourceExecution.observed_support setup wire route
    (RegistrationNativeMldsa.owned source credential) created.seed scalar _ before result supported
  have mask := RegistrationNativePublicMaskInvariant.query_canonical setup checks wire
    (RegistrationNativeMldsa.owned source credential) selectedOwner selectedAccept (setup.dh.publicKey scalar)
    query before.1 (result.1, result.2.1) good.mask raw
  have metadata := RegistrationNativePublicInvariantRun.query_good setup checks wire
    (RegistrationNativeMldsa.owned source credential) selectedOwner selectedAccept (setup.dh.publicKey scalar)
    query before.1 (result.1, result.2.1)
    ⟨(RegistrationNativePublicInvariantOwners.restored_holds scalar before.1.beacons).mpr good.coherent, good.empty⟩ raw
  exact ⟨roots.1, roots.2, mask,
    (RegistrationNativePublicInvariantOwners.restored_holds scalar result.2.1.beacons).mp metadata.1, metadata.2⟩

private theorem project_program {Index S T Result : Type} {spec : OracleSpec Index}
    (sourceImpl : QueryImpl spec (StateT S ProbComp)) (targetImpl : QueryImpl spec (StateT T ProbComp))
    (restore : S → T) (view : T → T) (idempotent : ∀ state, view (view state) = view state)
    (invariant : S → Prop)
    (keeps : ∀ query before result, invariant before → result ∈ support ((sourceImpl query).run before) → invariant result.2)
    (step : ∀ query before, invariant before →
      Prod.map id (view ∘ restore) <$> (sourceImpl query).run before =
        Prod.map id view <$> (targetImpl query).run (restore before))
    (stable : ∀ query, RegistrationStateView.Stable view (targetImpl query))
    (work : OracleComp spec Result) (before : S) (valid : invariant before) :
    Prod.map id (view ∘ restore) <$> (simulateQ sourceImpl work).run before =
      Prod.map id view <$> (simulateQ targetImpl work).run (restore before) := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure, Prod.map_def, id_eq, Function.comp_def]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
      calc
        _ = (sourceImpl query).run before >>= fun reached =>
            Prod.map id view <$> (simulateQ targetImpl (next reached.1)).run ((view ∘ restore) reached.2) := by
          apply bind_congr_of_forall_mem_support
          rintro ⟨value, after⟩ supported
          exact (ih value after (keeps query before (value, after) valid supported)).trans
            (RegistrationStateView.program_stable view idempotent targetImpl stable (next value) (restore after))
        _ = (Prod.map id (view ∘ restore) <$> (sourceImpl query).run before) >>= fun reached =>
            Prod.map id view <$> (simulateQ targetImpl (next reached.1)).run reached.2 := by
          rw [bind_map_left]
          rfl
        _ = (Prod.map id view <$> (targetImpl query).run (restore before)) >>= fun reached =>
            Prod.map id view <$> (simulateQ targetImpl (next reached.1)).run reached.2 := by rw [step query before valid]
        _ = _ := by
          rw [bind_map_left]
          apply bind_congr
          rintro ⟨value, after⟩
          exact (RegistrationStateView.program_stable view idempotent targetImpl stable (next value) after).symm

private theorem execute_program (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (scalar : PqxdhJointGapDh.ScalarBytes) (credential : RegistrationNativeMldsa.Credential source)
    (selectedOwner selectedAccept : Nat) (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value)
    (before : State n KemSK source) :
    (RegistrationNativePublicSourceExecution.execute setup wire route (RegistrationNativeMldsa.owned source credential) created.seed scalar
      (simulateQ (RegistrationNativePublicFrontend.handler setup checks wire source (RegistrationNativeMldsa.owned source credential)
        selectedOwner selectedAccept (setup.dh.publicKey scalar)) work)).run before =
      (simulateQ (fun query => RegistrationNativePublicSourceExecution.execute setup wire route
        (RegistrationNativeMldsa.owned source credential) created.seed scalar
        (RegistrationNativePublicFrontend.handler setup checks wire source (RegistrationNativeMldsa.owned source credential)
          selectedOwner selectedAccept (setup.dh.publicKey scalar) query)) work).run before := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => rfl
  | query_bind query next ih =>
      rw [simulateQ_bind, RegistrationNativePublicSourceExecution.execute_bind,
        simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      simp only [simulateQ_spec_query]
      apply bind_congr
      rintro ⟨value, after⟩
      exact ih value after

/-- The complete arbitrary adaptive native typed client has its literal eager-source outcome, including the entire final protocol state and original ledger whenever that ledger is the client's output. -/
theorem program_source (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (correct : PqxdhSecretInputKdf.SourceRootCorrect setup.source setup.hmac)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (scalar : PqxdhJointGapDh.ScalarBytes)
    (credential : RegistrationNativeMldsa.Credential source) (selectedOwner selectedAccept : Nat)
    (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value) (before : State n KemSK source)
    (good : Good setup created.seed scalar selectedOwner before) :
    Prod.map id (fun after => RegistrationNativePublicSourceState.project
      (RegistrationNativePublicSourceState.roots setup created.seed scalar) scalar after.1 after.2) <$>
      (RegistrationNativePublicSourceExecution.execute setup wire route (RegistrationNativeMldsa.owned source credential) created.seed scalar
        (simulateQ (RegistrationNativePublicFrontend.handler setup checks wire source (RegistrationNativeMldsa.owned source credential)
          selectedOwner selectedAccept (setup.dh.publicKey scalar)) work)).run before =
      Prod.map id RegistrationNativePublicSourceState.nativeView <$>
        (simulateQ (RegistrationNativeScalarEager.handler setup checks wire route representation created source credential selectedOwner scalar) work).run
          (RegistrationNativePublicSourceState.restore (RegistrationNativePublicSourceState.roots setup created.seed scalar)
            scalar before.1 before.2) := by
  rw [execute_program]
  apply project_program _ _
    (fun state => RegistrationNativePublicSourceState.restore (RegistrationNativePublicSourceState.roots setup created.seed scalar) scalar state.1 state.2)
    RegistrationNativePublicSourceState.nativeView RegistrationNativeMainViewLift.view_idempotent
    (Good setup created.seed scalar selectedOwner)
  · exact query_good setup checks wire route created scalar credential selectedOwner selectedAccept
  · intro query current valid
    exact query_source setup checks wire route representation correct created scalar credential selectedOwner selectedAccept query current valid
  · exact RegistrationNativeScalarEagerView.handler_input setup checks wire route representation created credential selectedOwner scalar
  · exact good

end BeaconcryptCore.Computational.RegistrationNativePublicSourceProgram

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicSourceProgram.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicSourceProgram.query_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicSourceProgram.query_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicSourceProgram.query_good
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicSourceProgram.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicSourceProgram.program_source
