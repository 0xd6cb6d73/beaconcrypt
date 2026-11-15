-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeExperimentProjection

/-! The concrete native parsed-accept counter counts every decoded typed accept, including authentication, replay and allocation rejection. Other actual role operations preserve it. Structural command bills bound this counter without identifying it with an encapsulation getter or successful-session ordinal. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeExperimentCounts
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeExperiment (State)
open RegistrationNativeRawAdapter (TypedSpec kind)
open RegistrationNativeWire (Wire)
open PqxdhDeploymentInterface (Mode Budget FreshBounds)
attribute [local irreducible] RegistrationServerSdkSource.accept

variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι} {mlSource : RegistrationNativeMldsa.Source}

private theorem server_count (work : StateT (RegistrationServerFrontendCompiler.State n) ProbComp Value)
    (before : State n KemSK mlSource) (result : Value × State n KemSK mlSource)
    (supported : result ∈ support ((RegistrationNativeExperiment.server work).run before)) :
    result.2.parsedAccepts = before.parsedAccepts := by
  simp only [RegistrationNativeExperiment.server, StateT.run, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  rfl

private theorem world_count (work : StateT (PqxdhRecordLiftWorld.State n) ProbComp Value)
    (before : State n KemSK mlSource) (result : Value × State n KemSK mlSource)
    (supported : result ∈ support ((RegistrationNativeExperiment.world work).run before)) :
    result.2.parsedAccepts = before.parsedAccepts := server_count _ before result supported

private theorem trusted_count (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (query : (RegistrationNativeBeaconFrontend.Trusted n KemSK).Domain)
    (before : State n KemSK mlSource)
    (result : (RegistrationNativeBeaconFrontend.Trusted n KemSK).Range query × State n KemSK mlSource)
    (supported : result ∈ support
      ((RegistrationNativeExperiment.trusted setup checks representation created mlSource query).run before)) :
    result.2.parsedAccepts = before.parsedAccepts := by
  cases query with
  | inl query => exact world_count _ before result supported
  | inr query =>
      simp only [RegistrationNativeExperiment.trusted, StateT.run, bind_pure_comp, support_map] at supported
      obtain ⟨inner, reached, rfl⟩ := supported
      rfl

private theorem beacon_count (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : RegistrationNativeBeaconFrontend.M n KemSK mlSource RegistrationServerRoleBackend.State Value)
    (before : State n KemSK mlSource) (result : Value × State n KemSK mlSource)
    (supported : result ∈ support ((RegistrationNativeExperiment.beacon setup checks representation created work).run before)) :
    result.2.parsedAccepts = before.parsedAccepts := by
  simp only [RegistrationNativeExperiment.beacon, StateT.run, bind_pure_comp, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact simulateQ_run_preservesInv _ (fun state => state.parsedAccepts = before.parsedAccepts)
    (fun query state previous after reached => (trusted_count setup checks representation created query state after reached).trans previous)
    _ before rfl inner reached

private theorem record_count (setup : Setup base KemSK) (wire : Wire) (route : RawCtxServerRouting.SenderDecoder)
    (query : PqxdhRecordLiftInterface.RecordQuery) (before : State n KemSK mlSource)
    (result : (PqxdhRecordLiftInterface.RecordSpec .O).Range query × State n KemSK mlSource)
    (supported : result ∈ support ((RegistrationNativeExperiment.record setup wire route query mlSource).run before)) :
    result.2.parsedAccepts = before.parsedAccepts := by
  cases query with
  | inl query => exact world_count _ before result supported
  | inr query =>
      rcases query with ⟨owner, query⟩
      cases query <;>
        cases found : before.beacons[owner]? with
        | none =>
            simp only [RegistrationNativeExperiment.record, StateT.run, found, mem_support_pure_iff] at supported
            subst result
            rfl
        | some selected =>
            simp only [RegistrationNativeExperiment.record, StateT.run, found] at supported
            exact world_count _ before result supported

/-- Every actual parsed accept increments once even if it rejects; every other typed source query preserves the counter. -/
theorem typed_step (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential mlSource)
    (query : TypedSpec.Domain) (before : State n KemSK mlSource)
    (result : TypedSpec.Range query × State n KemSK mlSource)
    (supported : result ∈ support
      ((RegistrationNativeExperiment.handler setup checks wire route representation created mlSource credential query).run before)) :
    result.2.parsedAccepts = before.parsedAccepts + (if kind query = 3 then 1 else 0) := by
  cases query with
  | inl coin => simpa [kind] using world_count _ before result supported
  | inr query =>
      cases query with
      | create edPin mlPin keyId => simpa [kind] using beacon_count setup checks representation created _ before result supported
      | bundle owner => simpa [kind] using beacon_count setup checks representation created _ before result supported
      | accept packet =>
          change result ∈ support ((RegistrationNativeExperiment.server
            (RegistrationServerSdkSource.accept setup (RegistrationNativeWire.ledgerCodec wire) checks route mlSource.verify
              representation created packet)).run { before with parsedAccepts := before.parsedAccepts + 1 }) at supported
          simpa only [kind, ite_true] using server_count _ _ result supported
      | build handle application => simpa [kind] using server_count _ before result supported
      | finish owner packet => simpa [kind] using beacon_count setup checks representation created _ before result supported
      | hmac key message =>
          simp only [RegistrationNativeExperiment.handler, StateT.run_pure, mem_support_pure_iff] at supported
          subst result
          simp [kind]
      | hash bytes => simpa [kind] using world_count _ before result supported
      | serverSend keyId plaintext => simpa [kind] using record_count setup wire route (.inl (.inl (plaintext, keyId))) before result supported
      | serverRaw raw => simpa [kind] using record_count setup wire route (.inl (.inr raw)) before result supported
      | beaconSend owner plaintext => simpa [kind] using record_count setup wire route (.inr (owner, .inl plaintext)) before result supported
      | beaconRaw owner raw => simpa [kind] using record_count setup wire route (.inr (owner, .inr raw)) before result supported

/-- The actual supported counter increment is bounded by the typed program's structural accept bill. -/
theorem program_bound (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential mlSource)
    (work : OracleComp TypedSpec Value) (cap : Nat) (bounded : work.IsQueryBoundP (fun query => kind query = 3) cap)
    (before : State n KemSK mlSource) (result : Value × State n KemSK mlSource)
    (supported : result ∈ support
      ((simulateQ (RegistrationNativeExperiment.handler setup checks wire route representation created mlSource credential) work).run before)) :
    result.2.parsedAccepts ≤ before.parsedAccepts + cap := by
  induction work using OracleComp.inductionOn generalizing cap before result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      subst result
      simp only []
      omega
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      rw [simulateQ_bind, StateT.run_bind, simulateQ_spec_query, mem_support_bind_iff] at supported
      obtain ⟨inner, reached, tail⟩ := supported
      have first := typed_step setup checks wire route representation created credential query before inner reached
      have rest := ih inner.1 _ (bounded.2 inner.1) inner.2 result tail
      by_cases selected : kind query = 3
      · have positive := bounded.1.resolve_left (not_not.mpr selected)
        simp only [selected, ite_true] at first rest
        omega
      · simp only [selected, ite_false] at first rest
        omega

/-- The unchanged native secrecy compiler charges a typed accept only to an original public raw accept, never to its hidden sends or coins. -/
theorem compiled_accept_bill (setup : Setup base KemSK) (wire : Wire) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (bounds : FreshBounds) (mode : Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (budget : Budget) (bounded : RegistrationNativeInterface.Respects budget work) :
    (RegistrationNativeFullCompiler.compile setup.source.crypto wire created.server.server.metadata.sender bounds mode work).IsQueryBoundP
      (fun query => kind query = 3) budget.accept := by
  have bill := RegistrationNativeExperimentProjection.compile_bound setup wire created bounds mode work budget bounded 3
  have unit : ∀ full : Fin 14, PqxdhDeploymentCompileSecrecy.wrapCost bounds (3 : Fin 12) full = if full = 3 then 1 else 0 := by
    intro full
    fin_cases full <;> simp [PqxdhDeploymentCompileSecrecy.wrapCost]
  simpa [unit, PqxdhDeploymentInterface.Budget.cap] using bill

/-- Every completed actual full native run satisfies the original public accept budget, without identifying parsed, successful and primitive callback ordinals. -/
theorem run_bound (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential mlSource)
    (bounds : FreshBounds) (mode : Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (budget : Budget) (bounded : RegistrationNativeInterface.Respects budget work)
    (before : State n KemSK mlSource) (result : Value × (RegistrationNativeLedger.State × State n KemSK mlSource))
    (supported : result ∈ support
      (RegistrationNativeExperiment.run setup checks wire route representation created mlSource credential bounds mode work before)) :
    result.2.2.parsedAccepts ≤ before.parsedAccepts + budget.accept := by
  rw [RegistrationNativeExperimentProjection.compile_run, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact program_bound setup checks wire route representation created credential _ budget.accept
    (compiled_accept_bill setup wire created bounds mode work budget bounded) before inner reached

end BeaconcryptCore.Computational.RegistrationNativeExperimentCounts

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeExperimentCounts.typed_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeExperimentCounts.typed_step
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeExperimentCounts.program_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeExperimentCounts.program_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeExperimentCounts.compiled_accept_bill' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeExperimentCounts.compiled_accept_bill
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeExperimentCounts.run_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeExperimentCounts.run_bound
