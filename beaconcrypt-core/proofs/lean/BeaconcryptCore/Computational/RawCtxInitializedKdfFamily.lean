import BeaconcryptCore.Computational.RawCtxNativeKdfFamilyBounds
import BeaconcryptCore.Computational.RawCtxKdfRequestViews
import BeaconcryptCore.Refinement.PqxdhConcreteSession

/-!
Both actual extracted role initializers use the supplied root and source64 response, then share its exact prefix with the same complete76 stream used by ongoing/private/public calls. Full arbitrary adaptive continuation equality preserves actual kernel replies and the complete primitive state after erasing only the memo table. Every original initializer, including repeated roots, is counted once.

The interface and kernel replies are private protocol context. It does not install a new owner, resample an earlier root, add a public initial-kernel capability or prove input freshness. The source64-to-full76 projection can perform extra local tail computation; sampled full responses must charge the entire reservation. No native library/ABI/work equivalence, random public HKDF, snapshot/restore or global-security claim is added.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxInitializedKdfFamily
open PqxdhJointKdf PqxdhJointKdfGame RawCtxKdfRequestTable
open BeaconcryptCore.Refinement.PqxdhConcreteSession
open BeaconcryptCore.Computational.PqxdhInitialRatchetComplementarity

/-- The role chooses source orientation; the complete supplied root alone selects the stream. -/
abbrev InitialRequest := Bool × Std.Array Std.U8 32#usize
abbrev InitialOracle := InitialRequest →ₒ RustM ConcreteRatchetKernel
abbrev Spec := RawCtxServerServices.BackendSpec + InitialOracle

def initialReply (source : FixedHkdfSha512NoSaltSource) (request : InitialRequest) : RustM ConcreteRatchetKernel :=
  if request.1 then initializeBeacon request.2 (RawCtxSourceHkdf.initialResponse source.crypto)
  else initializeServer request.2 (RawCtxSourceHkdf.initialResponse source.crypto)

def initialProject (request : InitialRequest) (output : PqxdhFullSecretInputKdf.FullOutput) :
    RustM ConcreteRatchetKernel :=
  pqxdh.concrete.resume_initial_ratchet_kdf
    (if request.1 then beaconPending request.2 else serverPending request.2)
    (initialResponse output)

def compiler : QueryImpl Spec (OracleComp RawCtxNativeKdfFamily.FamilySpec)
  | .inl request => RawCtxNativeKdfFamily.compiler request
  | .inr request => initialProject request <$>
      RawCtxNativeKdfFamily.FamilySpec.query (.inr (address ⟨request.2, ratchet.SYM_RATCHET_INFO⟩))

noncomputable def sourceImpl {Auxiliary : Type} (source : FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) : QueryImpl Spec (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp)
  | .inl request => RawCtxProtocolBackend.backend source writer request
  | .inr request => pure (initialReply source request)

/-- The complete response executes the original extracted initializer at its supplied root. -/
theorem initial_projection (source : FixedHkdfSha512NoSaltSource) (request : InitialRequest) :
    initialProject request (productionStream source.crypto (address ⟨request.2, ratchet.SYM_RATCHET_INFO⟩)) =
      initialReply source request := by
  rcases request with ⟨role, root⟩
  cases role <;> simp [initialProject, initialReply, initializeBeacon_eq, initializeServer_eq,
    initialResponse_source]

/-- Both initialization and later source/public calls factor through the same complete-stream interpreter. -/
theorem compiler_real {Auxiliary : Type} (source : FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) :
    directImpl source (RawCtxProtocolBackend.backend (Auxiliary := Auxiliary) source writer) ∘ₛ compiler =
      sourceImpl source writer := by
  funext query
  cases query with
  | inl request => exact congrFun (RawCtxNativeKdfFamily.compiler_real source writer) request
  | inr request =>
      simp [QueryImpl.compose, compiler, directImpl, OracleSpec.query, sourceImpl, initial_projection]

/-- Arbitrary adaptive initialization/backend interleavings retain every kernel reply and the complete shared state. -/
theorem source_complete {Auxiliary Result : Type} (source : FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (client : OracleComp Spec Result)
    (state : RawCtxSharedPrimitive.SharedState Auxiliary) (table : Table)
    (consistent : Consistent source table) :
    (simulateQ (sourceImpl source writer) client).run state =
      (fun result => (result.1, result.2.1)) <$>
        (simulateQ (tableImpl source (RawCtxProtocolBackend.backend source writer))
          (simulateQ compiler client)).run (state, table) := by
  simpa only [← QueryImpl.simulateQ_compose, compiler_real] using
    table_complete source (RawCtxProtocolBackend.backend source writer)
      (simulateQ compiler client) state table consistent

def needsStream : Spec.Domain → Bool
  | .inl request => RawCtxNativeKdfFamilyBounds.needsStream request
  | .inr _ => true

/-- Every initializer is charged once, including repeated roots and the unused 76-byte tail reservation. -/
theorem compiler_step (query : Spec.Domain) :
    (compiler query).IsQueryBoundP (fun query => query.isRight = true) (if needsStream query then 1 else 0) := by
  cases query with
  | inl request => exact RawCtxNativeKdfFamilyBounds.compiler_step request
  | inr request =>
      simp [compiler, needsStream, isQueryBoundP_map_iff]
      exact (isQueryBoundP_query_iff (spec := RawCtxNativeKdfFamily.FamilySpec)
        (p := fun query => query.isRight = true) _ _).2 (by simp)

/-- The same stream budget counts original initializers together with all private and public derivations. -/
theorem compiler_bound {Result : Type} (client : OracleComp Spec Result) (budget : Nat)
    (bounded : client.IsQueryBoundP (fun query => needsStream query = true) budget) :
    (simulateQ compiler client).IsQueryBoundP (fun query => query.isRight = true) budget := by
  exact RawCtxSourceOpen.simulate_bound compiler _ _ client budget bounded compiler_step

end BeaconcryptCore.Computational.RawCtxInitializedKdfFamily

/-- info: 'BeaconcryptCore.Computational.RawCtxInitializedKdfFamily.initial_projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInitializedKdfFamily.initial_projection

/-- info: 'BeaconcryptCore.Computational.RawCtxInitializedKdfFamily.compiler_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInitializedKdfFamily.compiler_real

/-- info: 'BeaconcryptCore.Computational.RawCtxInitializedKdfFamily.source_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInitializedKdfFamily.source_complete

/-- info: 'BeaconcryptCore.Computational.RawCtxInitializedKdfFamily.compiler_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInitializedKdfFamily.compiler_step

/-- info: 'BeaconcryptCore.Computational.RawCtxInitializedKdfFamily.compiler_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInitializedKdfFamily.compiler_bound
