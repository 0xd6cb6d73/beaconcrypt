import BeaconcryptCore.Computational.RawCtxServerMixed
import BeaconcryptCore.Computational.PqxdhJointKdfGame

/-!
Explicit client randomness, public BLAKE2b commitment queries and real fixed-HKDF projections accompany the same source Server operations. Public HKDF calls evaluate the source function; they do not read or allocate a random HKDF table. Honest private primitive draws remain within the backend interpreter. These operations preserve the Server map while retaining actual shared-cache effects.

The shared presentation uses the existing total functional AEAD, total CTX ROM and optional functional writer contracts. Its KDF callback is still arbitrary here; consistency with the same fixed source needs the separately checked concrete callback instantiation. Seven complete-state equations supply no key-independence, reveal/freshness, arbitrary-registration or global-security conclusion. The raw API returns actual optional plaintext; the enclosing network observation must account for declassification.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxServerServices
open RawCtxServerRouting PqxdhJointKdfGame

abbrev PublicSpec := unifSpec + (RawCtxMixedOwner.HashSpec + JointKdfViewSpec)
abbrev SourceSpec := RawCtxServerMixed.SourceSpec + PublicSpec
abbrev BackendSpec := unifSpec + (RawCtxMixedOwner.NativeSpec + JointKdfViewSpec)

def nativeLift : QueryImpl RawCtxMixedOwner.NativeSpec (OracleComp BackendSpec) :=
  fun query => BackendSpec.query (.inr (.inl query))

def publicLift : QueryImpl PublicSpec (OracleComp BackendSpec)
  | .inl coin => BackendSpec.query (.inl coin)
  | .inr (.inl bytes) => BackendSpec.query (.inr (.inl (.inr (.inr (.inr (.inl bytes))))))
  | .inr (.inr query) => BackendSpec.query (.inr (.inr query))

noncomputable def serverImpl {Metadata PeerMetadata : Type} (senderId : Metadata → Std.U64)
    (route : SenderDecoder) (decode : RawCtxReceive.FrameDecoder) :
    QueryImpl SourceSpec (StateT (State Metadata PeerMetadata) (OracleComp BackendSpec)) :=
  fun query state => match query with
  | .inl request => simulateQ nativeLift ((RawCtxServerMixed.serverImpl senderId route decode request).run state)
  | .inr request => do
      let result ← publicLift request
      pure (result, state)

noncomputable def backendImpl {Auxiliary : Type} (source : FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp)) :
    QueryImpl BackendSpec (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp) :=
  fun query state => match query with
  | .inl coin => do
      let result ← unifSpec.query coin
      pure (result, state)
  | .inr (.inl request) => (RawCtxMixedShared.sharedImpl source.crypto writer kdf request).run state
  | .inr (.inr query) => pure (query.project (PqxdhJointKdf.productionStream source.crypto query.address), state)

/-- Public and private commitment invocations are the same query at the same shared backend. -/
theorem same_hash (bytes : Pqxdh.Bytes) :
    publicLift (.inr (.inl bytes)) =
      nativeLift (.inr (.inr (.inr (.inl bytes)))) := by
  rfl

/-- Native source operations use the unchanged shared-cache interpreter. -/
theorem native_interpretation {Auxiliary : Type} (source : FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp)) :
    backendImpl source writer kdf ∘ₛ nativeLift = RawCtxMixedShared.sharedImpl source.crypto writer kdf := by
  funext query state
  simp [QueryImpl.compose, nativeLift, backendImpl, OracleSpec.query, StateT.run]

/-- Public projections evaluate the same fixed source and leave all private/cache state intact. -/
theorem public_hkdf {Auxiliary : Type} (source : FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp))
    (query : JointKdfViewQuery) (state : RawCtxSharedPrimitive.SharedState Auxiliary) :
    (((backendImpl source writer kdf ∘ₛ publicLift) (.inr (.inr query))).run state) =
      pure (query.project (PqxdhJointKdf.productionStream source.crypto query.address), state) := by
  simp [QueryImpl.compose, publicLift, backendImpl, OracleSpec.query, StateT.run]

/-- Public BLAKE2b calls read and extend the identical cache used by private commitments. -/
theorem public_hash {Auxiliary : Type} (source : FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp))
    (bytes : Pqxdh.Bytes) (state : RawCtxSharedPrimitive.SharedState Auxiliary) :
    (((backendImpl source writer kdf ∘ₛ publicLift) (.inr (.inl bytes))).run state) = (do
      let result ← (CtxRomAuth.ctxRandomOracle ((), bytes)).run state.2
      pure (some result.1.toList, (state.1, result.2))) := by
  simpa [QueryImpl.compose, publicLift, backendImpl, OracleSpec.query, StateT.run] using
    RawCtxMixedShared.shared_hash source.crypto writer kdf bytes state

/-- The caller receives its actual uniform answer; this channel reveals no private primitive draw. -/
theorem public_coin {Auxiliary : Type} (source : FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp))
    (coin : unifSpec.Domain) (state : RawCtxSharedPrimitive.SharedState Auxiliary) :
    (((backendImpl source writer kdf ∘ₛ publicLift) (.inl coin)).run state) = (do
      let result ← unifSpec.query coin
      pure (result, state)) := by
  simp [QueryImpl.compose, publicLift, backendImpl, OracleSpec.query, StateT.run]

noncomputable def sourceImpl {Metadata PeerMetadata Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp))
    (senderId : Metadata → Std.U64) (route : SenderDecoder) (decode : RawCtxReceive.FrameDecoder) :
    QueryImpl SourceSpec
      (StateT (State Metadata PeerMetadata × RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp) :=
  fun query state => match query with
  | .inl request => (RawCtxServerMixed.sourceImpl (RawCtxMixedShared.sharedImpl source.crypto writer kdf)
      senderId route decode request).run state
  | .inr request => do
      let result ← (((backendImpl source writer kdf ∘ₛ publicLift) request).run state.2)
      pure (result.1, (state.1, result.2))

/-- The complete source interpreter retains actual Server operations and all public-service effects in one state. -/
theorem server_interpretation {Metadata PeerMetadata Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp))
    (senderId : Metadata → Std.U64) (route : SenderDecoder) (decode : RawCtxReceive.FrameDecoder) :
    ((backendImpl source writer kdf).mapStateTBase
      (serverImpl (PeerMetadata := PeerMetadata) senderId route decode)).flattenStateT =
      sourceImpl source writer kdf senderId route decode := by
  funext query state
  cases query <;> simp only [QueryImpl.flattenStateT, QueryImpl.mapStateTBase, serverImpl, sourceImpl, StateT.run, StateT.mk]
  case inl request =>
    rw [← QueryImpl.simulateQ_compose, native_interpretation]
    exact congrFun (congrFun (RawCtxServerMixed.server_interpretation
      (RawCtxMixedShared.sharedImpl source.crypto writer kdf) senderId route decode) request) state
  case inr request =>
    simp only [QueryImpl.compose, bind_pure_comp, simulateQ_map]
    change (fun x => (x.1.1, x.1.2, x.2)) <$>
      (((fun a => (a, state.1)) <$> simulateQ (backendImpl source writer kdf) (publicLift request)).run state.2) = _
    rw [StateT.run_map]
    simp only [Functor.map_map, StateT.run]

/-- Arbitrary adaptive source/public interleaving preserves the original result and both complete private states. -/
theorem schedule_interpretation {Metadata PeerMetadata Auxiliary Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp))
    (senderId : Metadata → Std.U64) (route : SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp SourceSpec Result) (state : State Metadata PeerMetadata)
    (primitive : RawCtxSharedPrimitive.SharedState Auxiliary) :
    (simulateQ (backendImpl source writer kdf)
      ((simulateQ (serverImpl senderId route decode) client).run state)).run primitive =
      (fun result => ((result.1, result.2.1), result.2.2)) <$>
        (simulateQ (sourceImpl source writer kdf senderId route decode) client).run (state, primitive) := by
  rw [simulateQ_mapStateTBase_run_eq_map_flattenStateT, server_interpretation]

end BeaconcryptCore.Computational.RawCtxServerServices

/-- info: 'BeaconcryptCore.Computational.RawCtxServerServices.same_hash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxServerServices.same_hash

/-- info: 'BeaconcryptCore.Computational.RawCtxServerServices.native_interpretation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxServerServices.native_interpretation

/-- info: 'BeaconcryptCore.Computational.RawCtxServerServices.public_hkdf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxServerServices.public_hkdf

/-- info: 'BeaconcryptCore.Computational.RawCtxServerServices.public_hash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxServerServices.public_hash

/-- info: 'BeaconcryptCore.Computational.RawCtxServerServices.public_coin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxServerServices.public_coin

/-- info: 'BeaconcryptCore.Computational.RawCtxServerServices.server_interpretation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxServerServices.server_interpretation

/-- info: 'BeaconcryptCore.Computational.RawCtxServerServices.schedule_interpretation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxServerServices.schedule_interpretation
