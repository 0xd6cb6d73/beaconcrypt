import BeaconcryptCore.Computational.RawCtxServerServiceBounds
import BeaconcryptCore.Computational.RawCtxSourceHkdf

/-!
The concrete record backend uses one fixed HKDF-SHA-512/no-salt source for private derivations and real public projections. The same CTX commitment cache and auxiliary state serve public queries and both native record directions. Four statements identify this source callback, complete Server interpretation and its actual uniform-call ledger. No arbitrary private KDF parameter remains in this backend.

These are functional source and resource statements, not key-independence or security reductions. Native primitive/codec/map/slot representations and total functional AEAD/CTX ROM contracts remain explicit. Existing native KDF/seal/open/hash/writer caps and public HKDF counts retain real local primitive work. Full state in the equations is private analysis state; API plaintext needs a network declassification/freshness policy. Registration, identity generation, reveals, persistence and global cryptographic composition remain separate.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxProtocolBackend
open RawCtxServerRouting PqxdhJointKdfGame

noncomputable def backend {Auxiliary : Type} (source : FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) :
    QueryImpl RawCtxServerServices.BackendSpec
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp) :=
  RawCtxServerServices.backendImpl source writer (RawCtxSourceHkdf.kdfImpl source)

/-- Private ongoing derivation uses the same complete fixed source stream as public projections. -/
theorem private_hkdf {Auxiliary : Type} (source : FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (request : beaconcrypt_core.ratchet.SymmetricRatchetKdfRequest)
    (state : RawCtxSharedPrimitive.SharedState Auxiliary) :
    (backend source writer (.inr (.inl (.inl request)))).run state =
      pure (RawCtxSourceHkdf.response source.crypto request, state) := by
  rfl

/-- Public fixed-HKDF calls remain the exact same source function and preserve all private/cache state. -/
theorem public_hkdf {Auxiliary : Type} (source : FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (query : JointKdfViewQuery)
    (state : RawCtxSharedPrimitive.SharedState Auxiliary) :
    (((backend source writer ∘ₛ RawCtxServerServices.publicLift)
      (.inr (.inr query))).run state) =
      pure (query.project (PqxdhJointKdf.productionStream source.crypto query.address), state) := by
  exact RawCtxServerServices.public_hkdf source writer (RawCtxSourceHkdf.kdfImpl source) query state

noncomputable def serverSource {Metadata PeerMetadata Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (senderId : Metadata → Std.U64) (route : SenderDecoder) (decode : RawCtxReceive.FrameDecoder) :
    QueryImpl RawCtxServerServices.SourceSpec
      (StateT (State Metadata PeerMetadata × RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp) :=
  RawCtxServerServices.sourceImpl source writer (RawCtxSourceHkdf.kdfImpl source) senderId route decode

/-- One fixed source interprets the entire adaptive Server/public computation and retains both complete private states. -/
theorem server_schedule {Metadata PeerMetadata Auxiliary Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (senderId : Metadata → Std.U64) (route : SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp RawCtxServerServices.SourceSpec Result) (state : State Metadata PeerMetadata)
    (primitive : RawCtxSharedPrimitive.SharedState Auxiliary) :
    (simulateQ (backend source writer)
      ((simulateQ (RawCtxServerServices.serverImpl senderId route decode) client).run state)).run primitive =
      (fun result => ((result.1, result.2.1), result.2.2)) <$>
        (simulateQ (serverSource source writer senderId route decode) client).run (state, primitive) := by
  exact RawCtxServerServices.schedule_interpretation source writer (RawCtxSourceHkdf.kdfImpl source)
    senderId route decode client state primitive

/-- All caller coins and every private/public commitment miss are counted with the actual deterministic HKDF callback. -/
theorem server_uniform {Metadata PeerMetadata Auxiliary Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (senderId : Metadata → Std.U64) (route : SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp RawCtxServerServices.SourceSpec Result)
    (budget : RawCtxServerServiceBounds.Budget)
    (bounded : RawCtxServerServiceBounds.Bounded client budget)
    (state : State Metadata PeerMetadata × RawCtxSharedPrimitive.SharedState Auxiliary) :
    ((simulateQ (serverSource source writer senderId route decode) client).run state).IsTotalQueryBound
      (budget .coin + 64 * (budget .send + budget .raw + budget .hash)) := by
  simpa only [Nat.zero_mul, Nat.add_zero, serverSource] using
    RawCtxServerServiceBounds.schedule_uniform source writer (RawCtxSourceHkdf.kdfImpl source) 0
      (RawCtxSourceHkdf.kdf_uniform source) senderId route decode client budget bounded state

end BeaconcryptCore.Computational.RawCtxProtocolBackend

/-- info: 'BeaconcryptCore.Computational.RawCtxProtocolBackend.private_hkdf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxProtocolBackend.private_hkdf

/-- info: 'BeaconcryptCore.Computational.RawCtxProtocolBackend.public_hkdf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxProtocolBackend.public_hkdf

/-- info: 'BeaconcryptCore.Computational.RawCtxProtocolBackend.server_schedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxProtocolBackend.server_schedule

/-- info: 'BeaconcryptCore.Computational.RawCtxProtocolBackend.server_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxProtocolBackend.server_uniform
