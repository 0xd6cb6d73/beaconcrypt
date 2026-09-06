import BeaconcryptCore.Computational.RawCtxCanonicalSeal
import BeaconcryptCore.Refinement.ProtocolComposition
import BeaconcryptCore.Computational.PqxdhJointKdfGame

/-!
This module supplies exact fixed-width extracted responses from the already selected functional HKDF-SHA-512/no-salt source. The ongoing response retains all 76 bytes at the actual requested input and info; initialization uses 64 bytes and root derivation uses 32 bytes. Existing byte-representation laws are derived by exact conversions rather than assumed for these constructed interpreters. The source prefix contract identifies initialization and public root projections with the same complete functional stream. No independent key/nonce/chain sampler or HKDF random table is introduced.

The private KDF callback preserves the whole auxiliary state and CTX commitment cache, and arbitrary KDF continuations retain that complete state. HKDF-SHA-512 and BLAKE2b commitments are distinct algorithms; sharing primitive state does not route HMAC-SHA-512 calls into the BLAKE2b table. This deterministic functional KDF callback makes zero uniform queries, so its mixed source instantiation has uniform cap 64*(qSend+qRaw). Actual HKDF/HMAC, conversion, byte, logging and library work remain real local work. The preceding source caps still count qSend+51*qRaw KDF callbacks.

These thirteen statements instantiate a supplied functional source and its existing prefix contract. They do not prove libsodium, compiler/ABI correspondence, native errors/length limits or allocation/timing behavior. In particular, constructing response arrays from source.crypto.hkdf is not an independent equality to unmodeled native library execution. The exact native legal-input primitive contract remains explicit. The fixed source function is retained across all calls; no security assumption is strengthened, no uniform/independent output property follows, and the global adaptive multi-owner/reveal/freshness proof remains separate. The initial/root representation laws do not imply completed registration or initializer distribution correctness.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
open PqxdhRefinement BeaconcryptCore.Refinement.RepresentationBridge
open BeaconcryptCore.Refinement.ProtocolComposition
set_option autoImplicit false

namespace BeaconcryptCore.Computational.RawCtxSourceHkdf
open PqxdhJointKdf PqxdhJointKdfGame

/-- Convert the existing functional primitive's actual bytes to the fixed source response array. -/
def response (c : Pqxdh.Crypto) (request : SymmetricRatchetKdfRequest) : RatchetKdfResponse :=
  ⟨⟨(c.hkdf (absBytes request.input) (absBytes request.info) 76).map concreteByte,
    by simp [c.hkdf_length]⟩⟩

/-- The response retains the requested input, requested label and all 76 actual HKDF bytes. -/
theorem response_bytes (c : Pqxdh.Crypto) (request : SymmetricRatchetKdfRequest) :
    absBytes (response c request).bytes =
      c.hkdf (absBytes request.input) (absBytes request.info) 76 := by
  simp [response, absBytes, List.map_map, Function.comp_def]

/-- The actual fixed source label discharges the existing ongoing-ratchet functional boundary. -/
theorem response_law (c : Pqxdh.Crypto) : KdfLaw c (response c) := by
  intro chain
  rw [response_bytes]
  have info : absBytes ratchet.SYM_RATCHET_INFO = Pqxdh.INFO_R := by
    simpa only [pqxdh.SYM_RATCHET_INFO] using absBytes_SYM_RATCHET_INFO
  rw [info]
  rfl

/-- Every selected chain/key/nonce is a projection of the same complete source response. -/
theorem response_projections (c : Pqxdh.Crypto) (chain : RatchetChain) :
    absChain (interpretedStep (response c) chain).chain = Pqxdh.nextChain c (absChain chain) ∧
      absMaterial (interpretedStep (response c) chain).material = Pqxdh.msgMaterial c (absChain chain) := by
  have parts := interpretedStep_bytes (response c) chain
  have actual := response_law c chain
  simpa only [interpretedResponse, actual, Pqxdh.nextChain, Pqxdh.msgMaterial, Pqxdh.ratchetOut]
    using parts

/-- Private source KDF and public complete-stream queries identify the same exact input and label. -/
theorem response_stream (source : FixedHkdfSha512NoSaltSource) (request : SymmetricRatchetKdfRequest) :
    absBytes (response source.crypto request).bytes =
      streamBytes (productionStream source.crypto ⟨absBytes request.info, absBytes request.input⟩) := by
  rw [response_bytes]
  rfl

/-- The initial source response uses the same function at its actual 64-byte output width. -/
def initialResponse (c : Pqxdh.Crypto) (request : SymmetricRatchetKdfRequest) :
    pqxdh.concrete.InitialRatchetKdfResponse :=
  ⟨⟨(c.hkdf (absBytes request.input) (absBytes request.info) 64).map concreteByte,
    by simp [c.hkdf_length]⟩⟩

/-- The 64-byte initialization adapter retains the whole requested HKDF output. -/
theorem initialResponse_bytes (c : Pqxdh.Crypto) (request : SymmetricRatchetKdfRequest) :
    absBytes (initialResponse c request).bytes =
      c.hkdf (absBytes request.input) (absBytes request.info) 64 := by
  simp [initialResponse, absBytes, List.map_map, Function.comp_def]

/-- The exact initial-response law is derived from the same supplied source function. -/
theorem initialResponse_law (c : Pqxdh.Crypto) : InitialKdfLaw c (initialResponse c) := by
  intro root
  rw [initialResponse_bytes]
  have info : absBytes ratchet.SYM_RATCHET_INFO = Pqxdh.INFO_R := by
    simpa only [pqxdh.SYM_RATCHET_INFO] using absBytes_SYM_RATCHET_INFO
  rw [info]

/-- Source initial and ongoing calls keep the ordinary same-stream prefix correlation; no independent key material is sampled. -/
theorem initialResponse_prefix (source : FixedHkdfSha512NoSaltSource)
    (input : Std.Array Std.U8 32#usize) :
    absBytes (initialResponse source.crypto ⟨input, ratchet.SYM_RATCHET_INFO⟩).bytes =
      (absBytes (response source.crypto ⟨input, ratchet.SYM_RATCHET_INFO⟩).bytes).take 64 := by
  rw [initialResponse_bytes, response_bytes]
  have info : absBytes ratchet.SYM_RATCHET_INFO = Pqxdh.INFO_R := by
    simpa only [pqxdh.SYM_RATCHET_INFO] using absBytes_SYM_RATCHET_INFO
  simpa only [info] using source.prefixConsistent.ratchetPrefix (absBytes input)

/-- The root wrapper uses the same fixed functional source at the actual validated 192-byte input. -/
def rootResponse (c : Pqxdh.Crypto) (input : pqxdh.RootKeyInput) : Std.Array Std.U8 32#usize :=
  ⟨(c.hkdf (absBytes input.bytes) Pqxdh.INFO_PQ 32).map concreteByte,
    by simp [c.hkdf_length]⟩

/-- Exact source bytes discharge the existing root-response representation law. -/
theorem rootResponse_law (c : Pqxdh.Crypto) : RootKdfLaw c (rootResponse c) := by
  intro input
  simp [rootResponse, absBytes, List.map_map, Function.comp_def, Pqxdh.rootSecret]

/-- The root response and public root projection use the same source stream and existing functional prefix law. -/
theorem rootResponse_stream (source : FixedHkdfSha512NoSaltSource) (input : pqxdh.RootKeyInput) :
    absBytes (rootResponse source.crypto input) =
      rootProjection (productionStream source.crypto (rootAddress (absBytes input.bytes))) := by
  rw [rootResponse_law]
  exact rootSecret_eq_rootProjection source.crypto source.prefixConsistent _

/-- This source HKDF callback is deterministic and leaves the entire separate CTX cache and auxiliary state unchanged. -/
def kdfImpl {Auxiliary : Type} (source : FixedHkdfSha512NoSaltSource) :
    QueryImpl RawCtxSharedPrimitive.KdfSpec
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp) :=
  fun request => pure (response source.crypto request)

/-- The handler returns the real functional response and exactly preserves the supplied primitive state. -/
theorem kdf_step {Auxiliary : Type} (source : FixedHkdfSha512NoSaltSource)
    (request : SymmetricRatchetKdfRequest) (state : RawCtxSharedPrimitive.SharedState Auxiliary) :
    (kdfImpl source request).run state = pure (response source.crypto request, state) := by
  rfl

/-- Zero uniform queries means deterministic primitive work, not zero HKDF computation. -/
theorem kdf_uniform {Auxiliary : Type} (source : FixedHkdfSha512NoSaltSource)
    (request : SymmetricRatchetKdfRequest) (state : RawCtxSharedPrimitive.SharedState Auxiliary) :
    ((kdfImpl source request).run state).IsTotalQueryBound 0 := by
  trivial

/-- Arbitrary repeated KDF work preserves the same full CTX cache; no independent stream table is substituted. -/
theorem kdf_complete {Auxiliary Result : Type} (source : FixedHkdfSha512NoSaltSource)
    (client : OracleComp RawCtxSharedPrimitive.KdfSpec Result)
    (state : RawCtxSharedPrimitive.SharedState Auxiliary) :
    (simulateQ (kdfImpl source) client).run state =
      (fun result => (result, state)) <$>
        simulateQ (fun request => (pure (response source.crypto request) : ProbComp _)) client := by
  induction client using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, kdf_step, pure_bind,
        ih]

/-- Actual mixed execution uses this same HKDF source and the existing CTX table; only commitment misses draw uniform bytes. -/
theorem mixed_uniform {Metadata Auxiliary Result : Type} (source : FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp RawCtxMixedOwner.SourceSpec Result) (qSend qRaw : Nat)
    (hSend : client.IsQueryBoundP (fun query => query.isLeft = true) qSend)
    (hRaw : client.IsQueryBoundP (fun query => query.isRight = true) qRaw)
    (owner : RawCtxWholeOwner.OwnerState Metadata) (primitive : RawCtxSharedPrimitive.SharedState Auxiliary) :
    (RawCtxMixedShared.sharedSchedule source.crypto writer (kdfImpl source) sender decode
      client owner primitive).IsTotalQueryBound (64 * (qSend + qRaw)) := by
  simpa only [Nat.zero_mul, Nat.zero_add] using
    RawCtxMixedShared.shared_schedule_uniform source.crypto writer (kdfImpl source) 0
      (kdf_uniform source) sender decode client owner primitive qSend qRaw hSend hRaw

end BeaconcryptCore.Computational.RawCtxSourceHkdf

/--
info: 'BeaconcryptCore.Computational.RawCtxSourceHkdf.response_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceHkdf.response_bytes

/--
info: 'BeaconcryptCore.Computational.RawCtxSourceHkdf.response_law' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceHkdf.response_law

/--
info: 'BeaconcryptCore.Computational.RawCtxSourceHkdf.response_projections' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceHkdf.response_projections

/--
info: 'BeaconcryptCore.Computational.RawCtxSourceHkdf.response_stream' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceHkdf.response_stream

/--
info: 'BeaconcryptCore.Computational.RawCtxSourceHkdf.initialResponse_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceHkdf.initialResponse_bytes

/--
info: 'BeaconcryptCore.Computational.RawCtxSourceHkdf.initialResponse_law' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceHkdf.initialResponse_law

/--
info: 'BeaconcryptCore.Computational.RawCtxSourceHkdf.initialResponse_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceHkdf.initialResponse_prefix

/--
info: 'BeaconcryptCore.Computational.RawCtxSourceHkdf.rootResponse_law' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceHkdf.rootResponse_law

/--
info: 'BeaconcryptCore.Computational.RawCtxSourceHkdf.rootResponse_stream' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceHkdf.rootResponse_stream

/--
info: 'BeaconcryptCore.Computational.RawCtxSourceHkdf.kdf_step' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceHkdf.kdf_step

/--
info: 'BeaconcryptCore.Computational.RawCtxSourceHkdf.kdf_uniform' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceHkdf.kdf_uniform

/--
info: 'BeaconcryptCore.Computational.RawCtxSourceHkdf.kdf_complete' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceHkdf.kdf_complete

/--
info: 'BeaconcryptCore.Computational.RawCtxSourceHkdf.mixed_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceHkdf.mixed_uniform
