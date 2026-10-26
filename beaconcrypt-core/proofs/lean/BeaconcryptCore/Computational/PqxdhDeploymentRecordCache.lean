-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentNative

/-! Record primitives answered through source14 (CE-3 item g). A compiled program computes record HKDF, AEAD sealing and opening and the frame writer locally with the real functions, and asks every BLAKE2b commitment through the source14 `hash` command. Run under the source14 native handler, this is exactly the native record execution on the shared BLAKE2b cache: the same cache entries are read and written, no other state changes, and no further uniform draw is made. Local HKDF and AEAD are real work, not free; they are not charged as queries. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhDeploymentRecordCache
open PqxdhServerAuthExperiment PqxdhJointIdentity
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result : Type}

/-- The source14 interface with explicit Beacon field reads. -/
abbrev SourceSpec (KemSK : Type) := PqxdhRegistrationJointRevealSchedule.Spec KemSK

/-- The public BLAKE2b command of source14. -/
def hashQuery (bytes : Pqxdh.Bytes) : OracleComp (SourceSpec KemSK) CtxRomAuth.CtxDigest :=
  ((SourceSpec KemSK).query (.inl (.inr (.hash bytes))) : OracleComp (SourceSpec KemSK) _)

/-- Local record primitives: real HKDF, real AEAD sealing and opening and the codec frame writer are computed locally; BLAKE2b is the source14 `hash` command. -/
noncomputable def localPrimitives (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) :
    QueryImpl RawCtxMixedOwner.NativeSpec (OracleComp (SourceSpec KemSK))
  | .inl request => pure (RawCtxSourceHkdf.response setup.source.crypto request)
  | .inr (.inl input) =>
      pure (some (setup.source.crypto.aeadSeal input.key input.nonce input.associatedData input.plaintext))
  | .inr (.inr (.inl input)) => pure (RawCtxSourceOpen.baseOpen setup.source.crypto input)
  | .inr (.inr (.inr (.inl bytes))) => (fun digest => some digest.toList) <$> hashQuery bytes
  | .inr (.inr (.inr (.inr frame))) => pure (codec.frameWrite frame)

/-- Replace the shared BLAKE2b cache of a native state. -/
def setCtx (state : PqxdhRegistrationSchedule.State KemSK) (cache : CtxRomAuth.CtxRO.QueryCache) :
    PqxdhRegistrationSchedule.State KemSK :=
  { state with shared := (state.shared.1, { state.shared.2 with ctx := cache }) }

/-- The native KDF primitive is the real HKDF response and keeps the shared state. -/
theorem primitives_kdf (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (request : beaconcrypt_core.ratchet.SymmetricRatchetKdfRequest) (shared : RawCtxSharedPrimitive.SharedState Unit) :
    (PqxdhDeploymentNative.primitives setup codec (.inl request)).run shared =
      pure (RawCtxSourceHkdf.response setup.source.crypto request, shared) := by
  rfl

/-- The native opening primitive is the real AEAD opening and keeps the shared state. -/
theorem primitives_open (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (input : RawCtxSourceOpen.BaseInput) (shared : RawCtxSharedPrimitive.SharedState Unit) :
    (PqxdhDeploymentNative.primitives setup codec (.inr (.inr (.inl input)))).run shared =
      pure (RawCtxSourceOpen.baseOpen setup.source.crypto input, shared) := by
  rfl

/-- One record primitive call through source14 is the native record primitive on the shared cache. -/
theorem local_query (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (serverSeed : IdentitySeed) (query : RawCtxMixedOwner.NativeSpec.Domain)
    (state : PqxdhRegistrationSchedule.State KemSK) :
    (simulateQ (PqxdhRegistrationJointRevealSchedule.native setup codec checks serverSeed)
      (localPrimitives setup codec query)).run state =
      (fun result => (result.1, setCtx state result.2.2)) <$>
        (PqxdhDeploymentNative.primitives setup codec query).run ((), state.shared.2.ctx) := by
  rcases query with request | input | input | bytes | frame
  · rw [primitives_kdf]
    simp only [localPrimitives, simulateQ_pure, StateT.run_pure, map_pure, setCtx]
  · rw [PqxdhDeploymentNative.primitives, RawCtxMixedShared.shared_sealing]
    simp only [localPrimitives, simulateQ_pure, StateT.run_pure, map_pure, setCtx]
  · rw [primitives_open]
    simp only [localPrimitives, simulateQ_pure, StateT.run_pure, map_pure, setCtx]
  · rw [PqxdhDeploymentNative.primitives, RawCtxMixedShared.shared_hash]
    simp only [localPrimitives, hashQuery, simulateQ_map, simulateQ_spec_query, StateT.run_map,
      PqxdhRegistrationJointRevealSchedule.native, PqxdhRegistrationSchedule.handler,
      PqxdhRegistrationSchedule.onShared_run, PqxdhServerAuthNative.nativeHash, Functor.map_map, setCtx,
      bind_pure_comp]
  · rw [PqxdhDeploymentNative.primitives, RawCtxMixedShared.shared_writing]
    simp only [localPrimitives, simulateQ_pure, StateT.run_pure, map_pure, setCtx]

/-- Replacing the cache twice keeps only the second cache. -/
theorem setCtx_setCtx (state : PqxdhRegistrationSchedule.State KemSK) (first second : CtxRomAuth.CtxRO.QueryCache) :
    setCtx (setCtx state first) second = setCtx state second := rfl

/-- The cache of a state with a replaced cache is the replacement. -/
theorem setCtx_ctx (state : PqxdhRegistrationSchedule.State KemSK) (cache : CtxRomAuth.CtxRO.QueryCache) :
    (setCtx state cache).shared.2.ctx = cache := rfl

/-- Item (g) of the compile lemma: an arbitrary record program with its primitives answered through source14 has exactly the native record execution, with the same result and the same complete native poststate. -/
theorem local_record (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (serverSeed : IdentitySeed) (work : OracleComp RawCtxMixedOwner.NativeSpec Result)
    (state : PqxdhRegistrationSchedule.State KemSK) :
    (simulateQ (PqxdhRegistrationJointRevealSchedule.native setup codec checks serverSeed)
      (simulateQ (localPrimitives setup codec) work)).run state =
      (PqxdhDeploymentNative.record setup codec work).run state := by
  rw [PqxdhDeploymentNative.record_run]
  induction work using OracleComp.inductionOn generalizing state with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        StateT.run_bind, local_query, bind_map_left, map_bind]
      apply bind_congr
      rintro ⟨reply, ⟨⟩, cache⟩
      rw [ih reply (setCtx state cache)]
      rfl

end BeaconcryptCore.Computational.PqxdhDeploymentRecordCache

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentRecordCache.primitives_kdf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentRecordCache.primitives_kdf

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentRecordCache.primitives_open' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentRecordCache.primitives_open

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentRecordCache.local_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentRecordCache.local_query

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentRecordCache.setCtx_setCtx' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentRecordCache.setCtx_setCtx

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentRecordCache.setCtx_ctx' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentRecordCache.setCtx_ctx

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentRecordCache.local_record' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentRecordCache.local_record
