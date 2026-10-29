-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationAuthenticationExecutor
import BeaconcryptCore.Computational.MldsaSharedNative
import BeaconcryptCore.Refinement.ProtocolComposition

/-!
The extracted registration authentication controller is interpreted by the shared BLAKE2b random-oracle cache, an explicit ML-DSA verification primitive and the functional Ed25519 primitive. No boolean verification verdict, digest or poststate is supplied by a simulation hypothesis. Optional Ed outputs are represented only when their length fits the extracted slice type. This is the total-ROM source presentation; arbitrary native hash-allocation failures remain covered by the generic executor, rather than being silently identified with this specialization.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement

set_option autoImplicit false

namespace BeaconcryptCore.Computational.RegistrationAuthenticationShared

open CtxRomAuth
open BeaconcryptCore.Refinement.ProtocolComposition (concreteByte)
open BeaconcryptCore.Refinement.RegistrationInputs (hashBytes)
open BeaconcryptCore.Refinement.RegistrationAuthenticationFlow (Digest Opened)

def digestArray (digest : CtxDigest) : Digest :=
  ⟨digest.toList.map concreteByte, by simp⟩

theorem digest_array_bytes (digest : CtxDigest) : absBytes (digestArray digest) = digest.toList := by
  simp [digestArray, absBytes, List.map_map, Function.comp_def]

def openedBytes (reply : Option Pqxdh.Bytes) : Opened :=
  match reply with
  | none => .None
  | some bytes =>
    if fits : bytes.length ≤ Std.Usize.max then
      .Some ⟨bytes.map concreteByte, by simpa only [List.length_map] using fits⟩
    else .None

def verifyMldsa (verify : MldsaTranscriptAuth.Verify) (request : registration.MldsaVerificationRequest) : Bool :=
  verify (absBytes request.public_key) (absBytes request.context)
    (absBytes request.input) (absBytes request.signature)

def verifyEd25519 (crypto : Pqxdh.Crypto) (request : registration.Ed25519VerificationRequest) : Opened :=
  openedBytes (crypto.verify (absBytes request.public_key)
    (TranscriptAuthParts.absSlice request.signed))

/-- Actual hash request bytes are routed through the authentication branch of the shared record/authentication interface. -/
def callbacks (crypto : Pqxdh.Crypto) (verify : MldsaTranscriptAuth.Verify) :
    QueryImpl RegistrationAuthenticationExecutor.Spec (OracleComp MldsaSharedNative.Spec)
  | .hash request => do
      let digest ← MldsaSharedNative.authLift ((), hashBytes request)
      pure (.Some (digestArray digest))
  | .mldsa request => pure (verifyMldsa verify request)
  | .ed25519 request => pure (verifyEd25519 crypto request)

/-- The extracted controller and all record callbacks use one complete auxiliary/cache pair. -/
noncomputable def implementation {Auxiliary : Type} (crypto : Pqxdh.Crypto)
    (verify : MldsaTranscriptAuth.Verify) (writer : RawCtxMixedShared.Writer)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp)) :
    QueryImpl RegistrationAuthenticationExecutor.Spec
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp) :=
  MldsaSharedNative.primitives crypto writer kdf ∘ₛ callbacks crypto verify

private theorem map_state_apply {S X Y : Type} (mapResult : X → Y) (work : StateT S ProbComp X)
    (state : S) : (mapResult <$> work) state = Prod.map mapResult id <$> work state := by
  change (work state >>= fun result => pure (mapResult result.1, result.2)) = _
  simp only [bind_pure_comp]
  rfl

/-- The complete native hash reply and reached cache are those of the actual shared random oracle. -/
theorem hash_exact {Auxiliary : Type} (crypto : Pqxdh.Crypto) (verify : MldsaTranscriptAuth.Verify)
    (writer : RawCtxMixedShared.Writer)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp))
    (request : registration.HashRequest) (state : RawCtxSharedPrimitive.SharedState Auxiliary) :
    ((implementation crypto verify writer kdf (.hash request)).run state) =
      (fun result => (.Some (digestArray result.1), (state.1, result.2))) <$>
        (ctxRandomOracle ((), hashBytes request)).run state.2 := by
  simp only [implementation, QueryImpl.apply_compose, callbacks, MldsaSharedNative.authLift,
    bind_pure_comp, simulateQ_map, simulateQ_spec_query, MldsaSharedNative.primitives,
    StateT.run, map_state_apply, MldsaSharedNative.authentication, Functor.map_map]
  rfl

/-- Every supported extracted hash reply carries its actual shared-cache receipt and preserves unrelated primitive state. -/
theorem hash_reply_cached {Auxiliary : Type} (crypto : Pqxdh.Crypto) (verify : MldsaTranscriptAuth.Verify)
    (writer : RawCtxMixedShared.Writer)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp))
    (request : registration.HashRequest) (before after : RawCtxSharedPrimitive.SharedState Auxiliary)
    (reply : core.option.Option Digest)
    (supported : (reply, after) ∈ support
      ((implementation crypto verify writer kdf (.hash request)).run before)) :
    ∃ digest, reply = .Some (digestArray digest) ∧ after.1 = before.1 ∧
      before.2 ≤ after.2 ∧ after.2 ((), hashBytes request) = some digest := by
  rw [hash_exact, support_map] at supported
  obtain ⟨inner, member, same⟩ := supported
  have replySame : reply = .Some (digestArray inner.1) := (congrArg Prod.fst same).symm
  have afterSame : after = (before.1, inner.2) := (congrArg Prod.snd same).symm
  rw [replySame, afterSame]
  have cached := MldsaSharedAuthentication.query_cached (hashBytes request) before.2 inner member
  exact ⟨inner.1, rfl, rfl, cached.1, cached.2⟩

/-- The ML gate consumes all four actual extracted request operands and changes no primitive state. -/
theorem mldsa_exact {Auxiliary : Type} (crypto : Pqxdh.Crypto) (verify : MldsaTranscriptAuth.Verify)
    (writer : RawCtxMixedShared.Writer)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp))
    (request : registration.MldsaVerificationRequest) (state : RawCtxSharedPrimitive.SharedState Auxiliary) :
    ((implementation crypto verify writer kdf (.mldsa request)).run state) =
      pure (verify (absBytes request.public_key) (absBytes request.context)
        (absBytes request.input) (absBytes request.signature), state) := by
  rfl

/-- The attached-signature gate consumes the actual public key and complete signed bytes, retaining the primitive state. -/
theorem ed25519_exact {Auxiliary : Type} (crypto : Pqxdh.Crypto) (verify : MldsaTranscriptAuth.Verify)
    (writer : RawCtxMixedShared.Writer)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp))
    (request : registration.Ed25519VerificationRequest) (state : RawCtxSharedPrimitive.SharedState Auxiliary) :
    ((implementation crypto verify writer kdf (.ed25519 request)).run state) =
      pure (verifyEd25519 crypto request, state) := by
  rfl

noncomputable def begin {Auxiliary : Type} (crypto : Pqxdh.Crypto) (verify : MldsaTranscriptAuth.Verify)
    (writer : RawCtxMixedShared.Writer)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp))
    (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket) :=
  simulateQ (implementation crypto verify writer kdf) (RegistrationAuthenticationExecutor.begin pin packet)

/-- The entire extracted authentication program compiles into the common record/authentication interpreter, including every reached poststate. -/
theorem begin_shared {Auxiliary : Type} (crypto : Pqxdh.Crypto) (verify : MldsaTranscriptAuth.Verify)
    (writer : RawCtxMixedShared.Writer)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp))
    (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket)
    (state : RawCtxSharedPrimitive.SharedState Auxiliary) :
    (begin crypto verify writer kdf pin packet).run state =
      (simulateQ (MldsaSharedNative.primitives crypto writer kdf)
        (simulateQ (callbacks crypto verify) (RegistrationAuthenticationExecutor.begin pin packet))).run state := by
  rw [begin, implementation, QueryImpl.simulateQ_compose]

end BeaconcryptCore.Computational.RegistrationAuthenticationShared

/-- info: 'BeaconcryptCore.Computational.RegistrationAuthenticationShared.digest_array_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAuthenticationShared.digest_array_bytes

/-- info: 'BeaconcryptCore.Computational.RegistrationAuthenticationShared.hash_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAuthenticationShared.hash_exact

/-- info: 'BeaconcryptCore.Computational.RegistrationAuthenticationShared.hash_reply_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAuthenticationShared.hash_reply_cached

/-- info: 'BeaconcryptCore.Computational.RegistrationAuthenticationShared.mldsa_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAuthenticationShared.mldsa_exact

/-- info: 'BeaconcryptCore.Computational.RegistrationAuthenticationShared.ed25519_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAuthenticationShared.ed25519_exact

/-- info: 'BeaconcryptCore.Computational.RegistrationAuthenticationShared.begin_shared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAuthenticationShared.begin_shared
