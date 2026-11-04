-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicBundleBody
import BeaconcryptCore.Refinement.AdapterPublicWrapperState
import BeaconcryptCore.Computational.RegistrationNativeSourceEncoders
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
/-! The actual public Server response builder factors through original completion, first-record, signing, writer and container callbacks. Failed allocation, mutable transcript poststates, failed serialization and entry lenses remain explicit; no completed wrapper behavior is supplied as a primitive law. -/
namespace BeaconcryptCore.Refinement.AdapterPublicServerBuildBody
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterRecordRequestMonad (LiftRust liftRust)
open AdapterPublicWrapperLiftFunction (LiftFunction call)
universe u v w
private theorem call_apply {m : Type → Type} {A : Type u} {F : A → Type v} {G : A → Type w}
    [∀ a, LiftFunction m (F a) (G a)] (source : (a : A) → F a) (arg : A) :
    call (m := m) source arg = call (m := m) (source arg) := rfl
private theorem lift_ok {m : Type → Type} [Monad m] {A : Type} (value : A) :
    (liftRust (.ok value) : RustT m A) = pure value := rfl
private theorem call_result {m : Type → Type} [LiftRust m] {A : Type} (source : RustM A) :
    call (m := m) source = liftRust source := rfl
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [primitive : AdapterInitEdPrimitive.Operations] [PublicWrapperPlatform.Allocator]
variable [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable {m : Type → Type} [Monad m] [LawfulMonad m]
variable [localOps : LocalOperations (RustT m)] [crypto : CryptoOperations (RustT m)]
variable [containers : ContainerOperations (RustT m)] [codec : Codecs (RustT m)]
variable [children : ChildOperations (RustT m)]

abbrev Server := beaconcrypt_public_wrapper.server.Server
abbrev Reply := core.option.Option beaconcrypt_public_wrapper.server.RegResponse × Server

omit localOps crypto containers codec children in
def checked {A Error : Type} (self : Server) (work : RustM (core.result.Result A Error))
    (next : A → RustT m Reply) : RustT m Reply := do
  let result ← liftRust work
  match result with
  | .Err _ => pure (.None, self)
  | .Ok value => next value

omit localOps crypto containers codec children in
def finish (self : Server) (completion : peer.PublicationFinish (alloc.vec.Vec U8)) (inserted : Bool) :
    RustT m Reply :=
  checked self (completion.finish inserted) fun published => do
    let (control, identifier, bytes) ← liftRust published.into_parts
    pure (.Some ⟨bytes, identifier⟩, { self with control := control })

noncomputable def install (self : Server) (pending : peer.PeerInsert (alloc.vec.Vec U8)) : RustT m Reply := do
  let identifier ← liftRust pending.request
  let (remote, completion) ← liftRust pending.into_parts
  let binding ← liftRust (PublicWrapperPlatform.peerBinding remote)
  let identity ← liftRust (PublicWrapperPlatform.beaconIdentity binding)
  checked self (beaconcrypt_crypto.crypto_sign.PublicKey.from_bytes identity.to_slice) fun publicKey => do
    let (entry, back) ← containers.mapEntry core.U64.Insts.CoreCmpEq core.U64.Insts.CoreHashHash
      beaconcrypt_public_request.collections.KeyedHasher.Insts.CoreHashBuildHasherSipHasher13
      hashbrown.alloc.inner.Global.Insts.HashbrownAllocInnerAllocator self.known_ids identifier
    match entry with
    | .Occupied _ => finish { self with known_ids := back entry } completion false
    | .Vacant vacant =>
      let stored ← beaconcrypt_public_request.shared.EstablishedRemote.from_peer
        beaconcrypt_public_request.beaconcrypt_crypto.crypto_sign.PublicKey.Insts.BeaconcryptSharedSignaturePk publicKey remote
      let (changed, insertedBack) ← containers.vacantInsert hashbrown.alloc.inner.Global.Insts.HashbrownAllocInnerAllocator
        core.U64.Insts.CoreHashHash
        beaconcrypt_public_request.collections.KeyedHasher.Insts.CoreHashBuildHasherSipHasher13 vacant stored
      finish { self with known_ids := back (.Vacant (insertedBack changed)) } completion true

noncomputable def publish (self : Server) (ready : registration.ServerResponseReady) : RustT m Reply := do
  let message ← liftRust ready.message
  let buffer ← children.encodeResponse (BeaconcryptCore.Computational.RegistrationNativeSourceEncoders.responseSyntax message)
  checked self (ready.publish buffer) fun published =>
    checked self (peer.begin_peer_insert self.control published) (install self)

noncomputable def sign (self : Server) (pending : registration.ServerResponseHash) : RustT m Reply := do
  let request ← liftRust pending.request
  let hash ← children.executeHash request
  checked self (pending.resume hash) fun signing => do
    let identity ← liftRust (alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref self.identity)
    let request ← liftRust signing.request
    let signature ← localOps.auth_MldsaIdentity_sign_requested identity.mldsa_identity request
    let signatureView ← liftRust (core.option.Option.as_deref (alloc.vec.Vec.Insts.CoreOpsDerefDerefSlice U8) signature)
    checked self (signing.resume signatureView) (publish self)

noncomputable def write (self : Server) (pending : registration.ServerRecordWrite) : RustT m Reply := do
  let request ← liftRust pending.request
  let ciphertext ← localOps.ratchet_execute_write_request request
  let ciphertextView ← liftRust (core.option.Option.as_deref (alloc.vec.Vec.Insts.CoreOpsDerefDerefSlice U8) ciphertext)
  checked self (pending.resume ciphertextView) (sign self)

noncomputable def commit (self : Server) (pending : registration.ServerRecordCommitment) : RustT m Reply := do
  let (transcript, back) ← liftRust pending.transcript_mut
  let (digest, updated) ← children.commitmentHash transcript
  checked self ((back updated).resume digest) (write self)

noncomputable def sealRecord (self : Server) (pending : registration.ServerRecordAead) : RustT m Reply := do
  let request ← liftRust pending.request
  let detached ← localOps.ratchet_execute_seal_request request
  let view ← liftRust (core.option.Option.as_ref detached)
  let borrowed ← AdapterPublicWrapperRequestMonad.Option.map
    beaconcrypt_public_request.server.ProviderServerServer.build_registration_response.closure.Insts.CoreOpsFunctionFnOnceTupleSharedPairVecU8ArrayU816PairSharedSliceU8ArrayU816 view ()
  checked self (pending.resume borrowed) (commit self)

noncomputable def record (self : Server) (pending : registration.ServerInitialKdf) : RustT m Reply := do
  let request ← liftRust pending.request
  let bytes ← localOps.ratchet_initial_ratchet_hkdf request
  let response ← liftRust (pqxdh.concrete.InitialRatchetKdfResponse.from_bytes bytes)
  checked self (pending.resume (.Some response)) fun initialSeal => do
    let request ← liftRust initialSeal.request
    let response ← children.ratchetHkdf request
    checked self (initialSeal.resume (.Some response)) (sealRecord self)

noncomputable def reserved (self : Server) (pending : registration.ServerInitialKdf) : RustT m Reply := do
  let (allocation, known) ← containers.mapReserve core.U64.Insts.CoreCmpEq core.U64.Insts.CoreHashHash
    beaconcrypt_public_request.collections.KeyedHasher.Insts.CoreHashBuildHasherSipHasher13
    hashbrown.alloc.inner.Global.Insts.HashbrownAllocInnerAllocator self.known_ids 1#usize
  let current := { self with known_ids := known }
  match allocation with
  | .Err _ => pure (.None, current)
  | .Ok _ => record current pending

noncomputable def lookup (self : Server) (pending : peer.CompletionLookup) (plaintext : Slice U8) : RustT m Reply := do
  let identifier ← liftRust pending.request
  let size ← liftRust (CoreModels.core.slice.Slice.len plaintext)
  let admitted ← beaconcrypt_public_request.server.registration_response_len size identifier
  match admitted with
  | .None => pure (.None, self)
  | .Some _ =>
    let occupied ← containers.mapContains core.U64.Insts.CoreCmpEq core.U64.Insts.CoreHashHash
      beaconcrypt_public_request.collections.KeyedHasher.Insts.CoreHashBuildHasherSipHasher13
      hashbrown.alloc.inner.Global.Insts.HashbrownAllocInnerAllocator
      core.U64.Insts.CoreHashHash (hashbrown.Equivalent.Blanket core.U64.Insts.CoreCmpEq
        (core.borrow.Borrow.Blanket U64)) self.known_ids identifier
    checked self (pending.resume occupied) (reserved self)

noncomputable def build (self : Server) (token : beaconcrypt_public_wrapper.server.RegistrationOutput)
    (data : core.option.Option (Slice U8)) : RustT m Reply := do
  let application ← liftRust (transport.normalize_registration_application data)
  let plaintext ← liftRust (beaconcrypt_public_wrapper.server.registration_application_bytes application)
  let pin ← beaconcrypt_public_request.server.Server.authentication_pin self
  match pin with
  | .None => pure (.None, self)
  | .Some pin =>
    checked self (peer.begin_completion_lookup self.control pin token.registration plaintext)
      (fun pending => lookup self pending plaintext)

omit codec in
theorem source (self : Server) (token : beaconcrypt_public_wrapper.server.RegistrationOutput)
    (data : core.option.Option (Slice U8)) :
    beaconcrypt_public_request.server.Server.Insts.BeaconcryptServerProviderServer.build_registration_response
      (m := RustT m) self token data = build self token data := by
  simp only [beaconcrypt_public_request.server.Server.Insts.BeaconcryptServerProviderServer.build_registration_response,
    build, lookup, reserved, record, sealRecord, commit, write, sign, publish, install, finish, checked,
    call_apply, call_result]
  apply bind_congr
  intro application
  apply bind_congr
  intro plaintext
  apply bind_congr
  intro pin
  cases pin with
  | none =>
    simp only [core.option.Option.Insts.CoreOpsTry_traitTry.branch,
      core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
      core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual, lift_ok, pure_bind]
  | some pin =>
    simp only [core.option.Option.Insts.CoreOpsTry_traitTry.branch,
      core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch, lift_ok, pure_bind]
    apply bind_congr
    intro lookupResult
    cases lookupResult with
    | Err prior =>
      simp only [core.result.Result.ok,

        core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual, lift_ok, pure_bind]
    | Ok pending =>
      simp only [core.result.Result.ok,
         lift_ok, pure_bind]
      apply bind_congr
      intro identifier
      apply bind_congr
      intro size
      apply bind_congr
      intro admitted
      cases admitted with
      | none =>
        simp only [

          core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual, lift_ok, pure_bind]
      | some capacity =>
        simp only [
           lift_ok, pure_bind]
        apply bind_congr
        intro occupied
        apply bind_congr
        intro pendingResult
        cases pendingResult with
        | Err prior =>
          simp only [

            core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual, lift_ok, pure_bind]
        | Ok initial =>
          simp only [
             lift_ok, pure_bind]
          apply bind_congr
          rintro ⟨allocation, known⟩
          cases allocation with
          | Err prior =>
            simp only [

              core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual, lift_ok, pure_bind]
          | Ok unitValue =>
            cases unitValue
            simp only [
               lift_ok, pure_bind]
            apply bind_congr
            intro kdfRequest
            apply bind_congr
            intro initialBytes
            apply bind_congr
            intro initialResponse
            apply bind_congr
            intro initialResult
            cases initialResult with
            | Err prior =>
              simp only [

                core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual, lift_ok, pure_bind]
            | Ok initialSeal =>
              simp only [
                 lift_ok, pure_bind]
              apply bind_congr
              intro sealRequest
              apply bind_congr
              intro sealResponse
              apply bind_congr
              intro sealResult
              cases sealResult with
              | Err prior =>
                simp only [

                  core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual, lift_ok, pure_bind]
              | Ok aead =>
                simp only [
                   lift_ok, pure_bind]
                apply bind_congr
                intro aeadRequest
                apply bind_congr
                intro detached
                apply bind_congr
                intro detachedReference
                apply bind_congr
                intro detachedView
                apply bind_congr
                intro aeadResult
                cases aeadResult with
                | Err prior =>
                  simp only [

                    core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual, lift_ok, pure_bind]
                | Ok committed =>
                  simp only [
                     lift_ok, pure_bind]
                  apply bind_congr
                  rintro ⟨transcript, transcriptBack⟩
                  apply bind_congr
                  rintro ⟨digest, changedTranscript⟩
                  apply bind_congr
                  intro committedResult
                  cases committedResult with
                  | Err prior =>
                    simp only [

                      core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual, lift_ok, pure_bind]
                  | Ok written =>
                    simp only [
                       lift_ok, pure_bind]
                    apply bind_congr
                    intro writeRequest
                    apply bind_congr
                    intro ciphertext
                    apply bind_congr
                    intro ciphertextView
                    apply bind_congr
                    intro writeResult
                    cases writeResult with
                    | Err prior =>
                      simp only [

                        core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual, lift_ok, pure_bind]
                    | Ok hashed =>
                      simp only [
                         lift_ok, pure_bind]
                      apply bind_congr
                      intro hashRequest
                      apply bind_congr
                      intro digest
                      apply bind_congr
                      intro hashResult
                      cases hashResult with
                      | Err prior =>
                        simp only [

                          core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual, lift_ok, pure_bind]
                      | Ok signing =>
                        simp only [
                           lift_ok, pure_bind]
                        apply bind_congr
                        intro identity
                        apply bind_congr
                        intro signRequest
                        apply bind_congr
                        intro signature
                        apply bind_congr
                        intro signatureView
                        apply bind_congr
                        intro signResult
                        cases signResult with
                        | Err prior =>
                          simp only [

                            core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual, lift_ok, pure_bind]
                        | Ok ready =>
                          simp only [
                             lift_ok, pure_bind]
                          apply bind_congr
                          intro message
                          simp only [Aeneas.Std.lift, lift_ok, pure_bind,
                            BeaconcryptCore.Computational.RegistrationNativeSourceEncoders.responseSyntax]
                          apply bind_congr
                          intro buffer
                          apply bind_congr
                          intro publishResult
                          cases publishResult with
                          | Err prior =>
                            simp only [

                              core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual, lift_ok, pure_bind]
                          | Ok published =>
                            simp only [
                               lift_ok, pure_bind]
                            apply bind_congr
                            intro insertResult
                            cases insertResult with
                            | Err prior =>
                              simp only [

                                core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual, lift_ok, pure_bind]
                            | Ok insert =>
                              simp only [
                                 lift_ok, pure_bind]
                              apply bind_congr
                              intro remoteIdentifier
                              apply bind_congr
                              rintro ⟨remote, publicationFinish⟩
                              apply bind_congr
                              intro binding
                              apply bind_congr
                              intro publicBytes
                              simp only []
                              apply bind_congr
                              intro publicResult
                              cases publicResult with
                              | Err prior =>
                                simp only [

                                  core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual, lift_ok, pure_bind]
                              | Ok publicKey =>
                                simp only [
                                   lift_ok, pure_bind]
                                apply bind_congr
                                rintro ⟨entry, entryBack⟩
                                cases entry with
                                | Occupied occupied =>
                                  apply bind_congr
                                  intro finished
                                  cases finished with
                                  | Err prior =>
                                    simp only [

                                      core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual, lift_ok, pure_bind]
                                  | Ok published =>
                                    simp only [
                                       lift_ok, pure_bind]
                                | Vacant vacant =>
                                  apply bind_congr
                                  intro remoteValue
                                  apply bind_congr
                                  rintro ⟨changed, insertedBack⟩
                                  apply bind_congr
                                  intro finished
                                  cases finished with
                                  | Err prior =>
                                    simp only [

                                      core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual, lift_ok, pure_bind]
                                  | Ok published =>
                                    simp only [
                                       lift_ok, pure_bind]
end BeaconcryptCore.Refinement.AdapterPublicServerBuildBody

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerBuildBody.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerBuildBody.source
