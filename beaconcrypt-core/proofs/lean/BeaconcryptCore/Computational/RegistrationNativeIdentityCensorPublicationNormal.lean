-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorExternalSource
import BeaconcryptCore.PanicFreedom.RegistrationSigningContinuations
import BeaconcryptCore.Computational.RegistrationNativeIdentityReadyFailure

/-! Original publication controllers return normal rejection/publication results on arbitrary represented crypto replies whenever the individual writer returns a normal optional result. The final source instantiation derives that writer condition from its literal 6757 reservation/serialization body. No whole-handler normality or publication-security premise is used. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPublicationNormal
open BeaconcryptCore.Refinement
variable {S Encoded A : Type}

def Normal : RustM A → Prop
  | .ok _ => True
  | _ => False

def WriterNormal (encode : registration.SignedInitView → StateT S ProbComp (RustM (core.option.Option Encoded))) : Prop :=
  ∀ fields before result, result ∈ support ((encode fields).run before) → Normal result.1

private theorem pure_normal (value : A) (before : S) (result : RustM A × S)
    (possible : result ∈ support ((pure (.ok value) : StateT S ProbComp (RustM A)).run before)) : Normal result.1 := by
  rw [StateT.run_pure, support_pure, Set.mem_singleton_iff] at possible
  subst result
  trivial

/-- The actual Ready message and publish functions return normally on every normal source writer outcome. -/
theorem ready (encode : registration.SignedInitView → StateT S ProbComp (RustM (core.option.Option Encoded)))
    (encoder : WriterNormal encode) (pending : registration.BeaconInitReady) (before : S)
    (result : RustM (RegistrationBeaconInitExecutor.Result Encoded) × S)
    (possible : result ∈ support ((RegistrationNativePlatformBeaconPublication.ready encode pending).run before)) : Normal result.1 := by
  obtain ⟨fields, message⟩ := BeaconcryptCore.PanicFreedom.RegistrationTrivial.BeaconInitReady_message_total pending
  rw [RegistrationNativePlatformBeaconPublication.ready_run, message, mem_support_bind_iff] at possible
  obtain ⟨⟨written, middle⟩, called, later⟩ := possible
  have normal := encoder fields before (written, middle) called
  cases written with
  | fail error | div => cases normal
  | ok encoded =>
    change result ∈ support (pure (pending.publish encoded, middle) : ProbComp _) at later
    rw [support_pure, Set.mem_singleton_iff] at later
    subst result
    obtain ⟨published, returned⟩ := BeaconcryptCore.PanicFreedom.RegistrationTrivial.BeaconInitReady_publish_total pending encoded
    rw [returned]
    trivial

/-- Missing, wrong-width and admitted ML signatures all have the original normal rejection/Ready continuation. -/
theorem signing (impl : QueryImpl RegistrationBeaconInitExecutor.Spec (StateT S ProbComp))
    (encode : registration.SignedInitView → StateT S ProbComp (RustM (core.option.Option Encoded)))
    (encoder : WriterNormal encode) (payload : MldsaTranscriptAuth.Payload) (digest : CtxRomAuth.CtxDigest)
    (pending : registration.BeaconMldsaSigning) (before : S)
    (result : RustM (RegistrationBeaconInitExecutor.Result Encoded) × S)
    (possible : result ∈ support ((RegistrationNativePlatformBeaconPublication.fromSigning impl encode payload digest pending).run before)) : Normal result.1 := by
  obtain ⟨request, requested⟩ := BeaconcryptCore.PanicFreedom.RegistrationTrivial.BeaconMldsaSigning_request_total pending
  simp only [RegistrationNativePlatformBeaconPublication.fromSigning, RegistrationNativePlatformBeaconPublication.continueWith,
    requested, StateT.run_bind, mem_support_bind_iff] at possible
  obtain ⟨⟨signature, middle⟩, _called, later⟩ := possible
  cases signature with
  | none =>
    change result ∈ support ((pure (.ok (.Err pending.state.original_control)) : StateT S ProbComp _).run middle) at later
    exact pure_normal _ middle result later
  | some signature =>
    obtain ⟨effect, resumed, facts⟩ := RegistrationSigningContinuations.beacon_mldsa_signature_exact pending signature
    rw [resumed] at later
    cases effect <;> simp only [RegistrationSigningContinuations.signatureResult] at facts
    case Rejected previous => exact pure_normal _ middle result later
    case Ready selected => exact ready encode encoder selected middle result later

/-- Every actual digest feeds the original normal ML request construction. -/
theorem hash (impl : QueryImpl RegistrationBeaconInitExecutor.Spec (StateT S ProbComp))
    (encode : registration.SignedInitView → StateT S ProbComp (RustM (core.option.Option Encoded)))
    (encoder : WriterNormal encode) (pending : registration.BeaconInitHash) (before : S)
    (result : RustM (RegistrationBeaconInitExecutor.Result Encoded) × S)
    (possible : result ∈ support ((RegistrationNativePlatformBeaconPublication.fromHash impl encode pending).run before)) : Normal result.1 := by
  obtain ⟨request, requested⟩ := BeaconcryptCore.PanicFreedom.RegistrationTrivial.BeaconInitHash_request_total pending
  simp only [RegistrationNativePlatformBeaconPublication.fromHash, RegistrationNativePlatformBeaconPublication.continueWith,
    requested, StateT.run_bind, mem_support_bind_iff] at possible
  obtain ⟨⟨digest, middle⟩, _called, later⟩ := possible
  obtain ⟨next, resumed, _⟩ := RegistrationSigningContinuations.beacon_init_hash_some_exact pending (RegistrationAuthenticationShared.digestArray digest)
  rw [resumed] at later
  exact signing impl encode encoder _ digest next middle result later

private theorem fingerprint_resume (pending : registration.BeaconFingerprint) (digest : Array U8 64#usize) :
    ∃ selected, pending.resume (.Some digest) = .ok (.HashRequested selected) :=
  (RegistrationSigningContinuations.beacon_fingerprint_some_exact pending digest).imp (fun _ facts => facts.1)

attribute [local irreducible] registration.BeaconFingerprint.resume

/-- Every actual public fingerprint feeds the original normal unsigned-Init request. -/
theorem fingerprint (impl : QueryImpl RegistrationBeaconInitExecutor.Spec (StateT S ProbComp))
    (encode : registration.SignedInitView → StateT S ProbComp (RustM (core.option.Option Encoded)))
    (encoder : WriterNormal encode) (pending : registration.BeaconFingerprint) (before : S)
    (result : RustM (RegistrationBeaconInitExecutor.Result Encoded) × S)
    (possible : result ∈ support ((RegistrationNativePlatformBeaconPublication.fromFingerprint impl encode pending).run before)) : Normal result.1 := by
  obtain ⟨request, requested⟩ := BeaconcryptCore.PanicFreedom.RegistrationTrivial.BeaconFingerprint_request_total pending
  simp only [RegistrationNativePlatformBeaconPublication.fromFingerprint, RegistrationNativePlatformBeaconPublication.continueWith,
    requested, StateT.run_bind, mem_support_bind_iff] at possible
  obtain ⟨⟨digest, middle⟩, _called, later⟩ := possible
  obtain ⟨next, resumed⟩ := fingerprint_resume pending (RegistrationAuthenticationShared.digestArray digest)
  simp only [resumed] at later
  exact hash impl encode encoder next middle result later

/-- Every actual Ed reply returns normally and reaches only the source's rejected, next-Ed or fingerprint branch. -/
theorem ed (impl : QueryImpl RegistrationBeaconInitExecutor.Spec (StateT S ProbComp))
    (encode : registration.SignedInitView → StateT S ProbComp (RustM (core.option.Option Encoded)))
    (encoder : WriterNormal encode) (pending : registration.BeaconEd25519Signing) (before : S)
    (result : RustM (RegistrationBeaconInitExecutor.Result Encoded) × S)
    (possible : result ∈ support ((RegistrationNativePlatformBeaconPublication.fromEd impl encode pending).run before)) : Normal result.1 := by
  obtain ⟨request, requested, _⟩ := RegistrationSigning.ed_request_exact pending
  rw [RegistrationNativePlatformBeaconPublication.fromEd.eq_def] at possible
  simp only [requested, RegistrationNativePlatformBeaconPublication.continueWith, StateT.run_bind, mem_support_bind_iff] at possible
  obtain ⟨⟨reply, middle⟩, _called, later⟩ := possible
  obtain ⟨effect, resumed, facts⟩ := RegistrationSigning.ed_resume_refines pending reply
  rw [resumed] at later
  cases effect <;> simp only [RegistrationSigning.EdReplyTransition] at facts
  case Rejected previous => exact pure_normal _ middle result later
  case FingerprintRequested next => exact fingerprint impl encode encoder next middle result later
  case Ed25519SigningRequested next => exact ed impl encode encoder next middle result later
termination_by RegistrationBeaconInitExecutor.edRank pending
decreasing_by
  rename_i next _effectEq
  exact RegistrationBeaconInitExecutor.ed_rank pending reply next resumed

private theorem writer_normal {E : Type} (reserve : Usize → StateT S ProbComp (core.result.Result Unit E))
    (other : RegistrationSerializerReachableSource.OtherBranches) :
    WriterNormal (RegistrationNativeSourceWriterFailureView.writer reserve other) := by
  intro fields before result possible
  rw [RegistrationNativeSourceWriterFailureView.writer, RegistrationNativeSourceWriterReadback.init_source,
    StateT.run_map, support_map] at possible
  obtain ⟨⟨allocation, after⟩, _called, rfl⟩ := possible
  cases allocation <;> trivial

section Actual
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeIdentityCensorEdOutgoingSource (Full interpret)
open PqxdhEd25519EufCma (Ed25519Signature)
variable {n : Nat} {I KemSK Platform E : Type} {base : OracleSpec I} {mlSource : RegistrationNativeMldsa.Source}

/-- Every reached actual canonical or private-censored publication suffix returns a normal rejection/publication result. The writer condition is discharged from the literal fixed-capacity source serializer, including failed reservations and their P poststates. -/
theorem source_ed (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (selected index : Nat) (owner : RegistrationNativeIdentityFrontend.Owner mlSource) (placeholder : Ed25519Signature)
    (reserve : Usize → StateT Platform ProbComp (core.result.Result Unit E)) (censored : Bool)
    (pending : registration.BeaconEd25519Signing)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource))
    (result : RustM (RegistrationBeaconInitExecutor.Result (alloc.vec.Vec U8)) × Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource))
    (possible : result ∈ support ((RegistrationNativePlatformBeaconPublication.fromEd
      (m := StateT (Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)) ProbComp)
      (fun query => interpret setup.joint selected placeholder censored
        (RegistrationNativePlatformIdentityCtxMain.beacon (n := n) (Platform := Platform) (source := mlSource) setup checks representation created
          (RegistrationNativePlatformIdentityProgram.native
            (RegistrationNativeIdentityFrontend.outgoing (n := n) (Auxiliary := RegistrationServerRoleBackend.State) setup mlSource index owner query))))
      (fun fields => interpret setup.joint selected placeholder censored
        (RegistrationNativePlatformIdentityCtxMain.beacon (n := n) (Platform := Platform) (source := mlSource) setup checks representation created
          (RegistrationNativePlatformIdentityProgram.external (RegistrationNativeIdentityCensorConcreteWriter.encode reserve fields)))) pending).run before)) :
    Normal result.1 := by
  apply ed _ _ ?_ pending before result possible
  intro fields initial returned called
  dsimp only at called
  rw [RegistrationNativeIdentityCensorExternalSource.writer] at called
  exact writer_normal _ RegistrationNativeConcreteCodec.serializerBranches fields initial returned called

end Actual

/-- On these actual normal results, the stopped failure observation is absent exactly for successful publication. Divergence and abnormal failure cannot be mistaken for publication. -/
theorem success_iff (returned : RustM (RegistrationBeaconInitExecutor.Result (alloc.vec.Vec U8))) (normal : Normal returned) :
    RegistrationNativeIdentityReadyFailure.observe returned = none ↔
      ∃ published, returned = .ok (.Ok published) := by
  cases returned with
  | fail error | div => cases normal
  | ok reply => cases reply <;> simp [RegistrationNativeIdentityReadyFailure.observe]

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPublicationNormal
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPublicationNormal.ready' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPublicationNormal.ready
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPublicationNormal.signing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPublicationNormal.signing
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPublicationNormal.hash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPublicationNormal.hash
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPublicationNormal.fingerprint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPublicationNormal.fingerprint
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPublicationNormal.ed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPublicationNormal.ed
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPublicationNormal.source_ed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPublicationNormal.source_ed
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPublicationNormal.success_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPublicationNormal.success_iff
