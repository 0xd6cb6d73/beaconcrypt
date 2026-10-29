-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationWorldAuthentication
import BeaconcryptCore.Computational.RegistrationRootInput
import BeaconcryptCore.Computational.PqxdhJointPhase1Reports

/-! Native designation does not fix the accepted prekey. The actual attached verification result is translated to the existing joint Ed25519/converted-DH endpoint. A chronological owner signing history whose prekey messages have the source's fixed prekey yields either that exact prekey or a first-unissued valid field, without guessing a field. The history invariant and its source instrumentation are distinct from the final ordinary joint-EUF reduction. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeEdOrigin
open PqxdhEd25519EufCma
open PqxdhJointIdentity (History PublicIdentity Forgery signedMessages wins)
open PqxdhJointPhase1Reports (candidateFields selectUnissued)
open PqxdhServerAuthExperiment (Setup Codec)
variable {ι KemSK Reader Response : Type} {base : OracleSpec ι} {n : Nat}

/-- Retry attempts may change their one-time key, while PQ/prekey tags remain disjoint. -/
def Allowed (prekey : X25519PublicKey) (message : Pqxdh.Bytes) : Prop :=
  message = prekeyMessage prekey ∨
    (∃ key : PqxdhKemIndCca.MlKem768PublicKey, message = pqMessage key) ∨
    (∃ key : X25519PublicKey, message = oneTimeMessage key)

def FixedPrekey (prekey : X25519PublicKey) (history : History) : Prop :=
  ∀ message ∈ signedMessages history, Allowed prekey message

/-- Generated owners begin with the actual empty signing history. -/
theorem fixed_empty (prekey : X25519PublicKey) : FixedPrekey prekey [] := by
  simp [FixedPrekey, signedMessages]

/-- Logging a reached signing callback before its continuation preserves the fixed-prekey invariant, independently of later publication success. -/
theorem fixed_signed (prekey : X25519PublicKey) (history : History) (fixed : FixedPrekey prekey history)
    (message : Pqxdh.Bytes) (signature : Ed25519Signature) (allowed : Allowed prekey message) :
    FixedPrekey prekey (history ++ [.signed message signature]) := by
  intro actual member
  simp only [signedMessages, List.filterMap_append, List.filterMap_cons, List.filterMap_nil,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with earlier | rfl
  · exact fixed actual earlier
  · exact allowed

/-- Optional converted-DH observations retain the entire signing-message ledger. -/
theorem fixed_dh (prekey : X25519PublicKey) (history : History) (fixed : FixedPrekey prekey history)
    (peer : PqxdhJointIdentity.PeerEncoding) (reply : Option PqxdhJointIdentity.DhOutput) :
    FixedPrekey prekey (history ++ [.staticDh peer reply]) := by
  simpa only [FixedPrekey, signedMessages, List.filterMap_append, List.filterMap_cons,
    List.filterMap_nil, List.append_nil] using fixed

private theorem changed_prekey_fresh (prekey changed : X25519PublicKey) (history : History)
    (fixed : FixedPrekey prekey history) (different : changed ≠ prekey) :
    prekeyMessage changed ∉ signedMessages history := by
  intro member
  rcases fixed _ member with same | ⟨key, same⟩ | ⟨key, same⟩
  · exact different (prekeyMessage_injective same)
  · exact prekeyMessage_ne_pqMessage changed key same
  · exact prekeyMessage_ne_oneTimeMessage changed key same

/-- Any changed accepted prekey produces an actual first-unissued winning joint-EUF report. Reusing a signature on an old message does not count as a win. -/
theorem prekey_or_report (joint : PqxdhJointIdentity.Primitives) (publicKey : PublicIdentity)
    (candidate : Phase1Candidate) (decoded : Phase1KeyTuple) (history : History)
    (accepted : acceptPhase1Candidate joint.verify candidate = some (publicKey.ed25519, decoded))
    (prekey : X25519PublicKey) (fixed : FixedPrekey prekey history) :
    decoded.prekey = prekey ∨ ∃ forgery, selectUnissued history candidate = some forgery ∧
      wins joint publicKey forgery history = true := by
  classical
  by_cases same : decoded.prekey = prekey
  · exact Or.inl same
  · right
    obtain ⟨_, pqSignature, preSignature, oneSignature, pqAttached, _, preAttached, _, oneAttached, _⟩ :=
      acceptPhase1Candidate_some_witness joint.verify candidate publicKey.ed25519 decoded accepted
    have member : (⟨prekeyMessage decoded.prekey, preSignature⟩ : Forgery) ∈ candidateFields candidate := by
      simp [candidateFields, pqAttached, preAttached, oneAttached]
    have fresh := changed_prekey_fresh prekey decoded.prekey history fixed same
    cases selected : selectUnissued history candidate with
    | none => exact False.elim (fresh ((PqxdhJointPhase1Reports.selectUnissued_none_iff history candidate).mp selected _ member))
    | some forgery => exact ⟨forgery, rfl,
        PqxdhJointPhase1Reports.selected_weak_euf joint candidate publicKey decoded history accepted forgery selected⟩

attribute [local irreducible] RegistrationWorldAuthentication.begin
  RegistrationAuthenticationShared.begin RegistrationAuthenticationExecutor.begin

/-- Actual mandatory native authentication gives the unchanged detached classical acceptance result under its ordinary attached-format contract. -/
theorem accepted_detached (setup : Setup base KemSK) (codec : Codec Reader Response)
    (shortRejects : ∀ (publicKey : Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket)
    (before after : PqxdhRecordLiftWorld.State n)
    (events : List BeaconcryptCore.Refinement.RegistrationAuthenticationFlow.Event)
    (authenticated : registration.AuthenticatedInit)
    (supported : (.ok (events, .Accepted authenticated), after) ∈ support
      ((RegistrationWorldAuthentication.begin setup codec route verify pin packet).run before)) :
    acceptPhase1Candidate setup.joint.verify (RegistrationRootInput.candidate packet) =
      some (RegistrationRootInput.identity authenticated.registration, RegistrationRootInput.keys authenticated.registration) := by
  have accepted := RegistrationRootInput.accepted_source setup.source.crypto verify codec.frameWrite
    (RawCtxSourceHkdf.kdfImpl setup.source) pin packet _ _ events authenticated
    (RegistrationWorldAuthentication.begin_native_support setup codec route verify pin packet before after events authenticated supported)
  rw [PqxdhJointPhase1Reports.sourceAccept_eq _ setup.joint
    (PqxdhJointPhase1Reports.source_attached_adapter setup.source.crypto setup.joint setup.secretOfSeed setup.wiring shortRejects)] at accepted
  exact accepted

/-- Broad native identity designation plus actual history gives prekey origin or the explicit old joint-use weak-EUF report, retaining all native packet fields and failed-prefix poststates. -/
theorem native_prekey_or_report (setup : Setup base KemSK) (codec : Codec Reader Response)
    (shortRejects : ∀ (publicKey : Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket)
    (before after : PqxdhRecordLiftWorld.State n)
    (events : List BeaconcryptCore.Refinement.RegistrationAuthenticationFlow.Event)
    (authenticated : registration.AuthenticatedInit)
    (supported : (.ok (events, .Accepted authenticated), after) ∈ support
      ((RegistrationWorldAuthentication.begin setup codec route verify pin packet).run before))
    (publicKey : PublicIdentity) (designated : RegistrationRootInput.identity authenticated.registration = publicKey.ed25519)
    (prekey : X25519PublicKey) (history : History) (fixed : FixedPrekey prekey history) :
    (RegistrationRootInput.keys authenticated.registration).prekey = prekey ∨
      ∃ forgery, selectUnissued history (RegistrationRootInput.candidate packet) = some forgery ∧
        wins setup.joint publicKey forgery history = true := by
  have accepted := accepted_detached setup codec shortRejects route verify pin packet before after events authenticated supported
  rw [designated] at accepted
  exact prekey_or_report setup.joint publicKey (RegistrationRootInput.candidate packet)
    (RegistrationRootInput.keys authenticated.registration) history accepted prekey fixed

end BeaconcryptCore.Computational.RegistrationNativeEdOrigin

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEdOrigin.fixed_empty' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEdOrigin.fixed_empty
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEdOrigin.fixed_signed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEdOrigin.fixed_signed
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEdOrigin.fixed_dh' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEdOrigin.fixed_dh
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEdOrigin.prekey_or_report' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEdOrigin.prekey_or_report
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEdOrigin.accepted_detached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEdOrigin.accepted_detached
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEdOrigin.native_prekey_or_report' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEdOrigin.native_prekey_or_report
