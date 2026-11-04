-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPublicClient
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorRecognition
import BeaconcryptCore.Computational.RegistrationRootInput
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTyped

/-! The actual publicly stopped typed client returns either its first public hash-recognition witness or a valid selected-message field from its fixed accept packet. Its constructor uses public handles/messages and a known placeholder; the challenged seed and canonical signature occur only in the ordinary primitive interpreter. The ordinary joint weak-EUF advantage below is for this explicit client. Original native causal-event coverage is a separate source coupling obligation. -/
open OracleComp OracleSpec ENNReal
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorStoppedReduction
open PqxdhJointIdentity (PublicIdentity Forgery)
open PqxdhEd25519EufCma (Ed25519Signature)
open RegistrationNativeIdentityAdaptiveHashCapture (Candidate)
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativeIdentityCensorCompiler (Mode)
variable {S Value Auxiliary : Type}

def choose (primitives : PqxdhJointIdentity.Primitives) (identity : PublicIdentity) (target : Pqxdh.Bytes) :
    List Forgery → Option (Candidate primitives identity)
  | [] => none
  | current :: rest =>
      if valid : current.message = target ∧ primitives.verify identity.ed25519 current.message current.signature = true then
        some ⟨target, current.signature, by rw [← valid.1]; exact valid.2⟩
      else choose primitives identity target rest

/-- Every returned field is publicly verified and has exactly the selected public message. -/
theorem choose_target (primitives : PqxdhJointIdentity.Primitives) (identity : PublicIdentity) (target : Pqxdh.Bytes)
    (fields : List Forgery) (candidate : Candidate primitives identity)
    (chosen : choose primitives identity target fields = some candidate) : candidate.1 = target := by
  induction fields with
  | nil => cases chosen
  | cons current rest ih =>
    unfold choose at chosen
    split at chosen
    · cases Option.some.inj chosen
      rfl
    · exact ih chosen

/-- Any actual valid attached target field is captured; no signature uniqueness or canonical-signature equality is required. -/
theorem choose_complete (primitives : PqxdhJointIdentity.Primitives) (identity : PublicIdentity) (target : Pqxdh.Bytes)
    (fields : List Forgery) (forgery : Forgery) (member : forgery ∈ fields) (message : forgery.message = target)
    (valid : primitives.verify identity.ed25519 forgery.message forgery.signature = true) :
    ∃ candidate, choose primitives identity target fields = some candidate ∧ candidate.1 = target := by
  induction fields with
  | nil => cases member
  | cons current rest ih =>
    by_cases accepted : current.message = target ∧ primitives.verify identity.ed25519 current.message current.signature = true
    · exact ⟨⟨target, current.signature, by rw [← accepted.1]; exact accepted.2⟩,
        by rw [choose, dite_eq_left accepted], rfl⟩
    · have later : forgery ∈ rest := by
        rcases List.mem_cons.mp member with same | present
        · exact False.elim (accepted (same ▸ ⟨message, valid⟩))
        · exact present
      obtain ⟨candidate, selected, matching⟩ := ih later
      exact ⟨candidate, by simpa only [choose, accepted, ↓reduceDIte] using selected, matching⟩

def packet (primitives : PqxdhJointIdentity.Primitives) (identity : PublicIdentity) (target : Option Pqxdh.Bytes)
    (received : beaconcrypt_core.registration.InitPacket) : Option (Candidate primitives identity) :=
  target.bind fun message => choose primitives identity message
    (PqxdhJointPhase1Reports.candidateFields (RegistrationRootInput.candidate received))

/-- Submitted fields are an upper-bound observation: the retained callback reply is deliberately ignored. Successful accepted fields form a subset. -/
def result (primitives : PqxdhJointIdentity.Primitives) (identity : PublicIdentity)
    (returned : Value × (RegistrationNativeIdentityCensorPublicClient.ClientState S × Option RegistrationNativeIdentityCensorPublicClient.Stop)) :
    Option (Candidate primitives identity) :=
  match returned.2.2 with
  | some (.attempted received _reply) => packet primitives identity returned.2.1.1.2.target received
  | _ => none

/-- Public marker erasure leaves the exact executable censor and symbolic-hash requests. Stopping uses only the fixed bundle/accept ordinals and current public callback data. -/
def program (selected bundle accept : Nat) (placeholder : Ed25519Signature)
    (frontend : QueryImpl TypedSpec (StateT S (OracleComp RegistrationNativePlatformIdentityCtxCompiler.Spec)))
    (defaults : (query : TypedSpec.Domain) → TypedSpec.Range query) (work : OracleComp TypedSpec Value)
    (initial : S) (knownInputs : List Pqxdh.Bytes) :
    OracleComp RegistrationNativeIdentityCensorCompiler.Spec
      (Value × (RegistrationNativeIdentityCensorPublicClient.ClientState S × Option RegistrationNativeIdentityCensorPublicClient.Stop)) :=
  simulateQ (RegistrationNativeIdentityCensorOperational.erase placeholder)
    ((simulateQ (RegistrationNativeIdentityCensorPublicClient.freeze selected bundle accept placeholder frontend defaults) work).run
      (((initial, ({knownInputs := knownInputs} : Mode)), 0), none))

/-- Either an earlier recognized public input or the actual retained accept packet supplies the concrete field signature; the reduction never needs the canonical private reply. -/
def client (primitives : PqxdhJointIdentity.Primitives) (selected bundle accept : Nat) (placeholder : Ed25519Signature)
    (frontend : QueryImpl TypedSpec (StateT S (OracleComp RegistrationNativePlatformIdentityCtxCompiler.Spec)))
    (defaults : (query : TypedSpec.Domain) → TypedSpec.Range query) (work : PublicIdentity → OracleComp TypedSpec Value)
    (initial : S) (knownInputs : List Pqxdh.Bytes) (identity : PublicIdentity) :
    OracleComp RegistrationNativeIdentityCensorCompiler.Spec (Option (Candidate primitives identity)) :=
  (fun captured => match captured with
    | .inl recognized => some recognized
    | .inr returned => result primitives identity returned) <$>
      RegistrationNativeIdentityRecognitionCapture.capture (RegistrationNativeIdentityCensorRecognition.recognize primitives identity)
        (program selected bundle accept placeholder frontend defaults (work identity) initial knownInputs)

/-- One ordinary joint Ed/static-DH weak-EUF advantage bounds the selected valid-field event of this explicit stopped typed client, including public hash recognition before the fixed accept. -/
theorem bound (primitives : PqxdhJointIdentity.Primitives) (selected bundle accept : Nat) (placeholder : Ed25519Signature)
    (fallback : Forgery)
    (frontend : QueryImpl TypedSpec (StateT S (OracleComp RegistrationNativePlatformIdentityCtxCompiler.Spec)))
    (defaults : (query : TypedSpec.Domain) → TypedSpec.Range query) (work : PublicIdentity → OracleComp TypedSpec Value)
    (initial : S) (knownInputs : List Pqxdh.Bytes)
    (protocol : PublicIdentity → QueryImpl PqxdhJointPhase1Reports.ProtocolSpec
      (StateT Auxiliary (OracleComp PqxdhJointIdentity.AdversarySpec)))
    (cache : RegistrationNativeIdentityCensorRecognition.Cache) (before : Auxiliary) :
    Pr{let accepted ← (RegistrationNativeIdentityCensorRecognition.game primitives placeholder protocol
      (client primitives selected bundle accept placeholder frontend defaults work initial knownInputs) cache before)}[accepted = true] ≤
      PqxdhJointIdentity.advantage primitives
        (RegistrationNativeIdentityAdaptiveCensor.reduction placeholder fallback
          (RegistrationNativeIdentityCensorRecognition.work primitives protocol
            (client primitives selected bundle accept placeholder frontend defaults work initial knownInputs) cache before)) :=
  RegistrationNativeIdentityCensorRecognition.bound primitives placeholder fallback protocol
    (client primitives selected bundle accept placeholder frontend defaults work initial knownInputs) cache before

section Native
variable {n : Nat} {I KemSK Platform E : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
variable (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
variable (wire : RegistrationNativeWire.Wire) (route : RawCtxServerRouting.SenderDecoder)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
variable (credential : RegistrationNativeMldsa.Credential source) (keys : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (CoreModels.core.result.Result Unit E)) (erased : beaconcrypt_core.commitment.CommitmentTranscript)
variable (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
local notation "actual" => RegistrationNativePlatformIdentityCtxTyped.handler (n := n) setup checks wire route representation created credential keys failure allocation
  reserveRegistration reservePeer reserveFrame erased helper writer

/-- This concrete client executes the literal current Native typed dictionary. Independent auxiliary material stays in that dictionary; no challenged Ed seed or canonical signature is an argument. -/
noncomputable def nativeClient (selected bundle accept : Nat) (placeholder : Ed25519Signature)
    (defaults : (query : TypedSpec.Domain) → TypedSpec.Range query) (work : PublicIdentity → OracleComp TypedSpec Value)
    (initial : RegistrationNativeIdentityMain.State n KemSK source × Platform) (knownInputs : List Pqxdh.Bytes) (identity : PublicIdentity) :
    OracleComp RegistrationNativeIdentityCensorCompiler.Spec (Option (Candidate setup.joint identity)) :=
  client setup.joint selected bundle accept placeholder actual defaults work initial knownInputs identity

/-- The selected recognized-or-submitted-field probability of the literal stopped Native client has an explicit ordinary joint weak-EUF reduction. The original causal-event inclusion is not an assumption of this bound. -/
theorem native_bound (selected bundle accept : Nat) (placeholder : Ed25519Signature) (fallback : Forgery)
    (defaults : (query : TypedSpec.Domain) → TypedSpec.Range query) (work : PublicIdentity → OracleComp TypedSpec Value)
    (initial : RegistrationNativeIdentityMain.State n KemSK source × Platform) (knownInputs : List Pqxdh.Bytes)
    (protocol : PublicIdentity → QueryImpl PqxdhJointPhase1Reports.ProtocolSpec
      (StateT Auxiliary (OracleComp PqxdhJointIdentity.AdversarySpec)))
    (cache : RegistrationNativeIdentityCensorRecognition.Cache) (before : Auxiliary) :
    Pr{let accepted ← (RegistrationNativeIdentityCensorRecognition.game setup.joint placeholder protocol
      (nativeClient setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
        selected bundle accept placeholder defaults work initial knownInputs) cache before)}[accepted = true] ≤
      PqxdhJointIdentity.advantage setup.joint
        (RegistrationNativeIdentityAdaptiveCensor.reduction placeholder fallback
          (RegistrationNativeIdentityCensorRecognition.work setup.joint protocol
            (nativeClient setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
              selected bundle accept placeholder defaults work initial knownInputs) cache before)) :=
  bound setup.joint selected bundle accept placeholder fallback actual defaults work initial knownInputs protocol cache before

end Native
end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorStoppedReduction

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorStoppedReduction.choose_target' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorStoppedReduction.choose_target

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorStoppedReduction.choose_complete' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorStoppedReduction.choose_complete

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorStoppedReduction.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorStoppedReduction.bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorStoppedReduction.native_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorStoppedReduction.native_bound
