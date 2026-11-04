-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSigningSource
import BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedPacketClient
import BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedCutEvent
/-! Original attached fields are indexed only by the genuine reserved identity, original public parsed-accept ordinal and one of the three literal packet fields. The private event reads the successful before-call signing log; the executable stopping code uses only the public ordinal. -/
open OracleComp OracleSpec ENNReal
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedEvents
open RegistrationNativeRawAdapter (TypedSpec)
def observedMessages (handle : Nat) (trace : RegistrationNativePlatformIdentityCtxSigningLog.Trace) : List Pqxdh.Bytes :=
  (RegistrationNativePlatformIdentityCtxSigningSource.traceCalls trace).filterMap
    (RegistrationNativePlatformIdentityCtxSigningSource.selected handle)

/-- This is the original packet field and its own chronological before-signing history. -/
def Field {count : Nat} {S : Type} (joint : PqxdhJointIdentity.Primitives)
    (keys : Fin count → PqxdhJointIdentity.PublicIdentity) (identity : Fin count) (tag : Fin 3)
    (packet : beaconcrypt_core.registration.InitPacket)
    (before : S × RegistrationNativePlatformIdentityCtxSigningLog.Trace) : Prop :=
  ∃ forgery, RegistrationNativeIdentityUnissuedPacketClient.field tag (some packet)=some forgery ∧
    joint.verify (keys identity).ed25519 forgery.message forgery.signature=true ∧
    forgery.message ∉ observedMessages identity.val before.2

def At {count : Nat} {S A : Type} (joint : PqxdhJointIdentity.Primitives)
    (keys : Fin count → PqxdhJointIdentity.PublicIdentity) (identity : Fin count) (accept : Nat) (tag : Fin 3)
    (result : A × RegistrationNativeIdentityUnissuedCutEvent.State (S × RegistrationNativePlatformIdentityCtxSigningLog.Trace)) : Prop :=
  RegistrationNativeIdentityUnissuedCutEvent.At (Field joint keys identity tag) accept result

/-- The three literal packet positions cover an actual verified unissued field without changing its signature. -/
theorem field_cover {count : Nat} {S : Type} (joint : PqxdhJointIdentity.Primitives)
    (keys : Fin count → PqxdhJointIdentity.PublicIdentity) (identity : Fin count)
    (packet : beaconcrypt_core.registration.InitPacket)
    (before : S × RegistrationNativePlatformIdentityCtxSigningLog.Trace)
    (forgery : PqxdhJointIdentity.Forgery)
    (member : forgery ∈ PqxdhJointPhase1Reports.candidateFields (RegistrationRootInput.candidate packet))
    (valid : joint.verify (keys identity).ed25519 forgery.message forgery.signature=true)
    (fresh : forgery.message ∉ observedMessages identity.val before.2) :
    ∃ tag : Fin 3, Field joint keys identity tag packet before := by
  obtain ⟨tag,found⟩ := RegistrationNativeIdentityUnissuedPacketClient.field_exists packet forgery member
  exact ⟨tag,forgery,found,valid,fresh⟩

/-- Each fixed field event refers to the same complete original result and key family. -/
def Any {count accepts : Nat} {R A S : Type} (joint : PqxdhJointIdentity.Primitives)
    (keys : R → Fin count → PqxdhJointIdentity.PublicIdentity)
    (observe : R → A × RegistrationNativeIdentityUnissuedCutEvent.State (S × RegistrationNativePlatformIdentityCtxSigningLog.Trace))
    (result : R) : Prop :=
  ∃ identity : Fin count, ∃ accept : Fin accepts, ∃ tag : Fin 3,
    At joint (keys result) identity accept.val tag (observe result)

/-- The literal finite identity/accept/field cover incurs exactly the corresponding finite probability sum. -/
theorem finite_union {count accepts : Nat} {R A S : Type} (joint : PqxdhJointIdentity.Primitives)
    (keys : R → Fin count → PqxdhJointIdentity.PublicIdentity)
    (observe : R → A × RegistrationNativeIdentityUnissuedCutEvent.State (S × RegistrationNativePlatformIdentityCtxSigningLog.Trace))
    (work : ProbComp R) :
    Pr{let result ← work}[Any (accepts := accepts) joint keys observe result] ≤
      ∑ identity : Fin count, ∑ accept : Fin accepts, ∑ tag : Fin 3,
        Pr{let result ← work}[At joint (keys result) identity accept.val tag (observe result)] := by
  have identities := prEvent_exists_le work (fun identity : Fin count => fun result =>
    ∃ accept : Fin accepts, ∃ tag : Fin 3, At joint (keys result) identity accept.val tag (observe result))
  apply identities.trans
  apply Finset.sum_le_sum
  intro identity _identity
  have positions := prEvent_exists_le work (fun accept : Fin accepts => fun result =>
    ∃ tag : Fin 3, At joint (keys result) identity accept.val tag (observe result))
  apply positions.trans
  exact Finset.sum_le_sum (fun accept _accept => prEvent_exists_le work
    (fun tag : Fin 3 => fun result => At joint (keys result) identity accept.val tag (observe result)))

end BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedEvents

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedEvents.field_cover' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedEvents.field_cover

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedEvents.finite_union' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedEvents.finite_union
