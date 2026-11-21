-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationServerOpenReferenceSourceEntry

/-! Actual Server acceptance keeps the one-use session list unchanged or appends exactly one Ready while returning its original index. All authentication, replay, allocation, agreement and retention failure branches are included; no live-session premise is added. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationServerOpenReferenceSessionShape
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhSecretInputKdf (RootOutput)
open RegistrationNativeRelatedFamily (Message)
open RegistrationNativeKemReferenceEffects (Callbacks)
open RegistrationServerOpenReferenceSourceAccept (State close)
variable {n : Nat} {ι KemSK Extra : Type} {base : OracleSpec ι}
attribute [local irreducible] RegistrationAuthenticationExecutor.execute registration.begin_init_authentication

def Shape (before : List (Option RegistrationServerReferenceRoot.Ready))
    (reply : RustM (Option Nat)) (after : List (Option RegistrationServerReferenceRoot.Ready)) : Prop :=
  after = before ∨ ∃ ready, reply = .ok (some before.length) ∧ after = before ++ [some ready]

/-- Actual private replay insertion either keeps the session list or appends its literal Ready and returns the new index. -/
theorem retain (setup : Setup base KemSK) (seed : PqxdhJointIdentity.IdentitySeed)
    (scalar : PqxdhJointGapDh.ScalarBytes) (remember : Extra → Message → Option RootOutput → Extra)
    (services : Callbacks n KemSK Extra) (ready : RegistrationServerReferenceRoot.Ready)
    (before : State n KemSK Extra) (result : RustM (Option Nat) × State n KemSK Extra)
    (supported : result ∈ support ((close setup seed scalar remember services
      (RegistrationServerOpenReferenceCompiler.retain ready)).run before)) :
    Shape before.1.sessions result.1 result.2.1.sessions := by
  rw [RegistrationServerOpenReferenceSourceAccept.retain_run] at supported
  cases present : before.1.consumed.contains (absBytes ready.agreement.pending.registration_id.bytes) with
  | false =>
      simp only [RegistrationServerReferenceSourceRetain.retain, RegistrationServerOpenReferenceSourceAccept.project,
        RegistrationServerMaterialFrontend.retain_fresh ready before.1 present, StateT.run, map_pure,
        support_pure, Set.mem_singleton_iff] at supported
      cases supported
      exact Or.inr ⟨ready, rfl, rfl⟩
  | true =>
      have replay := RegistrationReplaySchedule.consume_replayed
        (RegistrationServerReferenceRoot.atRoot ready RegistrationBoundKeySchedule.zero) before.1.consumed
          (by simpa only [RegistrationServerReferenceRoot.atRoot, RegistrationBoundGate.atRoot] using present)
      simp only [RegistrationServerReferenceSourceRetain.retain, RegistrationServerOpenReferenceSourceAccept.project,
        RegistrationServerMaterialFrontend.retain, replay, StateT.run, map_pure,
        support_pure, Set.mem_singleton_iff] at supported
      cases supported
      exact Or.inl rfl

/-- The full actual post-authentication replay/reserve/agreement controller can append only the Ready returned by its real source preparation. -/
theorem after (setup : Setup base KemSK) (checks : Checks) (seed : PqxdhJointIdentity.IdentitySeed)
    (scalar : PqxdhJointGapDh.ScalarBytes) (remember : Extra → Message → Option RootOutput → Extra)
    (services : Callbacks n KemSK Extra) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) (before : State n KemSK Extra)
    (result : RustM (Option Nat) × State n KemSK Extra)
    (supported : result ∈ support ((close setup seed scalar remember services
      (RegistrationServerOpenReferenceCompiler.afterAuthentication setup checks packet authenticated)).run before)) :
    Shape before.1.sessions result.1 result.2.1.sessions := by
  rw [RegistrationServerOpenReferenceSourceAccept.after_run] at supported
  split at supported
  · rw [support_pure, Set.mem_singleton_iff] at supported
    cases supported
    exact Or.inl rfl
  · split at supported
    · rw [mem_support_bind_iff] at supported
      obtain ⟨completed, possible, continued⟩ := supported
      rw [RegistrationServerOpenReferenceSourceAccept.agreement_run, support_map] at possible
      obtain ⟨inner, _possible, equal⟩ := possible
      cases equal
      cases accepted : inner.1 with
      | fail error =>
          simp only [accepted, support_pure, Set.mem_singleton_iff] at continued
          cases continued
          exact Or.inl rfl
      | div =>
          simp only [accepted, support_pure, Set.mem_singleton_iff] at continued
          cases continued
          exact Or.inl rfl
      | ok outcome => cases outcome with
        | none =>
            simp only [accepted, support_pure, Set.mem_singleton_iff] at continued
            cases continued
            exact Or.inl rfl
        | some ready =>
            simp only [accepted] at continued
            exact retain setup seed scalar remember services ready (before.1, inner.2) result continued
    · rw [support_pure, Set.mem_singleton_iff] at supported
      cases supported
      exact Or.inl rfl

/-- Actual full mandatory-authentication acceptance has only the derived unchanged-or-single-append session-list shape. -/
theorem accept (setup : Setup base KemSK) (checks : Checks) (verify : MldsaTranscriptAuth.Verify)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (remember : Extra → Message → Option RootOutput → Extra) (services : Callbacks n KemSK Extra)
    (packet : registration.InitPacket) (before : State n KemSK Extra)
    (result : RustM (Option Nat) × State n KemSK Extra)
    (supported : result ∈ support ((close setup seed scalar remember services
      (RegistrationServerOpenReferenceCompiler.accept setup checks verify packet)).run before)) :
    Shape before.1.sessions result.1 result.2.1.sessions := by
  rw [RegistrationServerOpenReferenceCompiler.accept, RegistrationServerOpenReferenceSourceAccept.close_bind,
    RegistrationServerOpenReferenceSourceAccept.close_get, pure_bind,
    RegistrationServerOpenReferenceSourceAccept.close_bind,
    RegistrationServerOpenReferenceSourceEntry.close_effect] at supported
  simp only [bind_map_left, mem_support_bind_iff] at supported
  obtain ⟨⟨checked, checkedWorld⟩, _authenticated, continued⟩ := supported
  cases checked with
  | fail error =>
      rw [RegistrationServerOpenReferenceSourceAccept.close_pure, support_pure, Set.mem_singleton_iff] at continued
      cases continued
      exact Or.inl rfl
  | div =>
      rw [RegistrationServerOpenReferenceSourceAccept.close_pure, support_pure, Set.mem_singleton_iff] at continued
      cases continued
      exact Or.inl rfl
  | ok checked =>
      rcases checked with ⟨events, verdict⟩
      cases verdict
      all_goals try {
        rw [RegistrationServerOpenReferenceSourceAccept.close_pure, support_pure, Set.mem_singleton_iff] at continued
        cases continued
        exact Or.inl rfl }
      case Accepted authenticated =>
        exact after setup checks seed scalar remember services packet authenticated
          (before.1, (before.2.1, { before.2.2 with world := checkedWorld })) result continued

end BeaconcryptCore.Computational.RegistrationServerOpenReferenceSessionShape

/-- info: 'BeaconcryptCore.Computational.RegistrationServerOpenReferenceSessionShape.retain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerOpenReferenceSessionShape.retain
/-- info: 'BeaconcryptCore.Computational.RegistrationServerOpenReferenceSessionShape.after' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerOpenReferenceSessionShape.after
/-- info: 'BeaconcryptCore.Computational.RegistrationServerOpenReferenceSessionShape.accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerOpenReferenceSessionShape.accept
