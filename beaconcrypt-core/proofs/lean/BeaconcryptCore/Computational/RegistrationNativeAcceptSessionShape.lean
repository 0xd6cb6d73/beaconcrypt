-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationServerSdkSource

/-! Actual SDK acceptance can append exactly one session and returns that append position. Authentication and agreement retain the entire earlier session roster on every outcome. These source facts support transcript uniqueness without a parser-injectivity or session-eligibility assumption. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeAcceptSessionShape
private abbrev PeerMetadata := Std.Array U8 151#usize
open PqxdhServerAuthExperiment (Setup Codec Checks)
open RegistrationServerFrontendCompiler (State)
variable {n : Nat} {ι KemSK Reader Response : Type} {base : OracleSpec ι}

/-- Failure preserves the roster; success appends one actual capability and returns its fresh position. -/
def Shape (before : List (Option peer.ConsumedRegistration)) (reply : RustM (Option Nat))
    (after : List (Option peer.ConsumedRegistration)) : Prop :=
  (after = before ∧ ∀ handle, reply ≠ .ok (some handle)) ∨
    ∃ token, after = before ++ [some token] ∧ reply = .ok (some before.length)

theorem retain (created : PqxdhLiveServerConstruction.Created PeerMetadata)
    (accepted : agreement.ServerAgreement) (before after : State n) (reply : RustM (Option Nat))
    (supported : (reply, after) ∈ support ((RegistrationServerNativeSource.retain created accepted).run before)) :
    Shape before.sessions reply after.sessions := by
  simp only [RegistrationServerNativeSource.retain, RegistrationServerNativeSource.sourceStep,
    RegistrationWorldServerFrontend.retain, RegistrationServerFrontendCompiler.restore, StateT.run] at supported
  cases consumed : RegistrationReplaySchedule.consume accepted before.consumed with
  | fail error | div =>
      simp only [consumed, map_pure, mem_support_pure_iff] at supported
      cases supported
      exact Or.inl ⟨rfl, fun handle impossible => by cases impossible⟩
  | ok pair =>
      rcases pair with ⟨entry, history⟩
      cases entry with
      | none =>
          simp only [consumed, map_pure, mem_support_pure_iff] at supported
          cases supported
          exact Or.inl ⟨rfl, fun handle impossible => by cases impossible⟩
      | some token =>
          simp only [consumed, map_pure, mem_support_pure_iff] at supported
          cases supported
          exact Or.inr ⟨token, rfl, rfl⟩

theorem authenticate (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (created : PqxdhLiveServerConstruction.Created PeerMetadata)
    (packet : registration.InitPacket) (before after : State n)
    (reply : RustM (List BeaconcryptCore.Refinement.RegistrationAuthenticationFlow.Event × registration.InitAuthentication)) :
    (reply, after) ∈ support
      ((RegistrationServerNativeSource.authenticate setup codec route verify created packet).run before) →
    after.sessions = before.sessions := by
  simp only [RegistrationServerNativeSource.authenticate, RegistrationServerNativeSource.sourceStep,
    RegistrationWorldServerFrontend.authenticate, StateT.run, support_map]
  rintro ⟨result, ⟨actual, _, rfl⟩, same⟩
  exact (congrArg (fun pair => pair.2.sessions) same).symm

theorem agree (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created PeerMetadata)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (before after : State n) (reply : RustM agreement.AgreementEffect)
    (supported : (reply, after) ∈ support
      ((RegistrationServerNativeSource.agree setup checks representation created packet authenticated).run before)) :
    after.sessions = before.sessions := by
  simp only [RegistrationServerNativeSource.agree, StateT.run, support_map] at supported
  obtain ⟨result, _reached, same⟩ := supported
  cases same
  rfl

theorem afterAuthentication (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created PeerMetadata)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (before after : State n) (reply : RustM (Option Nat)) :
    (reply, after) ∈ support
      ((RegistrationServerSdkSource.afterAuthentication setup checks representation created packet authenticated).run before) →
    Shape before.sessions reply after.sessions := by
  unfold RegistrationServerSdkSource.afterAuthentication
  simp only [StateT.run]
  by_cases replay : before.consumed.contains (RegistrationReplaySchedule.identifier authenticated) = true
  · simp only [replay, ite_true, mem_support_pure_iff, Prod.mk.injEq]
    rintro ⟨rfl, rfl⟩
    exact Or.inl ⟨rfl, fun handle impossible => by cases impossible⟩
  · by_cases reserved : checks.reserveRegistration = true
    · simp only [replay, reserved, Bool.false_eq_true, ite_false, ite_true,
        mem_support_bind_iff]
      rintro ⟨⟨completed, middle⟩, called, continued⟩
      have same := agree setup checks representation created packet authenticated before middle completed called
      cases completed with
      | fail error | div =>
          simp only [mem_support_pure_iff, Prod.mk.injEq] at continued
          obtain ⟨rfl, rfl⟩ := continued
          exact Or.inl ⟨same, fun handle impossible => by cases impossible⟩
      | ok effect =>
          cases effect with
          | ServerComplete token =>
              have shaped := retain created token middle after reply continued
              simpa only [same] using shaped
          | _ =>
              simp only [mem_support_pure_iff, Prod.mk.injEq] at continued
              obtain ⟨rfl, rfl⟩ := continued
              exact Or.inl ⟨same, fun handle impossible => by cases impossible⟩
    · simp only [replay, reserved, Bool.false_eq_true, ite_false, mem_support_pure_iff, Prod.mk.injEq]
      rintro ⟨rfl, rfl⟩
      exact Or.inl ⟨rfl, fun handle impossible => by cases impossible⟩

attribute [local irreducible] RegistrationServerNativeSource.authenticate

theorem accept (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created PeerMetadata)
    (packet : registration.InitPacket) (before after : State n) (reply : RustM (Option Nat)) :
    (reply, after) ∈ support
      ((RegistrationServerSdkSource.accept setup codec checks route verify representation created packet).run before) →
    Shape before.sessions reply after.sessions := by
  unfold RegistrationServerSdkSource.accept
  simp only [StateT.run_bind, mem_support_bind_iff]
  rintro ⟨⟨checked, middle⟩, _, continued⟩
  have same : middle.sessions = before.sessions :=
    authenticate setup codec route verify created packet before middle checked (by assumption)
  cases checked with
  | fail error | div =>
      simp only [StateT.run_pure, mem_support_pure_iff, Prod.mk.injEq] at continued
      obtain ⟨rfl, rfl⟩ := continued
      exact Or.inl ⟨same, fun handle impossible => by cases impossible⟩
  | ok pair =>
      rcases pair with ⟨events, verdict⟩
      cases verdict with
      | Accepted authenticated =>
          have shaped := afterAuthentication setup checks representation created packet authenticated middle after reply continued
          simpa only [same] using shaped
      | _ =>
          simp only [StateT.run_pure, mem_support_pure_iff, Prod.mk.injEq] at continued
          obtain ⟨rfl, rfl⟩ := continued
          exact Or.inl ⟨same, fun handle impossible => by cases impossible⟩

attribute [local irreducible] RegistrationServerSdkSource.accept

/-- Actual successful acceptance returns the fresh append position and increases the roster length exactly once. -/
theorem success (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created PeerMetadata)
    (packet : registration.InitPacket) (before after : State n) (handle : Nat) :
    (.ok (some handle), after) ∈ support
      ((RegistrationServerSdkSource.accept setup codec checks route verify representation created packet).run before) →
    handle = before.sessions.length ∧ after.sessions.length = before.sessions.length + 1 := by
  intro _
  have shaped := accept setup codec checks route verify representation created packet before after (.ok (some handle)) (by assumption)
  rcases shaped with ⟨_same, impossible⟩ | ⟨token, appended, returned⟩
  · exact (impossible handle rfl).elim
  · simp only [RustM.ok.injEq, Option.some.injEq] at returned
    exact ⟨returned, by simp only [appended, List.length_append, List.length_singleton]⟩

end BeaconcryptCore.Computational.RegistrationNativeAcceptSessionShape

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeAcceptSessionShape.retain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeAcceptSessionShape.retain

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeAcceptSessionShape.authenticate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeAcceptSessionShape.authenticate

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeAcceptSessionShape.agree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeAcceptSessionShape.agree

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeAcceptSessionShape.afterAuthentication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeAcceptSessionShape.afterAuthentication

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeAcceptSessionShape.accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeAcceptSessionShape.accept

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeAcceptSessionShape.success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeAcceptSessionShape.success
