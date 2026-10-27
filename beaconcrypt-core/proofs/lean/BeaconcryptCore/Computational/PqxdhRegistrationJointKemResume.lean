-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointKemChallenge

/-! Resume the exact initialized source cut using the ordinary CCA challenge reply. Inactive cuts retain their complete saved context, and active cuts retain both the optional source result and the full reached joint/KEM histories. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointKemResume
open PqxdhKemIndCca PqxdhRegistrationJointKemChallenge PqxdhRegistrationJointKemCommands
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK A Result : Type}

/-- Inactive selection and a later reveal stop remain distinct; the original whole cut is retained in either case. -/
abbrev ResultState (KemSK A Result : Type) (count : Nat) :=
  Context KemSK A Result count × Option (Option (Outcome KemSK Result) × PqxdhDynamicKemJointSource.State KemSK)

/-- A challenge becomes exactly the source encapsulator's ciphertext and 32-byte shared-secret reply. -/
def reply (ciphertext : MlKem768Ciphertext) (candidate : MlKemSharedSecret) : PqxdhRegistrationJointKemCut.Reply :=
  some (PqxdhAcceptedRegistration.ciphertextArray ciphertext, PqxdhRootTableInitialization.rootArray candidate)

/-- The executable continuation uses no selected secret. Only a pending original encapsulation whose actual requested key equals the challenger key is resumed; other cases retain the entire context as inactive. -/
noncomputable def post (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (count : Nat) (selected : Fin (count + 1))
    (transcript : MlKemChallengeTranscript (Context KemSK A Result count)) (candidate : MlKemSharedSecret) :
    OracleComp (MlKemCCAOracleSpec baseSpec) (ResultState KemSK A Result count) := do
  match transcript.context with
  | .ready _ others (some (.pending request next)) state _ =>
    if request.2 = transcript.publicKey then
      let reached ← (((simulateQ (PqxdhDynamicKemJointRouter.post setup.joint setup.kem selected.val
        (PqxdhDynamicKemRouter.selectedReservation selected transcript.publicKey others)
        transcript.ciphertext candidate)
        (simulateQ (PqxdhRegistrationJointKemEncapsulation.actual setup)
          (next (reply transcript.ciphertext candidate)))).run).run state)
      pure (transcript.context, some reached)
    else pure (transcript.context, none)
  | _ => pure (transcript.context, none)

/-- Mathematical real-source resumption uses the original selected pair only inside the stopped source interpreter. -/
noncomputable def sourcePost (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (count : Nat) (selected : Fin (count + 1)) (chosen : MlKem768PublicKey × KemSK)
    (transcript : MlKemChallengeTranscript (Context KemSK A Result count)) (candidate : MlKemSharedSecret) :
    ProbComp (ResultState KemSK A Result count) := do
  match transcript.context with
  | .ready _ others (some (.pending request next)) state _ =>
    if request.2 = transcript.publicKey then
      let reached ← (((simulateQ (PqxdhDynamicKemJointRouter.stopped setup.baseImpl setup.joint setup.kem selected.val
        (List.ofFn (selected.insertNth chosen others)))
        (simulateQ (PqxdhRegistrationJointKemEncapsulation.actual setup)
          (next (reply transcript.ciphertext candidate)))).run).run state)
      pure (transcript.context, some reached)
    else pure (transcript.context, none)
  | _ => pure (transcript.context, none)

set_option backward.isDefEq.respectTransparency false in
/-- Under ordinary real-candidate decapsulation agreement, full postchallenge interpretation equals the same original cut resumed in the stopped source. The statement retains the cut, raw input metadata, all source results and both private histories. -/
theorem post_source (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (count : Nat) (selected : Fin (count + 1)) (chosen : MlKem768PublicKey × KemSK)
    (context : Context KemSK A Result count) (ciphertext : MlKem768Ciphertext) (candidate : MlKemSharedSecret)
    (agreement : setup.kem.decaps chosen.2 ciphertext = pure (some candidate)) :
    PqxdhDynamicKemPost.evaluate setup.baseImpl setup.kem chosen.2 ciphertext
      (post setup count selected ⟨chosen.1, ciphertext, context⟩ candidate) =
      sourcePost setup count selected chosen ⟨chosen.1, ciphertext, context⟩ candidate := by
  cases context with
  | failed state => rfl
  | ready created others cut state runtime =>
    cases cut with
    | none => rfl
    | some cut =>
      cases cut with
      | complete result => rfl
      | pending request next =>
        simp only [post, sourcePost]
        split
        · have same := PqxdhDynamicKemJointRouter.post_program setup.baseImpl setup.joint setup.kem selected.val
            (List.ofFn (selected.insertNth chosen others)) chosen.1 chosen.2
            (by simpa only [List.nil_append, List.length_nil, Nat.zero_add, Prod.mk.eta] using
              PqxdhLiveKemSelection.selected_index [] selected chosen others)
            ciphertext candidate agreement
            (simulateQ (PqxdhRegistrationJointKemEncapsulation.actual setup)
              (next (reply ciphertext candidate))) state
          rw [PqxdhDynamicKemRouter.selected_reservation] at same
          simpa only [PqxdhDynamicKemPost.evaluate, bind_pure_comp, simulateQ_map] using congrArg
            (fun work => (fun reached =>
              (Context.ready created others (some (.pending request next)) state runtime, some reached)) <$> work) same
        · rfl

/-- Ordinary recipient correctness on the actual key-generation and encapsulation supports discharges real resumption's agreement premise. No public-key injectivity or cross-key shared-secret property is used. -/
theorem supported_source (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (correct : MlKem768RecipientCorrectness setup.kem
      (PqxdhInitializerSecrecy.runtimeOfImpl (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl)))
    (count : Nat) (selected : Fin (count + 1)) (chosen : MlKem768PublicKey × KemSK)
    (generated : chosen ∈ support (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen))
    (context : Context KemSK A Result count) (ciphertext : MlKem768Ciphertext) (candidate : MlKemSharedSecret)
    (encapsulated : (ciphertext, candidate) ∈ support
      (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) (setup.kem.encaps chosen.1))) :
    PqxdhDynamicKemPost.evaluate setup.baseImpl setup.kem chosen.2 ciphertext
      (post setup count selected ⟨chosen.1, ciphertext, context⟩ candidate) =
      sourcePost setup count selected chosen ⟨chosen.1, ciphertext, context⟩ candidate :=
  post_source setup count selected chosen context ciphertext candidate
    (PqxdhChallengeSecretRouting.honest_decapsulation_program setup.baseImpl setup.kem
      functional correct generated encapsulated)

end BeaconcryptCore.Computational.PqxdhRegistrationJointKemResume

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemResume.post_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemResume.post_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemResume.supported_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemResume.supported_source
