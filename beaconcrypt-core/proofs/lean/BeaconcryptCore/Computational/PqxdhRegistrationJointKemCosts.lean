-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointKemRouting
import BeaconcryptCore.Computational.PqxdhRegistrationJointOpenUniform

/-! Actual command allowances instantiate the full selected-KEM CCA resource ledger. The open native bill covers all possible challenger replies; identity samplers, local decapsulation randomness and base callbacks are separately counted. Constructor and unselected reservation generation remain explicit prefix costs. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointKemCosts
open PqxdhKemIndCca PqxdhJointIdentity PqxdhServerAuthExperiment PqxdhServerAuthNative
open PqxdhRegistrationJointKemCommands (SourceSpec Budget program)
open PqxdhRegistrationJointKemRouting (pre post)
open PqxdhRegistrationJointGeneratedFinish (EncodedEntry)
open PqxdhDynamicKemJointSource (State)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result : Type}

/-- One source Beacon creation emits at most one generated joint identity request, regardless of failed or replaced service replies. -/
theorem identity_creations (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (client : OracleComp (SourceSpec KemSK) Result)
    (budget : Budget)
    (certified : ∀ source, client.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source))
    (owners : List EncodedEntry) (native : NativeState KemSK) :
    (program setup codec checks identityIndex publicIdentity client owners native).IsQueryBoundP
      (PqxdhDynamicKemJointBounds.IsIdentityCreate (KemSK := KemSK)) (budget (.inl 1)) := by
  have cap := PqxdhRegistrationJointOpenCosts.command_program setup codec checks identityIndex publicIdentity
    client budget certified owners native .identityCreate (by decide)
  have kinds : (PqxdhDynamicKemJointBounds.IsIdentityCreate (KemSK := KemSK)) =
      (fun query => PqxdhRegistrationJointServiceCosts.poolClass (KemSK := KemSK) query = .identityCreate) := by
    funext query
    rcases query with (coin | request) | (coin | request)
    case inl.inr =>
      cases request
      case service index call => cases call <;> simp [PqxdhDynamicKemJointBounds.IsIdentityCreate,
        PqxdhDynamicIdentityPool.IsCreate, PqxdhRegistrationJointServiceCosts.poolClass]
      all_goals simp [PqxdhDynamicKemJointBounds.IsIdentityCreate, PqxdhDynamicIdentityPool.IsCreate,
        PqxdhRegistrationJointServiceCosts.poolClass]
    case inr.inr => cases request <;> simp [PqxdhDynamicKemJointBounds.IsIdentityCreate,
      PqxdhRegistrationJointServiceCosts.poolClass]
    all_goals simp [PqxdhDynamicKemJointBounds.IsIdentityCreate, PqxdhDynamicIdentityPool.IsCreate,
      PqxdhRegistrationJointServiceCosts.poolClass]
  simpa only [program, kinds, PqxdhRegistrationJointOpenCosts.privateTotal] using cap

/-- Existing primitive resource contracts retain the CCA interpreter's direct local-decapsulation randomness class. -/
theorem local_uniform (setup : Setup baseSpec KemSK) (caps : KemCaps) (bounded : KemBound setup caps)
    (secret : KemSK) (ciphertext : MlKem768Ciphertext) :
    (setup.kem.decaps secret ciphertext).IsQueryBoundP
      (fun query => IsMlKemUniformQuery (.inl query)) caps.decapsUniform := by
  have same : (fun query : (unifSpec + baseSpec).Domain => IsMlKemUniformQuery (.inl query)) =
      PqxdhServerAuthSourceCosts.IsAmbientUniform := by
    funext query
    cases query <;> simp [IsMlKemUniformQuery, PqxdhServerAuthSourceCosts.IsAmbientUniform]
  simpa only [same] using bounded.decapsUniform secret ciphertext

/-- Complete all-reply prechallenge uniform bill: every original open native draw, every joint creation seed and all local decapsulation randomness remain charged. -/
theorem pre_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (client : OracleComp (SourceSpec KemSK) Result)
    (budget : Budget)
    (certified : ∀ source, client.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source))
    (owners : List EncodedEntry) (native : NativeState KemSK) (selected : Nat)
    (reservation : PqxdhDynamicKemRouter.Reservation KemSK) (state : State KemSK) :
    (pre setup codec checks identityIndex publicIdentity client owners native selected reservation state).IsQueryBoundP
      IsMlKemUniformQuery (32 * budget (.inl 1) + PqxdhRegistrationJointOpenUniform.total caps budget + caps.decapsUniform * budget (.inl 5)) :=
  PqxdhDynamicKemJointBounds.pre_uniform setup.joint setup.kem selected reservation
    (program setup codec checks identityIndex publicIdentity client owners native) _ _ _
    (identity_creations setup codec checks identityIndex publicIdentity client budget certified owners native)
    (PqxdhRegistrationJointOpenUniform.command_program setup codec checks caps bounded identityIndex publicIdentity client budget certified owners native)
    (PqxdhRegistrationJointKemCommands.decapsulations setup codec checks identityIndex publicIdentity client budget certified owners native)
    state caps.decapsUniform (local_uniform setup caps bounded)

/-- Postchallenge replacement keeps the same complete native/uniform bill on every typed reply. Handling the exact selected ciphertext locally adds no draw and does not remove other-key work. -/
theorem post_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (client : OracleComp (SourceSpec KemSK) Result)
    (budget : Budget)
    (certified : ∀ source, client.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source))
    (owners : List EncodedEntry) (native : NativeState KemSK) (selected : Nat)
    (reservation : PqxdhDynamicKemRouter.Reservation KemSK) (state : State KemSK)
    (challenge : MlKem768Ciphertext) (candidate : MlKemSharedSecret) :
    (post setup codec checks identityIndex publicIdentity client owners native selected reservation state challenge candidate).IsQueryBoundP
      IsMlKemUniformQuery (32 * budget (.inl 1) + PqxdhRegistrationJointOpenUniform.total caps budget + caps.decapsUniform * budget (.inl 5)) :=
  PqxdhDynamicKemJointBounds.post_uniform setup.joint setup.kem selected reservation challenge candidate
    (program setup codec checks identityIndex publicIdentity client owners native) _ _ _
    (identity_creations setup codec checks identityIndex publicIdentity client budget certified owners native)
    (PqxdhRegistrationJointOpenUniform.command_program setup codec checks caps bounded identityIndex publicIdentity client budget certified owners native)
    (PqxdhRegistrationJointKemCommands.decapsulations setup codec checks identityIndex publicIdentity client budget certified owners native)
    state caps.decapsUniform (local_uniform setup caps bounded)

/-- Local decapsulation retains every primitive base-oracle callback separately from direct uniform samples. -/
theorem local_base (setup : Setup baseSpec KemSK) (caps : KemCaps) (bounded : KemBound setup caps)
    (secret : KemSK) (ciphertext : MlKem768Ciphertext) :
    (setup.kem.decaps secret ciphertext).IsQueryBoundP
      (fun query => IsMlKemBaseQuery (.inl query)) caps.decapsBase := by
  have same : (fun query : (unifSpec + baseSpec).Domain => IsMlKemBaseQuery (.inl query)) =
      PqxdhServerAuthSourceCosts.IsAmbientBase := by
    funext query
    cases query <;> simp [IsMlKemBaseQuery, PqxdhServerAuthSourceCosts.IsAmbientBase]
  simpa only [same] using bounded.decapsBase secret ciphertext

/-- Concrete prechallenge base work is charged on every source finish attempt; local native encapsulation/base work is already included in the open uniform bill through its real interpreter. -/
theorem pre_base (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (client : OracleComp (SourceSpec KemSK) Result)
    (budget : Budget)
    (certified : ∀ source, client.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source))
    (owners : List EncodedEntry) (native : NativeState KemSK) (selected : Nat)
    (reservation : PqxdhDynamicKemRouter.Reservation KemSK) (state : State KemSK) :
    (pre setup codec checks identityIndex publicIdentity client owners native selected reservation state).IsQueryBoundP
      IsMlKemBaseQuery (caps.decapsBase * budget (.inl 5)) :=
  PqxdhDynamicKemJointBounds.pre_base setup.joint setup.kem selected reservation
    (program setup codec checks identityIndex publicIdentity client owners native) _
    (PqxdhRegistrationJointKemCommands.decapsulations setup codec checks identityIndex publicIdentity client budget certified owners native)
    state IsMlKemBaseQuery (fun _ => by simp [IsMlKemBaseQuery]) (fun _ => by simp [IsMlKemBaseQuery])
    caps.decapsBase (local_base setup caps bounded)

/-- Concrete postchallenge base work retains the same source allowance without forwarding the blocked ciphertext or omitting any other-key callback. -/
theorem post_base (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (client : OracleComp (SourceSpec KemSK) Result)
    (budget : Budget)
    (certified : ∀ source, client.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source))
    (owners : List EncodedEntry) (native : NativeState KemSK) (selected : Nat)
    (reservation : PqxdhDynamicKemRouter.Reservation KemSK) (state : State KemSK)
    (challenge : MlKem768Ciphertext) (candidate : MlKemSharedSecret) :
    (post setup codec checks identityIndex publicIdentity client owners native selected reservation state challenge candidate).IsQueryBoundP
      IsMlKemBaseQuery (caps.decapsBase * budget (.inl 5)) :=
  PqxdhDynamicKemJointBounds.post_base setup.joint setup.kem selected reservation challenge candidate
    (program setup codec checks identityIndex publicIdentity client owners native) _
    (PqxdhRegistrationJointKemCommands.decapsulations setup codec checks identityIndex publicIdentity client budget certified owners native)
    state IsMlKemBaseQuery (fun _ => by simp [IsMlKemBaseQuery]) (fun _ => by simp [IsMlKemBaseQuery])
    caps.decapsBase (local_base setup caps bounded)

end BeaconcryptCore.Computational.PqxdhRegistrationJointKemCosts

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemCosts.identity_creations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemCosts.identity_creations

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemCosts.local_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemCosts.local_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemCosts.pre_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemCosts.pre_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemCosts.post_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemCosts.post_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemCosts.local_base' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemCosts.local_base

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemCosts.pre_base' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemCosts.pre_base

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemCosts.post_base' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemCosts.post_base
