-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicationProject
import BeaconcryptCore.Computational.RegistrationNativePlatformHashReceipt
import BeaconcryptCore.Computational.RegistrationNativePlatformInitTupleCache
import BeaconcryptCore.Computational.RegistrationNativeMldsaRoleFrame

/-! Actual source Init publication preserves the complete Server-role signing subsequence through every crypto, recursive Ed, and terminal writer outcome. Only Beacon-role unsigned payloads are submitted; no key-byte distinctness or successful publication is assumed. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicationRole
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeBeaconFrontend (Owner M)
open RegistrationNativeMldsaShared (Local lower project)
open RegistrationNativeMldsaRoleFrame (serverReceipts)
open RegistrationNativeMldsaRoleSyntax (BeaconRole)
open RegistrationNativePlatformBeaconPublication
variable {n : Nat} {E Platform V W Encoded ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
private abbrev PWork (V : Type) := StateT RegistrationSigningShared.State (StateT Platform ProbComp) V
private def Keeps (work : PWork (Platform := Platform) V) : Prop :=
  ∀ before previous result, result ∈ support ((work.run before).run previous) → serverReceipts result.1.2.1 = serverReceipts before.1
private theorem pure_keeps (value : V) : Keeps (pure value : PWork (Platform := Platform) V) := by
  intro before previous result supported
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  rfl
private theorem bind_keeps (work : PWork (Platform := Platform) V)
    (next : V → PWork (Platform := Platform) W)
    (first : Keeps work) (rest : ∀ value, Keeps (next value)) : Keeps (work >>= next) := by
  intro before previous result supported
  simp only [StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, called, continued⟩ := supported
  exact (rest middle.1.1 middle.1.2 middle.2 result continued).trans (first before previous middle called)

private theorem continue_keeps {Input : Type} (action : RustM Input)
    (next : Input → PWork (Platform := Platform) (RustM (RegistrationBeaconInitExecutor.Result Encoded)))
    (law : ∀ value, Keeps (next value)) : Keeps (continueWith action next) := by
  cases action with
  | fail error | div => exact pure_keeps _
  | ok value => exact law value
private theorem ready_keeps (encode : registration.SignedInitView → PWork (Platform := Platform) (RustM (core.option.Option Encoded)))
    (law : ∀ view, Keeps (encode view)) (pending : registration.BeaconInitReady) : Keeps (ready encode pending) := by
  unfold ready
  exact continue_keeps _ _ fun view => bind_keeps _ _ (law view) fun _ => pure_keeps _
private theorem signing_keeps (impl : QueryImpl RegistrationBeaconInitExecutor.Spec (PWork (Platform := Platform)))
    (encode : registration.SignedInitView → PWork (Platform := Platform) (RustM (core.option.Option Encoded)))
    (queries : ∀ query, BeaconRole query → Keeps (impl query)) (encoding : ∀ view, Keeps (encode view))
    (payload : MldsaTranscriptAuth.Payload) (digest : CtxRomAuth.CtxDigest) (pending : registration.BeaconMldsaSigning) (role : payload.role = .beacon) :
    Keeps (fromSigning impl encode payload digest pending) := by
  unfold fromSigning
  apply continue_keeps _ _
  intro request
  apply bind_keeps _ _ (queries (.inl (.sign request payload digest)) role)
  intro signature
  apply continue_keeps _ _
  intro effect
  cases effect <;> first | exact pure_keeps _ | exact ready_keeps encode encoding _
private theorem hash_keeps (impl : QueryImpl RegistrationBeaconInitExecutor.Spec (PWork (Platform := Platform)))
    (encode : registration.SignedInitView → PWork (Platform := Platform) (RustM (core.option.Option Encoded)))
    (queries : ∀ query, BeaconRole query → Keeps (impl query)) (encoding : ∀ view, Keeps (encode view))
    (pending : registration.BeaconInitHash) : Keeps (fromHash impl encode pending) := by
  unfold fromHash
  apply continue_keeps _ _
  intro request
  apply bind_keeps _ _ (queries (.inl (.hash request)) trivial)
  intro digest
  apply continue_keeps _ _
  intro effect
  cases effect <;> first | exact pure_keeps _ | exact signing_keeps impl encode queries encoding _ _ _ rfl
private theorem fingerprint_keeps (impl : QueryImpl RegistrationBeaconInitExecutor.Spec (PWork (Platform := Platform)))
    (encode : registration.SignedInitView → PWork (Platform := Platform) (RustM (core.option.Option Encoded)))
    (queries : ∀ query, BeaconRole query → Keeps (impl query)) (encoding : ∀ view, Keeps (encode view))
    (pending : registration.BeaconFingerprint) : Keeps (fromFingerprint impl encode pending) := by
  unfold fromFingerprint
  apply continue_keeps _ _
  intro request
  apply bind_keeps _ _ (queries (.inl (.hash request)) trivial)
  intro digest
  apply continue_keeps _ _
  intro effect
  cases effect <;> first | exact pure_keeps _ | exact hash_keeps impl encode queries encoding _
private theorem ed_keeps (impl : QueryImpl RegistrationBeaconInitExecutor.Spec (PWork (Platform := Platform)))
    (encode : registration.SignedInitView → PWork (Platform := Platform) (RustM (core.option.Option Encoded)))
    (queries : ∀ query, BeaconRole query → Keeps (impl query)) (encoding : ∀ view, Keeps (encode view))
    (pending : registration.BeaconEd25519Signing) : Keeps (fromEd impl encode pending) := by
  rw [fromEd.eq_def]
  apply continue_keeps _ _
  intro request
  apply bind_keeps _ _ (queries (.inr request) trivial)
  intro reply
  cases resumed : pending.resume reply with
  | fail error | div => exact pure_keeps _
  | ok effect => cases effect with
    | Rejected previous => exact pure_keeps _
    | Ed25519SigningRequested next => exact ed_keeps impl encode queries encoding next
    | FingerprintRequested selected => exact fingerprint_keeps impl encode queries encoding selected
    | _ => exact pure_keeps _
termination_by RegistrationBeaconInitExecutor.edRank pending
decreasing_by exact RegistrationBeaconInitExecutor.ed_rank pending reply next resumed

/-- Every actual source publication stage preserves owner metadata under arbitrary crypto/writer replies, including failure and recursive Ed-signing stages. -/
private theorem publication (impl : QueryImpl RegistrationBeaconInitExecutor.Spec (PWork (Platform := Platform)))
    (encode : registration.SignedInitView → PWork (Platform := Platform) (RustM (core.option.Option Encoded)))
    (queries : ∀ query, BeaconRole query → Keeps (impl query)) (encoding : ∀ view, Keeps (encode view))
    (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin) (mldsa : Std.Array U8 1952#usize) :
    Keeps (begin impl encode control inputs coins pin mldsa) := by
  unfold begin
  apply continue_keeps _ _
  intro effect
  cases effect <;> first | exact pure_keeps _ | exact ed_keeps impl encode queries encoding _

private theorem shared_query (setup : Setup base KemSK) (owner : Owner source)
    (query : RegistrationBeaconInitExecutor.Spec.Domain) (allowed : BeaconRole query)
    (before : RegistrationSigningShared.State)
    (result : RegistrationBeaconInitExecutor.Spec.Range query × RegistrationSigningShared.State)
    (supported : result ∈ support ((RegistrationNativeMldsaShared.implementation setup owner query).run before)) :
    serverReceipts result.2.1 = serverReceipts before.1 := by
  cases query with
  | inl query => cases query with
    | hash request =>
        simp only [RegistrationNativeMldsaShared.implementation, RegistrationSigningShared.implementation,
          MldsaSharedNative.authentication, StateT.run, support_map] at supported
        obtain ⟨inner, _queried, same⟩ := supported
        cases same
        rfl
    | sign request payload digest =>
        change payload.role = .beacon at allowed
        simp only [RegistrationNativeMldsaShared.implementation, RegistrationSigningShared.implementation, StateT.run, support_map] at supported
        obtain ⟨reply, _signed, same⟩ := supported
        cases same
        simp [serverReceipts, allowed]
  | inr request =>
      simp only [RegistrationNativeMldsaShared.implementation, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      cases supported
      rfl

private theorem query_keeps (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (owner : Owner source)
    (query : RegistrationBeaconInitExecutor.Spec.Domain) (allowed : BeaconRole query) :
    Keeps (RegistrationNativePlatformPublicationProject.shared coins setup owner query) := by
  intro before previous result supported
  exact shared_query setup owner query allowed before result.1
    (RegistrationNativePlatformHashReceipt.native_support coins _ _ previous result.2 supported)

private theorem encoding_keeps (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (view : registration.SignedInitView) :
    Keeps (StateT.lift (RegistrationNativePlatformPublicationProject.encode writer view)) := by
  intro before previous result supported
  simp only [StateT.run_lift, bind_pure_comp, StateT.run_map, support_map] at supported
  obtain ⟨inner, _called, same⟩ := supported
  exact (congrArg (fun value => serverReceipts value.1.2.1) same).symm

/-- Every actual shared source Init publication retains the literal Server-role receipt subsequence under all admitted crypto/writer replies. -/
theorem shared (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (owner : Owner source)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (scalar : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin) (mldsa : Std.Array U8 1952#usize)
    (before : RegistrationSigningShared.State) (previous : Platform)
    (result : (RustM (RegistrationBeaconInitExecutor.Result (alloc.vec.Vec U8)) × RegistrationSigningShared.State) × Platform)
    (supported : result ∈ support (((begin (RegistrationNativePlatformPublicationProject.shared coins setup owner)
      (fun view => StateT.lift (RegistrationNativePlatformPublicationProject.encode writer view)) control inputs scalar pin mldsa).run before).run previous)) :
    serverReceipts result.1.2.1 = serverReceipts before.1 :=
  publication _ _ (query_keeps coins setup owner) (encoding_keeps writer) _ _ _ _ _ before previous result supported

/-- Literal complete source Init publication preserves its actual Local Server-role receipt subsequence, including failed terminal writers. -/
theorem outgoing (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (checks : Checks) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (index : Nat) (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (before after : Local n KemSK source) (previous next : Platform)
    (reply : RustM (RegistrationBeaconInitExecutor.Result (alloc.vec.Vec U8)))
    (supported : ((reply, after), next) ∈ support
      (((RegistrationNativePlatformInitTupleCache.program coins setup checks representation created writer index owner oneTime).run before).run previous)) :
    serverReceipts (project after).1 = serverReceipts (project before).1 := by
  have same := RegistrationNativePlatformPublicationProject.begin_project coins setup checks representation created writer index owner
    ⟨owner.pin.binding⟩ (RegistrationNativeBeaconFrontend.inputs setup owner)
    ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime)⟩ owner.pin owner.mldsa.publicKey before previous
  have projected : (reply, (project after, next)) ∈ support
      ((RegistrationNativePlatformPackedState.pack (begin (RegistrationNativePlatformPublicationProject.shared coins setup owner)
        (fun view => StateT.lift (RegistrationNativePlatformPublicationProject.encode writer view))
        ⟨owner.pin.binding⟩ (RegistrationNativeBeaconFrontend.inputs setup owner)
        ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime)⟩ owner.pin owner.mldsa.publicKey)).run (project before, previous)) := by
    rw [← same, support_map]
    refine ⟨(reply, (after, next)), ?_, rfl⟩
    change (reply, (after, next)) ∈ support
      ((fun result => (result.1.1, (result.1.2, result.2))) <$>
        ((RegistrationNativePlatformInitTupleCache.program coins setup checks representation created writer index owner oneTime).run before).run previous)
    rw [support_map]
    exact ⟨((reply, after), next), supported, rfl⟩
  simp only [RegistrationNativePlatformPackedState.pack, StateT.run, support_map] at projected
  obtain ⟨⟨⟨value, state⟩, platform⟩, called, equal⟩ := projected
  cases equal
  exact shared coins setup owner writer _ _ _ _ _ (project before) previous _ called

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicationRole

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicationRole.shared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicationRole.shared

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicationRole.outgoing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicationRole.outgoing
