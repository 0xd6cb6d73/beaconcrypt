-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityOriginalCausalInitialized
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedCutProbability
/-! The actual initialized original issued event has a finite i/a/b cover on its SAME source game. Original creation bounds derive final handle eligibility, including later-created aliases. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityIssuedOriginalFinite
variable {Value : Type}
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
variable {n : Nat} {I KemSK Platform E : Type} {base : OracleSpec I}
variable (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (CoreModels.core.result.Result Unit E)) (erased : beaconcrypt_core.commitment.CommitmentTranscript)
variable (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))

variable (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : Aeneas.Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (previous : Platform)



open RegistrationNativeIdentityUnissuedOriginalCore (Original Observation original project PoolEvent)

variable (initial : RegistrationNativeExperiment.Initial n KemSK source)
local notation "actual" => RegistrationNativeIdentityUnissuedOriginalCore.original setup checks wire route representation view failure allocation
  reserveRegistration reservePeer reserveFrame erased helper writer source bounds mode adversary previous initial

/-- The literal original Respects bound controls every final generated source row; no final-owner count shortcut is used. -/
theorem pool_bound (budget : PqxdhDeploymentInterface.Budget)
    (bounded : RegistrationNativeInterface.Respects budget (adversary initial.public))
    (result : Original n KemSK Platform Value source) (supported : result ∈ support actual) :
    result.2.2.1.2.1.seeds.length ≤ budget.create+1 := by
  have same := RegistrationNativeIdentityUnissuedOriginalMarginal.marginal setup checks wire route representation view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer source bounds mode adversary previous initial budget bounded
  have image : project source result ∈ support (project source <$> actual) := by
    rw [support_map]
    exact ⟨result,supported,rfl⟩
  rw [support_eq_of_evalDistEq same,support_map] at image
  obtain ⟨family,reached,projection⟩ := image
  have capacity := RegistrationNativePlatformIdentityCtxFamily.capacity setup.joint (budget.create+1) _ _ family reached
  have lengthEq := congrArg (fun result => result.2.1.seeds.length) projection
  change (PqxdhDynamicIdentityRouting.sourceState family.1 family.2.2.1).seeds.length=result.2.2.1.2.1.seeds.length at lengthEq
  rw [PqxdhDynamicIdentityRouting.sourceState_length _ _ capacity] at lengthEq
  exact lengthEq ▸ capacity

omit initial in
def At (budget : PqxdhDeploymentInterface.Budget) (identity : Fin (budget.create+1)) (accept : Fin budget.accept) (bundle : Fin budget.bundle)
    (result : Option (Original n KemSK Platform Value source)) : Prop :=
  result.elim False (fun result => RegistrationNativeIdentityCensorIssuedCutProbability.At setup.joint
    (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) budget identity.val accept.val bundle.val
      ((result.1,result.2.1),(result.2.2.1,result.2.2.2)))

omit initial in
def Any (budget : PqxdhDeploymentInterface.Budget) (result : Option (Original n KemSK Platform Value source)) : Prop :=
  ∃ identity : Fin (budget.create+1),∃ accept : Fin budget.accept,∃ bundle : Fin budget.bundle,At setup wire source budget identity accept bundle result

local notation "game" => RegistrationNativeIdentityUnissuedOriginalInitialized.game (n := n) setup checks wire route representation view failure allocation
  reserveRegistration reservePeer reserveFrame erased helper writer source ensureInit identityIndex serverKeyId bounds mode adversary previous

omit initial in
/-- Every original initialized issued witness selects finite public i/a/b coordinates from its own actual generated row and original chronology. -/
theorem cover (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publication,RegistrationNativeInterface.Respects budget (adversary publication))
    (result : Option (Original n KemSK Platform Value source)) (supported : result ∈ support game)
    (failed : RegistrationNativeIdentityOriginalCausalInitialized.Issued setup wire source budget result) : Any setup wire source budget result := by
  simp only [RegistrationNativeIdentityUnissuedOriginalInitialized.game,mem_support_bind_iff] at supported
  obtain ⟨initialized,_startup,called⟩ := supported
  cases initialized with
  | none =>
    simp only [mem_support_pure_iff] at called
    cases called
    cases failed
  | some initial =>
    rw [support_map] at called
    obtain ⟨finished,reached,rfl⟩ := called
    obtain ⟨attempt,⟨issued⟩⟩ := failed
    let frontend := RegistrationNativePlatformIdentityCtxTyped.handler (n := n) setup checks wire route representation initial.created initial.credential
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
    let handler := RegistrationNativePlatformIdentityCtxSigningSource.typedHandler setup.joint frontend
    unfold RegistrationNativeIdentityUnissuedOriginalCore.original at reached
    have path := RegistrationNativeFullRegistrationJournal.path setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)
      initial.created.server.server.metadata.sender bounds handler mode (adversary initial.public) _ finished reached
    have good := RegistrationNativePlatformIdentityCtxKeyJournal.path_good setup checks wire route representation initial.created initial.credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer path
      ⟨RegistrationNativePlatformIdentityCtxInitial.initial_owned setup.joint initial previous _,by exact List.nodup_nil⟩
    obtain ⟨seed,row,_identity⟩ := good.1 attempt.finalOwner (List.mem_of_getElem? attempt.finalFound)
    have within := (List.getElem?_eq_some_iff.mp row).1
    have capacity := pool_bound setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      source bounds mode adversary previous initial budget (bounded initial.public) finished reached
    refine ⟨⟨attempt.finalOwner.identity.handle,lt_of_lt_of_le within capacity⟩,
      RegistrationNativePlatformIdentityCtxFiniteCover.acceptanceOrdinal attempt,
      RegistrationNativePlatformIdentityCtxFiniteCover.bundleOrdinal issued.cut,attempt,rfl,rfl,issued,rfl⟩

omit initial in
/-- All coordinates are unioned on the original unchanged initialized source distribution, preserving failed parsed accepts and every attempted bundle. -/
theorem finite_union (budget : PqxdhDeploymentInterface.Budget) :
    Pr{let result ← game}[Any setup wire source budget result] ≤
      ∑ identity : Fin (budget.create+1),∑ accept : Fin budget.accept,∑ bundle : Fin budget.bundle,
        Pr{let result ← game}[At setup wire source budget identity accept bundle result] := by
  have identities := prEvent_exists_le game (fun identity : Fin (budget.create+1) => fun result =>
    ∃ accept : Fin budget.accept,∃ bundle : Fin budget.bundle,At setup wire source budget identity accept bundle result)
  apply identities.trans
  apply Finset.sum_le_sum
  intro identity _identity
  have positions := prEvent_exists_le game (fun accept : Fin budget.accept => fun result =>
    ∃ bundle : Fin budget.bundle,At setup wire source budget identity accept bundle result)
  apply positions.trans
  exact Finset.sum_le_sum (fun accept _accept => prEvent_exists_le game
    (fun bundle : Fin budget.bundle => fun result => At setup wire source budget identity accept bundle result))

omit initial in
/-- Original initialized issued-event mass pays only the finite same-run generated-handle/accept/bundle family. -/
theorem bound (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publication,RegistrationNativeInterface.Respects budget (adversary publication)) :
    Pr{let result ← game}[RegistrationNativeIdentityOriginalCausalInitialized.Issued setup wire source budget result] ≤
      ∑ identity : Fin (budget.create+1),∑ accept : Fin budget.accept,∑ bundle : Fin budget.bundle,
        Pr{let result ← game}[At setup wire source budget identity accept bundle result] := by
  apply le_trans (b := Pr{let result ← game}[Any setup wire source budget result])
  · apply prEvent_mono_of_support
    exact cover setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      source ensureInit identityIndex serverKeyId bounds mode adversary previous budget bounded
  · exact finite_union setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      source ensureInit identityIndex serverKeyId bounds mode adversary previous budget

omit initial in
noncomputable def cutGame (bundle : Nat) : ProbComp (Option
    (RegistrationNativeIdentityCensorIssuedCutProbability.Stopped (n := n) (KemSK := KemSK) (Platform := Platform) (source := source)
      (A := Value × RegistrationNativeLedger.State) ×
     RegistrationNativeIdentityCensorIssuedCutProbability.Result (n := n) (KemSK := KemSK) (Platform := Platform) (source := source)
      (A := Value × RegistrationNativeLedger.State))) := do
  let initialized ← RegistrationNativeExperiment.start (n := n) setup source ensureInit identityIndex serverKeyId
  match initialized with
  | none => pure none
  | some initial =>
      let frontend := RegistrationNativePlatformIdentityCtxTyped.handler (n := n) setup checks wire route representation initial.created initial.credential
        view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      let compiled := RegistrationNativeFullCompiler.compile setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)
        initial.created.server.server.metadata.sender bounds mode (adversary initial.public)
      some <$> RegistrationNativeIdentityCensorIssuedCutProbability.coupled setup.joint frontend bundle compiled
        (((RegistrationNativeIdentityMainProfile.fromInitial initial,previous),{}),
          (PqxdhDynamicIdentityPool.initialState,(RegistrationNativeWorldCache.cache initial.state,[PqxdhRefinement.absBytes initial.credential.publicKey])))

omit initial in
def Matched (budget : PqxdhDeploymentInterface.Budget) (identity : Fin (budget.create+1)) (accept : Fin budget.accept) (bundle : Fin budget.bundle)
    (result : Option
      (RegistrationNativeIdentityCensorIssuedCutProbability.Stopped (n := n) (KemSK := KemSK) (Platform := Platform) (source := source)
        (A := Value × RegistrationNativeLedger.State) ×
       RegistrationNativeIdentityCensorIssuedCutProbability.Result (n := n) (KemSK := KemSK) (Platform := Platform) (source := source)
        (A := Value × RegistrationNativeLedger.State))) : Prop :=
  result.elim False (RegistrationNativeIdentityCensorIssuedCutProbability.Matched setup.joint
    (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) budget identity.val accept.val bundle.val)

omit initial in
/-- Independent literal startup transports each original finite event to its SAME actual before-b cutoff and complete retained suffix. -/
theorem cut_probability (budget : PqxdhDeploymentInterface.Budget)
    (identity : Fin (budget.create+1)) (accept : Fin budget.accept) (bundle : Fin budget.bundle) :
    Pr{let result ← game}[At setup wire source budget identity accept bundle result] =
      Pr{let result ← (cutGame (n := n) setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
        source ensureInit identityIndex serverKeyId bounds mode adversary previous bundle.val)}[Matched setup wire source budget identity accept bundle result] := by
  classical
  unfold RegistrationNativeIdentityUnissuedOriginalInitialized.game cutGame
  apply prEvent_bind_congr
  intro initialized
  cases initialized with
  | none =>
    rw [prEvent_pure,prEvent_pure]
    rfl
  | some initial =>
    simp only [prEvent_map,At,Matched,Option.elim_some]
    unfold RegistrationNativeIdentityUnissuedOriginalCore.original
    rw [RegistrationNativeFullCompiler.compile_run,prEvent_map]
    exact RegistrationNativeIdentityCensorIssuedCutProbability.probability setup.joint
      (RegistrationNativePlatformIdentityCtxTyped.handler (n := n) setup checks wire route representation initial.created initial.credential
        view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer)
      bundle.val (RegistrationNativeFullCompiler.compile setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)
        initial.created.server.server.metadata.sender bounds mode (adversary initial.public))
      (((RegistrationNativeIdentityMainProfile.fromInitial initial,previous),{}),
        (PqxdhDynamicIdentityPool.initialState,(RegistrationNativeWorldCache.cache initial.state,[PqxdhRefinement.absBytes initial.credential.publicKey])))
      rfl (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) budget identity.val accept.val

omit initial in
/-- The actual original initialized Issued mass is bounded by a finite family of exact same-cut/whole-suffix events. -/
theorem cut_bound (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publication,RegistrationNativeInterface.Respects budget (adversary publication)) :
    Pr{let result ← game}[RegistrationNativeIdentityOriginalCausalInitialized.Issued setup wire source budget result] ≤
      ∑ identity : Fin (budget.create+1),∑ accept : Fin budget.accept,∑ bundle : Fin budget.bundle,
        Pr{let result ← (cutGame (n := n) setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
          source ensureInit identityIndex serverKeyId bounds mode adversary previous bundle.val)}[Matched setup wire source budget identity accept bundle result] := by
  apply (bound setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
    source ensureInit identityIndex serverKeyId bounds mode adversary previous budget bounded).trans
  apply Finset.sum_le_sum
  intro identity _identity
  apply Finset.sum_le_sum
  intro accept _accept
  apply Finset.sum_le_sum
  intro bundle _bundle
  exact (cut_probability setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
    source ensureInit identityIndex serverKeyId bounds mode adversary previous budget identity accept bundle).le

end BeaconcryptCore.Computational.RegistrationNativeIdentityIssuedOriginalFinite
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityIssuedOriginalFinite.pool_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityIssuedOriginalFinite.pool_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityIssuedOriginalFinite.cover' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityIssuedOriginalFinite.cover
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityIssuedOriginalFinite.finite_union' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityIssuedOriginalFinite.finite_union
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityIssuedOriginalFinite.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityIssuedOriginalFinite.bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityIssuedOriginalFinite.cut_probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityIssuedOriginalFinite.cut_probability
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityIssuedOriginalFinite.cut_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityIssuedOriginalFinite.cut_bound
