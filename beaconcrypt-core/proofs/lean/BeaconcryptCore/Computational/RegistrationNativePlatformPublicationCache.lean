-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformBundleOwnerPhase
import BeaconcryptCore.Computational.RegistrationNativeBundlePhases

/-! Actual source Init publication extends its single shared native cache through every primitive, signature and terminal writer outcome. Complete external poststates and failed prefixes are retained; no publication-success or cache-frame premise is supplied. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicationCache
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeBeaconFrontend (Owner M)
open RegistrationNativeMldsaShared (Local lower)
open RegistrationNativeWorldCache (cache)
open RegistrationNativePlatformBeaconPublication
variable {n : Nat} {E Platform V W Encoded ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
private abbrev PWork (V : Type) := StateT (Local n KemSK source) (StateT Platform ProbComp) V
private def Keeps (work : PWork (n := n) (KemSK := KemSK) (source := source) (Platform := Platform) V) : Prop :=
  ∀ before previous result, result ∈ support ((work.run before).run previous) → cache before.2.2 ≤ cache result.1.2.2.2
private theorem pure_keeps (value : V) : Keeps (pure value : PWork (n := n) (KemSK := KemSK) (source := source) (Platform := Platform) V) := by
  intro before previous result supported
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  exact le_refl _
private theorem bind_keeps (work : PWork (n := n) (KemSK := KemSK) (source := source) (Platform := Platform) V)
    (next : V → PWork (n := n) (KemSK := KemSK) (source := source) (Platform := Platform) W)
    (first : Keeps work) (rest : ∀ value, Keeps (next value)) : Keeps (work >>= next) := by
  intro before previous result supported
  simp only [StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, called, continued⟩ := supported
  exact (first before previous middle called).trans (rest middle.1.1 middle.1.2 middle.2 result continued)

private theorem continue_keeps {Input : Type} (action : RustM Input)
    (next : Input → PWork (n := n) (KemSK := KemSK) (source := source) (Platform := Platform) (RustM (RegistrationBeaconInitExecutor.Result Encoded)))
    (law : ∀ value, Keeps (next value)) : Keeps (continueWith action next) := by
  cases action with
  | fail error | div => exact pure_keeps _
  | ok value => exact law value
private theorem ready_keeps (encode : registration.InitView → PWork (n := n) (KemSK := KemSK) (source := source) (Platform := Platform) (RustM (core.option.Option Encoded)))
    (law : ∀ view, Keeps (encode view)) (pending : registration.BeaconInitReady) : Keeps (ready encode pending) := by
  unfold ready
  exact continue_keeps _ _ fun view => bind_keeps _ _ (law view) fun _ => pure_keeps _
private theorem hash_keeps (impl : QueryImpl RegistrationBeaconInitExecutor.Spec (PWork (n := n) (KemSK := KemSK) (source := source) (Platform := Platform)))
    (encode : registration.InitView → PWork (n := n) (KemSK := KemSK) (source := source) (Platform := Platform) (RustM (core.option.Option Encoded)))
    (queries : ∀ query, Keeps (impl query)) (encoding : ∀ view, Keeps (encode view))
    (pending : registration.BeaconInitHash) : Keeps (fromHash impl encode pending) := by
  unfold fromHash
  apply continue_keeps _ _
  intro request
  apply bind_keeps _ _ (queries _)
  intro digest
  apply continue_keeps _ _
  intro effect
  cases effect <;> first | exact pure_keeps _ | exact ready_keeps encode encoding _
private theorem ed_keeps (impl : QueryImpl RegistrationBeaconInitExecutor.Spec (PWork (n := n) (KemSK := KemSK) (source := source) (Platform := Platform)))
    (encode : registration.InitView → PWork (n := n) (KemSK := KemSK) (source := source) (Platform := Platform) (RustM (core.option.Option Encoded)))
    (queries : ∀ query, Keeps (impl query)) (encoding : ∀ view, Keeps (encode view))
    (pending : registration.BeaconEd25519Signing) : Keeps (fromEd impl encode pending) := by
  rw [fromEd.eq_def]
  apply continue_keeps _ _
  intro request
  apply bind_keeps _ _ (queries _)
  intro reply
  cases resumed : pending.resume reply with
  | fail error | div => exact pure_keeps _
  | ok effect => cases effect with
    | Rejected previous => exact pure_keeps _
    | Ed25519SigningRequested next => exact ed_keeps impl encode queries encoding next
    | HashRequested selected => exact hash_keeps impl encode queries encoding selected
    | _ => exact pure_keeps _
termination_by RegistrationBeaconInitExecutor.edRank pending
decreasing_by exact RegistrationBeaconInitExecutor.ed_rank pending reply next resumed

/-- Every actual source publication stage preserves owner metadata under arbitrary crypto/writer replies, including failure and recursive Ed-signing stages. -/
private theorem publication (impl : QueryImpl RegistrationBeaconInitExecutor.Spec (PWork (n := n) (KemSK := KemSK) (source := source) (Platform := Platform)))
    (encode : registration.InitView → PWork (n := n) (KemSK := KemSK) (source := source) (Platform := Platform) (RustM (core.option.Option Encoded)))
    (queries : ∀ query, Keeps (impl query)) (encoding : ∀ view, Keeps (encode view))
    (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin) :
    Keeps (begin impl encode control inputs coins pin) := by
  unfold begin
  apply continue_keeps _ _
  intro effect
  cases effect <;> first | exact pure_keeps _ | exact ed_keeps impl encode queries encoding _

private theorem outgoing_keeps (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (checks : Checks) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (index : Nat) (owner : Owner source)
    (query : RegistrationBeaconInitExecutor.Spec.Domain) :
    Keeps (RegistrationNativePlatformBundleLower.native (n := n) coins setup checks representation created
      (RegistrationNativeBeaconFrontend.outgoing setup source index owner query)) := by
  intro before previous result supported
  have actual : result.1 ∈ support ((lower setup checks representation created
      (RegistrationNativeBeaconFrontend.outgoing setup source index owner query)).run before) :=
    RegistrationNativePlatformHashReceipt.native_support coins _ _ previous result.2 supported
  exact RegistrationNativeWorldCache.localProgram setup checks representation created _ before result.1 actual

private theorem encoder_keeps
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) (view : registration.InitView) :
    Keeps (RegistrationNativePlatformInitWriterFrame.encoder (n := n) (KemSK := KemSK) (source := source) writer view) := by
  intro before previous result supported
  rw [RegistrationNativePlatformInitWriterFrame.encoder_frame] at supported
  simp only [StateT.run_lift, bind_pure_comp, StateT.run_map, support_map] at supported
  obtain ⟨inner, _called, same⟩ := supported
  cases same
  exact le_refl _

/-- Every complete actual source publication outcome retains every earlier shared native hash receipt. -/
theorem outgoing (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (checks : Checks) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (index : Nat) (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (before : Local n KemSK source) (previous : Platform)
    (result : (RustM (RegistrationBeaconInitExecutor.Result (alloc.vec.Vec U8)) × Local n KemSK source) × Platform)
    (supported : result ∈ support (((RegistrationNativePlatformInitTupleCache.program coins setup checks representation created writer index owner oneTime).run before).run previous)) :
    cache before.2.2 ≤ cache result.1.2.2.2 :=
  publication _ _ (outgoing_keeps coins setup checks representation created index owner) (encoder_keeps writer)
    _ _ _ _ before previous result supported

private theorem native_keeps (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (checks : Checks) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : M n KemSK source RegistrationServerRoleBackend.State V) :
    Keeps (RegistrationNativePlatformBundleLower.native coins setup checks representation created work) := by
  intro before previous result supported
  have actual : result.1 ∈ support ((lower setup checks representation created work).run before) :=
    RegistrationNativePlatformHashReceipt.native_support coins _ _ previous result.2 supported
  exact RegistrationNativeWorldCache.localProgram setup checks representation created work before result.1 actual

attribute [local irreducible] RegistrationNativePlatformBundleLower.native
  RegistrationNativePlatformGenericBundle.encoderWith

set_option maxHeartbeats 1000000 in
/-- The complete actual local source bundle extends its cache through selection, every failed publication and the later phase/World suffix. -/
theorem bundle (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (checks : Checks) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) (index : Nat)
    (before : Local n KemSK source) (previous : Platform)
    (result : (RustM (Option (alloc.vec.Vec U8)) × Local n KemSK source) × Platform)
    (supported : result ∈ support
      (((RegistrationNativePlatformBundleLower.bundle coins setup checks representation created
        (RegistrationNativePlatformGenericBundle.encoderWith (source := source) (Auxiliary := RegistrationServerRoleBackend.State)
          (RegistrationNativePlatformExperiment.writer (n := n) (KemSK := KemSK) (source := source) writer)) index).run before).run previous)) :
    cache before.2.2 ≤ cache result.1.2.2.2 := by
  have law : Keeps (RegistrationNativePlatformBundleLower.bundle (n := n) coins setup checks representation created
      (RegistrationNativePlatformGenericBundle.encoderWith (source := source) (Auxiliary := RegistrationServerRoleBackend.State)
        (RegistrationNativePlatformExperiment.writer (n := n) (KemSK := KemSK) (source := source) writer)) index) := by
    unfold RegistrationNativePlatformBundleLower.bundle
    apply bind_keeps _ _ (native_keeps coins setup checks representation created _)
    intro current
    cases current[index]? with
    | none => exact pure_keeps _
    | some owner =>
      dsimp only
      cases owner.phase with
      | fresh | freshWithCoins _ =>
        apply bind_keeps _ _ ?_
        · intro oneTime
          apply bind_keeps _ _ (publication _ _ (outgoing_keeps coins setup checks representation created index owner) (encoder_keeps writer) _ _ _ _)
          intro published
          cases published with
          | fail error | div => exact pure_keeps _
          | ok answer => cases answer with
            | Err previous => exact pure_keeps _
            | Ok completed =>
              apply bind_keeps _ _ (native_keeps coins setup checks representation created _)
              intro ignored
              exact bind_keeps _ _ (native_keeps coins setup checks representation created _) (fun _ => pure_keeps _)
        · first | exact pure_keeps _ | exact native_keeps coins setup checks representation created _
      | _ => exact pure_keeps _
  exact law before previous result supported

private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : A → B) (work : StateT S m A) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

/-- Literal complete native source bundle execution retains every earlier shared-cache entry on all outcomes. -/
theorem native_bundle (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (checks : Checks) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) (index : Nat)
    (before : RegistrationNativeExperiment.State n KemSK source) (previous : Platform)
    (result : (RustM (Option Pqxdh.Bytes) × RegistrationNativeExperiment.State n KemSK source) × Platform)
    (supported : result ∈ support
      (((RegistrationNativePlatformExperiment.bundle coins setup checks representation created source writer index).run before).run previous)) :
    cache before ≤ cache result.1.2 := by
  rw [← RegistrationNativePlatformBundleLower.sourceBundle_actual] at supported
  simp only [RegistrationNativePlatformBundleLower.sourceBundle, StateT.run, map_apply, support_map] at supported
  obtain ⟨⟨⟨reply, current⟩, platform⟩, called, same⟩ := supported
  cases same
  exact bundle coins setup checks representation created writer index
    (before.beacons, (RegistrationWorldAgreementCompiler.erase before.server.world, before)) previous ((reply, current), platform) called

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicationCache


/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicationCache.outgoing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicationCache.outgoing

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicationCache.bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicationCache.bundle

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicationCache.native_bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicationCache.native_bundle
