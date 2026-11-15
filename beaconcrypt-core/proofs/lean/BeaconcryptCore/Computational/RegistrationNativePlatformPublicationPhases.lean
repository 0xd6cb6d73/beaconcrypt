-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformBundleOwnerPhase
import BeaconcryptCore.Computational.RegistrationNativeBundlePhases

/-! Actual source Init publication changes attached Ed signing histories but retains every lifecycle phase. The actual terminal writer preserves all Local state while retaining arbitrary external state and every source failure. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicationPhases
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeBeaconFrontend (Owner M)
open RegistrationNativeMldsaShared (Local lower)
open RegistrationNativeBundlePhases (phases)
open RegistrationNativePlatformBeaconPublication
variable {n : Nat} {E Platform V W Encoded ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
private abbrev PWork (V : Type) := StateT (Local n KemSK source) (StateT Platform ProbComp) V
private def Keeps (work : PWork (n := n) (KemSK := KemSK) (source := source) (Platform := Platform) V) : Prop :=
  ∀ before previous result, result ∈ support ((work.run before).run previous) → phases result.1.2.1 = phases before.1
private theorem pure_keeps (value : V) : Keeps (pure value : PWork (n := n) (KemSK := KemSK) (source := source) (Platform := Platform) V) := by
  intro before previous result supported
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  rfl
private theorem bind_keeps (work : PWork (n := n) (KemSK := KemSK) (source := source) (Platform := Platform) V)
    (next : V → PWork (n := n) (KemSK := KemSK) (source := source) (Platform := Platform) W)
    (first : Keeps work) (rest : ∀ value, Keeps (next value)) : Keeps (work >>= next) := by
  intro before previous result supported
  simp only [StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, called, continued⟩ := supported
  exact (rest middle.1.1 middle.1.2 middle.2 result continued).trans (first before previous middle called)

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

private theorem native_source (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (checks : Checks) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : M n KemSK source RegistrationServerRoleBackend.State V)
    (before after : Local n KemSK source) (previous next : Platform) (value : V)
    (supported : ((value, after), next) ∈ support (((RegistrationNativePlatformBundleLower.native coins setup checks representation created work).run before).run previous)) :
    ((value, after.1), after.2.1) ∈ support ((work.run before.1).run before.2.1) := by
  have actual : (value, after) ∈ support ((lower setup checks representation created work).run before) :=
    RegistrationNativePlatformHashReceipt.native_support coins _ _ previous next supported
  simp only [lower, StateT.run, support_map] at actual
  obtain ⟨inner, possible, same⟩ := actual
  have localEq := congrArg Prod.snd same
  have replyEq := congrArg Prod.fst same
  cases replyEq
  change (inner.1.1.2, (inner.1.2, inner.2)) = after at localEq
  rw [← localEq]
  apply OracleComp.support_simulateQ_run'_subset
    (RegistrationNativeExperiment.trusted setup checks representation created source) _ before.2.2
  rw [StateT.run'_eq, support_map]
  exact Set.mem_image_of_mem Prod.fst possible

private theorem outgoing_keeps (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (checks : Checks) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (index : Nat) (owner : Owner source)
    (query : RegistrationBeaconInitExecutor.Spec.Domain) :
    Keeps (RegistrationNativePlatformBundleLower.native (n := n) coins setup checks representation created
      (RegistrationNativeBeaconFrontend.outgoing setup source index owner query)) := by
  intro before previous result supported
  have actual := native_source coins setup checks representation created
    (RegistrationNativeBeaconFrontend.outgoing setup source index owner query) before result.1.2 previous result.2 result.1.1 supported
  have law := RegistrationNativeBundlePhases.outgoing_phases (n := n) setup index owner (RegistrationBeaconInitExecutor.Spec.query query)
    before.1 before.2.1 ((result.1.1, result.1.2.1), result.1.2.2.1)
  simp only [simulateQ_spec_query] at law
  exact law actual

private theorem encoder_keeps
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) (view : registration.InitView) :
    Keeps (RegistrationNativePlatformInitWriterFrame.encoder (n := n) (KemSK := KemSK) (source := source) writer view) := by
  intro before previous result supported
  rw [RegistrationNativePlatformInitWriterFrame.encoder_frame] at supported
  simp only [StateT.run_lift, bind_pure_comp, StateT.run_map, support_map] at supported
  obtain ⟨inner, _called, same⟩ := supported
  exact (congrArg (fun value => phases value.1.2.1) same).symm

/-- Complete actual source publication preserves every owner's exact phase through all primitive and writer outcomes. -/
theorem outgoing (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (checks : Checks) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (index : Nat) (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (before : Local n KemSK source) (previous : Platform)
    (result : (RustM (RegistrationBeaconInitExecutor.Result (alloc.vec.Vec U8)) × Local n KemSK source) × Platform)
    (supported : result ∈ support (((RegistrationNativePlatformInitTupleCache.program coins setup checks representation created writer index owner oneTime).run before).run previous)) :
    phases result.1.2.1 = phases before.1 :=
  publication _ _ (outgoing_keeps coins setup checks representation created index owner) (encoder_keeps writer)
    _ _ _ _ before previous result supported

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicationPhases

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicationPhases.outgoing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicationPhases.outgoing
