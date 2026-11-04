-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityBundle
import BeaconcryptCore.Computational.RegistrationNativeIdentityBundleRun

/-! Complete owner lookup and optional scalar dispatch for the effectful generated-Ed bundle. The actual source writer, its P poststate and every failed publication prefix remain in the same execution. Private seed witnesses interpret generated handles; they are absent from the executable bundle client. This correspondence does not establish whole-runtime credential ownership or causal publication security. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityBundleRun
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhJointIdentity (IdentitySeed)
open RegistrationNativePlatformIdentityProgram
open RegistrationNativePlatformIdentityBundle (bundled originalBundled)
variable {n : Nat} {ι KemSK Auxiliary Platform E : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

noncomputable def start (setup : Setup base KemSK) (index : Nat)
    (owner : RegistrationNativeIdentityFrontend.Owner source)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) :
    M n KemSK Auxiliary Platform source (RustM (Option (alloc.vec.Vec U8))) := do
  let selected : Option (Option PqxdhJointGapDh.ScalarBytes) := match owner.phase with
    | .fresh => some none
    | .freshWithCoins scalar => some (some scalar)
    | _ => none
  match selected with
  | none => pure (.ok none)
  | some supplied => do
    let scalar ← match supplied with
      | some scalar => pure scalar
      | none => native (RegistrationNativeIdentityFrontend.sample PqxdhJointGapDh.sampleScalar)
    bundled setup index owner scalar writer

noncomputable def originalStart (setup : Setup base KemSK) (index : Nat)
    (owner : RegistrationNativeBeaconFrontend.Owner source)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) :
    Original n KemSK Auxiliary Platform source (RustM (Option (alloc.vec.Vec U8))) := do
  let selected : Option (Option PqxdhJointGapDh.ScalarBytes) := match owner.phase with
    | .fresh => some none
    | .freshWithCoins scalar => some (some scalar)
    | _ => none
  match selected with
  | none => pure (.ok none)
  | some supplied => do
    let scalar ← match supplied with
      | some scalar => pure scalar
      | none => original (RegistrationNativeBeaconFrontend.sample PqxdhJointGapDh.sampleScalar)
    originalBundled setup index owner scalar writer

noncomputable def bundle (setup : Setup base KemSK) (index : Nat)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) :
    M n KemSK Auxiliary Platform source (RustM (Option (alloc.vec.Vec U8))) := do
  let owners ← get
  match owners[index]? with
  | none => pure (.ok none)
  | some owner => start setup index owner writer

noncomputable def originalBundle (setup : Setup base KemSK) (index : Nat)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) :
    Original n KemSK Auxiliary Platform source (RustM (Option (alloc.vec.Vec U8))) := do
  let owners ← get
  match owners[index]? with
  | none => pure (.ok none)
  | some owner => originalStart setup index owner writer

/-- Actual supplied or sampled one-time material is used on both sides; all other phases reject without a writer call. -/
theorem start_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (seeds : List IdentitySeed) (index : Nat) (owner : RegistrationNativeIdentityFrontend.Owner source) (seed : IdentitySeed)
    (found : seeds[owner.identity.handle]? = some seed) (publicKey : owner.identity.publicIdentity = setup.joint.publicKeys seed)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) :
    Related (n := n) (Auxiliary := Auxiliary) setup checks representation created seeds
      (start setup index owner writer) (originalStart setup index (RegistrationNativeIdentityFrontend.restore seed owner) writer) := by
  cases phase : owner.phase with
  | fresh =>
    simp only [start, originalStart, RegistrationNativeIdentityFrontend.restore, phase]
    exact related_bind setup checks representation created seeds _ _ _ _
      (native_related setup checks representation created seeds _ _
        (RegistrationNativeIdentityCommonSource.sample_source setup checks representation created seeds _))
      (native_keeps setup checks representation created _
        (RegistrationNativeIdentityCommonSource.sample_keeps setup checks representation created _))
      (fun scalar => RegistrationNativePlatformIdentityBundle.bundled_source setup checks representation created seeds index owner seed scalar found publicKey writer)
  | freshWithCoins scalar =>
    simpa only [start, originalStart, RegistrationNativeIdentityFrontend.restore, phase, pure_bind] using
      RegistrationNativePlatformIdentityBundle.bundled_source (n := n) (Auxiliary := Auxiliary) setup checks representation created seeds index owner seed scalar found publicKey writer
  | initSent pending scalar | established completed | aborted aborted =>
    simpa only [start, originalStart, RegistrationNativeIdentityFrontend.restore, phase] using
      (related_pure (n := n) (Auxiliary := Auxiliary) (source := source) (Platform := Platform) setup checks representation created seeds (.ok none : RustM (Option (alloc.vec.Vec U8))))

theorem start_keeps (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (index : Nat) (owner : RegistrationNativeIdentityFrontend.Owner source)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) :
    Keeps (n := n) (Auxiliary := Auxiliary) setup checks representation created (start setup index owner writer) := by
  cases phase : owner.phase with
  | fresh =>
    simp only [start, phase]
    exact keeps_bind setup checks representation created _ _
      (native_keeps setup checks representation created _
        (RegistrationNativeIdentityCommonSource.sample_keeps setup checks representation created _))
      (fun scalar => RegistrationNativePlatformIdentityBundle.bundled_keeps setup checks representation created index owner scalar writer)
  | freshWithCoins scalar =>
    simpa only [start, phase, pure_bind] using
      RegistrationNativePlatformIdentityBundle.bundled_keeps (n := n) (Auxiliary := Auxiliary) setup checks representation created index owner scalar writer
  | initSent pending scalar | established completed | aborted aborted =>
    simpa only [start, phase] using
      (keeps_pure (n := n) (Auxiliary := Auxiliary) (source := source) (Platform := Platform) setup checks representation created (.ok none : RustM (Option (alloc.vec.Vec U8))))

/-- The full effectful bundle uses the actual private generated row selected by owner lookup, preserving every other owner and the complete continued native/P state. -/
theorem bundle_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (seeds : List IdentitySeed) (index : Nat)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (before : RegistrationNativeIdentitySourceSimulation.NewState n KemSK Auxiliary source × Platform)
    (prior : before.1.2.identities.seeds = seeds)
    (owned : RegistrationNativeIdentityRealization.Owned setup.joint before.1.2.identities before.1.1.1) :
    Prod.map id (project seeds) <$> runNew setup checks representation created (bundle setup index writer) before =
      runOld setup checks representation created (originalBundle setup index writer) (project seeds before) := by
  cases selected : before.1.1.1[index]? with
  | none =>
    simp only [runNew, runOld, bundle, originalBundle, StateT.run_bind, StateT.run_get, pure_bind,
      project, RegistrationNativeIdentitySourceSimulation.view, RegistrationNativeIdentityRealization.owners,
      List.getElem?_map, selected, Option.map_none, StateT.run_pure, simulateQ_pure, map_pure, Prod.map_def, id_eq]
  | some owner =>
    obtain ⟨seed, receipt⟩ := owned owner (List.mem_of_getElem? selected)
    have found : seeds[owner.identity.handle]? = some seed := by rw [← prior]; exact receipt.1
    have nativeOwner : RegistrationNativeIdentityRealization.owner ⟨seeds, []⟩ owner =
        RegistrationNativeIdentityFrontend.restore seed owner := by
      simp only [RegistrationNativeIdentityRealization.owner,
        RegistrationNativeIdentityRealization.seed_found ⟨seeds, []⟩ owner.identity seed found]
    have nativeFound : (project seeds before).1.1.1[index]? = some (RegistrationNativeIdentityFrontend.restore seed owner) := by
      simp only [project, RegistrationNativeIdentitySourceSimulation.view,
        RegistrationNativeIdentityRealization.owners, List.getElem?_map, selected, Option.map_some, nativeOwner]
    have actual := start_source setup checks representation created seeds index owner seed found receipt.2 writer before prior
    simpa only [runNew, runOld, bundle, originalBundle, StateT.run_bind, StateT.run_get, pure_bind,
      selected, nativeFound] using actual

theorem bundle_keeps (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (index : Nat) (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) :
    Keeps (n := n) (Auxiliary := Auxiliary) (source := source) setup checks representation created (bundle setup index writer) := by
  intro before result supported
  cases selected : before.1.1.1[index]? with
  | none =>
    simp only [runNew, bundle, StateT.run_bind, StateT.run_get, pure_bind, selected,
      StateT.run_pure, simulateQ_pure, map_pure, mem_support_pure_iff] at supported
    cases supported
    rfl
  | some owner =>
    have same : runNew setup checks representation created (bundle setup index writer) before =
        runNew setup checks representation created (start setup index owner writer) before := by
      simp only [runNew, bundle, StateT.run_bind, StateT.run_get, pure_bind, selected]
    rw [same] at supported
    exact start_keeps setup checks representation created index owner writer before result supported

end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityBundleRun
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityBundleRun.start_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityBundleRun.start_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityBundleRun.start_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityBundleRun.start_keeps
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityBundleRun.bundle_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityBundleRun.bundle_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityBundleRun.bundle_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityBundleRun.bundle_keeps
