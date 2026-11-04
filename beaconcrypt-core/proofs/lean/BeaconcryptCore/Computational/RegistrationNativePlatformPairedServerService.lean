-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPrivateKdfState
import BeaconcryptCore.Computational.RegistrationNativePlatformSourceCompletion
import BeaconcryptCore.Computational.RegistrationNativePairedServerService
import BeaconcryptCore.Computational.RegistrationNativePlatformSourceBuild
import BeaconcryptCore.Computational.RegistrationServerPublicationWorldCompiler
/-! The corrected source material service retains stateful sealing, mutable hashing, response signing and both runtime writers in one monad. Its protected public branch receives only material44 and a private World slot; the generated whole kernel is removed by the checked source continuation and the actual hidden installation body. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPairedServerService
open PqxdhRecordLiftInterface
open RegistrationNativePairedChoice (Choice PrivateChoice publicChoice)
variable {n : Nat} {Encoded : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
variable (sealing : record_effects.AeadSealRequest → m (RustM (core.option.Option (Slice U8 × Std.Array U8 16#usize))))
variable (hash : commitment.CommitmentTranscript → m RegistrationNativePlatformCommitment.HashReply)
variable (write : record_effects.RecordWriteRequest → m (RustM (core.option.Option (Slice U8))))
variable (sign : QueryImpl RegistrationSigningShared.Spec m)
variable (encode : registration.SignedResponseView → m (RustM (core.option.Option Encoded)))
variable (effects : QueryImpl (EnvEffects n) m)

def knownStage (control : pqxdh.ServerState) (initial : RegistrationBoundKeySchedule.PublicInitial)
    (output : PqxdhServerAuthKeySchedule.Output) : m (RustM (RegistrationHiddenInstall.Result Encoded)) := do
  let published ← RegistrationNativePlatformBoundPublication.program sealing hash write sign encode initial output
  simulateQ effects (RegistrationNativePairedServerService.knownAfter control published)

def hiddenStage (control : pqxdh.ServerState) (slot : Slot n) (initial : RegistrationBoundKeySchedule.PublicInitial)
    (output : PqxdhServerAuthKeySchedule.Output) : m (RustM (RegistrationHiddenInstall.Result Encoded)) := do
  let published ← RegistrationNativePlatformBoundPublication.program sealing hash write sign encode initial output
  simulateQ effects (RegistrationHiddenInstall.after control slot published)

def publicHidden (control : pqxdh.ServerState) (initial : RegistrationBoundKeySchedule.PublicInitial)
    (reference : RegistrationNativePairedDemand.Reference n) : m (RustM (RegistrationHiddenInstall.Result Encoded)) := do
  let published ← RegistrationNativePlatformBoundPublication.thin sealing hash write sign encode initial reference.material
  simulateQ effects (RegistrationHiddenInstall.after control reference.slot published)

/-- The entire actual stateful source publication uses only material44 publicly before the same native hidden-reference insertion. -/
theorem stage_split (control : pqxdh.ServerState) (slot : Slot n) (initial : RegistrationBoundKeySchedule.PublicInitial)
    (material : PqxdhDeploymentHiddenLayout.Material) (seed : PqxdhRecordLiftSeed.Seed) :
    hiddenStage sealing hash write sign encode effects control slot initial (PqxdhDeploymentHiddenLayout.joinOutput material seed) =
      publicHidden sealing hash write sign encode effects control initial ⟨slot, material⟩ := by
  simp only [hiddenStage, publicHidden, RegistrationNativePlatformBoundPublication.split,
    bind_map_left, RegistrationHiddenInstall.after_map]

def privateBranch (control : pqxdh.ServerState) (initial : RegistrationBoundKeySchedule.PublicInitial) :
    PrivateChoice n → m (RustM (RegistrationHiddenInstall.Result Encoded))
  | .known output => knownStage sealing hash write sign encode effects control initial output
  | .hidden slot output => hiddenStage sealing hash write sign encode effects control slot initial output

def publicBranch (control : pqxdh.ServerState) (initial : RegistrationBoundKeySchedule.PublicInitial) :
    Choice n → m (RustM (RegistrationHiddenInstall.Result Encoded))
  | .known output => knownStage sealing hash write sign encode effects control initial output
  | .hidden reference => publicHidden sealing hash write sign encode effects control initial reference

/-- The concrete source known/hidden branches preserve the complete common effects and outputs after only the protected private seed is erased. -/
theorem branch_split (control : pqxdh.ServerState) (initial : RegistrationBoundKeySchedule.PublicInitial)
    (choice : PrivateChoice n) :
    publicBranch sealing hash write sign encode effects control initial (publicChoice choice) =
      privateBranch sealing hash write sign encode effects control initial choice := by
  cases choice with
  | known output => rfl
  | hidden slot output =>
    simpa only [publicBranch, privateBranch, publicChoice, PqxdhDeploymentHiddenLayout.join_split] using
      (stage_split sealing hash write sign encode effects control slot initial
        (PqxdhDeploymentHiddenLayout.splitOutput output).1 (PqxdhDeploymentHiddenLayout.splitOutput output).2).symm

def admitted (demand : RegistrationNativeRelatedFamily.Message → m (Option (Choice n)))
    (control : pqxdh.ServerState) (initial : RegistrationBoundKeySchedule.PublicInitial)
    (message : RegistrationNativeRelatedFamily.Message) : m (RustM (RegistrationHiddenInstall.Result Encoded)) := do
  let selected ← demand message
  match selected with
  | none => pure (.ok (.Err control))
  | some choice => publicBranch sealing hash write sign encode effects control initial choice

/-- Material demand occurs once at this reached admission; optional absence and all stateful failed prefixes are retained. -/
theorem admitted_split (demand : RegistrationNativeRelatedFamily.Message → m (Option (PrivateChoice n)))
    (control : pqxdh.ServerState) (initial : RegistrationBoundKeySchedule.PublicInitial)
    (message : RegistrationNativeRelatedFamily.Message) :
    admitted sealing hash write sign encode effects (fun message => Option.map publicChoice <$> demand message)
      control initial message = (do
        let selected ← demand message
        match selected with
        | none => pure (.ok (.Err control))
        | some choice => privateBranch sealing hash write sign encode effects control initial choice) := by
  simp only [admitted, bind_map_left]
  apply bind_congr
  intro selected
  cases selected with
  | none => rfl
  | some choice => exact branch_split sealing hash write sign encode effects control initial choice

private theorem known_install (control : pqxdh.ServerState) (published : registration.PublishedServerResponse Encoded) :
    simulateQ effects (RegistrationNativePairedServerService.knownInstall control published) =
      RegistrationNativePlatformServerCompletion.installWith (fun query => effects (.inr query)) control published := by
  have body : RegistrationNativePairedServerService.knownInstall (n := n) control published =
      RegistrationNativePlatformServerCompletion.installWith
        (fun query => ((EnvEffects n).query (.inr query) : OracleComp (EnvEffects n) _)) control published := rfl
  rw [body, RegistrationNativePlatformServerCompletion.installWith_interpret]
  simp only [simulateQ_spec_query]

private theorem known_after (control : pqxdh.ServerState)
    (published : RustM (RegistrationWorldServerPublication.Result Encoded)) :
    simulateQ effects (RegistrationNativePairedServerService.knownAfter control published) =
      RegistrationNativePlatformServerCompletion.continueResult published
        (RegistrationNativePlatformServerCompletion.installWith (fun query => effects (.inr query)) control) := by
  cases published with
  | fail error => rfl
  | div => rfl
  | ok result => cases result with
    | Err previous => rfl
    | Ok published => exact known_install effects control published

private theorem continuation (control : pqxdh.ServerState)
    (completed : RustM RegistrationServerRecordExecutor.Result) :
    RegistrationNativePlatformServerCompletion.continueResult completed (fun response => do
      let published ← RegistrationNativePlatformServerPublication.program sign encode response
      RegistrationNativePlatformServerCompletion.continueResult published
        (RegistrationNativePlatformServerCompletion.installWith (fun query => effects (.inr query)) control)) = (do
      let published ← RegistrationNativePlatformBoundPublication.after sign encode completed
      simulateQ effects (RegistrationNativePairedServerService.knownAfter control published)) := by
  cases completed with
  | fail error => simp only [RegistrationNativePlatformServerCompletion.continueResult,
      RegistrationNativePlatformBoundPublication.after, RegistrationNativePlatformServerPublication.continueResult, pure_bind]; rfl
  | div => simp only [RegistrationNativePlatformServerCompletion.continueResult,
      RegistrationNativePlatformBoundPublication.after, RegistrationNativePlatformServerPublication.continueResult, pure_bind]; rfl
  | ok result => cases result with
    | Err previous => simp only [RegistrationNativePlatformServerCompletion.continueResult,
        RegistrationNativePlatformBoundPublication.after, RegistrationNativePlatformServerPublication.continueResult, pure_bind]; rfl
    | Ok response =>
      simp only [RegistrationNativePlatformServerCompletion.continueResult,
        RegistrationNativePlatformBoundPublication.after, RegistrationNativePlatformServerPublication.continueResult]
      apply bind_congr
      intro published
      exact (known_after effects control published).symm

section Source
open PqxdhServerAuthExperiment (Setup Codec)
variable {Auxiliary ι KemSK Reader Response : Type} {base : OracleSpec ι}

/-- The actual private source completion runs the exact two-KDF accounting prefix and then this same stateful known-material service, with no whole-controller correspondence premise. -/
theorem source (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (sealing : record_effects.AeadSealRequest → StateT (RegistrationWorldAgreement.State n Auxiliary) m
      (RustM (core.option.Option (Slice U8 × Std.Array U8 16#usize))))
    (hash : commitment.CommitmentTranscript → StateT (RegistrationWorldAgreement.State n Auxiliary) m RegistrationNativePlatformCommitment.HashReply)
    (write : record_effects.RecordWriteRequest → StateT (RegistrationWorldAgreement.State n Auxiliary) m (RustM (core.option.Option (Slice U8))))
    (sign : QueryImpl RegistrationSigningShared.Spec (StateT (RegistrationWorldAgreement.State n Auxiliary) m))
    (encode : registration.SignedResponseView → StateT (RegistrationWorldAgreement.State n Auxiliary) m (RustM (core.option.Option Encoded)))
    (effects : QueryImpl (EnvEffects n) (StateT (RegistrationWorldAgreement.State n Auxiliary) m))
    (control : pqxdh.ServerState) (pending : registration.ServerInitialKdf) (root : PqxdhSecretInputKdf.RootOutput)
    (role : pending.pending = PqxdhInitialRatchetComplementarity.serverPending
      (PqxdhRootTableInitialization.rootArray root)) (before : RegistrationWorldAgreement.State n Auxiliary) :
    (RegistrationNativePlatformSourceCompletion.fromInitialSource
      (RegistrationNativePlatformServerCompletion.records coins setup codec) sealing hash write sign
      (fun query => effects (.inr query)) encode control pending).run before =
      (knownStage sealing hash write sign encode effects control (RegistrationBoundKeySchedule.publicInitial pending)
        (PqxdhServerAuthKeySchedule.fromRoot setup.source root)).run
          (RegistrationNativePlatformPrivateKdfState.ratchetState (RegistrationNativePlatformPrivateKdfState.initialState before)) := by
  simp only [RegistrationNativePlatformSourceCompletion.fromInitialSource, knownStage,
    RegistrationNativePlatformBoundPublication.program, StateT.run_bind]
  rw [RegistrationNativePlatformPrivateKdfState.source coins setup codec sealing hash write pending root role before]
  simp only [bind_assoc]
  apply bind_congr
  rintro ⟨completed, current⟩
  exact congrArg (fun work => work.run current) (continuation sign encode effects control completed)

noncomputable def nativeEffects (coins : QueryImpl unifSpec m) :
    QueryImpl (EnvEffects n) (StateT (RegistrationWorldAgreement.State n Auxiliary) m) :=
  fun query => RegistrationNativePlatformServerCompletion.liftNative coins
    (RegistrationServerPublicationWorldCompiler.effect query)

/-- The actual source SDK completion supplies these concrete signing, raw writer, stateful response encoder and native installation leaves to the private material service. -/
theorem finish_source {E : Type}
    (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (sealing : record_effects.AeadSealRequest → StateT (RegistrationServerRootCompiler.Local n) m
      (RustM (core.option.Option (Slice U8 × Std.Array U8 16#usize))))
    (hash : commitment.CommitmentTranscript → StateT (RegistrationServerRootCompiler.Local n) m RegistrationNativePlatformCommitment.HashReply)
    (signing : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) m)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) m)
    (control : pqxdh.ServerState) (pending : registration.ServerInitialKdf) (root : PqxdhSecretInputKdf.RootOutput)
    (role : pending.pending = PqxdhInitialRatchetComplementarity.serverPending
      (PqxdhRootTableInitialization.rootArray root)) (before : RegistrationServerRootCompiler.Local n) :
    (RegistrationNativePlatformSourceBuild.finishSource coins setup codec sealing hash signing helper writer control pending).run before =
      (knownStage sealing hash (RegistrationNativePlatformSourceBuild.write helper)
        (RegistrationNativePlatformServerCompletion.outgoing coins signing) (RegistrationNativePlatformSourceBuild.encode writer)
        (nativeEffects coins) control (RegistrationBoundKeySchedule.publicInitial pending)
        (PqxdhServerAuthKeySchedule.fromRoot setup.source root)).run
          (RegistrationNativePlatformPrivateKdfState.ratchetState (RegistrationNativePlatformPrivateKdfState.initialState before)) := by
  exact source coins setup codec sealing hash (RegistrationNativePlatformSourceBuild.write helper)
    (RegistrationNativePlatformServerCompletion.outgoing coins signing) (RegistrationNativePlatformSourceBuild.encode writer)
    (nativeEffects coins) control pending root role before

end Source

end BeaconcryptCore.Computational.RegistrationNativePlatformPairedServerService

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPairedServerService.stage_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPairedServerService.stage_split

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPairedServerService.branch_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPairedServerService.branch_split

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPairedServerService.admitted_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPairedServerService.admitted_split

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPairedServerService.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPairedServerService.source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPairedServerService.finish_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPairedServerService.finish_source
