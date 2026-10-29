-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordPairedCommon
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomServerTrace

/-! The actual Server material controller establishes its own demanded descriptor and actual returned choice before the complete publication/insertion suffix. Native lookup, occupancy, preflight, cancellation and one-use Ready movement can only skip that stage. This is a trace-preserving proof on the full compiled controller, independent of the surrounding World interpreter. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordPairedServer
open RegistrationNativeSecretWordInterface (Spec liftLocal)
open RegistrationNativeSecretWordMessage (Message ServerState ServerReady)
open RegistrationNativeSecretWordAtomServerTrace (compile)
open RegistrationNativeSecretWordPairedTrace (State handler step Safe)
open RegistrationServerReferenceCompiler (Environment)
variable {n : Nat} {KemSK Value : Type}

private theorem bind_apply {S X Y : Type} {m : Type → Type} [Monad m]
    (work : StateT S m X) (next : X → StateT S m Y) (before : S) :
    (work >>= next) before = (do let result ← work before; next result.1 result.2) := rfl

private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : X → Y) (work : StateT S m X) (before : S) :
    (observe <$> work) before = Prod.map observe id <$> work before := StateT.run_map observe work before

private theorem compile_pure (selected : Bool) (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (value : Value) (before : Environment) :
    compile (n := n) (KemSK := KemSK) selected source wire sign (pure value) before = pure (value, before) := by
  simp only [compile, simulateQ_pure, StateT.run_pure]

private theorem compile_bind {Next : Type} (selected : Bool) (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (work : OracleComp (RegistrationNativeSecretWordInterface.WordPairedPublicSpec n) Value)
    (next : Value → OracleComp (RegistrationNativeSecretWordInterface.WordPairedPublicSpec n) Next) (before : Environment) :
    compile (n := n) (KemSK := KemSK) selected source wire sign (work >>= next) before = (do
      let result ← compile selected source wire sign work before
      compile selected source wire sign (next result.1) result.2) := by
  simp only [compile, simulateQ_bind, StateT.run_bind]

private theorem compile_effect (selected : Bool) (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (query : (PqxdhRecordLiftInterface.EnvEffects n).Domain) (before : Environment) :
    compile (n := n) (KemSK := KemSK) selected source wire sign (RegistrationNativeSecretWordServerMaterial.effect query) before =
      (fun reply => (reply, before)) <$> ((Spec n KemSK).query (.inl (.inr (.inl (.inr (.inr query))))) : OracleComp (Spec n KemSK) _) := by
  simp only [compile, RegistrationNativeSecretWordServerMaterial.effect, simulateQ_spec_query,
    RegistrationNativeSecretWordServerCompiler.service, RegistrationNativeCommonCompiler.common, StateT.run_lift,
    bind_pure_comp, simulateQ_map, RegistrationNativeSecretWordInterface.effect, liftLocal]
  rfl

private theorem common_compile (selected : Bool) (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (work : OracleComp (RegistrationNativePairedServerService.Common n) Value) (before : Environment) :
    compile (n := n) (KemSK := KemSK) selected source wire sign
      (simulateQ RegistrationNativeSecretWordServerMaterial.commonLift work) before =
      RegistrationNativeSecretWordAtomCommonTrace.compile selected source wire.frameWrite sign work before := by
  unfold compile RegistrationNativeSecretWordAtomCommonTrace.compile
  rw [← QueryImpl.simulateQ_compose]
  have same : RegistrationNativeSecretWordServerCompiler.service (n := n) (KemSK := KemSK) source wire sign ∘ₛ
      RegistrationNativeSecretWordServerMaterial.commonLift =
      RegistrationNativeCommonCompiler.common RegistrationNativeSecretWordInterface.effect source wire.frameWrite sign := by
    funext query
    simp only [QueryImpl.compose, RegistrationNativeSecretWordServerMaterial.commonLift,
      simulateQ_spec_query, RegistrationNativeSecretWordServerCompiler.service]
  rw [same]

private theorem admitted_run (selected : Bool) (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (control : pqxdh.ServerState) (initial : RegistrationBoundKeySchedule.PublicInitial)
    (reference : Message) (before : Environment) :
    compile (n := n) (KemSK := KemSK) selected source wire sign
      (RegistrationNativeSecretWordServerMaterial.admitted wire.encodeResponse control initial reference) before = (do
        let chosen ← ((Spec n KemSK).query (.inl (.inr (.inl (.inl reference)))) : OracleComp (Spec n KemSK) (Option (RegistrationNativePairedChoice.Choice n)))
        match chosen with
        | none => pure (.ok (.Err control), before)
        | some choice => RegistrationNativeSecretWordAtomCommonTrace.compile selected source wire.frameWrite sign (RegistrationNativePairedServerService.publicBranch wire.encodeResponse control initial choice) before) := by
  simp only [compile, RegistrationNativeSecretWordServerMaterial.admitted, simulateQ_bind, simulateQ_spec_query,
    StateT.run_bind, RegistrationNativeSecretWordServerCompiler.service, StateT.run_lift, bind_pure_comp,
    simulateQ_bind, RegistrationNativeSecretWordInterface.demand, liftLocal, simulateQ_spec_query, bind_map_left]
  apply bind_congr
  intro chosen
  cases chosen with
  | none => simp only [simulateQ_pure, StateT.run_pure]
  | some choice => exact common_compile selected source wire sign _ before

/-- The actual Server admitted stage checks all hidden installation attempts against this same demand's returned slot and descriptor. -/
theorem admitted (selected : Bool) (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (control : pqxdh.ServerState) (initial : RegistrationBoundKeySchedule.PublicInitial)
    (reference : Message) (before : Environment) :
    Safe (compile (n := n) (KemSK := KemSK) selected source wire sign
      (RegistrationNativeSecretWordServerMaterial.admitted wire.encodeResponse control initial reference) before) := by
  intro trace result clean supported
  rw [admitted_run, simulateQ_bind, simulateQ_spec_query, StateT.run_bind] at supported
  simp only [handler, StateT.run, bind_map_left, mem_support_bind_iff] at supported
  obtain ⟨chosen, _possible, continued⟩ := supported
  cases chosen with
  | none =>
      exact RegistrationNativeSecretWordPairedTrace.pure_safe _ _ result
        (by simp only [step, RegistrationNativeSecretWordPairedTrace.Fits, decide_true, Bool.not_true, Bool.or_false, clean]) continued
  | some choice =>
      exact RegistrationNativeSecretWordPairedCommon.server selected source wire.frameWrite sign wire.encodeResponse control initial choice
        reference before (step (.inl (.inr (.inl (.inl reference)))) (some choice) trace)
        (by simp only [step, RegistrationNativeSecretWordPairedTrace.Fits, decide_true, Bool.not_true, Bool.or_false, clean])
        ⟨rfl, rfl⟩ result continued

private theorem finished (selected : Bool) (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (published : RustM (RegistrationNativePairedServerService.Result Pqxdh.Bytes))
    (before : ServerState) (env : Environment) :
    Safe (compile (n := n) (KemSK := KemSK) selected source wire sign
      ((RegistrationNativeSecretWordServerMaterial.finish published).run before) env) := by
  cases published with
  | fail error | div =>
      simp only [RegistrationNativeSecretWordServerMaterial.finish, StateT.run, compile_pure]
      exact RegistrationNativeSecretWordPairedTrace.pure_safe _
  | ok published =>
      cases published <;> simp only [RegistrationNativeSecretWordServerMaterial.finish, StateT.run, compile_pure]
      all_goals exact RegistrationNativeSecretWordPairedTrace.pure_safe _

attribute [local irreducible] peer.begin_completion_lookup RegistrationServerSdkSource.preflight

/-- Native lookup, preflight and reservation either stop or enter the same actual admitted material stage; every branch preserves paired provenance. -/
theorem complete (selected : Bool) (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (reservePeer : Bool) (ready : ServerReady) (application : Slice U8)
    (before : ServerState) (env : Environment) :
    Safe (compile (n := n) (KemSK := KemSK) selected source wire sign
      ((RegistrationNativeSecretWordServerMaterial.complete wire reservePeer ready application).run before) env) := by
  simp only [RegistrationNativeSecretWordServerMaterial.complete, StateT.run]
  split <;> try (rw [compile_pure]; exact RegistrationNativeSecretWordPairedTrace.pure_safe _)
  split <;> try (rw [compile_pure]; exact RegistrationNativeSecretWordPairedTrace.pure_safe _)
  split <;> try (rw [compile_pure]; exact RegistrationNativeSecretWordPairedTrace.pure_safe _)
  rw [compile_bind]
  apply RegistrationNativeSecretWordPairedTrace.bind_safe
  · rw [compile_effect]
    apply RegistrationNativeSecretWordPairedSafe.free
    intro role
    simp [RegistrationNativeSecretWordAtomInstallPredicate.GlobalInstall,
      RegistrationNativeSecretWordAtomInstallCaps.Install, RegistrationNativeSecretWordAtomInstallCaps.InstallEnv,
      isQueryBoundP_map_iff, isQueryBoundP_query_iff]
  · intro occupied
    split <;> try (rw [compile_pure]; exact RegistrationNativeSecretWordPairedTrace.pure_safe _)
    split <;> try (rw [compile_pure]; exact RegistrationNativeSecretWordPairedTrace.pure_safe _)
    rw [compile_bind]
    apply RegistrationNativeSecretWordPairedTrace.bind_safe _ _ (admitted selected source wire sign before.control _ ready.reference occupied.2)
    intro published
    exact finished selected source wire sign published.1 before published.2

/-- The exact one-use native build moves its Ready before every cancellation or callback and derives its paired-provenance safety internally. -/
theorem build (selected : Bool) (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (reservePeer : Bool) (handle : Nat) (application : Option (Slice U8))
    (before : ServerState) (env : Environment) :
    Safe (compile (n := n) (KemSK := KemSK) selected source wire sign
      ((RegistrationNativeSecretWordServerMaterial.build wire reservePeer handle application).run before) env) := by
  simp only [RegistrationNativeSecretWordServerMaterial.build, StateT.run]
  rcases formed : RegistrationNativeSecretWordServerMaterial.take handle before with ⟨chosen, after⟩
  cases chosen with
  | none => rw [compile_pure]; exact RegistrationNativeSecretWordPairedTrace.pure_safe _
  | some ready =>
      cases application with
      | none => rw [compile_pure]; exact RegistrationNativeSecretWordPairedTrace.pure_safe _
      | some application => exact complete selected source wire sign reservePeer ready application after env

/-- The whole actual public-frontend Server build retains the same complete paired-monitor certificate. -/
theorem frontend_build {ι : Type} {base : OracleSpec ι} (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (checks : PqxdhServerAuthExperiment.Checks) (wire : RegistrationNativeWire.Wire)
    (source : RegistrationNativeMldsa.Source)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (handle : Nat) (application : Option (Slice U8)) (before : RegistrationNativeSecretWordMessage.State source) :
    Safe ((RegistrationNativeSecretWordFrontend.handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey
      (.inr (.build handle application))).run before) := by
  have exactProgram : (RegistrationNativeSecretWordFrontend.handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey
        (.inr (.build handle application))).run before =
      (fun reached => (reached.1.1, { before with server := reached.1.2, environment := reached.2 })) <$>
        compile false setup.source wire sign
          ((RegistrationNativeSecretWordServerMaterial.build wire checks.reservePeer handle application).run before.server) before.environment := by
    simp only [RegistrationNativeSecretWordFrontend.handler, RegistrationNativeSecretWordFrontend.serverOpen,
      RegistrationNativeSecretWordServerCompiler.build, StateT.run, compile]
    rfl
  rw [exactProgram, ← bind_pure_comp]
  exact RegistrationNativeSecretWordPairedTrace.bind_safe _ _
    (build false setup.source wire sign checks.reservePeer handle application before.server before.environment)
    (fun _ => RegistrationNativeSecretWordPairedTrace.pure_safe _)

end BeaconcryptCore.Computational.RegistrationNativeSecretWordPairedServer
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordPairedServer.admitted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordPairedServer.admitted
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordPairedServer.complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordPairedServer.complete
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordPairedServer.build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordPairedServer.build
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordPairedServer.frontend_build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordPairedServer.frontend_build
