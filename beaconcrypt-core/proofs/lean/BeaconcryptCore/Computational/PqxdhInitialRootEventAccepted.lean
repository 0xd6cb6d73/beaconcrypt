import BeaconcryptCore.Computational.PqxdhInitialRootEventCompiler

/-!
The accepted root continuation retains the complete original installed-origin and publication transcript and tests the actual fixed-source lineage freshness only after the source run. The executable continuation takes the prepared protocol state and supplied root, never the selected KEM secret. Its uniform interpretation is identified with the exact source experiment by callback and complete-program equations.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.PqxdhInitialRootEventAccepted
open PqxdhJointKdf PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf
open PqxdhCorrelatedExpand PqxdhCorrelatedExtractFamily PqxdhCorrelatedExpandHybrid
open PqxdhInitialBeaconAmbient PqxdhKemIndCca PqxdhEd25519EufCma PqxdhJointIdentity
open PqxdhPrivateKemSource PqxdhGeneratedBeaconState PqxdhPhase1AcceptanceOracle
open PqxdhInitializerSecrecy PqxdhPhase2SourceAux PqxdhChallengeSecretRouting
open PqxdhStatefulPhase1EufCma PqxdhPhase2GeneratedDriver PqxdhAuthenticatedRootExperiment
open PqxdhSourceAuthenticatedRoot PqxdhPrivateAcceptedRoot
variable {ι M P I K X Response A KemSK : Type} {baseSpec : OracleSpec ι} {S B : Nat}
variable {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1)) (post : Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (prepared : PqxdhPrivateRootSource.Prepared setup (driver env.toDriverEnvironment program).State) (ready : Ready)

abbrev Snapshot := PqxdhInitialOriginPostPath.Snapshot M P (IdentityHandle I) (DhPair setup) (KemHandle K) S (B + 1)

noncomputable def selectedMessage : Message := coordinates
  (serverCoordinates env.source.crypto env.server.ikSk ready.ephemeral.toList
    prepared.1.context.publicIdentity.ed25519 prepared.1.context.generated.before.publicKey prepared.1.context.generated.after.publicKey)

noncomputable def front : PqxdhInitialOriginPostPath.Front M P (IdentityHandle I) (DhPair setup) (KemHandle K) S (B + 1) :=
  let before := PqxdhInitialGenericProtocol.fromNative ConcreteRatchetKernel.refined prepared.1.context.selection.2
  ⟨before.roles, before.controls, before.consumed⟩

noncomputable def client :=
  PqxdhInitialNativeCarried.original (X := X ⊕ PqxdhPhase2JointIdentity.Converted) (Response := Response) env.source (PqxdhInitialSelectedOrigin.mark env.source (selectedMessage env program prepared ready))
    env.senderId env.route env.decode
    (PqxdhInitialSourceExperiment.execution (PqxdhInitialRootLabelService.realInitial env.source ready.root)
      env.index env.metadata ready (post prepared.1.context.selection.1) (front env program prepared))

noncomputable def decision (selected : RawCtxProtocolReveals.Owner S (B + 1)) (number : Std.U64)
    (ancestors disclosed : List RatchetChain)
    (result : Bool × Snapshot (M := M) (P := P) (I := I) (K := K) (S := S) (B := B) (setup := setup)) : Bool :=
  @decide (PqxdhInitialPublishedEvent.Gate selected number result ∧ RawCtxLiveLineage.Fresh
    (RawCtxPublishedLineage.lineage (productionStream env.source.crypto)
      (RawCtxFreshChainCut.concreteChain (PqxdhInitialSourceExperiment.root env.source ready.root
        (PqxdhInitialRootLabelService.realInitial env.source ready.root) selected)) (number.val - 1) ++ ancestors)
    disclosed result.2.1.roles.2) (Classical.propDecidable _)

noncomputable def target (selected : RawCtxProtocolReveals.Owner S (B + 1)) (number : Std.U64)
    (ancestors disclosed : List RatchetChain) : OracleComp (LocalPostSpec baseSpec) Bool :=
  (fun result => decision env ready selected number ancestors disclosed result.1) <$>
    (simulateQ (PqxdhInitialRootEventCompiler.target env.source env.recordWriter attachedVerify primitives 1 env.localImpl
      env.aux ready.ciphertext) (client env program post prepared ready)).run
      (prepared.1.context.selection.2.primitive, prepared.2)

variable (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK)

/-- The concrete source external callbacks are precisely the actual prepared-input callbacks with only their source initializer installed. -/
theorem external_source :
    PqxdhInitialRootEventCompiler.sourceExternal env.source attachedVerify primitives 1 env.localImpl env.aux ready.ciphertext
      baseImpl kem secret (selectedMessage env program prepared ready) ready.root =
    PqxdhInitialOriginFinishPath.withInitial env.source (selectedMessage env program prepared ready) ready.root
      (PqxdhInitialRootLabelService.realInitial env.source ready.root)
      (PqxdhInitialPreparedSourceInput.other env baseImpl kem attachedVerify primitives secret ready.ciphertext) := by
  funext query
  rcases query with query | (reply | (secrets | (query | query))) <;> rfl

noncomputable def sourceGame (selected : RawCtxProtocolReveals.Owner S (B + 1)) (number : Std.U64)
    (ancestors disclosed : List RatchetChain) : ProbComp Bool :=
  PqxdhInitialSourceExperiment.game env.source env.recordWriter (selectedMessage env program prepared ready) ready.root
    (PqxdhInitialRootLabelService.realInitial env.source ready.root)
    (PqxdhInitialPreparedSourceInput.other env baseImpl kem attachedVerify primitives secret ready.ciphertext)
    env.senderId env.route env.decode env.index env.metadata ready (post prepared.1.context.selection.1)
    (front env program prepared) selected number ancestors disclosed prepared.1.context.selection.2.primitive prepared.2 ∅ 0

/-- The complete published-record source event under a real initializer is exactly the new executable accepted continuation at the uniform-root endpoint, without an equality-of-final-events premise. -/
theorem source_uniform (selected : RawCtxProtocolReveals.Owner S (B + 1)) (number : Std.U64)
    (ancestors disclosed : List RatchetChain) :
    sourceGame env attachedVerify primitives program post prepared ready baseImpl kem secret selected number ancestors disclosed =
    (simulateQ uniformImpl (simulateQ (rootPost env.source baseImpl kem secret ready.ciphertext)
      (target env attachedVerify primitives program post prepared ready selected number ancestors disclosed))).run'
        (PqxdhInitialRootLabelService.completeCache (selectedMessage env program prepared ready) ready.root ∅) := by
  rw [sourceGame, PqxdhInitialSourceReal.game_source]
  have same := PqxdhInitialRootEventCompiler.observed_uniform env.source env.recordWriter attachedVerify primitives 1 env.localImpl
    env.aux ready.ciphertext baseImpl kem secret (selectedMessage env program prepared ready) ready.root
    (client env program post prepared ready) (decision env ready selected number ancestors disclosed)
    (prepared.1.context.selection.2.primitive, prepared.2) ∅
  rw [external_source] at same
  exact same

/-- The root reduction uses the original complete authenticated preparation and coordinates, then the source event continuation. Neither prepare nor resume receives the selected secret key. -/
noncomputable def protocol (selected : RawCtxProtocolReveals.Owner S (B + 1)) (number : Std.U64)
    (ancestors disclosed : List RatchetChain) : Protocol baseSpec :=
  { PqxdhAuthenticatedRootExperiment.protocol env kem attachedVerify primitives program post with
    resume := fun _ ciphertext mode root => match mode with
      | .completed decision => pure decision
      | .pending prepared ephemeral => match root with
        | none => pure false
        | some root => target env attachedVerify primitives program post prepared
            (PqxdhPrivateAcceptedRoot.ready env.server env.application prepared.1.context.publicIdentity.ed25519
              prepared.1.context.generated.after.publicKey ephemeral ciphertext root) selected number ancestors disclosed }

/-- The actual new root endpoint supplies exactly the prepared source carrier and fresh root used by the source initializer reduction. All completed branches and the full adaptive pending continuation are included. -/
theorem uniform_source (selected : RawCtxProtocolReveals.Owner S (B + 1)) (number : Std.U64)
    (ancestors disclosed : List RatchetChain) :
    𝒟[uniformGame (rootReduction env.source baseImpl kem
      (protocol env attachedVerify primitives program post kem selected number ancestors disclosed))] =
    𝒟[PqxdhInitialPreparedSourceInput.uniformRoot env baseImpl kem attachedVerify primitives program post selected number ancestors disclosed] := by
  simp only [uniformGame, StateT.run'_eq, PqxdhInitialRootContext.reduction_complete,
    PqxdhInitialPreparedSourceInput.uniformRoot, PqxdhInitialSourceInitialSecrecy.real,
    PqxdhInitialPreparedSourceInput.prior, PqxdhCorrelatedExtractFamily.prepare,
    bind_assoc, pure_bind, map_bind, map_pure]
  refine evalDist_bind_congr (fun keys _ => ?_)
  refine evalDist_bind_congr (fun mode _ => ?_)
  refine evalDist_bind_congr (fun pair _ => ?_)
  cases mode with
  | completed decision =>
    simp only [PqxdhInitialRootContext.firstMiss, protocol, PqxdhAuthenticatedRootExperiment.protocol,
      PqxdhInitialRootContext.afterRoot, PqxdhInitialPreparedSourceInput.input,
      simulateQ_pure, StateT.run_pure, map_pure]
    exact (OracleComp.ProgramLogic.Relational.evalDist_bind_const_of_no_failure
      ($ᵗ RootOutput) (pure decision : ProbComp Bool)).symm
  | pending prepared ephemeral =>
    simp only [PqxdhInitialRootContext.firstMiss, protocol, PqxdhAuthenticatedRootExperiment.protocol,
      PqxdhInitialRootContext.afterRoot, PqxdhInitialPreparedSourceInput.input, map_bind]
    refine evalDist_bind_congr (fun root _ => ?_)
    have same := source_uniform env attachedVerify primitives program post prepared
      (PqxdhPrivateAcceptedRoot.ready env.server env.application prepared.1.context.publicIdentity.ed25519
        prepared.1.context.generated.after.publicKey ephemeral pair.1 root) baseImpl kem keys.2 selected number ancestors disclosed
    exact congrArg evalDist same.symm

end BeaconcryptCore.Computational.PqxdhInitialRootEventAccepted

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialRootEventAccepted.external_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialRootEventAccepted.external_source

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialRootEventAccepted.source_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialRootEventAccepted.source_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialRootEventAccepted.uniform_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialRootEventAccepted.uniform_source

