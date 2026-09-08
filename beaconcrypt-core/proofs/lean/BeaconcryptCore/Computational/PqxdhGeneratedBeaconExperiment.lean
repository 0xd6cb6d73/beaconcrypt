import BeaconcryptCore.Computational.PqxdhGeneratedBeaconSelector
import BeaconcryptCore.Computational.PqxdhGeneratedRootSource
import BeaconcryptCore.Computational.PqxdhProtocolNativeAcceptance

/-!
The authenticated root execution now includes generation of a new Beacon, optional Phase1 serialization and publication, adaptive native record/public/ reveal scheduling, selected Server acceptance, its native response builder and the same scheduler after publication. The single fixed source is used for root and record derivations. Both reductions are constructed in this same experiment; the source program has no honest-selected-key premise. This hop replaces only the authenticated target KEM contribution by one shared uniform secret. Extract, evolving chains and the absent Phase2/identity-KEM-reveal/restore capabilities still require further simulations before a global security claim.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhGeneratedBeaconExperiment
open PqxdhEd25519EufCma PqxdhJointIdentity PqxdhStatefulPhase1EufCma PqxdhPrivateKemSource
open PqxdhGeneratedBeaconState PqxdhGeneratedBeaconSelector

variable {ι : Type} {baseSpec : OracleSpec ι} {M P I K A : Type} {S B : Nat}

structure Environment (setup : StatefulPhase1Setup baseSpec) (M P I K A : Type) (S B : Nat)
    extends PqxdhGeneratedBeaconSelector.Environment setup M P I K A S B where
  native : PqxdhOptionalKemSource.SourceKemInterface baseSpec
  server : Pqxdh.ServerState
  application : Option Pqxdh.Bytes
  ephemeralGen : OracleComp (unifSpec + baseSpec) (List.Vector UInt8 32)
  aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec
    (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp)
  index : Fin S
  metadata : P

def Environment.parameters {setup : StatefulPhase1Setup baseSpec}
    (env : Environment setup M P I K A S B) : PqxdhPrivateRootSource.Parameters baseSpec :=
  ⟨env.source, env.native, env.server, env.application, env.ephemeralGen⟩

abbrev Post (Selection : Type) (S B : Nat) := Selection →
  RustM (Option PqxdhServerRegistrationPublication.Response) →
    OracleComp (RawCtxProtocolReveals.SourceSpec S B) Bool

/-- Complete native poststate remains private; only the actual response and requested replies enter the public continuation. -/
noncomputable def observer {setup : StatefulPhase1Setup baseSpec}
    (env : Environment setup M P I K A S B)
    (program : Program baseSpec setup.Context S (B + 1)) (post : Post program.Selection S (B + 1)) :
    PqxdhPrivateAcceptedRoot.Continuation setup (driver env.toEnvironment program).State where
  completed output _ := match output with
    | none => pure false
    | some output => PqxdhProtocolRegistration.coins (Prod.fst <$>
        (simulateQ (PqxdhRegistrationProtocolState.sourceImpl env.source env.recordWriter env.senderId env.route env.decode)
          (post output.context.selection.1 (ok none))).run output.context.selection.2)
  accepted output ready := match output with
    | none => pure false
    | some output => PqxdhProtocolRegistration.coins (do
        let result ← (PqxdhRegistrationProtocolState.build env.source env.recordWriter env.aux env.senderId
          env.index env.metadata ready).run output.context.selection.2
        Prod.fst <$> (simulateQ
          (PqxdhRegistrationProtocolState.sourceImpl env.source env.recordWriter env.senderId env.route env.decode)
          (post output.context.selection.1 result.1)).run result.2)

noncomputable def protocol {KemSK : Type} {setup : StatefulPhase1Setup baseSpec}
    (env : Environment setup M P I K A S B)
    (kem : PqxdhKemIndCca.MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1)) (post : Post program.Selection S (B + 1)) :=
  PqxdhGeneratedRootSource.rootProtocol kem env.parameters attachedVerify primitives setup
    (driver env.toEnvironment program) (observer env program post)

noncomputable def actual {KemSK : Type} {setup : StatefulPhase1Setup baseSpec}
    (env : Environment setup M P I K A S B) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : PqxdhKemIndCca.MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1)) (post : Post program.Selection S (B + 1)) :=
  PqxdhGeneratedRootSource.actualGame baseImpl kem env.parameters attachedVerify primitives setup
    (driver env.toEnvironment program) (observer env program post)

noncomputable def correlated {KemSK : Type} {setup : StatefulPhase1Setup baseSpec}
    (env : Environment setup M P I K A S B) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : PqxdhKemIndCca.MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1)) (post : Post program.Selection S (B + 1)) :=
  simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl)
    (PqxdhChallengeSecretRouting.randomMain env.source kem
      (PqxdhInitializerSecrecy.runtimeOfImpl (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl))
      (protocol env kem attachedVerify primitives program post))

/-- The actual generated/native scheduler discharges both source restrictions from the same public adversary, including the failed-writer entry. -/
theorem authenticated_bound {KemSK : Type} {setup : StatefulPhase1Setup baseSpec}
    (env : Environment setup M P I K A S B) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : PqxdhKemIndCca.MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (compatible : PqxdhOptionalKemSource.HonestKeyCompatibility baseImpl kem env.native)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation kem)
    (correct : PqxdhKemIndCca.MlKem768RecipientCorrectness kem
      (PqxdhInitializerSecrecy.runtimeOfImpl (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl)))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (adapter : PqxdhEd25519EufCma.HasAttachedVerificationAdapter attachedVerify primitives.verify)
    (program : Program baseSpec setup.Context S (B + 1))
    (noSign : ∀ reply, (program.main reply).IsQueryBoundP
      (PqxdhProtocolSelector.SelectorClass (PqxdhPrivateKemQueryBounds.SelectorSource (baseSpec := baseSpec) PqxdhJointPhase1AcceptanceComposition.IsSigning)) 0)
    (noCreate : ∀ reply, (program.main reply).IsQueryBoundP
      (PqxdhProtocolSelector.SelectorClass (PqxdhPrivateKemQueryBounds.SelectorSource (baseSpec := baseSpec) PqxdhPrivatePhase1Prefix.Creating)) 0)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : Forgery)
    (post : Post program.Selection S (B + 1)) :
    (actual env baseImpl kem attachedVerify primitives program post).boolDistAdvantage
      (correlated env baseImpl kem attachedVerify primitives program post) ≤
      (advantage primitives (PqxdhGeneratedPhase1Prefix.privateReduction primitives baseImpl kem setup
        (driver env.toEnvironment program) fallback ordinaryFallback)).toReal +
      kem.IND_CCA_Advantage (PqxdhInitializerSecrecy.runtimeOfImpl (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl))
        (PqxdhChallengeSecretRouting.reduction env.source kem
          (protocol env kem attachedVerify primitives program post)).toINDCCA := by
  exact PqxdhGeneratedRootSource.authenticated_correlated_bound baseImpl kem env.parameters compatible functional correct
    attachedVerify primitives adapter setup (driver env.toEnvironment program)
    (fun index publicIdentity generated transcript => driver_source_bound env.toEnvironment program
      PqxdhJointPhase1AcceptanceComposition.IsSigning 0 noSign index publicIdentity generated transcript)
    (fun index publicIdentity generated transcript => driver_source_bound env.toEnvironment program
      PqxdhPrivatePhase1Prefix.Creating 0 noCreate index publicIdentity generated transcript)
    fallback ordinaryFallback (observer env program post)

set_option backward.isDefEq.respectTransparency false in
/-- The same original source run supplies the reached Server identity, allocation and consumed fields used by root acceptance. -/
theorem reached_root_fields {KemSK : Type} {setup : StatefulPhase1Setup baseSpec}
    (env : Environment setup M P I K A S B) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : PqxdhKemIndCca.MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1)) (secretIdentity : M → Pqxdh.Bytes)
    (initialMatch : PqxdhProtocolServerInvariant.RootFields env.source.crypto secretIdentity
      env.senderId env.index env.server env.initial)
    (result : Option (PqxdhPrivateCandidateAcceptance.Outcome
      (PqxdhPrivatePhase1Prefix.Retained setup KemSK (driver env.toEnvironment program).State)) ×
        PqxdhPhase1AcceptanceOracle.BareState 1)
    (present : result ∈ support (PqxdhPrivateSourceCoins.privateRun attachedVerify primitives 1
      (PqxdhGeneratedPhase1Prefix.program baseImpl kem setup (driver env.toEnvironment program)))) :
    ∃ output, result.1.map PqxdhPrivateRootSource.eraseOutput = some output ∧
      PqxdhProtocolServerInvariant.RootFields env.source.crypto secretIdentity env.senderId env.index
        env.server output.context.selection.2 := by
  rw [PqxdhGeneratedPhase1Prefix.program_complete] at present
  simp only [mem_support_bind_iff] at present
  obtain ⟨seed, _, generated, _, selectedResult, selectedSupport, finished⟩ := present
  obtain rfl := eq_of_mem_support_pure _ finished
  have retained := driver_server_fields env.toEnvironment program attachedVerify primitives 1 baseImpl kem generated.secret
    0 (primitives.publicKeys seed) (PqxdhPrivateRootSource.eraseGenerated generated) _ _ selectedResult
    (by simpa only [PqxdhProtocolSelector.selectorImpl, QueryImpl.simulateQ_compose] using selectedSupport)
  obtain ⟨controls, consumed, fields⟩ := retained
  refine ⟨_, rfl, ?_⟩
  simpa only [PqxdhProtocolServerInvariant.RootFields, PqxdhPrivateRootSource.eraseOutput,
    PqxdhPrivateRootSource.eraseRetained, controls, consumed, (fields env.index).1, (fields env.index).2] using initialMatch

/-- Source-derived branch facts execute the actual extracted acceptance, exact 192-byte root derivation and native builder on the reached state. -/
theorem accepted_native_run {setup : StatefulPhase1Setup baseSpec}
    (env : Environment setup M P I K A S B)
    (program : Program baseSpec setup.Context S (B + 1)) (post : Post program.Selection S (B + 1))
    (secretIdentity : M → Pqxdh.Bytes)
    (output : PqxdhPrivateCandidateAcceptance.Outcome
      (PqxdhPrivatePhase1Prefix.Retained setup Unit (driver env.toEnvironment program).State))
    (related : PqxdhProtocolServerInvariant.RootFields env.source.crypto secretIdentity env.senderId
      env.index env.server output.context.selection.2)
    (execution : PqxdhPrivateAcceptedRoot.Ready)
    (admitted : PqxdhProtocolBranchSupport.ReadyFrom env.source env.server env.application (some output) execution) :
    ∃ identity keys ephemeral ciphertext secret,
      output.accepted = some (identity, keys) ∧
      (observer env program post).accepted (some output) execution = PqxdhProtocolRegistration.coins (do
        let result ← (PqxdhProtocolNativeAcceptance.nativeAccept env.source env.recordWriter env.aux secretIdentity
          env.senderId env.index env.metadata env.application identity keys ephemeral ciphertext secret).run output.context.selection.2
        Prod.fst <$> (simulateQ (PqxdhRegistrationProtocolState.sourceImpl env.source env.recordWriter env.senderId env.route env.decode)
          (post output.context.selection.1 result.1)).run result.2) := by
  obtain ⟨identity, keys, ephemeral, ciphertext, secret, candidate, fresh, valid, rfl⟩ := admitted
  refine ⟨identity, keys, ephemeral, ciphertext, secret, candidate, ?_⟩
  simp only [observer]
  rw [PqxdhProtocolNativeAcceptance.native_accept_eq_build env.source env.recordWriter env.aux secretIdentity
    env.senderId env.index env.metadata output.context.selection.2 env.server related env.application
    identity keys ephemeral ciphertext secret fresh valid]

end BeaconcryptCore.Computational.PqxdhGeneratedBeaconExperiment

/--
info: 'BeaconcryptCore.Computational.PqxdhGeneratedBeaconExperiment.authenticated_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhGeneratedBeaconExperiment.authenticated_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhGeneratedBeaconExperiment.reached_root_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhGeneratedBeaconExperiment.reached_root_fields

/--
info: 'BeaconcryptCore.Computational.PqxdhGeneratedBeaconExperiment.accepted_native_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhGeneratedBeaconExperiment.accepted_native_run
