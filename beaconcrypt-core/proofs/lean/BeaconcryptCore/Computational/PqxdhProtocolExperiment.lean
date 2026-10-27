import BeaconcryptCore.Computational.PqxdhProtocolAcceptance

/-!
This experiment instantiates the private accepted-root continuation with the actual reached record/public/reveal scheduler and actual native registration builder. The environment is fixed before the fresh target Beacon identity and KEM key are generated. Existing native role objects may be correlated with one another; they cannot depend on that unavailable fresh target seed. The selected Server's immutable root fields are related explicitly to the fixed root parameters, while its evolving peers remain in the reached scheduler state.

The first distance bound changes the authenticated target KEM contribution and retains its repeated private-root correlation. It charges the existing joint Ed25519/X25519 weak-EUF and ordinary one-key ML-KEM IND-CCA reductions once each. It does not replace fixed HKDF, establish independent evolving keys, install the fresh Beacon into the native role family or claim a global protocol theorem. Native allocation, codec, writer and consumption representation contracts remain explicit.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhProtocolExperiment
open PqxdhEd25519EufCma PqxdhJointIdentity PqxdhJointIdentityFamily PqxdhJointIdentityFreshness
open PqxdhJointPhase1SourceWriter PqxdhJointPhase1AcceptanceComposition
open PqxdhPhase1AcceptanceOracle PqxdhPrivateSourceCoins PqxdhPrivateCandidateAcceptance
open PqxdhPrivateKemSource PqxdhPrivatePhase1Prefix
open PqxdhKemIndCca PqxdhInitializerSecrecy PqxdhStatefulPhase1EufCma
open PqxdhJointKdf PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhSecretInputInitializer
open PqxdhSourceAuthenticatedRoot PqxdhHiddenRoot PqxdhPrivateRootSource
open PqxdhChallengeSecretRouting PqxdhPrivateAcceptedRoot

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK : Type}
variable {M P I D K A : Type} {S B : Nat}

/-- Fixed source inputs and native owner state, chosen before fresh target generation. -/
structure Environment (baseSpec : OracleSpec ι) (M P I D K A : Type) (S B : Nat) where
  parameters : Parameters baseSpec
  writer : RawCtxMixedShared.Writer
  aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec
    (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp)
  senderId : M → Std.U64
  route : RawCtxServerRouting.SenderDecoder
  decode : RawCtxReceive.FrameDecoder
  index : Fin S
  metadata : P
  initial : PqxdhRegistrationProtocolState.State M P I D K A S B

abbrev Post (Selection : Type) (S B : Nat) := Option Selection →
  RustM (Option PqxdhServerRegistrationPublication.Response) →
    OracleComp (RawCtxProtocolReveals.SourceSpec S B) Bool

noncomputable def Environment.selector (env : Environment baseSpec M P I D K A S B)
    {Context : Type} (program : PqxdhProtocolSelector.Program baseSpec Context S B) :=
  PqxdhProtocolSelector.selected env.parameters.source env.writer env.senderId env.route env.decode
    program env.initial

noncomputable def Environment.plan (env : Environment baseSpec M P I D K A S B)
    (setup : StatefulPhase1Setup baseSpec) (program : PqxdhProtocolSelector.Program baseSpec setup.Context S B)
    (post : Post program.Selection S B) :=
  PqxdhProtocolRegistration.plan env.parameters.source env.writer env.aux env.senderId env.route env.decode
    setup env.index env.metadata env.initial post

noncomputable def Environment.observer (env : Environment baseSpec M P I D K A S B)
    (setup : StatefulPhase1Setup baseSpec) (program : PqxdhProtocolSelector.Program baseSpec setup.Context S B)
    (post : Post program.Selection S B) := (env.plan setup program post).continuation env.parameters.source

noncomputable def Environment.protocol (env : Environment baseSpec M P I D K A S B)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : StatefulPhase1Setup baseSpec) (program : PqxdhProtocolSelector.Program baseSpec setup.Context S B)
    (post : Post program.Selection S B) :=
  rootProtocol kem env.parameters attachedVerify primitives setup (env.selector program) (env.observer setup program post)

/-- The all-candidate source root runs the compiled adaptive prefix and the reached native response builder. -/
noncomputable def Environment.actual (env : Environment baseSpec M P I D K A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : StatefulPhase1Setup baseSpec) (program : PqxdhProtocolSelector.Program baseSpec setup.Context S B)
    (post : Post program.Selection S B) : ProbComp Bool :=
  actualGame baseImpl kem env.parameters attachedVerify primitives setup (env.selector program)
    (env.observer setup program post)

/-- The target contribution is uniform with the existing same-secret routing; public fixed HKDF remains real. -/
noncomputable def Environment.correlated (env : Environment baseSpec M P I D K A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : StatefulPhase1Setup baseSpec) (program : PqxdhProtocolSelector.Program baseSpec setup.Context S B)
    (post : Post program.Selection S B) : ProbComp Bool :=
  simulateQ (kemAmbientImpl baseImpl) (randomMain env.parameters.source kem (runtimeOfImpl (kemAmbientImpl baseImpl))
    (env.protocol kem attachedVerify primitives setup program post))

noncomputable def Environment.authenticationReduction (env : Environment baseSpec M P I D K A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (primitives : Primitives) (setup : StatefulPhase1Setup baseSpec)
    (program : PqxdhProtocolSelector.Program baseSpec setup.Context S B)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : Forgery) :=
  privateReduction primitives baseImpl kem setup (env.selector program) fallback ordinaryFallback

noncomputable def Environment.kemReduction (env : Environment baseSpec M P I D K A S B)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : StatefulPhase1Setup baseSpec) (program : PqxdhProtocolSelector.Program baseSpec setup.Context S B)
    (post : Post program.Selection S B) :=
  (reduction env.parameters.source kem (env.protocol kem attachedVerify primitives setup program post)).toINDCCA

/-- Original public-program restrictions, not an honest-selected-key premise, discharge the two source restrictions. -/
theorem authenticated_bound (env : Environment baseSpec M P I D K A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (compatible : PqxdhOptionalKemSource.HonestKeyCompatibility baseImpl kem env.parameters.native)
    (functional : FunctionalDecapsulation kem)
    (correct : MlKem768RecipientCorrectness kem (runtimeOfImpl (kemAmbientImpl baseImpl)))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (adapter : HasAttachedVerificationAdapter attachedVerify primitives.verify)
    (setup : StatefulPhase1Setup baseSpec) (program : PqxdhProtocolSelector.Program baseSpec setup.Context S B)
    (noSign : ∀ transcript, (program.main transcript).IsQueryBoundP
      (PqxdhProtocolSelector.SelectorClass (PqxdhPrivateKemQueryBounds.SelectorSource (baseSpec := baseSpec) IsSigning)) 0)
    (noCreate : ∀ transcript, (program.main transcript).IsQueryBoundP
      (PqxdhProtocolSelector.SelectorClass (PqxdhPrivateKemQueryBounds.SelectorSource (baseSpec := baseSpec) Creating)) 0)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : Forgery)
    (post : Post program.Selection S B) :
    (env.actual baseImpl kem attachedVerify primitives setup program post).boolDistance
      (env.correlated baseImpl kem attachedVerify primitives setup program post) ≤
      (advantage primitives (env.authenticationReduction baseImpl kem primitives setup program fallback ordinaryFallback)).toReal +
      (kem.IND_CCA_Advantage (runtimeOfImpl (kemAmbientImpl baseImpl))
        (env.kemReduction kem attachedVerify primitives setup program post)).toReal := by
  exact PqxdhAcceptedRegistration.authenticated_registration_bound baseImpl kem env.parameters compatible functional
    correct attachedVerify primitives adapter setup (env.selector program)
    (fun transcript => PqxdhProtocolSelector.selected_source_bound env.parameters.source env.writer env.senderId
      env.route env.decode program env.initial IsSigning transcript 0 (noSign transcript))
    (fun transcript => PqxdhProtocolSelector.selected_source_bound env.parameters.source env.writer env.senderId
      env.route env.decode program env.initial Creating transcript 0 (noCreate transcript))
    fallback ordinaryFallback (env.plan setup program post)

/-- A supported generated prefix supplies the actual pending token and consumed update before the complete native builder and continued scheduler. -/
theorem reached_accepted_run (env : Environment baseSpec M P I D K A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : StatefulPhase1Setup baseSpec) (program : PqxdhProtocolSelector.Program baseSpec setup.Context S B)
    (post : Post program.Selection S B) (secretIdentity : M → Pqxdh.Bytes)
    (initialMatch : PqxdhProtocolServerInvariant.RootFields env.parameters.source.crypto secretIdentity
      env.senderId env.index env.parameters.server env.initial)
    (prefixResult : Option (Outcome (Retained setup KemSK
      (program.Selection × PqxdhRegistrationProtocolState.State M P I D K A S B))) × BareState 1)
    (present : prefixResult ∈ support (privateRun attachedVerify primitives 1
      (PqxdhPrivatePhase1Prefix.program baseImpl kem setup (env.selector program)))) :
    ∃ output, prefixResult.1.map eraseOutput = some output ∧
      ∀ (identity : Ed25519PublicKey) (keys : Phase1KeyTuple) (ephemeral : List.Vector UInt8 32)
        (ciphertext : MlKem768Ciphertext) (secret : MlKemSharedSecret) (root : RootOutput),
        identity.toList ++ keys.oneTime.toList ∉ env.parameters.server.consumed →
        rootFailure env.parameters.source.crypto env.parameters.server.ikSk ephemeral.toList
          identity keys.prekey keys.oneTime = none →
        ∃ pending,
          PqxdhProtocolAcceptance.accept env.parameters.source.crypto secretIdentity env.senderId env.index env.metadata
            output.context.selection.2 identity keys ephemeral ciphertext secret =
              ok (.Ok (output.context.selection.2.controls env.index, pending)) ∧
          PqxdhRefinement.absBytes pending.root_key_input.bytes = hiddenRootIKM
            (serverCoordinates env.parameters.source.crypto env.parameters.server.ikSk ephemeral.toList
              identity keys.prekey keys.oneTime) secret ∧
          ((env.observer setup program post).accepted (some output)
            (ready env.parameters.server env.parameters.application identity keys.oneTime ephemeral ciphertext root)) =
            PqxdhProtocolRegistration.coins (do
              let result ← (PqxdhRegistrationProtocolState.nativeBuild env.parameters.source env.writer env.aux
                env.senderId env.index env.metadata pending root env.parameters.application).run
                  { output.context.selection.2 with
                    consumed := Function.update output.context.selection.2.consumed env.index
                      (PqxdhRefinement.absBytes pending.registration_id.bytes :: output.context.selection.2.consumed env.index) }
              Prod.fst <$> (simulateQ (PqxdhRegistrationProtocolState.sourceImpl env.parameters.source env.writer
                env.senderId env.route env.decode) (post (some output.context.selection.1) result.1)).run result.2) := by
  obtain ⟨output, outputEq, related⟩ := PqxdhProtocolServerInvariant.reached_root_fields env.parameters.source env.writer
    env.senderId env.route env.decode setup program env.initial attachedVerify primitives 1 baseImpl kem
    prefixResult present secretIdentity env.index env.parameters.server initialMatch
  refine ⟨output, outputEq, ?_⟩
  intro identity keys ephemeral ciphertext secret root fresh valid
  obtain ⟨pending, accepted, rootBytes, _, builder⟩ := PqxdhProtocolAcceptance.accepted_builder
    env.parameters.source env.writer env.aux secretIdentity env.senderId env.index env.metadata
    output.context.selection.2 env.parameters.server related env.parameters.application identity keys ephemeral ciphertext
    secret root fresh valid
  refine ⟨pending, accepted, rootBytes, ?_⟩
  rw [Environment.observer, Environment.plan, PqxdhProtocolRegistration.accepted_run]
  simp only [PqxdhProtocolRegistration.reached, PqxdhProtocolRegistration.choice, Option.map_some, builder]

end BeaconcryptCore.Computational.PqxdhProtocolExperiment

/--
info: 'BeaconcryptCore.Computational.PqxdhProtocolExperiment.authenticated_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhProtocolExperiment.authenticated_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhProtocolExperiment.reached_accepted_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhProtocolExperiment.reached_accepted_run
