import BeaconcryptCore.Computational.PqxdhInitialAliasBound
import BeaconcryptCore.Computational.PqxdhInitialCurrentSecrecy

/-!
The private initializer alias coupling consumes the exact current authenticated-root prepared state and the exact executable Server/post client. Repeated selected coordinates and equal-byte roots are accounted in the same source execution. Public HKDF remains real. The only query-bound premise is a syntactic initializer count for the displayed executable client, which the concrete source certificate supplies separately.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialCurrentAliases
open PqxdhJointKdfGame PqxdhKemIndCca PqxdhCorrelatedExpand PqxdhCorrelatedExpandHybrid
open PqxdhCorrelatedExtractFamily PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhInitialLegalObserver
open PqxdhAuthenticatedRootExperiment PqxdhStatefulPhase1EufCma PqxdhPhase2GeneratedDriver
open PqxdhEd25519EufCma PqxdhJointIdentity PqxdhSourceAuthenticatedRoot PqxdhPrivateAcceptedRoot
variable {ι M P I K X Response A KemSK : Type} {baseSpec : OracleSpec ι} {S B : Nat}
variable {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1)) (post : Post (baseSpec := baseSpec) program.Selection S (B + 1))

noncomputable def selected (context : Context env kem attachedVerify primitives program post) : Message :=
  match context.state with
  | .completed _ => List.Vector.replicate 128 0
  | .pending prepared ephemeral => coordinates (serverCoordinates env.source.crypto env.server.ikSk ephemeral.toList
      prepared.1.context.publicIdentity.ed25519 prepared.1.context.generated.before.publicKey prepared.1.context.generated.after.publicKey)

noncomputable def client (context : Context env kem attachedVerify primitives program post) :
    OracleComp PqxdhInitialLabelCompiler.Spec Bool :=
  match context.state with
  | .completed decision => pure decision
  | .pending prepared ephemeral =>
      accepted env baseImpl kem attachedVerify primitives program post context.secretKey
        (selected env kem attachedVerify primitives program post context) prepared
        (ready env.server env.application prepared.1.context.publicIdentity.ed25519 prepared.1.context.generated.after.publicKey
          ephemeral context.ciphertext (List.Vector.replicate 32 0))

/-- This root-free original client is exactly the current initializer observer in every completed/pending mode and for every supplied64-byte response. -/
theorem observer_client (context : Context env kem attachedVerify primitives program post)
    (response : PqxdhInitialRootLabelService.Response) :
    (simulateQ (PqxdhInitialRootLabelService.labelledFull env.source (QueryImpl.ofLift unifSpec ProbComp)
      (selected env kem attachedVerify primitives program post context) response)
      (client env baseImpl kem attachedVerify primitives program post context)).run' ∅ =
      PqxdhInitialLegalObserver.observe env baseImpl kem attachedVerify primitives program post context response := by
  cases mode : context.state <;> simp only [client, PqxdhInitialLegalObserver.observe, mode, selected, acceptedDecision]
  · rfl

/-- Erasing the private initializer root-candidate trace recovers the exact current ordinary observer for every supplied64 response. -/
theorem trace_decision (context : Context env kem attachedVerify primitives program post) (output : HmacBlock) :
    Prod.fst <$> PqxdhInitialAliasBound.observed env.source
      (selected env kem attachedVerify primitives program post)
      (client env baseImpl kem attachedVerify primitives program post) context output =
      PqxdhInitialLegalObserver.observe env baseImpl kem attachedVerify primitives program post context
        (RawCtxSelectedInitialConstructor.response64 output) := by
  have projected := congrArg (Functor.map Prod.fst)
    (PqxdhInitialRootAliases.trace_source env.source
      (selected env kem attachedVerify primitives program post context)
      (RawCtxSelectedInitialConstructor.response64 output)
      (client env baseImpl kem attachedVerify primitives program post context) (∅, []))
  simpa only [PqxdhInitialAliasBound.observed, Functor.map_map, Prod.map_fst, id_eq,
    ← StateT.run'_eq, observer_client] using projected

noncomputable def tracedRandom : ProbComp (RootOutput × (HmacBlock × PqxdhInitialAliasBound.Trace Bool)) :=
  PqxdhInitialAliasBound.sampleCut
    (PqxdhCorrelatedExtractFamily.prepare baseImpl kem (protocol env kem attachedVerify primitives program post)) >>=
    PqxdhInitialAliasBound.left env.source (selected env kem attachedVerify primitives program post)
      (client env baseImpl kem attachedVerify primitives program post)

noncomputable def consistentRandom : ProbComp Bool :=
  (fun result => result.2.2.1) <$>
    (PqxdhInitialAliasBound.sampleCut
      (PqxdhCorrelatedExtractFamily.prepare baseImpl kem (protocol env kem attachedVerify primitives program post)) >>=
      PqxdhInitialAliasBound.right env.source (selected env kem attachedVerify primitives program post)
        (client env baseImpl kem attachedVerify primitives program post))

/-- The statistical comparison starts at exactly the actual current randomized64 initializer game, retaining the original root draw order before its complete source continuation. -/
theorem random_source :
    (fun result => result.2.2.1) <$> tracedRandom env baseImpl kem attachedVerify primitives program post =
      PqxdhInitialCurrentSecrecy.random env baseImpl kem attachedVerify primitives program post := by
  simp only [tracedRandom, PqxdhInitialAliasBound.sampleCut, PqxdhInitialAliasBound.left,
    map_bind, Functor.map_map, bind_assoc, pure_bind, PqxdhInitialCurrentSecrecy.random,
    PqxdhInitialLegalObserver.sample]
  simp only [trace_decision]

/-- The complete current coordinate-randomized initializer differs from the value-consistent private initializer by at most one uniform-root guess per attempted initializer callback. -/
theorem random_bound (budget : Nat)
    (bounded : ∀ context, (client env baseImpl kem attachedVerify primitives program post context).IsQueryBoundP
      PqxdhInitialRootAliases.IsInitializer budget) :
    (PqxdhInitialCurrentSecrecy.random env baseImpl kem attachedVerify primitives program post).boolDistance
      (consistentRandom env baseImpl kem attachedVerify primitives program post) ≤
        ((budget : ENNReal) / (2 ^ 256 : ENNReal)).toReal := by
  rw [← random_source env baseImpl kem attachedVerify primitives program post]
  have total := PqxdhInitialAliasBound.cut_bound env.source (selected env kem attachedVerify primitives program post)
    (client env baseImpl kem attachedVerify primitives program post)
    (PqxdhCorrelatedExtractFamily.prepare baseImpl kem (protocol env kem attachedVerify primitives program post))
    budget bounded
  have projected := (discreteDistance_map_le
    (fun result : RootOutput × (HmacBlock × PqxdhInitialAliasBound.Trace Bool) => result.2.2.1) _ _).trans total
  simpa only [tracedRandom, consistentRandom, ProbComp.boolDistance,
    ← prEvent_eq_evalDist_singleton] using
    (abs_prEvent_toReal_sub_le_discreteDistance _ _).trans projected

/-- The actual current uniform-root source endpoint reaches one value-consistent randomized initializer through ordinary Extract and two-query HMAC reductions plus the explicit original initializer-candidate loss. -/
theorem primitive_bound (hmac : HmacSha512) (correct : PqxdhFullSecretInputKdf.SourceFullCorrect env.source hmac)
    (budget : Nat)
    (bounded : ∀ context, (client env baseImpl kem attachedVerify primitives program post context).IsQueryBoundP
      PqxdhInitialRootAliases.IsInitializer budget) :
    (uniformGame (PqxdhCorrelatedExpand.rootReduction env.source baseImpl kem
      (protocol env kem attachedVerify primitives program post))).boolDistance
      (consistentRandom env baseImpl kem attachedVerify primitives program post) ≤
    (extractRealGame hmac (PqxdhInitialCurrentSecrecy.joint env baseImpl kem attachedVerify primitives program post)
      (fullExtractReduction hmac .ratchet (PqxdhInitialCurrentSecrecy.observer env baseImpl kem attachedVerify primitives program post))).boolDistance
      (extractUniformGame (PqxdhInitialCurrentSecrecy.joint env baseImpl kem attachedVerify primitives program post)
        (fullExtractReduction hmac .ratchet (PqxdhInitialCurrentSecrecy.observer env baseImpl kem attachedVerify primitives program post))) +
    (hmacPrfRealGame hmac (fullExpandReduction .ratchet
      (PqxdhInitialCurrentSecrecy.joint env baseImpl kem attachedVerify primitives program post)
      (PqxdhInitialCurrentSecrecy.observer env baseImpl kem attachedVerify primitives program post))).boolDistance
      (hmacPrfRandomGame (fullExpandReduction .ratchet
        (PqxdhInitialCurrentSecrecy.joint env baseImpl kem attachedVerify primitives program post)
        (PqxdhInitialCurrentSecrecy.observer env baseImpl kem attachedVerify primitives program post))) +
      ((budget : ENNReal) / (2 ^ 256 : ENNReal)).toReal := by
  exact (ProbComp.boolDistance_triangle _
    (PqxdhInitialCurrentSecrecy.random env baseImpl kem attachedVerify primitives program post) _).trans
    (add_le_add (PqxdhInitialCurrentSecrecy.primitive_bound env baseImpl kem attachedVerify primitives program post hmac correct)
      (random_bound env baseImpl kem attachedVerify primitives program post budget bounded))

end BeaconcryptCore.Computational.PqxdhInitialCurrentAliases

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialCurrentAliases.observer_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialCurrentAliases.observer_client

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialCurrentAliases.trace_decision' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialCurrentAliases.trace_decision

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialCurrentAliases.random_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialCurrentAliases.random_source

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialCurrentAliases.random_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialCurrentAliases.random_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialCurrentAliases.primitive_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialCurrentAliases.primitive_bound
