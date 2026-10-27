import BeaconcryptCore.Computational.PqxdhGeneratedBeaconState
import BeaconcryptCore.Computational.PqxdhGeneratedPhase1Prefix
import BeaconcryptCore.Computational.PqxdhProtocolQueryBounds

/-!
The trusted generated driver installs the new Beacon through the actual optional Phase1 publication continuation before the first public scheduler request. Failed serialization supplies no original bundle to the public program. Successful serialization supplies the exact signed fields and writer bytes under the native codec contract. All reached native objects and shared primitive effects remain private continuation state; the public program receives only its entry reply and its requested oracle replies.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhGeneratedBeaconSelector
open PqxdhEd25519EufCma PqxdhJointIdentity PqxdhStatefulPhase1EufCma PqxdhPrivateKemSource
open PqxdhGeneratedPhase1Prefix PqxdhGeneratedBeaconState

variable {ι : Type} {baseSpec : OracleSpec ι} {M P I K A : Type} {S B : Nat}

structure Published (Context : Type) where
  transcript : Phase1PublicTranscript Context
  serialized : Pqxdh.Bytes

structure Program (baseSpec : OracleSpec ι) (Context : Type) (S B : Nat) where
  Selection : Type
  main : Option (Published Context) →
    OracleComp (PqxdhProtocolSelector.Spec baseSpec S B) (Phase1Candidate × Selection)

structure Environment (setup : StatefulPhase1Setup baseSpec) (M P I K A : Type) (S B : Nat) where
  source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource
  recordWriter : RawCtxMixedShared.Writer
  phase1Writer : QueryImpl PqxdhBeaconPhase1Publication.WriterSpec
    (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp)
  senderId : M → Std.U64
  route : RawCtxServerRouting.SenderDecoder
  decode : RawCtxReceive.FrameDecoder
  binding : beaconcrypt_core.pqxdh.ServerBinding
  initial : InitialState setup M P I K A S B

def bundle {Context : Type} (transcript : Phase1PublicTranscript Context) : Phase1Candidate :=
  ⟨transcript.identityKey, transcript.preKey, transcript.oneTimeKey, transcript.pqKey⟩

/-- The private compiler has no identity seed or target KEM secret argument. -/
noncomputable def driver {setup : StatefulPhase1Setup baseSpec}
    (env : Environment setup M P I K A S B) (program : Program baseSpec setup.Context S (B + 1)) : Driver setup where
  State := program.Selection × State setup M P I K A S (B + 1)
  main index publicIdentity generated transcript := do
    let started ← PqxdhProtocolSelector.coins
      (start setup env.phase1Writer index publicIdentity generated env.binding (bundle transcript) env.initial)
    let selected ← (simulateQ
      (PqxdhProtocolSelector.compiler env.source env.recordWriter env.senderId env.route env.decode)
      (program.main (started.1.map (fun bytes => ⟨transcript, bytes⟩)))).run started.2
    pure (selected.1.1, (selected.1.2, selected.2))

/-- Actual Phase1 callback effects and publication precede the entire adaptive native/joint-identity/CCA scheduler. -/
theorem driver_complete {KemSK : Type} {setup : StatefulPhase1Setup baseSpec}
    (env : Environment setup M P I K A S B) (program : Program baseSpec setup.Context S (B + 1))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : PqxdhKemIndCca.MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK)
    (index : Nat) (publicIdentity : PublicIdentity) (generated : Generated setup Unit)
    (transcript : Phase1PublicTranscript setup.Context) (identities : PqxdhPhase1AcceptanceOracle.BareState count) :
    (simulateQ (PqxdhProtocolSelector.selectorImpl attachedVerify primitives count baseImpl kem secret)
      ((driver env program).main index publicIdentity generated transcript)).run identities = (do
        let started ← start setup env.phase1Writer index publicIdentity generated env.binding (bundle transcript) env.initial
        (fun result => ((result.1.1, (result.1.2, result.2.1)), result.2.2)) <$>
          (simulateQ (PqxdhProtocolSelector.directImpl env.source env.recordWriter env.senderId env.route env.decode
            attachedVerify primitives count baseImpl kem secret)
            (program.main (started.1.map (fun bytes => ⟨transcript, bytes⟩)))).run (started.2, identities)) := by
  simp only [driver, simulateQ_bind, StateT.run_bind,
    PqxdhProtocolSelector.selector_coins, bind_map_left]
  apply bind_congr
  intro started
  rw [PqxdhProtocolSelector.compiler_complete]
  simp only [simulateQ_pure, StateT.run_pure, bind_pure_comp, Functor.map_map]

/-- Source signing/creation restrictions come from the actual public program on both serialization outcomes. Native writer coins are excluded only from these declared source classes. -/
theorem driver_class_bound {setup : StatefulPhase1Setup baseSpec}
    (env : Environment setup M P I K A S B) (program : Program baseSpec setup.Context S (B + 1))
    (predicate : (SelectorSpec baseSpec).Domain → Prop) [DecidablePred predicate]
    (excluded : ∀ coin, ¬ predicate (.inr (.inl (.inl coin)))) (budget : Nat)
    (bounded : ∀ reply, (program.main reply).IsQueryBoundP (PqxdhProtocolSelector.SelectorClass predicate) budget)
    (index : Nat) (publicIdentity : PublicIdentity) (generated : Generated setup Unit)
    (transcript : Phase1PublicTranscript setup.Context) :
    ((driver env program).main index publicIdentity generated transcript).IsQueryBoundP predicate budget := by
  have first := PqxdhProtocolSelector.coins_excluded predicate excluded
    (start setup env.phase1Writer index publicIdentity generated env.binding (bundle transcript) env.initial)
  simpa only [driver, Nat.zero_add] using isQueryBoundP_bind first (m := budget) (fun started _ => by
    simpa only [bind_pure_comp, isQueryBoundP_map_iff] using
      PqxdhProtocolSelector.compiler_bound env.source env.recordWriter env.senderId env.route env.decode
        predicate excluded (program.main (started.1.map (fun bytes => ⟨transcript, bytes⟩))) budget (bounded _) started.2)

/-- The ordinary source signing/creation bounds specialize the declared-class law. -/
theorem driver_source_bound {setup : StatefulPhase1Setup baseSpec}
    (env : Environment setup M P I K A S B) (program : Program baseSpec setup.Context S (B + 1))
    (predicate : PqxdhPhase1AcceptanceOracle.SourceSpec.Domain → Prop) [DecidablePred predicate]
    (budget : Nat)
    (bounded : ∀ reply, (program.main reply).IsQueryBoundP
      (PqxdhProtocolSelector.SelectorClass (PqxdhPrivateKemQueryBounds.SelectorSource (baseSpec := baseSpec) predicate)) budget)
    (index : Nat) (publicIdentity : PublicIdentity) (generated : Generated setup Unit)
    (transcript : Phase1PublicTranscript setup.Context) :
    ((driver env program).main index publicIdentity generated transcript).IsQueryBoundP
      (PqxdhPrivateKemQueryBounds.SelectorSource (baseSpec := baseSpec) predicate) budget := by
  have first := PqxdhProtocolSelector.coins_excluded
    (PqxdhPrivateKemQueryBounds.SelectorSource (baseSpec := baseSpec) predicate)
    (by intro coin; simp [PqxdhPrivateKemQueryBounds.SelectorSource])
    (start setup env.phase1Writer index publicIdentity generated env.binding (bundle transcript) env.initial)
  simpa only [driver, Nat.zero_add] using isQueryBoundP_bind first (m := budget) (fun started _ => by
    simpa only [bind_pure_comp, isQueryBoundP_map_iff] using
      PqxdhProtocolSelector.compiler_bound env.source env.recordWriter env.senderId env.route env.decode
        (PqxdhPrivateKemQueryBounds.SelectorSource (baseSpec := baseSpec) predicate)
        (by intro coin; simp [PqxdhPrivateKemQueryBounds.SelectorSource])
        (program.main (started.1.map (fun bytes => ⟨transcript, bytes⟩))) budget (bounded _) started.2)

/-- The full compiler bill charges the Phase1 writer plus every scheduled native coin and forwarded selector request. -/
theorem driver_total {setup : StatefulPhase1Setup baseSpec}
    (env : Environment setup M P I K A S B) (program : Program baseSpec setup.Context S (B + 1))
    (qWrite : Nat) (writerBound : ∀ fields primitive, ((env.phase1Writer fields).run primitive).IsTotalQueryBound qWrite)
    (budget : PqxdhProtocolQueryBounds.Budget)
    (bounded : ∀ reply, PqxdhProtocolQueryBounds.Bounded (program.main reply) budget)
    (index : Nat) (publicIdentity : PublicIdentity) (generated : Generated setup Unit)
    (transcript : Phase1PublicTranscript setup.Context) :
    ((driver env program).main index publicIdentity generated transcript).IsTotalQueryBound
      (qWrite + PqxdhProtocolQueryBounds.compilerBill budget) := by
  dsimp only [driver]
  apply isTotalQueryBound_bind
    (PqxdhProtocolQueryBounds.coins_total _ qWrite
      (start_uniform setup env.phase1Writer qWrite writerBound index publicIdentity generated env.binding (bundle transcript) env.initial))
  intro started
  simp only [bind_pure_comp, IsTotalQueryBound]
  rw [isQueryBound_map_iff]
  exact PqxdhProtocolQueryBounds.compiler_total env.source env.recordWriter env.senderId env.route env.decode
    (program.main (started.1.map (fun bytes => ⟨transcript, bytes⟩))) budget (bounded _) started.2

set_option backward.isDefEq.respectTransparency false in
/-- The actual generated/publication/selection execution preserves every Server field used by root acceptance. -/
theorem driver_server_fields {KemSK : Type} {setup : StatefulPhase1Setup baseSpec}
    (env : Environment setup M P I K A S B) (program : Program baseSpec setup.Context S (B + 1))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : PqxdhKemIndCca.MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK)
    (index : Nat) (publicIdentity : PublicIdentity) (generated : Generated setup Unit)
    (transcript : Phase1PublicTranscript setup.Context) (identities : PqxdhPhase1AcceptanceOracle.BareState count)
    (result : (Phase1Candidate × (program.Selection × State setup M P I K A S (B + 1))) ×
      PqxdhPhase1AcceptanceOracle.BareState count)
    (present : result ∈ support ((simulateQ
      (PqxdhProtocolSelector.selectorImpl attachedVerify primitives count baseImpl kem secret)
      ((driver env program).main index publicIdentity generated transcript)).run identities)) :
    result.1.2.2.controls = env.initial.controls ∧ result.1.2.2.consumed = env.initial.consumed ∧
      ∀ server, (result.1.2.2.roles.1.1 server).server.identity = (env.initial.roles.1.1 server).server.identity ∧
        (result.1.2.2.roles.1.1 server).server.metadata = (env.initial.roles.1.1 server).server.metadata := by
  rw [driver_complete] at present
  dsimp only [driver] at present
  rw [mem_support_bind_iff] at present
  obtain ⟨started, startedSupport, selectedSupport⟩ := present
  rw [support_map] at selectedSupport
  obtain ⟨selected, selectedSupport, rfl⟩ := selectedSupport
  obtain ⟨servers, controls, consumed⟩ := start_servers setup env.phase1Writer index publicIdentity generated
    env.binding (bundle transcript) env.initial started startedSupport
  have fields := PqxdhProtocolServerInvariant.direct_fields env.source env.recordWriter env.senderId env.route env.decode
    attachedVerify primitives count baseImpl kem secret _ _ selected selectedSupport
  obtain ⟨laterControls, laterConsumed⟩ := PqxdhProtocolSelector.direct_controls env.source env.recordWriter env.senderId env.route env.decode
    attachedVerify primitives count baseImpl kem secret _ _ selected selectedSupport
  exact ⟨laterControls.trans controls, laterConsumed.trans consumed, fun server =>
    ⟨(fields server).1.trans (congrArg (fun family => (family server).server.identity) servers),
      (fields server).2.trans (congrArg (fun family => (family server).server.metadata) servers)⟩⟩

end BeaconcryptCore.Computational.PqxdhGeneratedBeaconSelector

/--
info: 'BeaconcryptCore.Computational.PqxdhGeneratedBeaconSelector.driver_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhGeneratedBeaconSelector.driver_complete

/--
info: 'BeaconcryptCore.Computational.PqxdhGeneratedBeaconSelector.driver_class_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhGeneratedBeaconSelector.driver_class_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhGeneratedBeaconSelector.driver_source_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhGeneratedBeaconSelector.driver_source_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhGeneratedBeaconSelector.driver_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhGeneratedBeaconSelector.driver_total

/--
info: 'BeaconcryptCore.Computational.PqxdhGeneratedBeaconSelector.driver_server_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhGeneratedBeaconSelector.driver_server_fields
