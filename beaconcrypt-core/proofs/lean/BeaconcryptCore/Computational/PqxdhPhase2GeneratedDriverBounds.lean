import BeaconcryptCore.Computational.PqxdhPhase2GeneratedDriver
import BeaconcryptCore.Computational.PqxdhPhase2SourceSchedulerBounds

/-!
The actual generated driver pays for its optional Phase1 writer and every operation of the enlarged native scheduler. Source signing and creation restrictions are derived from explicit caller restrictions on both publication outcomes. The constructed authentication reduction retains the same full source program and all candidate branches.
-/

open OracleComp OracleSpec ENNReal CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhPhase2GeneratedDriverBounds
open PqxdhEd25519EufCma PqxdhJointIdentity PqxdhStatefulPhase1EufCma PqxdhPrivateKemSource
open PqxdhGeneratedBeaconState PqxdhPrivateKemQueryBounds PqxdhPrivatePhase1Prefix
open PqxdhJointPhase1AcceptanceComposition PqxdhPrivateSourceCoins
open PqxdhDynamicIdentityRouting (DynamicForgery)
open PqxdhPhase2GeneratedDriver PqxdhPhase2SourceSchedulerBounds
variable {ι : Type} {baseSpec : OracleSpec ι} {M P I K X Response A : Type} {S B : Nat}

private theorem driver_class_bound {setup : StatefulPhase1Setup baseSpec}
    (env : Environment setup M P I K X Response A S B) (program : Program baseSpec setup.Context S (B + 1))
    (predicate : PqxdhPhase1AcceptanceOracle.SourceSpec.Domain → Prop) [DecidablePred predicate]
    (budget : Nat) (bounded : ∀ reply (state : State setup M P I K A S (B + 1)),
      ((simulateQ (PqxdhPhase2SourceScheduler.compiler env.source env.recordWriter env.senderId
        env.route env.decode env.localImpl) (program.main reply)).run state).IsQueryBoundP
          (SelectorSource (baseSpec := baseSpec) predicate) budget)
    (index : Nat) (publicIdentity : PublicIdentity) (generated : Generated setup Unit)
    (transcript : Phase1PublicTranscript setup.Context) :
    ((driver env program).main index publicIdentity generated transcript).IsQueryBoundP
      (SelectorSource (baseSpec := baseSpec) predicate) budget := by
  have first := PqxdhProtocolSelector.coins_excluded
    (SelectorSource (baseSpec := baseSpec) predicate)
    (by intro coin; simp [SelectorSource])
    (start setup env.phase1Writer index publicIdentity generated env.binding
      (PqxdhGeneratedBeaconSelector.bundle transcript) env.initial)
  simpa only [driver, Nat.zero_add] using isQueryBoundP_bind first (m := budget) (fun started _ => by
    simp only [bind_pure_comp, isQueryBoundP_map_iff]
    exact bounded _ started.2)

/-- Both actual publication outcomes preserve the declared caller signing and creation caps; native finish adds neither class. -/
theorem driver_source_caps {setup : StatefulPhase1Setup baseSpec}
    (env : Environment setup M P I K X Response A S B) (program : Program baseSpec setup.Context S (B + 1))
    (qSign qCreate : Nat)
    (signBound : ∀ reply, (program.main reply).IsQueryBoundP (ForwardedSource (baseSpec := baseSpec) IsSigning) qSign)
    (createBound : ∀ reply, (program.main reply).IsQueryBoundP (ForwardedSource (baseSpec := baseSpec) Creating) qCreate)
    (index : Nat) (publicIdentity : PublicIdentity) (generated : Generated setup Unit)
    (transcript : Phase1PublicTranscript setup.Context) :
    let work := (driver env program).main index publicIdentity generated transcript
    work.IsQueryBoundP (SelectorSource (baseSpec := baseSpec) IsSigning) qSign ∧
      work.IsQueryBoundP (SelectorSource (baseSpec := baseSpec) Creating) qCreate := by
  constructor
  · exact driver_class_bound env program IsSigning qSign
      (fun reply state => (compiler_source_caps env.source env.recordWriter env.senderId env.route env.decode
        env.localImpl (program.main reply) qSign qCreate (signBound reply) (createBound reply) state).1)
      index publicIdentity generated transcript
  · exact driver_class_bound env program Creating qCreate
      (fun reply state => (compiler_source_caps env.source env.recordWriter env.senderId env.route env.decode
        env.localImpl (program.main reply) qSign qCreate (signBound reply) (createBound reply) state).2)
      index publicIdentity generated transcript

/-- The complete generated-driver source bill includes actual Phase1 writer work and every classified native or forwarded scheduler operation. -/
theorem driver_total {setup : StatefulPhase1Setup baseSpec}
    (env : Environment setup M P I K X Response A S B) (program : Program baseSpec setup.Context S (B + 1))
    (qWrite : Nat) (writerBound : ∀ fields primitive, ((env.phase1Writer fields).run primitive).IsTotalQueryBound qWrite)
    (qLocal : Nat) (localBound : ∀ query state, ((env.localImpl query).run state).IsTotalQueryBound qLocal)
    (budget : Budget) (bounded : ∀ reply, Bounded (program.main reply) budget)
    (index : Nat) (publicIdentity : PublicIdentity) (generated : Generated setup Unit)
    (transcript : Phase1PublicTranscript setup.Context) :
    ((driver env program).main index publicIdentity generated transcript).IsTotalQueryBound
      (qWrite + bill qLocal budget) := by
  dsimp only [driver]
  apply isTotalQueryBound_bind
    (PqxdhProtocolQueryBounds.coins_total _ qWrite
      (start_uniform setup env.phase1Writer qWrite writerBound index publicIdentity generated env.binding
        (PqxdhGeneratedBeaconSelector.bundle transcript) env.initial))
  intro started
  simp only [bind_pure_comp, IsTotalQueryBound]
  rw [isQueryBound_map_iff]
  exact compiler_total env.source env.recordWriter env.senderId env.route env.decode env.localImpl qLocal localBound
    (program.main (started.1.map (fun bytes => ⟨transcript, bytes⟩))) budget (bounded _) started.2

/-- The source-restricted enlarged experiment has exactly the original caps of three signing requests and one identity creation. -/
theorem program_source_caps {KemSK : Type} {setup : StatefulPhase1Setup baseSpec}
    (env : Environment setup M P I K X Response A S B) (program : Program baseSpec setup.Context S (B + 1))
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : PqxdhKemIndCca.MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (noSign : ∀ reply, (program.main reply).IsQueryBoundP (ForwardedSource (baseSpec := baseSpec) IsSigning) 0)
    (noCreate : ∀ reply, (program.main reply).IsQueryBoundP (ForwardedSource (baseSpec := baseSpec) Creating) 0) :
    let work := PqxdhGeneratedPhase1Prefix.program baseImpl kem setup (driver env program)
    work.IsQueryBoundP (fun query => IsSigning (translated query)) 3 ∧
      work.IsQueryBoundP (fun query => Creating (translated query)) 1 := by
  constructor
  · exact PqxdhGeneratedPhase1Prefix.program_sign_bound baseImpl kem setup (driver env program)
      (fun index identity generated transcript =>
        (driver_source_caps env program 0 0 noSign noCreate index identity generated transcript).1)
  · exact PqxdhGeneratedPhase1Prefix.program_create_bound baseImpl kem setup (driver env program)
      (fun index identity generated transcript =>
        (driver_source_caps env program 0 0 noSign noCreate index identity generated transcript).2)

/-- Accepted fresh same-identity substitutions in the actual enlarged source execution are charged once to the constructed joint-use weak-EUF reduction. -/
theorem authentication_bound {KemSK : Type} {setup : StatefulPhase1Setup baseSpec}
    (env : Environment setup M P I K X Response A S B) (program : Program baseSpec setup.Context S (B + 1))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (adapter : HasAttachedVerificationAdapter attachedVerify primitives.verify)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : PqxdhKemIndCca.MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (noSign : ∀ reply, (program.main reply).IsQueryBoundP (ForwardedSource (baseSpec := baseSpec) IsSigning) 0)
    (noCreate : ∀ reply, (program.main reply).IsQueryBoundP (ForwardedSource (baseSpec := baseSpec) Creating) 0)
    (fallback : DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery) :
    Pr[Changed | privateRun attachedVerify primitives 1
      (PqxdhGeneratedPhase1Prefix.program baseImpl kem setup (driver env program))] ≤
      PqxdhJointIdentity.advantage primitives
        (PqxdhGeneratedPhase1Prefix.privateReduction primitives baseImpl kem setup (driver env program) fallback ordinaryFallback) := by
  exact PqxdhGeneratedPhase1Prefix.authentication_bound attachedVerify primitives adapter baseImpl kem setup
    (driver env program)
    (fun index identity generated transcript => (driver_source_caps env program 0 0 noSign noCreate index identity generated transcript).1)
    (fun index identity generated transcript => (driver_source_caps env program 0 0 noSign noCreate index identity generated transcript).2)
    fallback ordinaryFallback

/-- The same single authentication loss covers arbitrary complete private continuations; the stopped forgery reduction need not execute their secret-dependent work. -/
theorem authentication_continuation_bound {KemSK Result : Type} {setup : StatefulPhase1Setup baseSpec}
    (env : Environment setup M P I K X Response A S B) (program : Program baseSpec setup.Context S (B + 1))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (adapter : HasAttachedVerificationAdapter attachedVerify primitives.verify)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : PqxdhKemIndCca.MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (noSign : ∀ reply, (program.main reply).IsQueryBoundP (ForwardedSource (baseSpec := baseSpec) IsSigning) 0)
    (noCreate : ∀ reply, (program.main reply).IsQueryBoundP (ForwardedSource (baseSpec := baseSpec) Creating) 0)
    (fallback : DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery)
    (next onChanged : Option (PqxdhPrivateCandidateAcceptance.Outcome
      (Retained setup KemSK (driver env program).State)) × PqxdhPhase1AcceptanceOracle.BareState 1 → ProbComp Result) :
    (𝒟[privateRun attachedVerify primitives 1
      (PqxdhGeneratedPhase1Prefix.program baseImpl kem setup (driver env program)) >>= next]).tvDist
      (𝒟[privateRun attachedVerify primitives 1
        (PqxdhGeneratedPhase1Prefix.program baseImpl kem setup (driver env program)) >>= fun state =>
        if changedBit state then onChanged state else next state]) ≤
      (PqxdhJointIdentity.advantage primitives
        (PqxdhGeneratedPhase1Prefix.privateReduction primitives baseImpl kem setup (driver env program) fallback ordinaryFallback)).toReal := by
  exact PqxdhGeneratedPhase1Prefix.authentication_continuation_bound attachedVerify primitives adapter baseImpl kem setup
    (driver env program)
    (fun index identity generated transcript => (driver_source_caps env program 0 0 noSign noCreate index identity generated transcript).1)
    (fun index identity generated transcript => (driver_source_caps env program 0 0 noSign noCreate index identity generated transcript).2)
    fallback ordinaryFallback next onChanged

/-- Subsequent source work is charged at every complete candidate and private-state result, including publication and finish failure. -/
theorem driver_continuation_total {Result : Type} {setup : StatefulPhase1Setup baseSpec}
    (env : Environment setup M P I K X Response A S B) (program : Program baseSpec setup.Context S (B + 1))
    (qWrite : Nat) (writerBound : ∀ fields primitive, ((env.phase1Writer fields).run primitive).IsTotalQueryBound qWrite)
    (qLocal : Nat) (localBound : ∀ query state, ((env.localImpl query).run state).IsTotalQueryBound qLocal)
    (budget : Budget) (bounded : ∀ reply, Bounded (program.main reply) budget)
    (index : Nat) (publicIdentity : PublicIdentity) (generated : Generated setup Unit)
    (transcript : Phase1PublicTranscript setup.Context)
    (next : Phase1Candidate × (driver env program).State → OracleComp (SelectorSpec baseSpec) Result)
    (qNext : Nat) (nextBound : ∀ result, (next result).IsTotalQueryBound qNext) :
    (((driver env program).main index publicIdentity generated transcript) >>= next).IsTotalQueryBound
      ((qWrite + bill qLocal budget) + qNext) := by
  exact isTotalQueryBound_bind
    (driver_total env program qWrite writerBound qLocal localBound budget bounded index publicIdentity generated transcript)
    nextBound

end BeaconcryptCore.Computational.PqxdhPhase2GeneratedDriverBounds

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2GeneratedDriverBounds.driver_source_caps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2GeneratedDriverBounds.driver_source_caps

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2GeneratedDriverBounds.driver_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2GeneratedDriverBounds.driver_total

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2GeneratedDriverBounds.program_source_caps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2GeneratedDriverBounds.program_source_caps

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2GeneratedDriverBounds.authentication_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2GeneratedDriverBounds.authentication_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2GeneratedDriverBounds.authentication_continuation_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2GeneratedDriverBounds.authentication_continuation_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2GeneratedDriverBounds.driver_continuation_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2GeneratedDriverBounds.driver_continuation_total
