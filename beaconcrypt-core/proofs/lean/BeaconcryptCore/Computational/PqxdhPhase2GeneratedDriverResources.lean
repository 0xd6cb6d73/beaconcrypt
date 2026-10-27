import BeaconcryptCore.Computational.PqxdhPhase2GeneratedDriverBounds
import BeaconcryptCore.Computational.PqxdhGeneratedRootQueryBounds

/-!
The enlarged concrete driver retains explicit ordinary uniform, base and logical-decapsulation ledgers. Real local source evaluation expands base and decapsulation work using their own sampling bounds, and actual identity/prekey/KEM/one-time generation is charged in source order. These conservative bounds are derived on complete program syntax, before any generator-order distribution law.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhPhase2GeneratedDriverResources
open PqxdhEd25519EufCma PqxdhJointIdentity PqxdhStatefulPhase1EufCma PqxdhPrivateKemSource
open PqxdhGeneratedBeaconState PqxdhPrivateKemQueryBounds PqxdhPrivatePhase1Prefix
open PqxdhJointPhase1AcceptanceComposition PqxdhPrivateSourceCoins
open PqxdhPhase2GeneratedDriver PqxdhPhase2GeneratedDriverBounds PqxdhPhase2SourceSchedulerBounds
open PqxdhKemIndCca PqxdhPrivateRootQueryBounds
variable {ι : Type} {baseSpec : OracleSpec ι} {M P I K X Response A : Type} {S B : Nat}

/-- Borrowing the actual complete driver charges both source and CCA coin channels, with zero extra creation derived from the caller. -/
theorem driver_uniform {setup : StatefulPhase1Setup baseSpec}
    (env : Environment setup M P I K X Response A S B) (program : Program baseSpec setup.Context S (B + 1))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives) (count : Nat)
    (qWrite : Nat) (writerBound : ∀ fields primitive, ((env.phase1Writer fields).run primitive).IsTotalQueryBound qWrite)
    (qLocal : Nat) (localBound : ∀ query state, ((env.localImpl query).run state).IsTotalQueryBound qLocal)
    (budget : Budget) (bounded : ∀ reply, Bounded (program.main reply) budget)
    (noSign : ∀ reply, (program.main reply).IsQueryBoundP (ForwardedSource (baseSpec := baseSpec) IsSigning) 0)
    (noCreate : ∀ reply, (program.main reply).IsQueryBoundP (ForwardedSource (baseSpec := baseSpec) Creating) 0)
    (index : Nat) (publicIdentity : PublicIdentity) (generated : Generated setup Unit)
    (transcript : Phase1PublicTranscript setup.Context) (identities : PqxdhPhase1AcceptanceOracle.BareState count) :
    ((simulateQ (borrowedSelector attachedVerify primitives count)
      ((driver env program).main index publicIdentity generated transcript)).run identities).IsQueryBoundP
        IsMlKemUniformQuery (2 * (qWrite + bill qLocal budget)) := by
  have total := driver_total env program qWrite writerBound qLocal localBound budget bounded index publicIdentity generated transcript
  simpa only [Nat.mul_zero, Nat.zero_add, two_mul] using
    PqxdhPrivateRootQueryBounds.borrowed_uniform_bound attachedVerify primitives count
      ((driver env program).main index publicIdentity generated transcript) 0
      (qWrite + bill qLocal budget) (qWrite + bill qLocal budget)
      (driver_source_caps env program 0 0 noSign noCreate index publicIdentity generated transcript).2
      total.isQueryBoundP total.isQueryBoundP identities

/-- Every non-uniform ordinary class, including base calls and attempted selected decapsulation, retains an explicit bound from the actual source program. -/
theorem driver_class {setup : StatefulPhase1Setup baseSpec}
    (env : Environment setup M P I K X Response A S B) (program : Program baseSpec setup.Context S (B + 1))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives) (count : Nat)
    (qWrite : Nat) (writerBound : ∀ fields primitive, ((env.phase1Writer fields).run primitive).IsTotalQueryBound qWrite)
    (qLocal : Nat) (localBound : ∀ query state, ((env.localImpl query).run state).IsTotalQueryBound qLocal)
    (budget : Budget) (bounded : ∀ reply, Bounded (program.main reply) budget)
    (predicate : (MlKemCCAOracleSpec baseSpec).Domain → Prop) [DecidablePred predicate]
    (excluded : ∀ coin, ¬ predicate (.inl (.inl coin)))
    (index : Nat) (publicIdentity : PublicIdentity) (generated : Generated setup Unit)
    (transcript : Phase1PublicTranscript setup.Context) (identities : PqxdhPhase1AcceptanceOracle.BareState count) :
    ((simulateQ (borrowedSelector attachedVerify primitives count)
      ((driver env program).main index publicIdentity generated transcript)).run identities).IsQueryBoundP
        predicate (qWrite + bill qLocal budget) := by
  exact PqxdhPrivateRootQueryBounds.borrowed_class_bound attachedVerify primitives count
    ((driver env program).main index publicIdentity generated transcript) predicate excluded
    (qWrite + bill qLocal budget)
    (driver_total env program qWrite writerBound qLocal localBound budget bounded index publicIdentity generated transcript).isQueryBoundP identities

/-- The actual source interpreter pays the sampling costs of every opaque base and selected-decapsulation call, on every reply. -/
theorem private_driver_uniform {KemSK : Type} {setup : StatefulPhase1Setup baseSpec}
    (env : Environment setup M P I K X Response A S B) (program : Program baseSpec setup.Context S (B + 1))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives) (count : Nat)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK)
    (uBase uDecap : Nat) (baseBound : ∀ query, (baseImpl query).IsTotalQueryBound uBase)
    (decapBound : ∀ ciphertext, (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl)
      (kem.decaps secret ciphertext)).IsTotalQueryBound uDecap)
    (qWrite : Nat) (writerBound : ∀ fields primitive, ((env.phase1Writer fields).run primitive).IsTotalQueryBound qWrite)
    (qLocal : Nat) (localBound : ∀ query state, ((env.localImpl query).run state).IsTotalQueryBound qLocal)
    (budget : Budget) (bounded : ∀ reply, Bounded (program.main reply) budget)
    (noSign : ∀ reply, (program.main reply).IsQueryBoundP (ForwardedSource (baseSpec := baseSpec) IsSigning) 0)
    (noCreate : ∀ reply, (program.main reply).IsQueryBoundP (ForwardedSource (baseSpec := baseSpec) Creating) 0)
    (index : Nat) (publicIdentity : PublicIdentity) (generated : Generated setup Unit)
    (transcript : Phase1PublicTranscript setup.Context) (identities : PqxdhPhase1AcceptanceOracle.BareState count) :
    ((simulateQ (privateImpl attachedVerify primitives count)
      (simulateQ (localSelector baseImpl kem secret)
        ((driver env program).main index publicIdentity generated transcript))).run identities).IsTotalQueryBound
      (2 * (qWrite + bill qLocal budget) + uBase * (qWrite + bill qLocal budget) + uDecap * (qWrite + bill qLocal budget)) := by
  rw [localSelector_complete]
  exact PqxdhPrivateRootGameBudgets.evalKem_uniform_bound baseImpl kem secret uBase uDecap baseBound decapBound
    _ _ _ _
    (driver_uniform env program attachedVerify primitives count qWrite writerBound qLocal localBound budget bounded
      noSign noCreate index publicIdentity generated transcript identities)
    (driver_class env program attachedVerify primitives count qWrite writerBound qLocal localBound budget bounded
      IsMlKemBaseQuery (fun _ => by simp [IsMlKemBaseQuery]) index publicIdentity generated transcript identities)
    (driver_class env program attachedVerify primitives count qWrite writerBound qLocal localBound budget bounded
      IsMlKemLogicalDecapsulationQuery (fun _ => by simp [IsMlKemLogicalDecapsulationQuery]) index publicIdentity generated transcript identities)

/-- Actual source generation and the complete enlarged private driver are charged before any evaluated generator interchange. -/
theorem program_uniform {KemSK : Type} {setup : StatefulPhase1Setup baseSpec}
    (env : Environment setup M P I K X Response A S B) (program : Program baseSpec setup.Context S (B + 1))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives) (count : Nat)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (uBase uDecap : Nat) (baseBound : ∀ query, (baseImpl query).IsTotalQueryBound uBase)
    (decapBound : ∀ secret ciphertext, (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl)
      (kem.decaps secret ciphertext)).IsTotalQueryBound uDecap)
    (uPrekey uKeygen uOneTime : Nat)
    (prekeyBound : ∀ identity, (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl)
      (setup.prekey identity)).IsTotalQueryBound uPrekey)
    (keygenBound : (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl) kem.keygen).IsTotalQueryBound uKeygen)
    (oneTimeBound : ∀ identity before target, (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl)
      (setup.oneTime identity before target)).IsTotalQueryBound uOneTime)
    (qWrite : Nat) (writerBound : ∀ fields primitive, ((env.phase1Writer fields).run primitive).IsTotalQueryBound qWrite)
    (qLocal : Nat) (localBound : ∀ query state, ((env.localImpl query).run state).IsTotalQueryBound qLocal)
    (budget : Budget) (bounded : ∀ reply, Bounded (program.main reply) budget)
    (noSign : ∀ reply, (program.main reply).IsQueryBoundP (ForwardedSource (baseSpec := baseSpec) IsSigning) 0)
    (noCreate : ∀ reply, (program.main reply).IsQueryBoundP (ForwardedSource (baseSpec := baseSpec) Creating) 0) :
    (privateRun attachedVerify primitives count
      (PqxdhGeneratedPhase1Prefix.program baseImpl kem setup (driver env program))).IsTotalQueryBound
      (32 + ((uPrekey + (uKeygen + uOneTime)) +
        (2 * (qWrite + bill qLocal budget) + uBase * (qWrite + bill qLocal budget) + uDecap * (qWrite + bill qLocal budget)))) := by
  exact PqxdhGeneratedRootQueryBounds.program_uniform_bound attachedVerify primitives count baseImpl kem setup
    (driver env program) _ _
    (fun identity => PqxdhPrivateRootGameBudgets.generate_uniform_bound baseImpl kem setup uPrekey uKeygen uOneTime
      prekeyBound keygenBound oneTimeBound identity)
    (fun index publicIdentity generated secret transcript identities => private_driver_uniform env program
      attachedVerify primitives count baseImpl kem secret uBase uDecap baseBound (decapBound secret)
      qWrite writerBound qLocal localBound budget bounded noSign noCreate index publicIdentity generated transcript identities)

/-- The actual one-key borrowed prefix pays its new identity and original prekey/one-time samplers before the enlarged native driver. -/
theorem prefix_uniform {setup : StatefulPhase1Setup baseSpec}
    (env : Environment setup M P I K X Response A S B) (program : Program baseSpec setup.Context S (B + 1))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (qPrekey qOneTime : Nat)
    (prekeyBound : ∀ identity, (ccaAmbient (setup.prekey identity)).IsQueryBoundP IsMlKemUniformQuery qPrekey)
    (oneTimeBound : ∀ identity before target, (ccaAmbient (setup.oneTime identity before target)).IsQueryBoundP IsMlKemUniformQuery qOneTime)
    (qWrite : Nat) (writerBound : ∀ fields primitive, ((env.phase1Writer fields).run primitive).IsTotalQueryBound qWrite)
    (qLocal : Nat) (localBound : ∀ query state, ((env.localImpl query).run state).IsTotalQueryBound qLocal)
    (budget : Budget) (bounded : ∀ reply, Bounded (program.main reply) budget)
    (noSign : ∀ reply, (program.main reply).IsQueryBoundP (ForwardedSource (baseSpec := baseSpec) IsSigning) 0)
    (noCreate : ∀ reply, (program.main reply).IsQueryBoundP (ForwardedSource (baseSpec := baseSpec) Creating) 0)
    (target : TargetKemPublicKey) :
    (PqxdhGeneratedRootSource.borrowedPrefix attachedVerify primitives setup (driver env program) target).IsQueryBoundP
      IsMlKemUniformQuery (32 + (qPrekey + (qOneTime + 2 * (qWrite + bill qLocal budget)))) := by
  exact PqxdhGeneratedRootQueryBounds.borrowedPrefix_bound attachedVerify primitives setup (driver env program)
    IsMlKemUniformQuery 32 qPrekey qOneTime (2 * (qWrite + bill qLocal budget))
    (ccaCoins_uniform _ _ sampleSeed_uniform_bound) prekeyBound oneTimeBound
    (fun index publicIdentity generated transcript identities => driver_uniform env program attachedVerify primitives 1
      qWrite writerBound qLocal localBound budget bounded noSign noCreate index publicIdentity generated transcript identities) target

end BeaconcryptCore.Computational.PqxdhPhase2GeneratedDriverResources

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2GeneratedDriverResources.driver_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2GeneratedDriverResources.driver_uniform

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2GeneratedDriverResources.driver_class' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2GeneratedDriverResources.driver_class

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2GeneratedDriverResources.private_driver_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2GeneratedDriverResources.private_driver_uniform

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2GeneratedDriverResources.program_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2GeneratedDriverResources.program_uniform

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2GeneratedDriverResources.prefix_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2GeneratedDriverResources.prefix_uniform
