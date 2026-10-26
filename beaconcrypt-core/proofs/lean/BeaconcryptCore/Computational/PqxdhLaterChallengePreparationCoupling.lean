import BeaconcryptCore.Computational.PqxdhLaterChallengeCollectorCoupling

/-! Couple the actual full generated preparation: the original pending packet and cache are shared, while common completed decisions retain their complete distributions. -/
open OracleComp OracleSpec CoreModels Aeneas OracleComp.ProgramLogic.Relational
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace BeaconcryptCore.Computational.PqxdhLaterChallengePreparationCoupling
open PqxdhEd25519EufCma PqxdhJointIdentity PqxdhStatefulPhase1EufCma PqxdhPrivateKemSource
open PqxdhGeneratedBeaconState PqxdhPhase1AcceptanceOracle PqxdhKemIndCca PqxdhInitializerSecrecy
open CtxRomAuth AdaptiveCtxSharedHash
variable {ι M P I K X Response A KemSK : Type} {baseSpec : OracleSpec ι} {S B : Nat}
variable (setup : StatefulPhase1Setup baseSpec)
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (callbacks : PqxdhSourceAuxiliary.Callbacks A)
    (program : PqxdhPhase2GeneratedDriver.Program baseSpec setup.Context S (B + 1))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))


local notation "Output" => PqxdhBorrowedSharedPrefix.LocalOutput (M := M) (P := P) (I := I) (K := K) (A := A) setup program
local notation "Mode" => PqxdhCommonSharedDispatch.Mode Output
local notation "Post" => PqxdhAuthenticatedRootExperiment.Post (baseSpec := baseSpec) program.Selection S (B + 1)

/-- Only the literal completed preparation constructor satisfies this predicate. -/
def Completed {PacketOutput : Type} : PqxdhCommonSharedDispatch.Mode PacketOutput → Prop
  | .completed _ => True
  | .pending _ _ => False

/-- A shared full preparation outcome or two retained completed outcomes. In particular, a pending source packet has the same private fields and actual reached ROM cache in both worlds. -/
def Related (left right : Mode × CtxRO.QueryCache) : Prop :=
  left = right ∨ (Completed left.1 ∧ Completed right.1)

/-- Arbitrary common executions retain both complete decision/cache marginals inside the explicit completed branch. -/
theorem completed_map (left right : OracleComp HashSpec Bool) (firstCache secondCache : CtxRO.QueryCache) :
    RelTriple
      ((simulateQ hashImpl ((PqxdhCommonSharedDispatch.Mode.completed : Bool → Mode) <$> left)).run firstCache)
      ((simulateQ hashImpl ((PqxdhCommonSharedDispatch.Mode.completed : Bool → Mode) <$> right)).run secondCache)
      (Related setup program) := by
  simp only [simulateQ_map, StateT.run_map]
  apply relTriple_map
  exact relTriple_post_mono (PqxdhFirstRecordStopTagged.product_coupling
    (fun _ _ => True.intro) (fun _ _ => True.intro)) (fun _ _ _ => Or.inr ⟨True.intro, True.intro⟩)

/-- The actual admission dispatch shares every pre-admission draw and pending source state for arbitrary outside continuations. Changed, failed and ineligible/common executions keep their original completed distributions. -/
theorem dispatch (first second : Post) (secret : KemSK) (output : Output) (cache : CtxRO.QueryCache) :
    RelTriple
      ((simulateQ hashImpl (PqxdhCommonSharedDispatch.dispatch setup env callbacks program first attachedVerify primitives baseImpl kem secret output)).run cache)
      ((simulateQ hashImpl (PqxdhCommonSharedDispatch.dispatch setup env callbacks program second attachedVerify primitives baseImpl kem secret output)).run cache)
      (Related setup program) := by
  simp only [PqxdhCommonSharedDispatch.dispatch]
  split
  · exact relTriple_post_mono (relTriple_refl _) (fun _ _ same => Or.inl same)
  · split
    · simp only [simulateQ_bind, StateT.run_bind]
      refine relTriple_bind (relTriple_refl _) ?_
      rintro reached _ rfl
      split
      · exact relTriple_post_mono (relTriple_refl _) (fun _ _ same => Or.inl same)
      · simp only [simulateQ_bind, StateT.run_bind]
        refine relTriple_bind (relTriple_refl _) ?_
        rintro encapsulated _ rfl
        exact completed_map setup program _ _ encapsulated.2 encapsulated.2
    · exact completed_map setup program _ _ cache cache

/-- The same generated identity/prekey/one-time prefix supplies both dispatches, retaining actual selection, all private fields and the ROM state before either outside continuation. -/
theorem run (first second : Post) (secret : KemSK) (target : TargetKemPublicKey) (cache : CtxRO.QueryCache) :
    RelTriple
      ((simulateQ hashImpl (PqxdhSourceSharedPreparation.run setup env callbacks program first attachedVerify primitives baseImpl kem secret target)).run cache)
      ((simulateQ hashImpl (PqxdhSourceSharedPreparation.run setup env callbacks program second attachedVerify primitives baseImpl kem secret target)).run cache)
      (Related setup program) := by
  simp only [PqxdhSourceSharedPreparation.run, simulateQ_bind, StateT.run_bind]
  refine relTriple_bind (relTriple_refl _) ?_
  rintro reached _ rfl
  exact dispatch setup env callbacks program attachedVerify primitives baseImpl kem first second secret reached.1 reached.2

local notation "Packet" => PqxdhSourceSharedPreparation.Packet Mode KemSK

/-- The entire private generated packet and reached cache agree whenever preparation is pending; completed branches retain both original outputs. -/
def PacketRelated (left right : Packet × CtxRO.QueryCache) : Prop :=
  left = right ∨ (Completed left.1.state ∧ Completed right.1.state)

/-- Couple the full original KEM generation, source preparation and outer encapsulation in source order. The locally generated KEM secret and challenge ciphertext remain only in the private packet; all common completed probability is retained. -/
theorem prepare (first second : Post) (cache : CtxRO.QueryCache) :
    RelTriple
      ((simulateQ hashImpl (PqxdhSourceSharedPreparation.prepare setup env callbacks program first attachedVerify primitives baseImpl kem)).run cache)
      ((simulateQ hashImpl (PqxdhSourceSharedPreparation.prepare setup env callbacks program second attachedVerify primitives baseImpl kem)).run cache)
      (PacketRelated setup program) := by
  simp only [PqxdhSourceSharedPreparation.prepare, simulateQ_bind, StateT.run_bind]
  refine relTriple_bind (relTriple_refl _) ?_
  rintro keys _ rfl
  refine relTriple_bind (run setup env callbacks program attachedVerify primitives baseImpl kem first second keys.1.2 keys.1.1 keys.2) ?_
  intro left right related
  rcases related with rfl | ⟨leftCompleted, rightCompleted⟩
  · exact relTriple_post_mono (relTriple_refl _) (fun _ _ same => Or.inl same)
  · simp only [RawCtxSelectiveSharedRom.coins_complete, bind_map_left, simulateQ_pure, StateT.run_pure]
    refine relTriple_bind (relTriple_refl _) ?_
    rintro encapsulated _ rfl
    exact relTriple_pure_pure (Or.inr ⟨leftCompleted, rightCompleted⟩)

end BeaconcryptCore.Computational.PqxdhLaterChallengePreparationCoupling

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengePreparationCoupling.completed_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengePreparationCoupling.completed_map

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengePreparationCoupling.dispatch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengePreparationCoupling.dispatch

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengePreparationCoupling.run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengePreparationCoupling.run

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengePreparationCoupling.prepare' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengePreparationCoupling.prepare
