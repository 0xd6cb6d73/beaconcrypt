-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointServiceSchedule

/-! Exact emitted-service classes for the complete executable registration scheduler. The ledger counts failed attempts and all typed replies. Native macro work retains its separate complete source uniform bill. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointServiceCosts
open PqxdhJointIdentity PqxdhJointGapDh PqxdhServerAuthExperiment
open PqxdhRegistrationJointServiceSchedule
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result : Type}

inductive Kind where
  | identityCreate | signing | staticDh | kemCreate | decapsulate | uniform | other
  | tail | accept | build | hmac | hash | read
  deriving DecidableEq

def poolClass : (PqxdhLiveKemBirth.Spec KemSK).Domain → Kind
  | .inl (.inr .create) => .identityCreate
  | .inl (.inr (.service _ (.sign _))) => .signing
  | .inl (.inr (.service _ (.staticDh _))) => .staticDh
  | .inr (.inr .create) => .kemCreate
  | .inr (.inr (.decapsulate _ _)) => .decapsulate
  | .inr (.inl _) => .uniform
  | _ => .other

def classify : (Spec KemSK Response).Domain → Kind
  | .inl (.inl query) => poolClass (KemSK := KemSK) query
  | .inl (.inr _) => .tail
  | .inr (.accept _) => .accept
  | .inr (.build _ _) => .build
  | .inr (.hmac _ _) => .hmac
  | .inr (.hash _) => .hash
  | .inr (.reveal _) => .read

def createCap (kind : Kind) : Nat :=
  (if kind = .identityCreate then 1 else 0) +
    ((if kind = .uniform then 32 else 0) + (if kind = .kemCreate then 1 else 0))

def bundleCap (kind : Kind) : Nat :=
  (if kind = .uniform then 32 else 0) + (if kind = .signing then 3 else 0)

def finishCap : Kind → Nat
  | .decapsulate | .staticDh => 1
  | .tail => 56
  | _ => 0

/-- The sparse matrix charges every actual source attempt against its emitted backend capabilities. -/
def cost (kind : Kind) : Fin 9 → Nat :=
  ![if kind = .uniform then 1 else 0, createCap kind, bundleCap kind,
    if kind = .accept then 1 else 0, if kind = .build then 1 else 0, finishCap kind,
    if kind = .hmac then 1 else 0, if kind = .hash then 1 else 0, if kind = .read then 1 else 0]

/-- The actual local sampler spends only local uniform queries; every identity, KEM, native and reveal capability remains unused. -/
theorem coins_queries (work : ProbComp Result) (budget : Nat) (bounded : work.IsTotalQueryBound budget) (kind : Kind) :
    (PqxdhLiveKemBirth.coins (KemSK := KemSK) work).IsQueryBoundP
      (fun query => poolClass (KemSK := KemSK) query = kind) (if kind = .uniform then budget else 0) := by
  rw [PqxdhLiveKemBirth.coins_class]
  cases kind <;> simp_all [poolClass, isQueryBoundP_true_iff]

/-- A constructor emits exactly the creation capabilities and its local prekey draw allowance; no signing, decapsulation, DH, reveal or native macro is hidden in this client. -/
theorem creation_queries (kind : Kind) :
    (PqxdhRegistrationJointCreation.client (KemSK := KemSK)).IsQueryBoundP
      (fun query => poolClass (KemSK := KemSK) query = kind) (createCap kind) := by
  unfold PqxdhRegistrationJointCreation.client createCap
  apply isQueryBoundP_bind
  case h => simp +contextual [isQueryBoundP_query_iff, poolClass, eq_comm]
  case h' =>
    rintro (_ | identity) _
    · trivial
    · apply isQueryBoundP_bind (coins_queries sampleScalar 32 sampleScalar_uniform kind)
      simp +contextual [bind_pure_comp, isQueryBoundP_map_iff, isQueryBoundP_query_iff, poolClass, eq_comm]

set_option backward.isDefEq.respectTransparency false in
/-- The actual ordered signing block emits at most three signing attempts and no other backend capability. -/
theorem signing_queries (codec : Codec Reader Response) (index : Nat)
    (identity : PqxdhEd25519EufCma.Ed25519PublicKey) (keys : PqxdhEd25519EufCma.Phase1KeyTuple) (kind : Kind) :
    (simulateQ (PqxdhRegistrationJointBundleCompiler.compiler (KemSK := KemSK) codec)
      (PqxdhLivePhase1Bundle.signing (D := ScalarBytes) index identity keys)).IsQueryBoundP
        (fun query => poolClass (KemSK := KemSK) query = kind) (if kind = .signing then 3 else 0) := by
  by_cases signs : kind = .signing
  all_goals simp [PqxdhLivePhase1Bundle.signing, PqxdhJointPhase1SourceWriter.signingProgram,
    PqxdhRegistrationJointBundleCompiler.compiler, poolClass, isQueryBoundP_query_bind_iff, signs, eq_comm]
  all_goals intro pre; cases pre <;> simp [PqxdhRegistrationJointBundleCompiler.compiler, isQueryBoundP_query_bind_iff, signs]
  all_goals intro one; cases one <;> simp [PqxdhRegistrationJointBundleCompiler.compiler, isQueryBoundP_query_iff, signs]

/-- The retained literal optional writer performs local codec work and emits no private-service request. -/
theorem writing_queries (codec : Codec Reader Response) (identity : Std.Array Std.U8 32#usize)
    (candidate : PqxdhEd25519EufCma.Phase1Candidate) (generated : Option ScalarBytes)
    (owner : PqxdhRegistrationJointBundle.Owner) (kind : Kind) :
    (simulateQ (PqxdhRegistrationJointBundleCompiler.compiler (KemSK := KemSK) codec)
      (PqxdhLivePhase1Bundle.writing identity candidate generated owner)).IsQueryBoundP
        (fun query => poolClass (KemSK := KemSK) query = kind) 0 := by
  unfold PqxdhLivePhase1Bundle.writing PqxdhBeaconPhase1Publication.afterSigning
  split <;> simp [PqxdhRegistrationJointBundleCompiler.compiler]
  split <;> simp

/-- Source preparation and optional publication add no backend request beyond the three actual signatures. -/
theorem after_queries (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (generated : Option ScalarBytes) (owner : PqxdhRegistrationJointBundle.Owner) (kind : Kind) :
    (simulateQ (PqxdhRegistrationJointBundleCompiler.compiler (KemSK := KemSK) codec)
      (PqxdhLivePhase1Bundle.afterGenerated (PqxdhRegistrationJointBundle.projection setup) generated owner)).IsQueryBoundP
        (fun query => poolClass (KemSK := KemSK) query = kind) (if kind = .signing then 3 else 0) := by
  unfold PqxdhLivePhase1Bundle.afterGenerated
  split
  all_goals simp only [simulateQ_pure, isQueryBoundP_pure, simulateQ_bind]
  apply isQueryBoundP_bind (n := if kind = .signing then 3 else 0) (m := 0) (signing_queries codec _ _ _ kind)
  rintro (_ | candidate) _
  · trivial
  · exact writing_queries codec _ candidate generated owner kind

/-- Every actual bundle emits at most 32 one-time byte draws and three signatures, including all writer failures and retained-coin retries. -/
theorem bundle_queries (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (owner : PqxdhRegistrationJointBundle.Owner) (kind : Kind) :
    (simulateQ (PqxdhRegistrationJointBundleCompiler.compiler (KemSK := KemSK) codec)
      (PqxdhLivePhase1Bundle.bundle (PqxdhRegistrationJointBundle.projection setup) owner)).IsQueryBoundP
        (fun query => poolClass (KemSK := KemSK) query = kind) (bundleCap kind) := by
  cases phase : owner.beacon.phase <;> simp only [PqxdhLivePhase1Bundle.bundle, phase,
    simulateQ_pure, isQueryBoundP_pure, simulateQ_bind, simulateQ_spec_query]
  case fresh =>
    apply isQueryBoundP_bind
    case h =>
      exact coins_queries (some <$> sampleScalar) 32
        (by simpa only [IsTotalQueryBound, isQueryBound_map_iff] using sampleScalar_uniform) kind
    case h' => exact fun generated _ => after_queries setup codec generated owner kind
  case freshWithCoins => exact (after_queries setup codec none owner kind).mono (Nat.le_add_left _ _)

end BeaconcryptCore.Computational.PqxdhRegistrationJointServiceCosts

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointServiceCosts.coins_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointServiceCosts.coins_queries

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointServiceCosts.creation_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointServiceCosts.creation_queries

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointServiceCosts.signing_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointServiceCosts.signing_queries

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointServiceCosts.writing_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointServiceCosts.writing_queries

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointServiceCosts.after_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointServiceCosts.after_queries

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointServiceCosts.bundle_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointServiceCosts.bundle_queries
