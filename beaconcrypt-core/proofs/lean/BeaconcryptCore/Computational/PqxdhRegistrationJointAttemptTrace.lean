-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointIssuedAttempts

/-! The private attempt ledger is computed from the actual prepared source fields before writing, using the same one-time draw and complete native return state. Projection removes only this bookkeeping. No successful publication is required to issue a tuple. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptTrace
open PqxdhEd25519EufCma PqxdhJointIdentity PqxdhJointGapDh PqxdhServerAuthExperiment
open PqxdhBeaconPhase1Publication PqxdhRegistrationJointIssuedAttempts
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- Exactly the tuple fed into the source signing block. -/
def keys (setup : Setup baseSpec KemSK)
    (prepared : Prepared ScalarBytes (PqxdhKemIndCca.MlKem768PublicKey × KemSK)) : Phase1KeyTuple :=
  ⟨setup.dh.publicKey prepared.prekey, setup.dh.publicKey prepared.oneTime, prepared.kem.1⟩

/-- Before writing, every prepared tuple is issued; an inactive owner issues none. -/
def issued (setup : Setup baseSpec KemSK) (owner : PqxdhRegistrationSchedule.Owner KemSK)
    (generated : Option ScalarBytes) : List Phase1KeyTuple :=
  ((prepare owner generated).map (keys setup)).toList

/-- The still-live fixed fields are never reconstructed after source erasure. -/
def basis (setup : Setup baseSpec KemSK) (owner : PqxdhRegistrationSchedule.Owner KemSK) :
    Option (X25519PublicKey × PqxdhKemIndCca.MlKem768PublicKey) :=
  match owner.beacon.phase with
  | .fresh _ prekey kem | .freshWithCoins _ prekey _ kem | .initSent _ prekey _ kem =>
      some (setup.dh.publicKey prekey, kem.1)
  | _ => none

abbrev NativeResult (KemSK : Type) :=
  (Option Pqxdh.Bytes × PqxdhRegistrationSchedule.Owner KemSK) × PqxdhDynamicIdentityPool.SourceState

/-- One source operation and its complete chronological attempt ledger. -/
def after (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (index : Nat)
    (owner : PqxdhRegistrationSchedule.Owner KemSK) (generated : Option ScalarBytes)
    (pool : PqxdhDynamicIdentityPool.SourceState) (attempts : List Phase1KeyTuple) :
    NativeResult KemSK × List Phase1KeyTuple :=
  (PqxdhRegistrationJointBundle.after setup codec index owner generated pool,
    attempts ++ issued setup owner generated)

/-- Source order and the actual one-time draw are unchanged; the ledger is not visible to the client. -/
def trace (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (index : Nat)
    (owner : PqxdhRegistrationSchedule.Owner KemSK) (pool : PqxdhDynamicIdentityPool.SourceState)
    (attempts : List Phase1KeyTuple) : ProbComp (NativeResult KemSK × List Phase1KeyTuple) :=
  match owner.beacon.phase with
  | .fresh _ _ _ => (fun scalar => after setup codec index owner (some scalar) pool attempts) <$> sampleScalar
  | .freshWithCoins _ _ _ _ => pure (after setup codec index owner none pool attempts)
  | _ => pure (((none, owner), pool), attempts)

/-- Forgetting the ledger retains the complete native result and identity-pool history of the same execution. -/
theorem trace_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (index : Nat)
    (owner : PqxdhRegistrationSchedule.Owner KemSK) (pool : PqxdhDynamicIdentityPool.SourceState)
    (attempts : List Phase1KeyTuple) :
    Prod.fst <$> trace setup codec index owner pool attempts =
      PqxdhRegistrationJointBundle.trace setup codec index owner pool := by
  cases phase : owner.beacon.phase <;> simp [trace, PqxdhRegistrationJointBundle.trace, phase, after]

/-- An actual prepared tuple uses the current source prekey and KEM fields. -/
theorem issued_basis (setup : Setup baseSpec KemSK) (owner : PqxdhRegistrationSchedule.Owner KemSK)
    (generated : Option ScalarBytes) (tuple : Phase1KeyTuple) (member : tuple ∈ issued setup owner generated) :
    basis setup owner = some (tuple.prekey, tuple.pqKey) := by
  cases phase : owner.beacon.phase <;> cases generated <;>
    simp [issued, prepare, phase, keys] at member <;> subst tuple <;> simp [basis, phase]

/-- A signing attempt and optional publication preserve both fixed source public fields on every branch. -/
theorem after_basis (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (index : Nat)
    (owner : PqxdhRegistrationSchedule.Owner KemSK) (generated : Option ScalarBytes)
    (pool : PqxdhDynamicIdentityPool.SourceState) :
    basis setup (PqxdhRegistrationJointBundle.after setup codec index owner generated pool).1.2 =
      basis setup owner := by
  cases phase : owner.beacon.phase <;> cases generated <;>
    simp only [PqxdhRegistrationJointBundle.after, prepare, phase, Option.map_none, Option.map_some]
  all_goals first | rfl | split <;> simp [publish, basis, phase]

/-- The actual tuple record and three source observations append together before either writer result. Earlier history and private seeds are retained in full. -/
theorem after_history (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (index : Nat)
    (owner : PqxdhRegistrationSchedule.Owner KemSK) (generated : Option ScalarBytes)
    (pool : PqxdhDynamicIdentityPool.SourceState) (attempts : List Phase1KeyTuple)
    (prepared : Prepared ScalarBytes (PqxdhKemIndCca.MlKem768PublicKey × KemSK))
    (ready : prepare owner generated = some prepared) :
    (after setup codec index owner generated pool attempts).2 = attempts ++ [keys setup prepared] ∧
      (after setup codec index owner generated pool attempts).1.2 =
        PqxdhJointPhase1SourceWriter.signedState setup.joint owner.beacon.identity index (keys setup prepared) pool := by
  exact ⟨by simp [after, issued, ready],
    PqxdhRegistrationJointBundle.after_history setup codec index owner generated pool prepared ready⟩

/-- The invariant refers only to still-live native fields and permits their erasure. -/
def LiveFixed (setup : Setup baseSpec KemSK) (owner : PqxdhRegistrationSchedule.Owner KemSK)
    (prekey : X25519PublicKey) (pqKey : PqxdhKemIndCca.MlKem768PublicKey) : Prop :=
  ∀ actual, basis setup owner = some actual → actual = (prekey, pqKey)

/-- Every tuple appended by an actual attempt has the same constructor prekey and KEM fields as its earlier attempts. -/
theorem after_fixed (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (index : Nat)
    (owner : PqxdhRegistrationSchedule.Owner KemSK) (generated : Option ScalarBytes)
    (pool : PqxdhDynamicIdentityPool.SourceState) (attempts : List Phase1KeyTuple)
    (prekey : X25519PublicKey) (pqKey : PqxdhKemIndCca.MlKem768PublicKey)
    (fixed : Fixed prekey pqKey attempts) (live : LiveFixed setup owner prekey pqKey) :
    Fixed prekey pqKey (after setup codec index owner generated pool attempts).2 := by
  intro tuple member
  exact (List.mem_append.mp member).elim (fixed tuple) (fun new => Prod.mk.inj (live _ (issued_basis setup owner generated tuple new)))

/-- The complete native finish can erase the fixed fields but cannot replace them, on success or rejection. -/
theorem finish_basis {A : Type} (setup : Setup baseSpec KemSK)
    (handler : QueryImpl (PqxdhRegistrationJointFinish.NativeSpec KemSK Response) (StateT A ProbComp))
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (owner : PqxdhRegistrationSchedule.Owner KemSK) (before : A)
    (result : (Option Pqxdh.Bytes × PqxdhRegistrationSchedule.Owner KemSK) × A)
    (supported : result ∈ support ((simulateQ handler (PqxdhBeaconPhase2Publication.nativeOwner decode raw owner)).run before)) :
    ∀ actual, basis setup result.1.2 = some actual → basis setup owner = some actual := by
  rcases result with ⟨⟨_ | plaintext, after⟩, final⟩
  case none =>
    have failed := PqxdhBeaconPhase2Publication.native_failure handler decode raw owner after before final supported
    cases phase : owner.beacon.phase <;> simp only [phase] at failed <;>
      simp [failed, PqxdhBeaconPhase2Preparation.abort, basis]
  case some =>
    obtain ⟨staged, _, _, published⟩ := PqxdhBeaconPhase2Publication.native_success handler decode raw plaintext owner after before final supported
    simp [show after = (PqxdhBeaconPhase2Publication.publish owner staged).2 from (congrArg Prod.snd published).symm, PqxdhBeaconPhase2Publication.publish, basis]

end BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptTrace

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptTrace.trace_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptTrace.trace_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptTrace.issued_basis' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptTrace.issued_basis

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptTrace.after_basis' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptTrace.after_basis

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptTrace.after_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptTrace.after_history

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptTrace.after_fixed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptTrace.after_fixed

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptTrace.finish_basis' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptTrace.finish_basis
