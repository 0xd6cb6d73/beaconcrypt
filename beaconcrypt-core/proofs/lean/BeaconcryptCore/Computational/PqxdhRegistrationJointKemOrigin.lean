-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointKemInitialization
import BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptOrigin

/-! The actual source signing-attempt tuple fixes the selected KEM public key by creation index. No public-key injectivity or honest-candidate assumption is used. Source authentication must still exclude the unissued-field alternative using the generated-index report history and freshness reduction. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointKemOrigin
open PqxdhJointIdentity PqxdhServerAuthExperiment PqxdhServerAuthNative PqxdhEd25519EufCma
open PqxdhRegistrationJointAttemptLedger (Receipt)
open PqxdhRegistrationJointIssuedAttempts (Fixed)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A Result : Type}

/-- An issued tuple uses the immutable constructor PQ field, even if its writer failed or later source operations erased live material. -/
theorem issued_pq (receipt : Receipt) (fixed : Fixed receipt.prekey receipt.pqKey receipt.attempts)
    (decoded : Phase1KeyTuple) (issued : decoded ∈ receipt.attempts) : decoded.pqKey = receipt.pqKey :=
  (fixed decoded issued).2

/-- The original created-prefix lookup determines the chosen public key at its exact reservation index. Equal public encodings at other indices do not affect this argument. -/
theorem selected_public (count : Nat) (selected : Fin (count + 1))
    (chosen : MlKem768PublicKey × KemSK) (others : Fin count → MlKem768PublicKey × KemSK)
    (created : Nat) (publicKey : MlKem768PublicKey)
    (found : ((List.ofFn (selected.insertNth chosen others)).take created)[selected.val]?.map Prod.fst = some publicKey) :
    publicKey = chosen.1 := by
  by_cases active : selected.val < created
  · simp only [List.getElem?_take, active, ite_true, _root_.dite_true, List.getElem?_ofFn, selected.isLt,
      Fin.eta, Fin.insertNth_apply_same, Option.map_some, Option.some.injEq] at found
    exact found.symm
  · simp [active] at found

/-- A literal accepted raw candidate after an actual initialized source prefix has either the selected owner's exact generated PQ key or an unissued original signed field at that owner's source index. The created-prefix relation is the concrete reservation projection, not a key-honesty or injectivity assumption. -/
theorem raw_selected (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (shortRejects : ∀ (publicKey : Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (work : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result)
    (runtime : A) (after : PqxdhRegistrationJointServerPrefix.State KemSK A)
    (outcome : PqxdhRegistrationJointInitializedSchedule.SourceOutcome KemSK Result)
    (supported : (some outcome, after) ∈ support ((PqxdhRegistrationJointInitializedSchedule.source setup codec checks ensureInit supplied work).run
      ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime)))
    (address : Nat) (entry : PqxdhRegistrationJointOwnership.Entry KemSK)
    (found : outcome.2.2.owners[address]? = some entry)
    (count : Nat) (selected : Fin (count + 1)) (chosen : MlKem768PublicKey × KemSK)
    (others : Fin count → MlKem768PublicKey × KemSK) (created : Nat)
    (reserved : outcome.2.2.pool.2.keys = (List.ofFn (selected.insertNth chosen others)).take created)
    (slot : entry.kemIndex = selected.val)
    (seed : IdentitySeed) (raw : Pqxdh.Bytes) (received : NativeState KemSK) (session : Nat)
    (accepted : (some session, received) ∈ support ((nativeAccept setup codec checks seed
      PqxdhRegistrationSchedule.observationScalar raw).run outcome.2.2.shared)) :
    ∃ original identity decoded,
      PqxdhRegistrationJointRawSignatures.candidate codec raw = some original ∧
      acceptPhase1Candidate setup.joint.verify original = some (identity, decoded) ∧
      (decoded.pqKey = chosen.1 ∨
        PqxdhRegistrationJointAttemptOrigin.Unissued outcome.2.2 entry.identityIndex original) := by
  obtain ⟨original, identity, decoded, receipt, parsed, verified, fixed, _, kem, _, origin⟩ :=
    PqxdhRegistrationJointAttemptOrigin.raw_origin setup codec checks shortRejects ensureInit supplied work runtime
      after outcome supported address entry found seed raw received session accepted
  refine ⟨original, identity, decoded, parsed, verified, ?_⟩
  rcases origin with issued | unissued
  · have selectedKey := selected_public count selected chosen others created receipt.pqKey
      (by simpa only [reserved, slot] using kem)
    exact Or.inl ((issued_pq receipt fixed decoded issued).trans selectedKey)
  · exact Or.inr unissued

end BeaconcryptCore.Computational.PqxdhRegistrationJointKemOrigin

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemOrigin.issued_pq' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemOrigin.issued_pq

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemOrigin.selected_public' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemOrigin.selected_public

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemOrigin.raw_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemOrigin.raw_selected
