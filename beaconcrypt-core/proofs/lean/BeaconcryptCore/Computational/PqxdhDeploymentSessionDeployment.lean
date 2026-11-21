-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentSessionFullSecurity

/-! Complete per-owner session agreement for the actual initialized common deployment experiment. The private root receipt is returned beside the merged final deployment state. Initialization failure keeps its actual runtime state and performs no seed draw; success executes the complete adaptive source program and its real continuation. Erasing the new receipt and the two unused old analysis histories recovers CE.game jointly over its public constructor value, output, secrecy ledger, all native fields, produced frames and runtime. -/

open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Computational.PqxdhDeploymentSessionDeployment
open PqxdhServerAuthExperiment PqxdhJointIdentity
open PqxdhDeploymentInterface (FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentServerAuth (serverAuthAdversary serverAuthBound)
open PqxdhDeploymentServerAuthBills (coinCap romCap hashCap totalCap)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhServerAuthBodyCosts PqxdhServerAuthGapDh PqxdhServerAuthAssumptions
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhEd25519EufCma CtxNonceAeadIntCtxt
variable {ι KemSK Reader Response A X : Type} {baseSpec : OracleSpec ι}

abbrev CEOutcome (KemSK X : Type) := PqxdhRegistrationJointServerBirth.ClientCreated Unit × X ×
  PqxdhDeploymentSecrecy.State KemSK
abbrev Outcome (KemSK X : Type) :=
  PqxdhDeploymentSessionFullExecution.PrefixAudit KemSK (PqxdhDeploymentSessionFullSecurity.SourceResult X) ×
    CEOutcome KemSK X

/-- The complete original deployment state, with only its two unused old proof histories forgotten. -/
def eraseNative (state : PqxdhDeploymentNative.State KemSK) : PqxdhDeploymentNative.State KemSK :=
  { state with native := PqxdhRegistrationR1Restriction.eraseShared state.native }

/-- The physical CE projection preserves its output, ledger, owners, caches, counters, frame log and runtime. -/
def eraseCE (outcome : Option (CEOutcome KemSK X) × A) : Option (CEOutcome KemSK X) × A :=
  (outcome.1.map fun result => (result.1, result.2.1, (result.2.2.1, eraseNative result.2.2.2)), outcome.2)

/-- Reassemble the final live record kernels and retain the root receipt beside that same complete state. -/
def merge (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit)
    (outcome : PqxdhDeploymentSessionFullSecurity.Outcome KemSK X) : Outcome KemSK X :=
  (outcome.1, created, outcome.2.1.1.1,
    (outcome.2.1.1.2, PqxdhDeploymentCompile.merge outcome.2.1.2 outcome.2.2))

/-- Actual runtime initialization, then an actually generated Server and one whole adaptive execution with the private target receipt. A failed initialization returns its reached runtime state. -/
noncomputable def game (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (c : Nat) :
    StateT A ProbComp (Option (Outcome KemSK X)) := fun runtime => do
  let ready ← ensureInit.run runtime
  if ready.1 then do
    let seed ← sampleSeed
    let created := PqxdhLiveServerConstruction.initialized (P := Unit) setup.joint identityIndex
      setup.serverKeyId .generated seed
    (fun result => (some (merge (PqxdhRegistrationJointServerBirth.encode created) result), ready.2)) <$>
      PqxdhDeploymentSessionFullExecution.full setup codec checks seed c
        (PqxdhDeploymentCompileSecrecy.compileFull setup codec route bounds mode adversary)
  else pure (none, ready.2)

/-- Forget only the new private root receipt. -/
def forget (outcome : Option (Outcome KemSK X) × A) : Option (CEOutcome KemSK X) × A :=
  (outcome.1.map Prod.snd, outcome.2)

/-- Kernel reassembly commutes with erasing the unused old analysis histories. -/
theorem merge_erased (copies : PqxdhDeploymentCompile.Local) (native : PqxdhRegistrationSchedule.State KemSK) :
    PqxdhDeploymentCompile.merge copies (PqxdhRegistrationR1Restriction.eraseShared native) =
      eraseNative (PqxdhDeploymentCompile.merge copies native) := by
  rfl

/-- The private receipt belongs to the actual complete CE experiment. Its erasure preserves the joint final public constructor, adversary output, secrecy ledger, every physical native field and runtime, under precisely the original CE-COMPILE codec contracts. -/
theorem game_erase (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (runtime : A) (c : Nat) :
    EvalDistEq (forget <$> (game setup codec checks route ensureInit identityIndex bounds mode adversary c).run runtime)
      (eraseCE <$> (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit identityIndex bounds mode adversary).run runtime) := by
  rw [← PqxdhDeploymentCompileSecrecy.compile_full_game setup codec checks route ensureInit identityIndex
    phase1 phase2 bounds mode adversary runtime]
  simp only [game, PqxdhRegistrationJointInitializedSchedule.native, PqxdhLiveServerConstruction.construct,
    StateT.run, map_bind, bind_assoc]
  refine EvalDistEq.bind_right (ensureInit runtime) fun ready => ?_
  cases ready.1 with
  | false => simp only [Bool.false_eq_true, ite_false, pure_bind, map_pure, forget, eraseCE,
      PqxdhDeploymentCompileSecrecy.mergeFull, Option.map_none]; exact EvalDistEq.refl _
  | true =>
      simp only [ite_true, map_bind, bind_map_left]
      refine EvalDistEq.bind_right sampleSeed fun seed => ?_
      have initial_eq : PqxdhRegistrationSchedule.initial (KemSK := KemSK)
          (PqxdhLiveServerConstruction.initialized setup.joint identityIndex setup.serverKeyId .generated seed) =
          PqxdhDeploymentSessionCoupling.initial setup seed := rfl
      rw [initial_eq]
      have coupled := (PqxdhDeploymentSessionFullExecution.full_erase setup codec checks seed c
        (PqxdhDeploymentCompileSecrecy.compileFull setup codec route bounds mode adversary)
        (PqxdhDeploymentServerAuthChain.compiled_unread setup codec route bounds mode adversary)).map
          (fun result => (some (PqxdhRegistrationJointServerBirth.encode
            (PqxdhLiveServerConstruction.initialized (P := Unit) setup.joint identityIndex setup.serverKeyId
              .generated seed), result.1.1.1, (result.1.1.2, PqxdhDeploymentCompile.merge result.1.2 result.2)), ready.2))
      simpa only [Functor.map_map, forget, merge, eraseCE, PqxdhDeploymentCompileSecrecy.mergeFull,
        Option.map_some, Prod.map, id_eq, merge_erased, PqxdhDeploymentServerAuthLocal.base,
        PqxdhLiveServerConstruction.initialized, StateT.run] using coupled

/-- Constructor rejection keeps its reached runtime and performs no Server or owner draw. -/
theorem game_rejected (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (runtime after : A) (c : Nat)
    (rejected : ensureInit.run runtime = pure (false, after)) :
    (game setup codec checks route ensureInit identityIndex bounds mode adversary c).run runtime =
      pure (none, after) := by
  change ensureInit runtime = pure (false, after) at rejected
  simp only [game, StateT.run, rejected, pure_bind, Bool.false_eq_true, ite_false]

/-- Failure means a target acceptance in this complete deployment run lacks the common root, initializer, token, assigned-ID, payload or associated-data agreement receipt. Initialization rejection contributes no failure. -/
noncomputable def decision (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (outcome : Option (Outcome KemSK X) × A) : Bool :=
  match outcome.1 with
  | none => false
  | some result => PqxdhServerAuthCommonProbability.decision setup codec checks result.1.2

theorem decision_spec (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (outcome : Option (Outcome KemSK X) × A) :
    decision setup codec checks outcome = true ↔
      ∃ result, outcome.1 = some result ∧ PqxdhDeploymentSessionReceipt.Failure setup codec checks result.1.2 := by
  rcases outcome with ⟨(_ | result), runtime⟩ <;>
    simp [decision, PqxdhServerAuthCommonProbability.decision, PqxdhDeploymentSessionReceipt.failure_iff]

/-- The actual optional runtime constructor can only lower the complete-agreement failure probability of the generated-Server experiment. -/
theorem decision_le_generated (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (runtime : A) (c : Nat) :
    Pr{let outcome ← (game setup codec checks route ensureInit identityIndex bounds mode adversary c).run runtime}[decision setup codec checks outcome = true] ≤
    Pr{let result ← PqxdhDeploymentSessionFullSecurity.generated setup codec checks route bounds mode adversary c}[PqxdhDeploymentSessionFullSecurity.decision setup codec checks result = true] := by
  simp only [game, StateT.run]
  refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun ready _ => ?_
  cases ready.1 with
  | false =>
      simp only [Bool.false_eq_true, ite_false]
      refine le_of_eq_of_le ((OracleComp.prEvent_eq_zero_iff _ _).mpr ?_) zero_le
      intro outcome member
      simp only [mem_support_pure_iff] at member
      subst member
      simp only [decision, Bool.false_eq_true, not_false_eq_true]
  | true =>
      simp only [ite_true]
      apply le_of_eq
      simp only [PqxdhDeploymentSessionFullSecurity.generated]
      apply prEvent_bind_congr sampleSeed _ _ _ _
      intro seed
      rw [prEvent_map]
      rfl

/-- Complete root, assigned-ID, payload and AD agreement in the initialized, merged common deployment experiment, at exactly the existing per-owner CE-A1 reductions and resource bills. Together with game_erase this concerns one actual whole CE execution, including constructor failure and the complete adaptive suffix. -/
theorem complete_agreement_billed (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X)
    (budget : Budget) (respects : budget.Respects adversary) (runtime : A) (c : Nat)
    (law : X25519ClassLaw setup.source.crypto) (spread : X25519ScalarSpread setup.source.crypto)
    (correct : SourceFullCorrect setup.source setup.hmac)
    (adapter : HasAttachedVerificationAdapter
      (fun identity => setup.source.crypto.verify identity.toList) setup.joint.verify)
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (frameBack : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (fallback : ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery) :
    (𝒟[decision setup codec checks <$>
      (game setup codec checks route ensureInit identityIndex bounds mode adversary c).run runtime] {true}).toReal ≤
      serverAuthBound setup codec checks caps (serverAuthAdversary setup codec route bounds mode adversary c)
        (coinCap caps bounds budget) budget.accept (romCap budget) (hashCap budget) fallback signatureFallback ∧
    PqxdhServerAuthCommonAuthentication.ReductionBills setup codec checks caps
      (serverAuthAdversary setup codec route bounds mode adversary c)
      (coinCap caps bounds budget) budget.accept (romCap budget) (hashCap budget) (totalCap caps bounds budget)
      budget.finish fallback signatureFallback := by
  have original := PqxdhDeploymentSessionFullSecurity.complete_agreement_billed setup codec checks caps bounded route
    bounds mode adversary budget respects c law spread correct adapter writable phase2 frameBack fallback signatureFallback
  refine ⟨?_, original.2⟩
  have gated := decision_le_generated setup codec checks route ensureInit identityIndex bounds mode adversary runtime c
  have finite : 𝒟[PqxdhDeploymentSessionFullSecurity.decision setup codec checks <$>
      PqxdhDeploymentSessionFullSecurity.generated setup codec checks route bounds mode adversary c] {true} ≠ ⊤ := by
    rw [← prEvent_eq_evalDist_singleton _ true]
    exact prEvent_ne_top _
  refine (ENNReal.toReal_mono finite ?_).trans original.1
  simpa only [← prEvent_eq_evalDist_singleton _ true, prEvent_map] using gated

end BeaconcryptCore.Computational.PqxdhDeploymentSessionDeployment

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionDeployment.merge_erased' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionDeployment.merge_erased
/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionDeployment.game_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionDeployment.game_erase
/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionDeployment.game_rejected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionDeployment.game_rejected
/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionDeployment.decision_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionDeployment.decision_spec
/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionDeployment.decision_le_generated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionDeployment.decision_le_generated
/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionDeployment.complete_agreement_billed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionDeployment.complete_agreement_billed
