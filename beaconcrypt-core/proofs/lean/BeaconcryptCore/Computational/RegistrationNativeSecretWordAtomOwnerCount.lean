-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerSource
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerTrace
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerInstallPrefix

/-! The actual traced incoming source uses the same terminal owner credit as the original controller. Preparation and abort cannot add attempts, and any material-stage atom identifies the selected retained owner through the actual indexed decapsulation and derived roster alignment. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerCount
open PqxdhServerAuthExperiment (Setup)
open PqxdhRecordLiftInterface (Role)
open RegistrationNativeSecretWordMessage (Message BeaconReady)
open RegistrationNativeSecretWord (Key Word)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordAtomOwnerSource (State drop routing)
open RegistrationNativeSecretWordAtomInstallTrace (atom count)
open RegistrationNativeSecretWordAtomInstallPredicate (LocalInstall)
open RegistrationServerReferenceCompiler (Environment)
open RegistrationBeaconReferenceCompiler (SelectedOwner)
open PqxdhKemIndCca
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

private theorem routing_paired (setup : Setup base KemSK) (scalar : Option PqxdhJointGapDh.ScalarBytes)
    (work : OracleComp (RegistrationNativeSecretWordBeaconMaterial.Spec n) Value) :
    simulateQ (routing (KemSK := KemSK) setup scalar) (simulateQ RegistrationNativeSecretWordInterface.paired work) =
      RegistrationNativeSecretWordAtomOwnerTrace.compile (KemSK := KemSK) work := by
  unfold RegistrationNativeSecretWordAtomOwnerTrace.compile
  cases scalar with
  | none => rfl
  | some scalar =>
      simp only [routing, QueryImpl.simulateQ_compose]
      congr 1
      rw [← QueryImpl.simulateQ_compose]
      rfl

variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (route : RawCtxServerRouting.SenderDecoder)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
  (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey)
  (challenge : MlKem768Ciphertext) (outer : QueryImpl Combined ProbComp)
local notation "provider" => RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge
local notation "lower" => RegistrationNativeSecretWordAtomOwnerSource.lower (n := n) setup wire route sign input inside provider outer

/-- A concrete installation-free incoming subprogram cannot charge an atom attempt, even with stale prior trace metadata. -/
theorem free (role : Role) (scalar : Option PqxdhJointGapDh.ScalarBytes)
    (work : StateT Environment (OracleComp (RegistrationNativeSecretWordInterface.LocalSpec n KemSK)) Value)
    (before : State n KemSK) (result : Value × State n KemSK)
    (bounded : (work.run before.1).IsQueryBoundP (LocalInstall (KemSK := KemSK) role) 0)
    (supported : result ∈ support ((lower scalar work).run before)) :
    count role result.2.2.1 ≤ count role before.2.1 := by
  have actual := RegistrationNativeSecretWordAtomOwnerSource.trace_support setup wire route sign input inside provider outer
    scalar work before result supported
  exact RegistrationNativeSecretWordAtomInstallTrace.free role _
    (RegistrationNativeSecretWordAtomOwnerSource.routing_bound setup role scalar _ 0 bounded)
    before.2.1 ((result.1, result.2.1), result.2.2.1) actual

/-- Actual paired incoming completion can charge only its own one attempt for its newly demanded descriptor. -/
theorem complete (scalar : Option PqxdhJointGapDh.ScalarBytes) (owner current : SelectedOwner source)
    (ready : BeaconReady) (before : State n KemSK)
    (result : (RustM (Option Pqxdh.Bytes) × SelectedOwner source) × State n KemSK)
    (supported : result ∈ support
      ((lower scalar ((RegistrationNativeSecretWordBeaconCompiler.complete setup.source owner ready).run current)).run before)) :
    count .beacon result.2.2.1 ≤ count .beacon before.2.1 + atom (some ready.reference) := by
  have actual := RegistrationNativeSecretWordAtomOwnerSource.trace_support setup wire route sign input inside provider outer
    scalar ((RegistrationNativeSecretWordBeaconCompiler.complete setup.source owner ready).run current) before result supported
  simp only [RegistrationNativeSecretWordBeaconCompiler.complete, StateT.run] at actual
  rw [routing_paired] at actual
  have bounded := RegistrationNativeSecretWordAtomOwnerTrace.complete .beacon setup.source owner current ready before.1 before.2.1
    ((result.1, result.2.1), result.2.2.1) actual
  simpa only [ite_true, Nat.one_mul] using bounded

/-- The same actual traced successful preparation uses its selected local owner and successful terminal gate, with no observer reset. -/
theorem preparation_owner (front : RegistrationNativeSecretWordMessage.State source)
    (index : Nat) (owner : RegistrationNativePublicOwners.Owner source)
    (before : State n KemSK) (afterOwner : SelectedOwner source) (ready : BeaconReady) (after : State n KemSK)
    (aligned : RegistrationNativeSecretWordTargetAlignment.Aligned front.beacons before.2.2.kem.1.keys)
    (found : front.beacons[index]? = some owner) (packet : Option registration.ResponsePacket)
    (word : ready.reference.kem = Word.atom)
    (supported : ((.ok (some ready), afterOwner), after) ∈ support
      ((lower owner.scalar ((RegistrationNativeSecretWordBeaconCompiler.finishPreparation setup source packet).run owner.view)).run before)) :
    index = selected ∧ RegistrationNativeSecretWordOwnerCredit.canFinish owner.view.phase = true := by
  have actual := Set.mem_image_of_mem (Prod.map id drop) supported
  rw [← support_map, RegistrationNativeSecretWordAtomOwnerSource.source] at actual
  exact RegistrationNativeSecretWordAtomOwnerIncoming.preparation_owner setup wire route sign input inside selected pairs
    publicKey challenge outer front.beacons before.2.2.kem.1.keys index owner aligned found packet afterOwner ready
    (drop before) (drop after) word actual

private theorem map_apply {Private Value Result : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : Value → Result) (work : StateT Private m Value) (before : Private) :
    (observe <$> work) before = Prod.map observe id <$> work before := StateT.run_map observe work before

attribute [local irreducible] RegistrationNativeSecretWordAtomOwnerSource.lower
  RegistrationNativeSecretWordTargetSource.implementation RegistrationNativeSecretWordInterpreter.handler

/-- The same retained owner can fund an atom attempt only when its actual terminal gate spends the selected owner's single credit. -/
theorem local_finish (front : RegistrationNativeSecretWordMessage.State source)
    (index : Nat) (owner : RegistrationNativePublicOwners.Owner source)
    (packet : Option registration.ResponsePacket) (before : State n KemSK)
    (result : (RustM (Option Pqxdh.Bytes) × SelectedOwner source) × State n KemSK)
    (aligned : RegistrationNativeSecretWordTargetAlignment.Aligned front.beacons before.2.2.kem.1.keys)
    (found : front.beacons[index]? = some owner)
    (supported : result ∈ support
      ((lower owner.scalar ((RegistrationNativeSecretWordBeaconCompiler.finish setup source packet).run owner.view)).run before)) :
    count .beacon result.2.2.1 ≤ count .beacon before.2.1 +
      RegistrationNativeSecretWordOwnerCredit.cost selected (.inr (.finish index packet)) front := by
  simp only [RegistrationNativeSecretWordBeaconCompiler.finish, StateT.run_bind, StateT.run_get, pure_bind] at supported
  cases phase : owner.view.phase with
  | fresh | freshWithCoins _ | established _ | aborted _ =>
      simp only [phase, RegistrationNativeSecretWordAtomOwnerSource.lower_pure, StateT.run_pure, mem_support_pure_iff] at supported
      cases supported
      dsimp only
      omega
  | initSent pending oneTime =>
      simp only [phase] at supported
      cases moved : pending.aborted_state with
      | fail error | div =>
          simp only [moved, RegistrationNativeSecretWordAtomOwnerSource.lower_pure, StateT.run_pure, mem_support_pure_iff] at supported
          cases supported
          dsimp only
          omega
      | ok aborted =>
          simp only [moved, StateT.run_bind] at supported
          rw [RegistrationNativeSecretWordAtomOwnerSource.lower_bind, StateT.run_bind, mem_support_bind_iff] at supported
          obtain ⟨⟨⟨prepared, current⟩, middle⟩, preparationAt, continued⟩ := supported
          have prepCount := free setup wire route sign input inside selected pairs publicKey challenge outer .beacon owner.scalar
            ((RegistrationNativeSecretWordBeaconCompiler.finishPreparation setup source packet).run owner.view) before
            ((prepared, current), middle)
            (RegistrationNativeSecretWordAtomOwnerInstallPrefix.preparation_free .beacon setup source packet owner.view before.1)
            preparationAt
          dsimp only at prepCount
          cases prepared with
          | fail error | div =>
              have last := free setup wire route sign input inside selected pairs publicKey challenge outer .beacon owner.scalar
                _ middle result (by
                  simpa only [seqRight_eq_bind, bind_pure_comp, StateT.run_map, map_apply, StateT.run, isQueryBoundP_map_iff] using
                    (RegistrationNativeSecretWordAtomOwnerInstallPrefix.abort_free .beacon (KemSK := KemSK) owner.view current middle.1)) continued
              omega
          | ok prepared => cases prepared with
            | none =>
                have last := free setup wire route sign input inside selected pairs publicKey challenge outer .beacon owner.scalar
                  _ middle result (by
                    simpa only [seqRight_eq_bind, bind_pure_comp, StateT.run_map, map_apply, StateT.run, isQueryBoundP_map_iff] using
                      (RegistrationNativeSecretWordAtomOwnerInstallPrefix.abort_free .beacon (KemSK := KemSK) owner.view current middle.1)) continued
                omega
            | some ready =>
                have last := complete setup wire route sign input inside selected pairs publicKey challenge outer owner.scalar
                  owner.view current ready middle result continued
                by_cases word : ready.reference.kem = Word.atom
                · have eligible := preparation_owner setup wire route sign input inside selected pairs publicKey challenge outer
                    front index owner before current ready middle aligned found packet word preparationAt
                  have paid : RegistrationNativeSecretWordOwnerCredit.cost selected (.inr (.finish index packet)) front = 1 := by
                    simp only [RegistrationNativeSecretWordOwnerCredit.cost, ite_eq_left eligible.1, found, ite_eq_left eligible.2]
                  simp only [atom, word] at last
                  omega
                · have noCharge : atom (some ready.reference) = 0 := by
                    unfold atom
                    cases actual : ready.reference.kem with
                    | atom => exact (word actual).elim
                    | literal secret => simp only [actual]
                  rw [noCharge] at last
                  omega

private theorem owners_present (front : RegistrationNativeSecretWordMessage.State source)
    (index : Nat) (packet : Option registration.ResponsePacket)
    (before : RegistrationNativeSecretWordFrontendTrace.State × RegistrationNativeSecretWordInterpreter.State n KemSK)
    (owner : RegistrationNativePublicOwners.Owner source) (found : front.beacons[index]? = some owner) :
    (simulateQ (RegistrationNativeSecretWordAtomTracedSource.word setup wire route sign input inside provider outer)
      (simulateQ (RegistrationNativeSecretWordInterface.liftLocal false)
        (((RegistrationNativeSecretWordOwners.finish setup source index packet).run front.beacons).run front.environment))).run before =
      (fun reached => (((reached.1.1, front.beacons.set index { owner with view := reached.1.2 }), reached.2.1), reached.2.2)) <$>
        (lower owner.scalar ((RegistrationNativeSecretWordBeaconCompiler.finish setup source packet).run owner.view)).run
          (front.environment, before) := by
  simp only [RegistrationNativeSecretWordOwners.finish, StateT.run, found, simulateQ_map, map_apply,
    RegistrationNativeSecretWordAtomOwnerSource.lower]
  cases scalar : owner.scalar <;>
    simp only [RegistrationNativeSecretWordAtomOwnerSource.routing, QueryImpl.simulateQ_compose,
      Functor.map_map]
  all_goals rfl

/-- The actual mixed roster finish funds at most the selected owner's one terminal credit, with the original chronological trace and complete source state retained. -/
theorem owners (front : RegistrationNativeSecretWordMessage.State source)
    (index : Nat) (packet : Option registration.ResponsePacket)
    (before : RegistrationNativeSecretWordFrontendTrace.State × RegistrationNativeSecretWordInterpreter.State n KemSK)
    (result : ((RustM (Option Pqxdh.Bytes) × RegistrationNativePublicOwners.State source) × Environment) ×
      (RegistrationNativeSecretWordFrontendTrace.State × RegistrationNativeSecretWordInterpreter.State n KemSK))
    (aligned : RegistrationNativeSecretWordTargetAlignment.Aligned front.beacons before.2.kem.1.keys)
    (supported : result ∈ support
      ((simulateQ (RegistrationNativeSecretWordAtomTracedSource.word setup wire route sign input inside provider outer)
        (simulateQ (RegistrationNativeSecretWordInterface.liftLocal false)
          (((RegistrationNativeSecretWordOwners.finish setup source index packet).run front.beacons).run front.environment))).run before)) :
    count .beacon result.2.1 ≤ count .beacon before.1 +
      RegistrationNativeSecretWordOwnerCredit.cost selected (.inr (.finish index packet)) front := by
  cases found : front.beacons[index]? with
  | none =>
      simp only [RegistrationNativeSecretWordOwners.finish, StateT.run, found, simulateQ_pure,
        ] at supported
      cases supported
      dsimp only
      omega
  | some owner =>
      rw [owners_present setup wire route sign input inside selected pairs publicKey challenge outer front index packet before owner found,
        support_map] at supported
      obtain ⟨reached, actual, equal⟩ := supported
      have bounded := local_finish setup wire route sign input inside selected pairs publicKey challenge outer front index owner
        packet (front.environment, before) reached aligned found actual
      have sameTrace := congrArg (fun result => result.2.1) equal
      rw [← sameTrace]
      exact bounded

end BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerCount
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerCount.free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerCount.free
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerCount.complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerCount.complete
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerCount.preparation_owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerCount.preparation_owner

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerCount.local_finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerCount.local_finish

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerCount.owners' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerCount.owners
