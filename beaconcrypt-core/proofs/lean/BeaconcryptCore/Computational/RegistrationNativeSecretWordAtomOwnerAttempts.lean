-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerCount
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomServerFrontend
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetAlignmentRun

/-! The actual selected local owner spends its sole terminal credit before decoding a finish reply. A material atom is linked through the same retained opaque handle and the derived current roster/private-pool alignment, so other owners cannot charge this role. The global potential retains the complete original raw ledger and private source state. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerAttempts
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordAtomTracedSource (State drop)
open RegistrationNativeSecretWordAtomInstallTrace (count)
open RegistrationNativeSecretWordOwnerCredit (credit cost)
open RegistrationNativeSecretWordTargetAlignmentRun (Holds)
open PqxdhKemIndCca
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (route : RawCtxServerRouting.SenderDecoder)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
  (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey)
  (challenge : MlKem768Ciphertext) (outer : QueryImpl Combined ProbComp)
  (selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
local notation "provider" => RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge
local notation "typed" => RegistrationNativeSecretWordAtomTracedSource.typed (n := n)
  setup wire route sign input inside provider outer checks selected selectedAccept publicPrekey

private theorem beacon_run (work : RegistrationNativeSecretWordOwners.M n KemSK RegistrationServerRoleBackend.State source Value)
    (before : RegistrationNativeSecretWordMessage.State source) :
    (RegistrationNativeSecretWordFrontend.beacon work).run before =
      (fun result => (result.1.1, { before with beacons := result.1.2, environment := result.2 })) <$>
        simulateQ (RegistrationNativeSecretWordInterface.liftLocal false) ((work.run before.beacons).run before.environment) := rfl

attribute [local irreducible] RegistrationNativeSecretWordFrontend.handler
  RegistrationNativeSecretWordServerCompiler.accept RegistrationNativeSecretWordServerCompiler.build

private theorem trace_cost (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State n KemSK source)
    (aligned : Holds (drop before)) (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State n KemSK source)
    (supported : result ∈ support ((typed query).run before)) :
    count .beacon result.2.2.1 ≤ count .beacon before.2.1 + cost selected query before.1 := by
  have actual := RegistrationNativeSecretWordAtomTracedSource.typed_support setup wire route sign input inside provider outer checks
    selected selectedAccept publicPrekey query before result supported
  cases query with
  | inl coin =>
      exact RegistrationNativeSecretWordAtomInstallTrace.free .beacon _
        (RegistrationNativeSecretWordAtomServerFrontend.other_free .beacon setup checks wire sign selected selectedAccept publicPrekey
          (.inl coin) (by simp only [RegistrationNativeRawAdapter.kind]; exact ⟨by decide, by decide⟩) before.1)
        before.2.1 ((result.1, result.2.1), result.2.2.1) actual
  | inr query => cases query with
    | build handle application =>
        simpa only [cost, reduceCtorEq, ite_false, Nat.zero_mul, Nat.add_zero] using
          RegistrationNativeSecretWordAtomServerFrontend.build_count .beacon setup checks wire sign selected selectedAccept publicPrekey
            handle application before.1 before.2.1 ((result.1, result.2.1), result.2.2.1) actual
    | finish index packet =>
        rw [RegistrationNativeSecretWordAtomTracedSource.typed, QueryImpl.flattenStateT_mapStateTBase_apply_run] at supported
        simp only [RegistrationNativeSecretWordFrontend.handler] at supported
        rw [beacon_run] at supported
        simp only [simulateQ_map, StateT.run_map, Functor.map_map, support_map] at supported
        obtain ⟨reached, called, equal⟩ := supported
        cases equal
        exact RegistrationNativeSecretWordAtomOwnerCount.owners setup wire route sign input inside selected pairs publicKey challenge outer
          before.1 index packet before.2 reached aligned called
    | _ =>
        exact RegistrationNativeSecretWordAtomInstallTrace.free .beacon _
          (RegistrationNativeSecretWordAtomServerFrontend.other_free .beacon setup checks wire sign selected selectedAccept publicPrekey
            _ (by simp only [RegistrationNativeRawAdapter.kind]; exact ⟨by decide, by decide⟩) before.1)
          before.2.1 ((result.1, result.2.1), result.2.2.1) actual

/-- Every actual traced typed callback preserves the derived roster alignment and spends the same terminal owner credit for its atom attempts. -/
theorem query_credit (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State n KemSK source)
    (aligned : Holds (drop before)) (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State n KemSK source)
    (supported : result ∈ support ((typed query).run before)) :
    Holds (drop result.2) ∧ count .beacon result.2.2.1 + credit selected result.2.1 ≤
      count .beacon before.2.1 + credit selected before.1 := by
  have droppedSource : (result.1, drop result.2) ∈ support
      ((RegistrationNativeSecretWordTargetSource.typed setup checks wire route sign input inside provider outer
        selected selectedAccept publicPrekey query).run (drop before)) := by
    rw [← RegistrationNativeSecretWordAtomTracedSource.typed_source setup wire route sign input inside provider outer checks
      selected selectedAccept publicPrekey query before, support_map]
    exact Set.mem_image_of_mem (Prod.map id drop) supported
  have keeps := RegistrationNativeSecretWordTargetAlignmentRun.typed_keeps setup checks wire route sign input inside selected pairs publicKey challenge outer
    selected selectedAccept publicPrekey query (drop before) aligned (result.1, drop result.2) droppedSource
  have observed := RegistrationNativeSecretWordAtomTracedSource.typed_support setup wire route sign input inside provider outer checks
    selected selectedAccept publicPrekey query before result supported
  have raw : (result.1, result.2.1) ∈ support
      ((RegistrationNativeSecretWordFrontend.handler (n := n) setup checks wire source sign selected selectedAccept publicPrekey query).run before.1) := by
    apply OracleComp.support_simulateQ_run'_subset RegistrationNativeSecretWordFrontendTrace.handler _ before.2.1
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem Prod.fst observed
  have consumed := RegistrationNativeSecretWordOwnerCredit.query_credit setup checks wire sign selected selectedAccept publicPrekey query before.1
    (result.1, result.2.1) raw
  have attempts := trace_cost setup checks wire route sign input inside selected pairs publicKey challenge outer selectedAccept publicPrekey
    query before aligned result supported
  refine ⟨keeps, ?_⟩
  dsimp only at consumed
  omega

/-- Every actual adaptive typed prefix preserves physical handle alignment while conserving the selected owner's chronological atom-attempt credit. -/
theorem program_credit (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value) (before : State n KemSK source)
    (aligned : Holds (drop before)) (result : Value × State n KemSK source)
    (supported : result ∈ support ((simulateQ typed work).run before)) :
    Holds (drop result.2) ∧ count .beacon result.2.2.1 + credit selected result.2.1 ≤
      count .beacon before.2.1 + credit selected before.1 := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      cases supported
      exact ⟨aligned, Nat.le_refl _⟩
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨middle, called, continued⟩ := supported
      have step := query_credit setup checks wire route sign input inside selected pairs publicKey challenge outer selectedAccept publicPrekey
        query before aligned middle called
      have rest := ih middle.1 middle.2 step.1 continued
      exact ⟨rest.1, rest.2.trans step.2⟩

/-- Actual initialized original-ledger execution has at most one Beacon atom installation attempt, deriving opaque-handle alignment from empty roster and pool. -/
theorem run_one (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (front : RegistrationNativeSecretWordMessage.State source) (privateState : RegistrationNativeSecretWordInterpreter.State n KemSK)
    (owners : front.beacons = []) (keys : privateState.kem.1.keys = [])
    (result : Value × (RegistrationNativeLedger.State × State n KemSK source))
    (supported : result ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds typed mode work
      (front, RegistrationNativeSecretWordFrontendTrace.initial, privateState))) : count .beacon result.2.2.2.1 ≤ 1 := by
  rw [RegistrationNativeFullCompiler.compile_run, support_map] at supported
  obtain ⟨reached, called, equal⟩ := supported
  cases equal
  have initial : Holds (drop (front, RegistrationNativeSecretWordFrontendTrace.initial, privateState)) := by
    change RegistrationNativeSecretWordTargetAlignment.Aligned front.beacons privateState.kem.1.keys
    rw [owners, keys]
    exact RegistrationNativeSecretWordTargetAlignment.empty
  have conserved := program_credit setup checks wire route sign input inside selected pairs publicKey challenge outer selectedAccept publicPrekey
    _ (front, RegistrationNativeSecretWordFrontendTrace.initial, privateState) initial reached called
  have available := RegistrationNativeSecretWordOwnerCredit.credit_le selected front
  simp only [count, RegistrationNativeSecretWordFrontendTrace.initial, List.countP_nil, Nat.zero_add] at conserved
  dsimp only
  unfold count
  omega

end BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerAttempts
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerAttempts.query_credit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerAttempts.query_credit
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerAttempts.program_credit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerAttempts.program_credit
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerAttempts.run_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerAttempts.run_one
