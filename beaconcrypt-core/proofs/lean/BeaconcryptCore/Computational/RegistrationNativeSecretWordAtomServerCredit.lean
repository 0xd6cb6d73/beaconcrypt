-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomSessionShape
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOrdinaryServer
import BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveFrontendState
import BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleCounter

/-! The actual early-provider Server owns one atom capability in total: before its selected parsed attempt it is a future credit, afterwards it can only be the single stored Ready. Native take spends that capability before cancellation or any completion failure. Ordinary public encapsulation cannot add atom credit. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomServerCredit
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordTargetServerExecution (lower localImpl)
open RegistrationNativeSecretWordAtomSessionCredit (count weight)
open PqxdhKemIndCca
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

abbrev State (n : Nat) (KemSK : Type) (source : RegistrationNativeMldsa.Source) :=
  RegistrationNativeSecretWordTargetSource.State n KemSK source

def credit (selectedAccept : Nat) (before : State n KemSK source) : Nat :=
  count before.1.server.sessions + RegistrationNativeSecretWordLifecycleCounter.available selectedAccept before.1.parsedAccepts

def cost (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State n KemSK source) : Nat :=
  match query with
  | .inr (.build handle _) => weight (RegistrationNativeSecretWordServerMaterial.take handle before.1.server).1
  | _ => 0

variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (route : RawCtxServerRouting.SenderDecoder)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
  (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey)
  (challenge : MlKem768Ciphertext) (outer : QueryImpl Combined ProbComp)
  (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
local notation "provider" => RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge
local notation "implementation" => RegistrationNativeSecretWordTargetSource.implementation (n := n)
  setup wire route sign input inside provider outer
local notation "typed" => RegistrationNativeSecretWordTargetSource.typed (n := n)
  setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey

attribute [local irreducible] RegistrationNativeSecretWordServerCompiler.accept RegistrationNativeSecretWordServerCompiler.build

private theorem serverOpen_run (chosen : Bool) (work : RegistrationNativeSecretWordServerCompiler.M n KemSK Value)
    (before : RegistrationNativeSecretWordMessage.State source) :
    (RegistrationNativeSecretWordFrontend.serverOpen chosen work).run before =
      (fun result => (result.1.1, { before with server := result.1.2, environment := result.2 })) <$>
        simulateQ (RegistrationNativeSecretWordInterface.liftLocal chosen)
          ((work.run before.server).run before.environment) := rfl

private theorem accept_run (packet : registration.InitPacket) (before : State n KemSK source) :
    (typed (.inr (.accept packet))).run before =
      (fun result => (result.1.1, ({ before.1 with server := result.1.2, environment := result.2.1, parsedAccepts := before.1.parsedAccepts + 1 }, result.2.2))) <$>
        (lower (localImpl setup wire route sign input inside provider outer (decide (before.1.parsedAccepts = selectedAccept)))
          ((RegistrationNativeSecretWordServerCompiler.accept setup checks source.verify packet).run before.1.server)).run
            (before.1.environment, before.2) := by
  rw [RegistrationNativeSecretWordTargetSource.typed_run]
  simp only [RegistrationNativeSecretWordFrontend.handler, StateT.run_bind, StateT.run_get, StateT.run_modify, pure_bind]
  rw [serverOpen_run, RegistrationNativeSecretWordTargetServerExecution.lower_run]
  simp only [simulateQ_map, StateT.run_map, ← QueryImpl.simulateQ_compose,
    RegistrationNativeSecretWordTargetServerExecution.localImpl, Functor.map_map]
  rfl

private theorem build_run (handle : Nat) (application : Option (Slice U8)) (before : State n KemSK source) :
    (typed (.inr (.build handle application))).run before =
      (fun result => (result.1.1, ({ before.1 with server := result.1.2, environment := result.2.1 }, result.2.2))) <$>
        (lower (localImpl setup wire route sign input inside provider outer false)
          ((RegistrationNativeSecretWordServerCompiler.build setup.source wire checks sign handle application).run before.1.server)).run
            (before.1.environment, before.2) := by
  rw [RegistrationNativeSecretWordTargetSource.typed_run]
  simp only [RegistrationNativeSecretWordFrontend.handler]
  rw [serverOpen_run, RegistrationNativeSecretWordTargetServerExecution.lower_run]
  simp only [simulateQ_map, StateT.run_map, ← QueryImpl.simulateQ_compose,
    RegistrationNativeSecretWordTargetServerExecution.localImpl, Functor.map_map]
  rfl

private theorem lower_support (chosen : Bool)
    (work : StateT RegistrationServerReferenceCompiler.Environment
      (OracleComp (RegistrationNativeSecretWordInterface.LocalSpec n KemSK)) Value)
    (before : RegistrationNativeSecretWordTargetServerExecution.Auxiliary n KemSK)
    (result : Value × RegistrationNativeSecretWordTargetServerExecution.Auxiliary n KemSK)
    (supported : result ∈ support ((lower (localImpl setup wire route sign input inside provider outer chosen) work).run before)) :
    (result.1, result.2.1) ∈ support (work.run before.1) := by
  rw [RegistrationNativeSecretWordTargetServerExecution.lower_run, support_map] at supported
  obtain ⟨reached, called, equal⟩ := supported
  cases equal
  exact OracleComp.support_simulateQ_run'_subset (localImpl setup wire route sign input inside provider outer chosen) _ before.2 (by
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem Prod.fst called)

private theorem accept_credit (packet : registration.InitPacket) (before : State n KemSK source)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range (.inr (.accept packet)) × State n KemSK source)
    (supported : result ∈ support ((typed (.inr (.accept packet))).run before)) :
    credit selectedAccept result.2 ≤ credit selectedAccept before := by
  rw [accept_run, support_map] at supported
  obtain ⟨reached, called, equal⟩ := supported
  cases equal
  have raw := lower_support setup wire route sign input inside selected pairs publicKey challenge outer
    (decide (before.1.parsedAccepts = selectedAccept)) _ _ reached called
  have shape := RegistrationNativeSecretWordAtomSessionShape.accept setup checks source.verify packet
    before.1.server before.1.environment (reached.1, reached.2.1) raw
  by_cases chosen : before.1.parsedAccepts = selectedAccept
  · have atMost := RegistrationNativeSecretWordAtomSessionShape.count_le _ _ _ shape
    simp only [credit, RegistrationNativeSecretWordLifecycleCounter.available, chosen]
    split_ifs <;> omega
  · have ordinary : count reached.1.2.sessions = count before.1.server.sessions := by
      apply RegistrationNativeSecretWordAtomSessionShape.count_ordinary _ _ _ shape
      intro handle returned
      have callback : ((.ok (some handle), reached.1.2), reached.2) ∈ support
          ((lower (localImpl setup wire route sign input inside provider outer false)
            ((RegistrationNativeSecretWordServerCompiler.accept setup checks source.verify packet).run before.1.server)).run
              (before.1.environment, before.2)) := by
        have sameResult : reached = ((.ok (some handle), reached.1.2), reached.2) := by
          apply Prod.ext
          · exact Prod.ext returned rfl
          · rfl
        rw [← sameResult]
        simpa only [chosen, decide_false] using called
      obtain ⟨ready, stored, literal⟩ := RegistrationNativeSecretWordAtomOrdinaryServer.accept_retained_not_atom
        setup wire route sign input inside selected pairs publicKey challenge outer checks source.verify packet
        before.1.server reached.1.2 (before.1.environment, before.2) reached.2 handle callback
      exact ⟨ready, stored, RegistrationNativeSecretWordAtomSessionCredit.nonatom ready literal⟩
    simp only [credit, ordinary, RegistrationNativeSecretWordLifecycleCounter.available]
    split_ifs <;> omega

private theorem build_credit (handle : Nat) (application : Option (Slice U8)) (before : State n KemSK source)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range (.inr (.build handle application)) × State n KemSK source)
    (supported : result ∈ support ((typed (.inr (.build handle application))).run before)) :
    credit selectedAccept result.2 + cost (.inr (.build handle application)) before = credit selectedAccept before := by
  rw [build_run, support_map] at supported
  obtain ⟨reached, called, equal⟩ := supported
  cases equal
  have raw := lower_support setup wire route sign input inside selected pairs publicKey challenge outer false _ _ reached called
  simp only [RegistrationNativeSecretWordServerCompiler.build, StateT.run] at raw
  have material : reached.1 ∈ support
      ((RegistrationNativeSecretWordServerMaterial.build (n := n) wire checks.reservePeer handle application).run before.1.server) := by
    apply OracleComp.support_simulateQ_run'_subset
      (RegistrationNativeSecretWordServerCompiler.service setup.source wire sign) _ before.1.environment
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem Prod.fst raw
  have consumed := RegistrationNativeSecretWordAtomSessionCredit.build_credit wire checks.reservePeer handle application
    before.1.server reached.1 material
  simp only [credit, cost]
  omega

private theorem quiet_credit (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (quiet : RegistrationNativeRawAdapter.kind query ≠ 3 ∧ RegistrationNativeRawAdapter.kind query ≠ 4)
    (increment : RegistrationNativeSecretWordTargetCounter.isAccept query = false)
    (before : State n KemSK source) (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State n KemSK source)
    (supported : result ∈ support ((typed query).run before)) :
    credit selectedAccept result.2 = credit selectedAccept before := by
  rw [RegistrationNativeSecretWordTargetSource.typed_run, support_map] at supported
  obtain ⟨reached, called, equal⟩ := supported
  cases equal
  have raw := OracleComp.support_simulateQ_run'_subset implementation _ before.2 (by
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem Prod.fst called)
  have same := RegistrationNativeSecretWordLiveFrontendState.quiet_server setup checks wire source sign
    selectedOwner selectedAccept publicPrekey query quiet before.1 reached.1 raw
  have advanced := RegistrationNativeSecretWordTargetCounter.typed_counter setup checks wire sign
    selectedOwner selectedAccept publicPrekey query before.1 reached.1 raw
  simp only [credit, same, advanced, increment, Bool.toNat_false, Nat.add_zero]

/-- Every actual typed Server call conserves stored/future atom credit and spends a moved atom token before all build outcomes. -/
theorem query_credit (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State n KemSK source)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State n KemSK source)
    (supported : result ∈ support ((typed query).run before)) :
    credit selectedAccept result.2 + cost query before ≤ credit selectedAccept before := by
  cases query with
  | inl coin =>
      have same := quiet_credit setup checks wire route sign input inside selected pairs publicKey challenge outer selectedOwner selectedAccept publicPrekey
        (.inl coin) (by simp only [RegistrationNativeRawAdapter.kind]; exact ⟨by decide, by decide⟩) rfl before result supported
      simpa only [cost, Nat.add_zero, same] using (Nat.le_refl (credit selectedAccept before))
  | inr query => cases query with
    | accept packet => simpa only [cost, Nat.add_zero] using accept_credit setup checks wire route sign input inside selected pairs publicKey challenge outer selectedOwner selectedAccept publicPrekey packet before result supported
    | build handle application => exact Nat.le_of_eq (build_credit setup checks wire route sign input inside selected pairs publicKey challenge outer selectedOwner selectedAccept publicPrekey handle application before result supported)
    | _ =>
      have same := quiet_credit setup checks wire route sign input inside selected pairs publicKey challenge outer selectedOwner selectedAccept publicPrekey
        _ (by simp only [RegistrationNativeRawAdapter.kind]; exact ⟨by decide, by decide⟩) rfl before result supported
      simpa only [cost, Nat.add_zero, same] using (Nat.le_refl (credit selectedAccept before))

end BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomServerCredit
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomServerCredit.query_credit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomServerCredit.query_credit
