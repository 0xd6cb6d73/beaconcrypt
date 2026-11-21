-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomServerCredit

/-! A private typed-command counter counts actual moved atom capabilities. The concrete source credit law bounds it over the complete original adaptive ledger without a query-budget assumption. Erasing this counter preserves the entire actual frontend and private interpreter state. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomServerRun
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordAtomServerCredit (State credit cost)
open PqxdhKemIndCca
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (route : RawCtxServerRouting.SenderDecoder)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
  (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey)
  (challenge : MlKem768Ciphertext) (outer : QueryImpl Combined ProbComp)
  (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
local notation "provider" => RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge
local notation "typed" => RegistrationNativeSecretWordTargetSource.typed (n := n)
  setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey

noncomputable def handler : QueryImpl RegistrationNativeRawAdapter.TypedSpec (StateT (State n KemSK source × Nat) ProbComp) :=
  fun query before => (fun result => (result.1, (result.2, before.2 + cost query before.1))) <$>
    (typed query).run before.1

/-- The counter changes no actual typed callback result or frontend/private source state. -/
theorem query_source (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State n KemSK source × Nat) :
    (fun result => (result.1, result.2.1)) <$> (handler setup checks wire route sign input inside selected pairs publicKey
      challenge outer selectedOwner selectedAccept publicPrekey query).run before = (typed query).run before.1 := by
  simp only [handler, StateT.run, Functor.map_map, id_map']

/-- Every adaptive typed execution conserves the single actual future/stored Server atom credit. -/
theorem program_credit (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value)
    (before : State n KemSK source × Nat) (result : Value × (State n KemSK source × Nat))
    (supported : result ∈ support ((simulateQ
      (handler setup checks wire route sign input inside selected pairs publicKey challenge outer selectedOwner selectedAccept publicPrekey)
      work).run before)) : result.2.2 + credit selectedAccept result.2.1 ≤ before.2 + credit selectedAccept before.1 := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      cases supported
      exact Nat.le_refl _
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind] at supported
      simp only [handler, StateT.run, bind_map_left, mem_support_bind_iff] at supported
      obtain ⟨middle, called, continued⟩ := supported
      have consumed := RegistrationNativeSecretWordAtomServerCredit.query_credit setup checks wire route sign input inside selected pairs
        publicKey challenge outer selectedOwner selectedAccept publicPrekey query before.1 middle called
      have later := ih middle.1 (middle.2, before.2 + cost query before.1) continued
      dsimp only at later
      omega

/-- From actual empty startup sessions and parsed ordinal zero, the whole original secrecy ledger can move an atom capability at most once. -/
theorem run_one (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (before : State n KemSK source)
    (sessions : before.1.server.sessions = []) (parsed : before.1.parsedAccepts = 0)
    (result : Value × (RegistrationNativeLedger.State × (State n KemSK source × Nat)))
    (supported : result ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds
      (handler setup checks wire route sign input inside selected pairs publicKey challenge outer selectedOwner selectedAccept publicPrekey)
      mode work (before, 0))) : result.2.2.2 ≤ 1 := by
  rw [RegistrationNativeFullCompiler.compile_run, support_map] at supported
  obtain ⟨reached, called, equal⟩ := supported
  cases equal
  have conserved := program_credit setup checks wire route sign input inside selected pairs publicKey challenge outer selectedOwner selectedAccept
    publicPrekey _ (before, 0) reached called
  simp only [credit, sessions, parsed, RegistrationNativeSecretWordAtomSessionCredit.count,
    RegistrationNativeSecretWordLifecycleCounter.available, Nat.zero_le, ite_true, Nat.zero_add] at conserved
  dsimp only
  omega

/-- Erasing only the private counter recovers the literal actual full original-ledger execution, including every reached private source state. -/
theorem program_source (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value) (before : State n KemSK source × Nat) :
    (fun result => (result.1, result.2.1)) <$>
      (simulateQ (handler setup checks wire route sign input inside selected pairs publicKey challenge outer selectedOwner selectedAccept publicPrekey) work).run before =
      (simulateQ typed work).run before.1 := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      simp only [handler, StateT.run, bind_map_left, map_bind]
      apply bind_congr
      intro middle
      exact ih middle.1 (middle.2, before.2 + cost query before.1)

end BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomServerRun
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomServerRun.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomServerRun.query_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomServerRun.program_credit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomServerRun.program_credit
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomServerRun.run_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomServerRun.run_one
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomServerRun.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomServerRun.program_source
