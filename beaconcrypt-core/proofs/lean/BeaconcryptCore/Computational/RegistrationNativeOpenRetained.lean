-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePublicRetained
import BeaconcryptCore.Computational.RegistrationNativeKemWorldUniform

/-! The additive retained client leaves every indexed KEM operation open. Its executable state keeps an empty placeholder pool; actual generated KEM secrets remain in the external service. Ordinary native World/publication work uses the existing concrete compiler, projecting only the private uniform counter before and after each component. The corresponding actual draw bills and source comparison are separate derived obligations; the real-only retained compiler remains unchanged. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeOpenRetained
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativePublicInterpreter (State)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

abbrev Spec (KemSK : Type) := RegistrationNativeRetainedService.Spec + RegistrationNativePublicFrontend.RoutedKem KemSK

def baseLift : QueryImpl RegistrationNativeRetainedService.Spec (OracleComp (Spec KemSK)) :=
  fun query => (Spec KemSK).query (.inl query)

def kemLift : QueryImpl (RegistrationNativePublicFrontend.RoutedKem KemSK) (OracleComp (Spec KemSK)) :=
  fun query => (Spec KemSK).query (.inr query)

def mask (before : State n KemSK) : State n KemSK :=
  { before with pool := PqxdhLiveKemBirth.empty, world := RegistrationNativeKemWorldUniform.mask before.world }

def ordinary (hmac : PqxdhSecretInputKdf.HmacSha512)
    (work : RegistrationNativePublicInterpreter.M n KemSK Value) :
    StateT (State n KemSK) (OracleComp (Spec KemSK)) Value := fun before =>
  Prod.map id mask <$> simulateQ baseLift ((RegistrationNativePublicRetained.ordinary hmac work).run (mask before))

noncomputable def compiler (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply) :
    QueryImpl (RegistrationNativePublicFrontend.Spec n KemSK) (StateT (State n KemSK) (OracleComp (Spec KemSK)))
  | .inl (.inl message) => StateT.lift (baseLift (.inr (.prepare message)))
  | .inl (.inr (.inl (.inl message))) => StateT.lift
      (Option.map RegistrationNativePairedChoice.Choice.known <$> baseLift (.inr (.demand message)))
  | .inl (.inr (.inl (.inr query))) => ordinary setup.hmac (RegistrationNativePublicInterpreter.common setup wire sign query)
  | .inl (.inr (.inr query)) => StateT.lift (kemLift query)
  | .inr query => ordinary setup.hmac (RegistrationNativePublicInterpreter.world
      (CborRecordWorldSimulation.guarded setup (RegistrationNativeWire.ledgerCodec wire) route (.inr (.inr query))))

/-- Every KEM getter is the literal external opaque-pool/public-encapsulation request, without a local secret-key pool or sampled real encapsulation implementation. -/
theorem kem_query (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (query : (RegistrationNativePublicFrontend.RoutedKem KemSK).Domain) (before : State n KemSK) :
    (compiler setup wire route sign (.inl (.inr (.inr query)))).run before =
      (fun value => (value, before)) <$> kemLift query := by
  simp only [compiler, StateT.run_lift, bind_pure_comp]
  rfl

/-- The explicit client mask contains no KEM private-key entries and is idempotent. -/
theorem mask_fields (before : State n KemSK) :
    (mask before).pool = PqxdhLiveKemBirth.empty ∧ mask (mask before) = mask before := by
  exact ⟨rfl, rfl⟩

/-- Every ordinary component returns an empty local pool independently of all external oracle answers. -/
theorem ordinary_empty (hmac : PqxdhSecretInputKdf.HmacSha512)
    (work : RegistrationNativePublicInterpreter.M n KemSK Value) (before : State n KemSK)
    (result : Value × State n KemSK)
    (supported : result ∈ support ((ordinary hmac work).run before)) :
    result.2.pool = PqxdhLiveKemBirth.empty := by
  simp only [ordinary, StateT.run, support_map] at supported
  obtain ⟨inner, _possible, equal⟩ := supported
  cases equal
  rfl

/-- Every actual command retains the initialized empty placeholder pool; only the external KEM service can own generated private keys. -/
theorem compiler_empty (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (query : (RegistrationNativePublicFrontend.Spec n KemSK).Domain) (before : State n KemSK)
    (result : (RegistrationNativePublicFrontend.Spec n KemSK).Range query × State n KemSK)
    (empty : before.pool = PqxdhLiveKemBirth.empty)
    (supported : result ∈ support ((compiler setup wire route sign query).run before)) :
    result.2.pool = PqxdhLiveKemBirth.empty := by
  rcases query with (message | (message | query) | query) | query
  · simp only [compiler, StateT.run_lift, bind_pure_comp, support_map] at supported
    obtain ⟨reply, _possible, equal⟩ := supported
    cases equal
    exact empty
  · simp only [compiler, StateT.run_lift, bind_pure_comp, support_map] at supported
    obtain ⟨reply, _possible, equal⟩ := supported
    cases equal
    exact empty
  · exact ordinary_empty _ _ before result supported
  · simp only [compiler, StateT.run_lift, bind_pure_comp, support_map] at supported
    obtain ⟨reply, _possible, equal⟩ := supported
    cases equal
    exact empty
  · exact ordinary_empty _ _ before result supported

/-- Arbitrary adaptive native frontend work never acquires the external pool's private keys in its executable state. -/
theorem program_empty (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) Value) (before : State n KemSK)
    (result : Value × State n KemSK) (empty : before.pool = PqxdhLiveKemBirth.empty)
    (supported : result ∈ support ((simulateQ (compiler setup wire route sign) work).run before)) :
    result.2.pool = PqxdhLiveKemBirth.empty := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      cases supported
      exact empty
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨reached, step, continued⟩ := supported
      exact ih reached.1 reached.2 (compiler_empty setup wire route sign query before reached empty step) continued

noncomputable def client (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) Value)
    (before : State n KemSK) : OracleComp (Spec KemSK) Value :=
  (simulateQ (compiler setup wire route sign) work).run'
    (mask (RegistrationNativePublicRetained.clear before))

end BeaconcryptCore.Computational.RegistrationNativeOpenRetained

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOpenRetained.kem_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOpenRetained.kem_query
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOpenRetained.mask_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOpenRetained.mask_fields
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOpenRetained.ordinary_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOpenRetained.ordinary_empty
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOpenRetained.compiler_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOpenRetained.compiler_empty
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOpenRetained.program_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOpenRetained.program_empty
