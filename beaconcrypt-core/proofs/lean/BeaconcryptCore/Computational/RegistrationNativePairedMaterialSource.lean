-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePairedTrace
import BeaconcryptCore.Computational.RegistrationNativeSecretWordPairedTrace
import BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedTrace
import BeaconcryptCore.Computational.RegistrationNativeSecretWordBeaconMaterial

/-! Evaluation transports the paired monitor over the open material language with arbitrary actual Choice replies. Common callbacks and installation results remain literal, and only demanded descriptor addresses are evaluated. The disjoint unused callback channel makes this a total open simulation without manufacturing a reply for any excluded preparation or KEM callback. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePairedMaterialSource
open PqxdhKemIndCca (MlKemSharedSecret)
open RegistrationNativeSecretWordInterface (WordPairedPublicSpec)
open RegistrationNativePairedServerService (Common PublicSpec)
variable {n : Nat} {KemSK Value : Type}

abbrev Target (n : Nat) (KemSK : Type) := RegistrationNativePublicFrontend.Spec n KemSK +
  RegistrationNativeSecretWordInterface.Spec n KemSK

def liftNative : QueryImpl (RegistrationNativePublicFrontend.Spec n KemSK) (OracleComp (Target n KemSK)) :=
  fun query => (Target n KemSK).query (.inl query)

def lower (candidate : MlKemSharedSecret) : QueryImpl (RegistrationNativeSecretWordInterface.Spec n KemSK)
    (OracleComp (Target n KemSK))
  | .inl (.inr (.inl (.inl message))) => (Target n KemSK).query (.inl
      (.inl (.inr (.inl (.inl (RegistrationNativeSecretWordMessage.eval candidate message))))))
  | .inl (.inr (.inl (.inr query))) => (Target n KemSK).query (.inl (.inl (.inr (.inl (.inr query)))))
  | query => (Target n KemSK).query (.inr query)

def observe (candidate : MlKemSharedSecret) (before : RegistrationNativeSecretWordPairedTrace.State n) : RegistrationNativePairedTrace.State n :=
  ⟨RegistrationNativeSecretWordCheckedTrace.state candidate before.trace, before.choice, before.bad⟩

def wordLift : QueryImpl (WordPairedPublicSpec n) (OracleComp (RegistrationNativeSecretWordInterface.Spec n KemSK)) :=
  RegistrationNativeSecretWordInterface.liftLocal false ∘ₛ RegistrationNativeSecretWordInterface.paired

def nativeLift : QueryImpl (PublicSpec n) (OracleComp (RegistrationNativePublicFrontend.Spec n KemSK)) :=
  fun query => (RegistrationNativePublicFrontend.Spec n KemSK).query (.inl (.inr (.inl query)))

private theorem fits_kernel (candidate : MlKemSharedSecret) (before : RegistrationNativeSecretWordPairedTrace.State n)
    (kernel : PqxdhRecordLiftInterface.KernelRef n) :
    RegistrationNativePairedTrace.FitsKernel (observe candidate before) kernel =
      RegistrationNativeSecretWordPairedTrace.FitsKernel before kernel := by
  cases kernel <;>
    simp only [RegistrationNativePairedTrace.FitsKernel, RegistrationNativeSecretWordPairedTrace.FitsKernel,
      observe, RegistrationNativeSecretWordCheckedTrace.state, Option.isSome_map]

private theorem common_fits (candidate : MlKemSharedSecret) (query : (Common n).Domain)
    (before : RegistrationNativeSecretWordPairedTrace.State n) :
    RegistrationNativePairedTrace.Fits (KemSK := KemSK) (.inl (.inr (.inl (.inr query)))) (observe candidate before) =
      RegistrationNativeSecretWordPairedTrace.Fits (KemSK := KemSK) (.inl (.inr (.inl (.inr query)))) before := by
  cases query with
  | inl publication => rfl
  | inr environment => cases environment with
    | inl coin => rfl
    | inr capability => cases capability <;> first | rfl | exact fits_kernel candidate before _

private theorem common_decide (candidate : MlKemSharedSecret) (query : (Common n).Domain)
    (before : RegistrationNativeSecretWordPairedTrace.State n) :
    decide (RegistrationNativePairedTrace.Fits (KemSK := KemSK) (.inl (.inr (.inl (.inr query)))) (observe candidate before)) =
      decide (RegistrationNativeSecretWordPairedTrace.Fits (KemSK := KemSK) (.inl (.inr (.inl (.inr query)))) before) := by
  by_cases good : RegistrationNativeSecretWordPairedTrace.Fits (KemSK := KemSK) (.inl (.inr (.inl (.inr query)))) before
  · have goodNative := Eq.mp (common_fits (KemSK := KemSK) candidate query before).symm good
    simp only [goodNative, good, decide_true]
  · have badNative : ¬ RegistrationNativePairedTrace.Fits (KemSK := KemSK) (.inl (.inr (.inl (.inr query)))) (observe candidate before) :=
      fun holds => good (Eq.mp (common_fits (KemSK := KemSK) candidate query before) holds)
    simp only [badNative, good, decide_false]

/-- Every actual Common installation keeps the same demanded descriptor, actual returned choice and hidden slot after evaluation. -/
theorem common_step (candidate : MlKemSharedSecret) (query : (Common n).Domain)
    (reply : (Common n).Range query) (before : RegistrationNativeSecretWordPairedTrace.State n) :
    RegistrationNativePairedTrace.step (KemSK := KemSK) (.inl (.inr (.inl (.inr query)))) reply (observe candidate before) =
      observe candidate (RegistrationNativeSecretWordPairedTrace.step (KemSK := KemSK) (.inl (.inr (.inl (.inr query)))) reply before) := by
  simp only [RegistrationNativePairedTrace.step, RegistrationNativeSecretWordPairedTrace.step]
  rw [common_decide candidate query before]
  cases query with
  | inl publication => rfl
  | inr environment => cases environment with
    | inl coin => rfl
    | inr capability => cases capability with
      | installServer keyId binding kernel =>
          simp only [
            RegistrationNativePairedTrace.updateChoice, RegistrationNativeSecretWordPairedTrace.updateChoice,
            RegistrationNativeG2Trace.begin, RegistrationNativeG2Trace.finish,
            RegistrationNativeSecretWordFrontendTrace.begin, RegistrationNativeSecretWordFrontendTrace.finish]
          simp only [observe]
          rw [← RegistrationNativeSecretWordCheckedTrace.attempt_state candidate .server,
            ← RegistrationNativeSecretWordCheckedTrace.installed_state candidate .server]
      | installBeacon owner shell kernel =>
          simp only [
            RegistrationNativePairedTrace.updateChoice, RegistrationNativeSecretWordPairedTrace.updateChoice,
            RegistrationNativeG2Trace.begin, RegistrationNativeG2Trace.finish,
            RegistrationNativeSecretWordFrontendTrace.begin, RegistrationNativeSecretWordFrontendTrace.finish]
          simp only [observe]
          rw [← RegistrationNativeSecretWordCheckedTrace.attempt_state candidate .beacon,
            ← RegistrationNativeSecretWordCheckedTrace.installed_state candidate .beacon]
      | _ => rfl

/-- The material demand itself retains every optional returned Choice while evaluating only its descriptor address. -/
theorem demand_step (candidate : MlKemSharedSecret) (message : RegistrationNativeSecretWordMessage.Message)
    (reply : Option (RegistrationNativePairedChoice.Choice n)) (before : RegistrationNativeSecretWordPairedTrace.State n) :
    RegistrationNativePairedTrace.step (KemSK := KemSK)
      (.inl (.inr (.inl (.inl (RegistrationNativeSecretWordMessage.eval candidate message))))) reply (observe candidate before) =
      observe candidate (RegistrationNativeSecretWordPairedTrace.step (KemSK := KemSK) (.inl (.inr (.inl (.inl message)))) reply before) := by
  simp only [RegistrationNativePairedTrace.step, RegistrationNativeSecretWordPairedTrace.step,
    RegistrationNativePairedTrace.updateChoice, RegistrationNativeSecretWordPairedTrace.updateChoice,
    RegistrationNativePairedTrace.Fits, RegistrationNativeSecretWordPairedTrace.Fits,
    RegistrationNativeG2Trace.begin, RegistrationNativeG2Trace.finish,
    RegistrationNativeSecretWordFrontendTrace.begin, RegistrationNativeSecretWordFrontendTrace.finish,
    observe, RegistrationNativeSecretWordCheckedTrace.state, Option.map_some, List.map_append,
    List.map_cons, List.map_nil, RegistrationNativeSecretWordCheckedTrace.event]

/-- The monitored material callback evaluates its address while retaining the exact arbitrary Choice or Common reply. -/
theorem query_source (candidate : MlKemSharedSecret) (query : (WordPairedPublicSpec n).Domain)
    (before : RegistrationNativeSecretWordPairedTrace.State n) :
    simulateQ liftNative ((simulateQ RegistrationNativePairedTrace.handler
      (simulateQ (nativeLift (KemSK := KemSK)) (RegistrationNativeSecretWordServerMaterial.realize candidate query))).run (observe candidate before)) =
      Prod.map id (observe candidate) <$> simulateQ (lower candidate)
        ((simulateQ RegistrationNativeSecretWordPairedTrace.handler (wordLift query)).run before) := by
  cases query with
  | inl message =>
      simp only [RegistrationNativeSecretWordServerMaterial.realize, nativeLift, wordLift, QueryImpl.compose,
        RegistrationNativeSecretWordInterface.paired, RegistrationNativeSecretWordInterface.liftLocal,
        simulateQ_spec_query, RegistrationNativePairedTrace.handler, RegistrationNativeSecretWordPairedTrace.handler,
        StateT.run, simulateQ_map, lower, liftNative, Functor.map_map]
      congr 1
      funext reply
      exact Prod.ext rfl (demand_step candidate message reply before)
  | inr common =>
      simp only [RegistrationNativeSecretWordServerMaterial.realize, nativeLift, wordLift, QueryImpl.compose,
        RegistrationNativeSecretWordInterface.paired, RegistrationNativeSecretWordInterface.liftLocal,
        simulateQ_spec_query, RegistrationNativePairedTrace.handler, RegistrationNativeSecretWordPairedTrace.handler,
        StateT.run, simulateQ_map, lower, liftNative, Functor.map_map]
      congr 1
      funext reply
      exact Prod.ext rfl (common_step candidate common reply before)

/-- The entire open material program transports the complete paired monitor with its actual adaptive replies, without replacing hidden choices by known outputs. -/
theorem program_source (candidate : MlKemSharedSecret) (work : OracleComp (WordPairedPublicSpec n) Value)
    (before : RegistrationNativeSecretWordPairedTrace.State n) :
    simulateQ liftNative ((simulateQ RegistrationNativePairedTrace.handler
      (simulateQ (nativeLift (KemSK := KemSK)) (simulateQ (RegistrationNativeSecretWordServerMaterial.realize candidate) work))).run (observe candidate before)) =
      Prod.map id (observe candidate) <$> simulateQ (lower candidate)
        ((simulateQ RegistrationNativeSecretWordPairedTrace.handler (simulateQ wordLift work)).run before) := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]; rfl
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      rw [query_source]
      simp only [bind_map_left, map_bind, Prod.map_def, id_eq]
      apply bind_congr
      intro reached
      exact ih reached.1 reached.2

private def literalEvent : RegistrationNativeG2Trace.Event → RegistrationNativeSecretWordFrontendTrace.Event
  | .prepare message => .prepare (RegistrationNativeSecretWordMessage.literal message)
  | .demand message => .demand (RegistrationNativeSecretWordMessage.literal message)
  | .encapsulate selected key ciphertext secret => .encapsulate selected key ciphertext (.literal secret)
  | .installAttempt role message => .installAttempt role (RegistrationNativeSecretWordMessage.literal message)
  | .install role message => .install role (RegistrationNativeSecretWordMessage.literal message)

private def literal (before : RegistrationNativePairedTrace.State n) : RegistrationNativeSecretWordPairedTrace.State n :=
  ⟨⟨before.trace.current.map RegistrationNativeSecretWordMessage.literal, before.trace.events.map literalEvent⟩,
    before.choice, before.bad⟩

private theorem observe_literal (candidate : MlKemSharedSecret) (before : RegistrationNativePairedTrace.State n) :
    observe candidate (literal before) = before := by
  have event (value : RegistrationNativeG2Trace.Event) :
      RegistrationNativeSecretWordCheckedTrace.event candidate (literalEvent value) = value := by
    cases value <;> simp only [literalEvent, RegistrationNativeSecretWordCheckedTrace.event,
      RegistrationNativeSecretWordMessage.eval_literal, RegistrationNativeSecretWord.Word.eval]
  rcases before with ⟨⟨current, events⟩, choice, bad⟩
  simp [observe, literal, RegistrationNativeSecretWordCheckedTrace.state, Option.map_map,
    List.map_map, Function.comp_def, RegistrationNativeSecretWordMessage.eval_literal, event]

private theorem lift_support {Result : Type} (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) Result)
    (result : Result) (supported : result ∈ support work) : result ∈ support (simulateQ liftNative work) := by
  induction work using OracleComp.inductionOn with
  | pure value => simpa only [simulateQ_pure, mem_support_pure_iff] using supported
  | query_bind query next ih =>
      simp only [mem_support_bind_iff] at supported
      obtain ⟨reply, _possible, later⟩ := supported
      simp only [simulateQ_bind, simulateQ_spec_query, liftNative, mem_support_bind_iff]
      exact ⟨reply, mem_support_query _ reply, ih reply later⟩

/-- A complete Word material controller's paired certificate transfers to the literal actual native material controller, retaining arbitrary hidden Choice replies. -/
theorem safe (candidate : MlKemSharedSecret) (work : OracleComp (WordPairedPublicSpec n) Value)
    (valid : RegistrationNativeSecretWordPairedTrace.Safe (simulateQ (wordLift (KemSK := KemSK)) work)) :
    RegistrationNativePairedTrace.Safe
      (simulateQ (nativeLift (KemSK := KemSK)) (simulateQ (RegistrationNativeSecretWordServerMaterial.realize candidate) work)) := by
  intro before result clean supported
  have lifted := lift_support _ result supported
  rw [← observe_literal candidate before, program_source, support_map] at lifted
  obtain ⟨wordResult, actual, equal⟩ := lifted
  have opened := PqxdhDeploymentEnvironment.support_simulateQ_subset (lower candidate) _ actual
  have cleanWord := valid (literal before) wordResult clean opened
  cases equal
  exact cleanWord

end BeaconcryptCore.Computational.RegistrationNativePairedMaterialSource
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePairedMaterialSource.common_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePairedMaterialSource.common_step
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePairedMaterialSource.demand_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePairedMaterialSource.demand_step
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePairedMaterialSource.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePairedMaterialSource.query_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePairedMaterialSource.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePairedMaterialSource.program_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePairedMaterialSource.safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePairedMaterialSource.safe
