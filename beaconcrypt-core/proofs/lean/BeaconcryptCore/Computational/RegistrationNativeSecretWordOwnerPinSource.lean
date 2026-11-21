-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordOwnerPinNoncreate
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetSource
import BeaconcryptCore.Computational.RegistrationNativeOwnerPinSummaryStep

/-! The literal Word source preserves configured owner pins through every optional constructor and every other raw callback. These are actual source laws under arbitrary Combined replies. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordOwnerPinSource
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordInterpreter (Provider)
open RegistrationNativeSecretWordTargetSource (State)
open RegistrationNativeSecretWordOwnerPins (key)
open RegistrationNativeOwnerPinSummaryStep (advance)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (route : RawCtxServerRouting.SenderDecoder)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
  (provider : Provider KemSK) (outer : QueryImpl Combined ProbComp)
  (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
local notation "typedImpl" => RegistrationNativeSecretWordTargetSource.typed (n := n) (source := source)
  setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey
local notation "rawImpl" => RegistrationNativeRawAdapter.handler wire typedImpl

private theorem state_map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : A → B) (work : StateT S m A) (before : S) : (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

/-- The actual typed constructor appends only its literal configured public binding on successful creation. -/
theorem typed_create (edPin : PqxdhBeaconPhase2Preparation.Word32) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (before : State n KemSK source) (reply : RustM (Option Nat)) (after : State n KemSK source)
    (supported : (reply, after) ∈ support ((typedImpl (.inr (.create edPin mlPin keyId))).run before)) :
    after.1.beacons.map key = match reply with | .ok (some _) => before.1.beacons.map key ++ [(edPin, keyId)] | _ => before.1.beacons.map key := by
  rw [RegistrationNativeSecretWordTargetSource.typed_run] at supported
  simp only [RegistrationNativeSecretWordFrontend.handler, RegistrationNativeSecretWordFrontend.beacon,
    StateT.run, simulateQ_map, state_map_apply, Functor.map_map, support_map] at supported
  obtain ⟨reached, called, returned⟩ := supported
  have possible : reached.1 ∈ support
      (simulateQ (RegistrationNativeSecretWordInterface.liftLocal (n := n) (KemSK := KemSK) false)
        (((RegistrationNativeSecretWordOwners.create (n := n) setup source selectedOwner publicPrekey edPin mlPin keyId).run before.1.beacons).run before.1.environment)) := by
    apply support_simulateQ_run'_subset
      (RegistrationNativeSecretWordTargetSource.implementation setup wire route sign input inside provider outer) _ before.2
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem Prod.fst called
  have native := RegistrationNativePublicSourceSupport.simulate_support _ _ _ possible
  have pins := RegistrationNativeSecretWordOwnerPins.create_keys setup selectedOwner publicPrekey edPin mlPin keyId before.1.beacons before.1.environment reached.1 native
  cases returned
  rcases reached with ⟨⟨⟨reply, owners⟩, environment⟩, privateState⟩
  cases reply with
  | ok option => cases option <;> exact pins
  | fail error => exact pins
  | div => exact pins

/-- Every other actual typed callback retains all immutable owner pins. -/
theorem typed_noncreate (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (quiet : RegistrationNativeRawAdapter.kind query ≠ 1)
    (before : State n KemSK source) (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State n KemSK source)
    (supported : result ∈ support ((typedImpl query).run before)) : result.2.1.beacons.map key = before.1.beacons.map key := by
  rw [RegistrationNativeSecretWordTargetSource.typed_run, support_map] at supported
  obtain ⟨reached, called, returned⟩ := supported
  cases returned
  apply RegistrationNativeSecretWordOwnerPinNoncreate.typed_same setup checks wire sign selectedOwner selectedAccept publicPrekey query quiet before.1 reached.1
  apply support_simulateQ_run'_subset
    (RegistrationNativeSecretWordTargetSource.implementation setup wire route sign input inside provider outer) _ before.2
  rw [StateT.run'_eq, support_map]
  exact Set.mem_image_of_mem Prod.fst called

/-- Any typed continuation without a constructor preserves every configured owner binding. -/
theorem typed_quiet (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value)
    (quiet : work.IsQueryBoundP (fun query => RegistrationNativeRawAdapter.kind query = 1) 0)
    (before : State n KemSK source) (result : Value × State n KemSK source)
    (supported : result ∈ support ((simulateQ typedImpl work).run before)) : result.2.1.beacons.map key = before.1.beacons.map key := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported; cases supported; rfl
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at quiet
      have absent : RegistrationNativeRawAdapter.kind query ≠ 1 := quiet.1.resolve_right (Nat.not_lt_zero _)
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨middle, reached, continued⟩ := supported
      have first := typed_noncreate setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey query absent before middle reached
      exact (ih middle.1 (by simpa using quiet.2 middle.1) middle.2 result continued).trans first

end BeaconcryptCore.Computational.RegistrationNativeSecretWordOwnerPinSource
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordOwnerPinSource.typed_create' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordOwnerPinSource.typed_create
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordOwnerPinSource.typed_noncreate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordOwnerPinSource.typed_noncreate
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordOwnerPinSource.typed_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordOwnerPinSource.typed_quiet
