-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleCore

/-! Role tags label actual callback queries by their enclosing original typed finish command. Erasing tags recovers the literal entire original frontend and secrecy ledger. A selected-owner decapsulation tag denotes a local owner role, independently of its private indexed KEM handle; source ownership supplies that separate operand correspondence. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleTags
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePublicFrontend (State)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

abbrev Spec (n : Nat) (KemSK : Type) : OracleSpec (Bool × (RegistrationNativePublicFrontend.Spec n KemSK).Domain) :=
  fun query => (RegistrationNativePublicFrontend.Spec n KemSK).Range query.2

def tag (selected : Bool) : QueryImpl (RegistrationNativePublicFrontend.Spec n KemSK) (OracleComp (Spec n KemSK)) :=
  fun query => (Spec n KemSK).query (selected, query)

def erase : QueryImpl (Spec n KemSK) (OracleComp (RegistrationNativePublicFrontend.Spec n KemSK)) :=
  fun query => (RegistrationNativePublicFrontend.Spec n KemSK).query query.2

/-- Tags are observational ghost data; dropping them restores the entire original query program. -/
theorem tag_source (selected : Bool) (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) Value) :
    simulateQ erase (simulateQ (tag selected) work) = work := by
  rw [← QueryImpl.simulateQ_compose]
  have same : erase ∘ₛ tag selected = (QueryImpl.id' (RegistrationNativePublicFrontend.Spec n KemSK)) := by
    funext query
    simp only [QueryImpl.compose, tag, simulateQ_spec_query, erase, QueryImpl.id'_apply]
  rw [same, simulateQ_id']

def selectedFinish (selected : Nat) : RegistrationNativeRawAdapter.TypedSpec.Domain → Bool
  | .inr (.finish index _) => decide (index = selected)
  | _ => false

noncomputable def handler (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding) :
    QueryImpl RegistrationNativeRawAdapter.TypedSpec (StateT (State source) (OracleComp (Spec n KemSK))) :=
  fun query before => simulateQ (tag (selectedFinish selectedOwner query))
    ((RegistrationNativePublicFrontend.handler setup checks wire source sign selectedOwner selectedAccept publicPrekey query).run before)

/-- Every tagged callback has precisely its original complete frontend state and reply after erasure. -/
theorem query_source (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State source) :
    simulateQ erase ((handler (n := n) setup checks wire sign selectedOwner selectedAccept publicPrekey query).run before) =
      (RegistrationNativePublicFrontend.handler setup checks wire source sign selectedOwner selectedAccept publicPrekey query).run before :=
  tag_source _ _

/-- Arbitrary adaptive role-tagged typed programs erase to the literal original complete frontend program. -/
theorem program_source (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value) (before : State source) :
    simulateQ erase ((simulateQ (handler (n := n) setup checks wire sign selectedOwner selectedAccept publicPrekey) work).run before) =
      (simulateQ (RegistrationNativePublicFrontend.handler setup checks wire source sign selectedOwner selectedAccept publicPrekey) work).run before := by
  rw [QueryImpl.simulateQ_mapStateTBase_run]
  have same : (erase (n := n) (KemSK := KemSK)).mapStateTBase
      (handler setup checks wire sign selectedOwner selectedAccept publicPrekey) =
      RegistrationNativePublicFrontend.handler setup checks wire source sign selectedOwner selectedAccept publicPrekey := by
    funext query current
    exact query_source setup checks wire sign selectedOwner selectedAccept publicPrekey query current
  rw [same]

noncomputable def run (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (before : State source) :
    OracleComp (Spec n KemSK) ((Value × RegistrationNativeLedger.State) × State source) :=
  (simulateQ (handler setup checks wire sign selectedOwner selectedAccept publicPrekey)
    (RegistrationNativeFullCompiler.compile setup.source.crypto wire serverKeyId bounds mode work)).run before

/-- Tagging retains the original full secrecy ledger and every hidden/fresh controller draw. -/
theorem run_source (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (before : State source) :
    simulateQ erase (run (n := n) setup checks wire sign selectedOwner selectedAccept publicPrekey serverKeyId bounds mode work before) =
      RegistrationNativePublicFrontend.run setup checks wire source sign selectedOwner selectedAccept publicPrekey serverKeyId bounds mode work before :=
  program_source setup checks wire sign selectedOwner selectedAccept publicPrekey _ before

def OwnerDecap : (Spec n KemSK).Domain → Prop
  | (true, .inl (.inr (.inr (.inr (.inl (.decapsulate _ _)))))) => True
  | _ => False
instance : DecidablePred (OwnerDecap (n := n) (KemSK := KemSK)) := fun query => by
  unfold OwnerDecap
  split <;> infer_instance

end BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleTags
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleTags.tag_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleTags.tag_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleTags.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleTags.query_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleTags.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleTags.program_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleTags.run_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleTags.run_source
