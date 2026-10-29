-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomServerAlias
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerAlias
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomRepeatMap
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasExposureBound

/-! The actual complete original-ledger alias client cannot repeat a selected role using two opaque atoms. Both role caps follow from its original one-use Server session and Beacon owner lifecycle, and order follows from the literal observer on the same supported result. A repeated native selected-input attempt in its evaluated chronology therefore exposes a protected candidate-equal literal in this same Word result. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasRepeat
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message input)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordService (Combined)
open PqxdhKemIndCca
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

private theorem closed_support {Result : Type} (outer : QueryImpl Combined ProbComp)
    (work : OracleComp Combined Result) (result : Result) (supported : result ∈ support (simulateQ outer work)) :
    result ∈ support work := by
  induction work using OracleComp.inductionOn with
  | pure value =>
      simpa only [simulateQ_pure, mem_support_pure_iff] using supported
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, mem_support_bind_iff] at supported ⊢
      obtain ⟨reply, _possible, later⟩ := supported
      exact ⟨reply, mem_support_query query reply, ih reply later⟩

/-- The original one-use lifecycle discharges both atom-attempt bounds on the exact complete client result, preserving its entire ledger and provider state. -/
theorem client_one (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (source : RegistrationNativeMldsa.Source) (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (interpret : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey)
    (challenge : MlKem768Ciphertext) (outer : QueryImpl Combined ProbComp)
    (selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (front : RegistrationNativeSecretWordMessage.State source) (ordinary : RegistrationNativePublicInterpreter.State n KemSK)
    (kem : RegistrationNativeSecretWordKemProvider.State KemSK) (sessions : front.server.sessions = [])
    (parsed : front.parsedAccepts = 0) (owners : front.beacons = []) (keys : kem.1.keys = [])
    (result : RegistrationNativeSecretWordAliasClient.Result source n KemSK Value)
    (supported : result ∈ support (simulateQ outer (RegistrationNativeSecretWordAliasClient.client setup checks wire source route sign interpret inside
      (RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge)
      selected selectedAccept publicPrekey serverKeyId bounds mode work front ordinary kem))) :
    ∀ role, RegistrationNativeSecretWordAtomInstallTrace.count role result.1.2 ≤ 1 := by
  intro role
  cases role with
  | server =>
      exact RegistrationNativeSecretWordAtomServerAlias.client_one setup checks wire source route sign interpret inside
        selected pairs publicKey challenge outer selected selectedAccept publicPrekey serverKeyId bounds mode work front ordinary kem sessions parsed result supported
  | beacon =>
      exact RegistrationNativeSecretWordAtomOwnerAlias.client_one setup checks wire source route sign interpret inside
        selected pairs publicKey challenge outer selectedAccept publicPrekey serverKeyId bounds mode work front ordinary kem owners keys result supported

/-- Same-result event order is derived from the actual literal observer even after all outer table effects have been closed. -/
theorem client_order (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (source : RegistrationNativeMldsa.Source) (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (interpret : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
    (provider : RegistrationNativeSecretWordInterpreter.Provider KemSK) (outer : QueryImpl Combined ProbComp)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (front : RegistrationNativeSecretWordMessage.State source) (ordinary : RegistrationNativePublicInterpreter.State n KemSK)
    (kem : RegistrationNativeSecretWordKemProvider.State KemSK)
    (result : RegistrationNativeSecretWordAliasClient.Result source n KemSK Value)
    (supported : result ∈ support (simulateQ outer (RegistrationNativeSecretWordAliasClient.client setup checks wire source route sign interpret inside
      provider selectedOwner selectedAccept publicPrekey serverKeyId bounds mode work front ordinary kem))) :
    ∀ role, RegistrationNativeSecretWordAtomTraceOrder.Good role result.1.2.events := by
  have actual := closed_support outer _ result supported
  have observed : result.1 ∈ support (RegistrationNativeSecretWordFrontendTrace.program (n := n)
      (RegistrationNativeSecretWordFrontend.run setup checks wire source sign selectedOwner selectedAccept publicPrekey serverKeyId bounds mode work front)) := by
    apply OracleComp.support_simulateQ_run'_subset (RegistrationNativeSecretWordInterpreter.handler setup wire route sign interpret inside provider)
      _ (RegistrationNativeSecretWordInterpreter.initial ordinary kem)
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem Prod.fst actual
  intro role
  exact RegistrationNativeSecretWordAtomTraceOrder.program_good role _ RegistrationNativeSecretWordFrontendTrace.initial
    (by simp [RegistrationNativeSecretWordAtomTraceOrder.Good, RegistrationNativeSecretWordAtomTraceOrder.stream,
      RegistrationNativeSecretWordFrontendTrace.initial]) result.1 observed

/-- A repeated selected native-input role attempt in this actual complete result exposes a candidate-equal literal in its same Word chronology; no new atom cap or lifecycle premise is assumed. -/
theorem repeated_literal (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (source : RegistrationNativeMldsa.Source) (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey)
    (challenge : MlKem768Ciphertext) (outer : QueryImpl Combined ProbComp)
    (selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (front : RegistrationNativeSecretWordMessage.State source) (ordinary : RegistrationNativePublicInterpreter.State n KemSK)
    (kem : RegistrationNativeSecretWordKemProvider.State KemSK) (sessions : front.server.sessions = [])
    (parsed : front.parsedAccepts = 0) (owners : front.beacons = []) (keys : kem.1.keys = [])
    (result : RegistrationNativeSecretWordAliasClient.Result source n KemSK Value)
    (supported : result ∈ support (simulateQ outer (RegistrationNativeSecretWordAliasClient.client setup checks wire source route sign
      (input setup.joint setup.dh seed scalar)
      (RegistrationNativeSecretWordProtection.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar)))
      (RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge)
      selected selectedAccept publicPrekey serverKeyId bounds mode work front ordinary kem)))
    (candidate : MlKemSharedSecret)
    (repeated : RegistrationNativeG2Trace.RepeatedRoleAttempt (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
      (RegistrationNativeSelectiveHiddenService.selected
        (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) candidate)
      (result.1.2.events.map (RegistrationNativeSecretWordCheckedTrace.event candidate))) :
    RegistrationNativeSecretWordAliasExposureBound.Exposure (input setup.joint setup.dh seed scalar)
      (RegistrationNativeSecretWordProtection.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) candidate result.1.2 := by
  have bounded := client_one setup checks wire source route sign (input setup.joint setup.dh seed scalar)
    (RegistrationNativeSecretWordProtection.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar)))
    selected pairs publicKey challenge outer selectedAccept publicPrekey serverKeyId bounds mode work front ordinary kem
    sessions parsed owners keys result supported
  have ordered := client_order setup checks wire source route sign (input setup.joint setup.dh seed scalar)
    (RegistrationNativeSecretWordProtection.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar)))
    (RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge)
    outer selected selectedAccept publicPrekey serverKeyId bounds mode work front ordinary kem result supported
  obtain ⟨role, message, key, exposed, formed, protectedInput, _word, literal⟩ :=
    RegistrationNativeSecretWordAtomRepeatMap.repeated_literal setup.joint setup.dh seed scalar candidate
      (setup.joint.staticDh seed (setup.dh.publicKey scalar)) result.1.2.events ordered bounded repeated
  exact ⟨role, message, key, exposed, formed, protectedInput, literal⟩

end BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasRepeat
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasRepeat.client_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasRepeat.client_one
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasRepeat.client_order' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasRepeat.client_order
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasRepeat.repeated_literal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasRepeat.repeated_literal
