-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallServerTyped
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetTracedSource

/-! The same actual successful monitored typed Server build contributes its literal current Ready descriptor once. The private World and key interpreter are erased only after that chronological callback has been isolated. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPeerTracedFinish
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message ServerReady)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordInterpreter (Provider)
open RegistrationNativeSecretWordTargetTracedSource (State)
open RegistrationNativeSecretWordInstallOrdinals (messages)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

/-- A successful actual monitored Server callback installs precisely its current retained descriptor in its own role. -/
theorem build (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
    (provider : Provider KemSK) (outer : QueryImpl Combined ProbComp)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (role : PqxdhRecordLiftInterface.Role) (handle : Nat) (payload : Option (Slice U8)) (keyId : U64) (bytes : Pqxdh.Bytes)
    (ready : ServerReady) (before after : State n KemSK source)
    (stored : before.1.1.server.sessions[handle]? = some (some ready))
    (supported : (.ok (some (keyId, bytes)), after) ∈ support
      ((RegistrationNativeSecretWordTargetTracedSource.typed setup checks wire route sign input inside provider outer
        selectedOwner selectedAccept publicPrekey (.inr (.build handle payload))).run before)) :
    messages role after.1.2.events = messages role before.1.2.events ++ if role = .server then [ready.reference] else [] := by
  simp only [RegistrationNativeSecretWordTargetTracedSource.typed, StateT.run, support_map] at supported
  obtain ⟨reached, called, returned⟩ := supported
  have possible : reached.1 ∈ support ((simulateQ RegistrationNativeSecretWordFrontendTrace.handler
      ((RegistrationNativeSecretWordFrontend.handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey
        (.inr (.build handle payload))).run before.1.1)).run before.1.2) := by
    apply OracleComp.support_simulateQ_run'_subset
      (RegistrationNativeSecretWordTargetSource.implementation setup wire route sign input inside provider outer) _ before.2
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem Prod.fst called
  have success : reached.1.1.1 = .ok (some (keyId, bytes)) := congrArg Prod.fst returned
  have traceEq : reached.1.2 = after.1.2 := congrArg (fun result => result.2.1.2) returned
  have bill := RegistrationNativeSecretWordInstallServerTyped.build_live setup checks wire sign selectedOwner selectedAccept publicPrekey
    role handle payload before.1.1 ready stored before.1.2 reached.1 possible
  rw [← traceEq]
  simpa only [success, RegistrationNativeInstallBeaconComplete.present, and_true] using bill
end BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPeerTracedFinish
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPeerTracedFinish.build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPeerTracedFinish.build
