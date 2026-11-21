-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallWitness

/-! The concrete original-prefix count invariant identifies the same installation ordinal without equating cuts from separate source executions. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOrdinalBase
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordInterpreter (Provider)
open RegistrationNativeSecretWordTargetTracedSource (State)
open RegistrationNativeSecretWordTargetPath (Path)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (route : RawCtxServerRouting.SenderDecoder)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
  (provider : Provider KemSK) (outer : QueryImpl Combined ProbComp)
  (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
  (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
local notation "typed" => RegistrationNativeSecretWordTargetTracedSource.typed (n := n) (source := source)
  setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey
local notation "full" => RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds typed

def PrefixCounts (candidate : PqxdhKemIndCca.MlKemSharedSecret) (before : State n KemSK source) : Prop :=
  ∀ role pre cut, Path full (RegistrationNativeLedger.empty, before) pre cut →
    RegistrationNativeInstallOrdinals.Counts role
      (cut.2.1.2.events.map (RegistrationNativeSecretWordCheckedTrace.event candidate)) cut.1.transcript

/-- The same actual monitored prefix count equals the number of earlier original successful public handles. -/
theorem prefix_count (candidate : PqxdhKemIndCca.MlKemSharedSecret) (role : PqxdhRecordLiftInterface.Role)
    (before : State n KemSK source) (pre : List RegistrationNativeInterface.Entry)
    (cut : RegistrationNativeLedger.State × State n KemSK source)
    (prior : Path full (RegistrationNativeLedger.empty, before) pre cut)
    (counted : RegistrationNativeInstallOrdinals.Counts role
      (cut.2.1.2.events.map (RegistrationNativeSecretWordCheckedTrace.event candidate)) cut.1.transcript) :
    (RegistrationNativeSecretWordInstallOrdinals.messages role cut.2.1.2.events).length =
      (RegistrationNativeInstallOrdinals.handles role pre).length := by
  have recorded := RegistrationNativeSecretWordTargetTracedPath.records setup checks wire route sign input inside provider outer
    selectedOwner selectedAccept publicPrekey serverKeyId bounds prior
  simp only [RegistrationNativeLedger.empty, List.nil_append] at recorded
  change (RegistrationNativeInstallOrdinals.messages role _).length = _ at counted
  rw [RegistrationNativeSecretWordInstallOrdinals.messages_eval, List.length_map, recorded] at counted
  exact counted
end BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOrdinalBase
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOrdinalBase.prefix_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOrdinalBase.prefix_count
