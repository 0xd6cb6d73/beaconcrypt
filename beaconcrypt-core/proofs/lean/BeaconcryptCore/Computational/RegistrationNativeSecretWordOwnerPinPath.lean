-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordOwnerPinSummary
import BeaconcryptCore.Computational.RegistrationNativeOwnerPinPrefix

/-! The original public designation pin belongs to the same actual owner at an earlier chronological source cut. The public summary only appends bindings, and the actual Word source implements that same summary from an empty roster. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordOwnerPinPath
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeInterface (Entry)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordInterpreter (Provider)
open RegistrationNativeSecretWordTargetSource (State)
open RegistrationNativeSecretWordTargetPath (Path)
open RegistrationNativeSecretWordOwnerPins (key)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (route : RawCtxServerRouting.SenderDecoder)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
  (provider : Provider KemSK) (outer : QueryImpl Combined ProbComp)
  (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding) (serverKeyId : U64)
local notation "typedImpl" => RegistrationNativeSecretWordTargetSource.typed (n := n) (source := source)
  setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey
variable (bounds : PqxdhDeploymentInterface.FreshBounds)
local notation "fullImpl" => RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds typedImpl

/-- Every actual original prefix from the empty roster has its own exact original public configured-pin summary. -/
theorem summary (before : State n KemSK source) (empty : before.1.beacons = [])
    {entries : List Entry} {after : RegistrationNativeLedger.State × State n KemSK source}
    (path : Path fullImpl (RegistrationNativeLedger.empty, before) entries after) :
    RegistrationNativeSecretWordOwnerPinSummary.Holds after.1.transcript after.2.1.beacons := by
  apply RegistrationNativeSecretWordTargetPath.preserves fullImpl
    (fun current => RegistrationNativeSecretWordOwnerPinSummary.Holds current.1.transcript current.2.1.beacons)
    (fun query current result prior called => RegistrationNativeSecretWordOwnerPinSummary.full setup checks wire route sign input inside provider outer
      selectedOwner selectedAccept publicPrekey serverKeyId bounds query current prior result called) path
  simp only [RegistrationNativeSecretWordOwnerPinSummary.Holds, RegistrationNativeLedger.empty,
    List.map_nil, PqxdhDeploymentTranscript.summarize, PqxdhDeploymentTranscript.Summary.empty, List.foldl_nil, empty]

/-- The exact configured owner pin at an actual earlier source cut equals the original final public designation binding at that index. -/
theorem owner (before : State n KemSK source) (empty : before.1.beacons = [])
    (pre post : List Entry) (cut : RegistrationNativeLedger.State × State n KemSK source)
    (path : Path fullImpl (RegistrationNativeLedger.empty, before) pre cut)
    (index : Nat) (current : RegistrationNativePublicOwners.Owner source)
    (found : cut.2.1.beacons[index]? = some current)
    (pin : PqxdhBeaconPhase2Preparation.Word32) (keyId : U64)
    (retained : (PqxdhDeploymentTranscript.summarize ((pre ++ post).map Entry.erase)).owners[index]? = some (pin, keyId)) :
    current.view.pin.binding = ⟨pin, keyId⟩ := by
  have actual := summary setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey serverKeyId bounds before empty path
  have recorded := RegistrationNativeSecretWordTargetPath.records fullImpl (fun reached => reached.1.transcript)
    (fun query first result called => RegistrationNativeSecretWordTargetLedger.step_trace setup checks wire route sign input inside provider outer
      selectedOwner selectedAccept publicPrekey serverKeyId bounds query first result called) path
  simp only [RegistrationNativeLedger.empty, List.nil_append] at recorded
  change (PqxdhDeploymentTranscript.summarize (cut.1.transcript.map Entry.erase)).owners = cut.2.1.beacons.map key at actual
  have pinned : (PqxdhDeploymentTranscript.summarize (pre.map Entry.erase)).owners[index]? = some (key current) := by
    rw [← recorded, actual, List.getElem?_map, found, Option.map_some]
  rw [List.map_append] at retained
  have equal := RegistrationNativeOwnerPinPrefix.lookup (pre.map Entry.erase) (post.map Entry.erase) index (key current) (pin, keyId) pinned retained
  have identity := congrArg Prod.fst equal
  have assigned := congrArg Prod.snd equal
  cases binding : current.view.pin.binding
  simp only [key, binding] at identity assigned
  cases identity
  cases assigned
  rfl
end BeaconcryptCore.Computational.RegistrationNativeSecretWordOwnerPinPath
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordOwnerPinPath.summary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordOwnerPinPath.summary
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordOwnerPinPath.owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordOwnerPinPath.owner
