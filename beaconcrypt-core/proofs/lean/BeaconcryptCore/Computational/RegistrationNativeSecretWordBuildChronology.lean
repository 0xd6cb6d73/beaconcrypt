-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordSessionSlotsSource
import BeaconcryptCore.Computational.RegistrationNativeSecretWordResponseLedger
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAcceptFreshSource

/-! A response of a successfully accepted native session must occur after that actual accept, and its pre-build Ready is exactly the same retained capability. Both cuts belong to one supported original full-ledger path. No independent source receipts are equated. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordBuildChronology
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message ServerReady)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordInterpreter (Provider)
open RegistrationNativeSecretWordTargetSource (State)
open RegistrationNativeInterface (Entry)
open RegistrationNativeSecretWordTargetPath (Path)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (route : RawCtxServerRouting.SenderDecoder)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
  (provider : Provider KemSK) (outer : QueryImpl Combined ProbComp)
  (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
  (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
local notation "typedImpl" => RegistrationNativeSecretWordTargetSource.typed (n := n) (source := source)
  setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey
local notation "fullImpl" => RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds typedImpl
local notation "FullState" => RegistrationNativeLedger.State × State n KemSK source

private theorem build_mem (transcript : List PqxdhDeploymentInterface.Entry) (handle : Nat)
    (response : PqxdhServerRegistrationPublication.Response)
    (found : PqxdhDeploymentTranscript.buildOf transcript handle = some response) :
    ∃ payload, (⟨.inl (.inr (.build handle payload)), some response⟩ : PqxdhDeploymentInterface.Entry) ∈ transcript := by
  obtain ⟨entry, member, value⟩ := List.exists_of_findSome?_eq_some found
  rcases entry with ⟨((coin | command) | secrecy), reply⟩
  · cases value
  · cases command with
    | build index payload =>
        cases reply with
        | none => cases value
        | some encoded =>
            simp only at value
            split at value
            · rename_i same
              simp only [Option.some.injEq] at value
              subst same value
              exact ⟨payload, member⟩
            · cases value
    | _ => cases value
  · cases value

private theorem native_build (entry : Entry) (handle : Nat) (payload : Option Pqxdh.Bytes)
    (response : PqxdhServerRegistrationPublication.Response)
    (same : entry.erase = (⟨.inl (.inr (.build handle payload)), some response⟩ : PqxdhDeploymentInterface.Entry)) :
    entry = (⟨.inl (.inr (.build handle payload)), some response⟩ : Entry) := by
  rcases entry with ⟨((coin | command) | secrecy), reply⟩
  · cases same
  · cases command <;> cases same
    rfl
  · cases same

/-- The first successful original build is an actual successful native entry with exactly those response bytes. -/
theorem original_build (entries : List Entry) (handle : Nat)
    (response : PqxdhServerRegistrationPublication.Response)
    (found : PqxdhDeploymentTranscript.buildOf (entries.map Entry.erase) handle = some response) :
    ∃ payload, (⟨.inl (.inr (.build handle payload)), some response⟩ : Entry) ∈ entries := by
  obtain ⟨payload, member⟩ := build_mem (entries.map Entry.erase) handle response found
  obtain ⟨native, nativeMember, erased⟩ := List.mem_map.mp member
  exact ⟨payload, native_build native handle payload response erased ▸ nativeMember⟩

private theorem no_earlier {before after : FullState} {entries : List Entry}
    (path : Path fullImpl before entries after) (handle : Nat)
    (fresh : handle = after.2.1.server.sessions.length) (payload : Option Pqxdh.Bytes)
    (response : PqxdhServerRegistrationPublication.Response)
    (member : (⟨.inl (.inr (.build handle payload)), some response⟩ : Entry) ∈ entries) : False := by
  obtain ⟨left, right, recorded⟩ := List.mem_iff_append.mp member
  obtain ⟨first, last, _prior, called, later⟩ := RegistrationNativeSecretWordTargetPath.split fullImpl path left _ right recorded
  obtain ⟨ready, found, _encoded⟩ := RegistrationNativeSecretWordResponseLedger.full setup checks wire route sign input inside
    provider outer selectedOwner selectedAccept publicPrekey serverKeyId bounds handle payload response first last called
  have step := RegistrationNativeSecretWordSessionSlotsSource.full setup checks wire route sign input inside provider outer
    selectedOwner selectedAccept publicPrekey serverKeyId bounds (.inl (.inr (.build handle payload))) first (some response, last) called
  have suffix := RegistrationNativeSecretWordSessionSlotsSource.path setup checks wire route sign input inside provider outer
    selectedOwner selectedAccept publicPrekey serverKeyId bounds later
  have below := (List.getElem?_eq_some_iff.mp found).1
  have size := step.1.trans suffix.1
  omega

/-- The successful original response uses the exact Ready retained by its earlier same-path accept. -/
theorem response {before first last after : FullState} {pre post : List Entry}
    (raw : Pqxdh.Bytes) (packet : registration.InitPacket) (handle : Nat)
    (decoded : RegistrationNativeWire.readInit wire raw = some packet)
    (prior : Path fullImpl before pre first)
    (called : (some handle, last) ∈ support ((fullImpl (.inl (.inr (.accept raw)))).run first))
    (later : Path fullImpl last post after) (ready : ServerReady)
    (stored : last.2.1.server.sessions[handle]? = some (some ready))
    (payload : Option Pqxdh.Bytes) (published : PqxdhServerRegistrationPublication.Response)
    (member : (⟨.inl (.inr (.build handle payload)), some published⟩ : Entry) ∈
      pre ++ ⟨.inl (.inr (.accept raw)), some handle⟩ :: post) :
    ∃ (buildFirst buildLast : FullState) (left right : List Entry),
      post = left ++ ⟨.inl (.inr (.build handle payload)), some published⟩ :: right ∧
      Path fullImpl last left buildFirst ∧
      (some published, buildLast) ∈ support ((fullImpl (.inl (.inr (.build handle payload)))).run buildFirst) ∧
      Path fullImpl buildLast right after ∧
      RegistrationNativeSecretWordResponse.EncodedFrom wire ready buildFirst.2.1.server.pin published.serialized := by
  have fresh := RegistrationNativeSecretWordAcceptFreshSource.full setup checks wire route sign input inside provider outer
    selectedOwner selectedAccept publicPrekey serverKeyId bounds raw packet handle decoded first last called
  rw [List.mem_append, List.mem_cons] at member
  rcases member with earlier | equal | subsequent
  · exact (no_earlier setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey
      serverKeyId bounds prior handle fresh payload published earlier).elim
  · cases equal
  · obtain ⟨left, right, recorded⟩ := List.mem_iff_append.mp subsequent
    obtain ⟨buildFirst, buildLast, beforeBuild, built, afterBuild⟩ :=
      RegistrationNativeSecretWordTargetPath.split fullImpl later left _ right recorded
    obtain ⟨actual, selected, encoded⟩ := RegistrationNativeSecretWordResponseLedger.full setup checks wire route sign input inside
      provider outer selectedOwner selectedAccept publicPrekey serverKeyId bounds handle payload published buildFirst buildLast built
    have slots := RegistrationNativeSecretWordSessionSlotsSource.path setup checks wire route sign input inside provider outer
      selectedOwner selectedAccept publicPrekey serverKeyId bounds beforeBuild
    have equal := slots.2 handle (List.getElem?_eq_some_iff.mp stored).1 actual selected
    have same : actual = ready := Option.some.inj (Option.some.inj (equal.symm.trans stored))
    subst actual
    exact ⟨buildFirst, buildLast, left, right, recorded, beforeBuild, built, afterBuild, encoded⟩

end BeaconcryptCore.Computational.RegistrationNativeSecretWordBuildChronology

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordBuildChronology.response' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordBuildChronology.response
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordBuildChronology.original_build' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordBuildChronology.original_build
