-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaBadCut
import BeaconcryptCore.Computational.RegistrationNativeMldsaMap

/-! Protected unsigned-origin failure is defined on literal original native credentials and callback state. The private table event is its exact representation, independent of any signing-key map. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaOriginEvent
open RegistrationNativeMldsa (Source Credential)
open RegistrationNativeMldsaMap (Map credential owner owners nativeState)
variable {n : Nat} {KemSK : Type}
attribute [local irreducible] RegistrationSigningShared.historyFor RegistrationAuthenticationNative.trial

inductive Bad (source : Source) (server : Credential source) :
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) → RegistrationNativeExperiment.State n KemSK source →
      RegistrationNativeRawAdapter.TypedSpec.Range query → Prop where
  | accept (packet : registration.InitPacket) (session : Nat)
      (before : RegistrationNativeExperiment.State n KemSK source)
      (current : RegistrationNativeBeaconFrontend.Owner source)
      (owned : current ∈ before.beacons) (keyProtected : packet.mldsa_public_key = current.mldsa.publicKey)
      (absent : ¬ MldsaTranscriptAuth.Issued (RegistrationAuthenticationNative.trial true before.server.pin packet
        (RegistrationSigningShared.historyFor (PqxdhRefinement.absBytes packet.mldsa_public_key)
          (RegistrationNativeMldsaShared.nativeProject before)))) :
      Bad source server (.inr (.accept packet)) before (.ok (some session))
  | finish (index : Nat) (packet : registration.ResponsePacket) (application : Pqxdh.Bytes)
      (before : RegistrationNativeExperiment.State n KemSK source)
      (current : RegistrationNativeBeaconFrontend.Owner source)
      (pending : registration.BeaconPending) (oneTime : PqxdhJointGapDh.ScalarBytes)
      (found : before.beacons[index]? = some current) (phase : current.phase = .initSent pending oneTime)
      (keyProtected : pending.binding.server_pin.public_key = server.publicKey)
      (absent : ¬ MldsaTranscriptAuth.Issued (RegistrationResponseExecutor.trial true pending packet
        (RegistrationSigningShared.historyFor (PqxdhRefinement.absBytes pending.binding.server_pin.public_key)
          (RegistrationNativeMldsaShared.nativeProject before)))) :
      Bad source server (.inr (.finish index (some packet))) before (.ok (some application))

/-- Replacing only private credential representations leaves this original public-key, phase, and same-cut signing-history event unchanged. -/
theorem mapped {left right : Source} (mapping : Map left right) (server : Credential left)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : RegistrationNativeExperiment.State n KemSK left)
    (reply : RegistrationNativeRawAdapter.TypedSpec.Range query) :
    Bad right (credential mapping server) query (nativeState mapping before) reply ↔ Bad left server query before reply := by
  constructor
  · intro bad
    cases bad with
    | accept packet session _ current owned keyProtected absent =>
        obtain ⟨original, member, same⟩ := List.mem_map.mp owned
        subst current
        exact .accept packet session before original member keyProtected absent
    | finish index packet application _ current pending oneTime found phase keyProtected absent =>
        change (owners mapping before.beacons)[index]? = some current at found
        rw [RegistrationNativeMldsaMap.owners_lookup] at found
        cases prior : before.beacons[index]? with
        | none => simp only [prior, Option.map_none] at found; cases found
        | some original =>
            simp only [prior, Option.map_some, Option.some.injEq] at found
            subst current
            exact .finish index packet application before original pending oneTime prior phase keyProtected absent
  · intro bad
    cases bad with
    | accept packet session _ current owned keyProtected absent =>
        exact .accept packet session (nativeState mapping before) (owner mapping current)
          (List.mem_map.mpr ⟨current, owned, rfl⟩) keyProtected absent
    | finish index packet application _ current pending oneTime found phase keyProtected absent =>
        have lookup : (owners mapping before.beacons)[index]? = some (owner mapping current) := by
          simp only [RegistrationNativeMldsaMap.owners_lookup, found, Option.map_some]
        exact .finish index packet application (nativeState mapping before) (owner mapping current) pending oneTime lookup phase keyProtected absent

/-- The earlier actual private-table bad cut is exactly the original event before applying its key map. -/
theorem table (source : Source) (server : Credential (RegistrationNativeMldsaOpaque.handleSource source))
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : RegistrationNativeMldsaTableStop.State (n := n) (KemSK := KemSK) source)
    (reply : RegistrationNativeRawAdapter.TypedSpec.Range query) :
    RegistrationNativeMldsaBadCut.Bad source server query before reply ↔
      Bad (RegistrationNativeMldsaOpaque.handleSource source) server query before.1 reply := by
  constructor
  · intro bad
    cases bad with
    | accept packet session before current owned keyProtected absent => exact .accept packet session _ current owned keyProtected absent
    | finish index packet application before current pending oneTime found phase keyProtected absent =>
        exact .finish index packet application _ current pending oneTime found phase keyProtected absent
  · intro bad
    cases bad with
    | accept packet session _ current owned keyProtected absent => exact .accept packet session before current owned keyProtected absent
    | finish index packet application _ current pending oneTime found phase keyProtected absent =>
        exact .finish index packet application before current pending oneTime found phase keyProtected absent

end BeaconcryptCore.Computational.RegistrationNativeMldsaOriginEvent

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaOriginEvent.mapped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaOriginEvent.mapped

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaOriginEvent.table' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaOriginEvent.table
