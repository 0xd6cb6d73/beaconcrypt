-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaBirthProvenance
import BeaconcryptCore.Computational.RegistrationNativeMldsaTableStop
import BeaconcryptCore.Computational.RegistrationNativeMldsaTypedOrigin

/-! Protected actual generated ML credentials select an already successful generation attempt at the same authentication cut. The original typed unsigned-origin failure then yields the executable candidate or a shared-cache collision, without choosing a future key or assuming independence of adaptive target selection. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaProtectedCoverage
attribute [local irreducible] RegistrationNativeExperiment.handler RegistrationSigningShared.historyFor
open RegistrationNativeMldsa (Source Credential)
open RegistrationNativeMldsaOpaque (Pool handleSource Live)
open RegistrationNativeMldsaBirthProvenance (Provenance)
open RegistrationNativeMldsaTableStop (Safe State callback observe Good)
open PqxdhServerAuthExperiment (Setup Checks)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι}
variable (source : Source)

/-- A literal successful private row and its actual attempted-generation ordinal, carrying only the displayed public key as selector data. -/
def BornKey (pool : Pool source) (ordinal : Nat) (publicKey : RegistrationNativeMldsaEuf.PublicKey) : Prop :=
  ∃ (handle : Nat) (key : Credential source), pool.keys[handle]? = some key ∧ pool.bornAt[handle]? = some ordinal ∧ key.publicKey = publicKey

/-- Any reached live credential has its own earlier successful generation receipt, even after prior failed generations. -/
theorem born_key (pool : Pool source) (good : Provenance source pool)
    (credential : Credential (handleSource source)) (key : Credential source) (live : Live source pool credential key) :
    ∃ ordinal, ordinal < pool.attempts ∧ BornKey source pool ordinal credential.publicKey := by
  obtain ⟨ordinal, generated, earlier, _same⟩ := RegistrationNativeMldsaBirthProvenance.live source pool good credential key live
  exact ⟨ordinal, earlier, credential.secret, key, live.1, generated, live.2.symm⟩

/-- The resource-derived attempt ceiling places the selected actual generation receipt in the finite reduction family. -/
theorem born_key_fin (pool : Pool source) (good : Provenance source pool)
    (credential : Credential (handleSource source)) (key : Credential source) (live : Live source pool credential key)
    (cap : Nat) (room : pool.attempts ≤ cap) :
    ∃ ordinal : Fin cap, BornKey source pool ordinal.val credential.publicKey := by
  obtain ⟨ordinal, earlier, born⟩ := born_key source pool good credential key live
  exact ⟨⟨ordinal, Nat.lt_of_lt_of_le earlier room⟩, born⟩

private theorem original (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : Credential (handleSource source))
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (free : RegistrationNativeMldsaReceiptPreservation.NonSigning query)
    (before : State (n := n) (KemSK := KemSK) source)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State (n := n) (KemSK := KemSK) source)
    (supported : result ∈ support ((callback source setup checks wire route representation created credential query).run before)) :
    (result.1, result.2.1) ∈ support ((RegistrationNativeExperiment.handler setup checks wire route representation created
      (handleSource source) credential query).run before.1) := by
  have law : RegistrationNativeMldsaProfile.handler (n := n) setup checks wire route representation created credential query =
      RegistrationNativeMldsaProgram.liftState (RegistrationNativeExperiment.handler setup checks wire route representation created
        (handleSource source) credential query) := by
    cases query with
    | inl coin => rfl
    | inr query => cases query with
      | create _ _ _ | bundle _ | build _ _ => exact False.elim free
      | _ => rfl
  change result ∈ support ((fun inner => (inner.1.1, (inner.1.2, inner.2))) <$>
    RegistrationNativeMldsaTableProgram.runState source
      (RegistrationNativeMldsaProfile.handler setup checks wire route representation created credential query) before.1 before.2) at supported
  rw [law, RegistrationNativeMldsaTableProgram.run_liftState, Functor.map_map, support_map] at supported
  obtain ⟨inner, possible, same⟩ := supported
  cases same
  exact possible

section Actual
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : Credential (handleSource source))
    (fallback : Credential source)

/-- Actual protected initial-Server response origin failure selects that generated key's earlier attempt, retaining the unchanged shared-cache collision alternative. -/
theorem finish (index : Nat) (owner : RegistrationNativeBeaconFrontend.Owner (handleSource source))
    (pending : registration.BeaconPending) (oneTime : PqxdhJointGapDh.ScalarBytes) (packet : registration.ResponsePacket)
    (before after : State (n := n) (KemSK := KemSK) source) (application : Pqxdh.Bytes)
    (safe : Safe source credential fallback before) (provenance : Provenance source before.2)
    (selected : before.1.beacons[index]? = some owner) (phase : owner.phase = .initSent pending oneTime)
    (keyProtected : pending.binding.server_pin.public_key = credential.publicKey)
    (supported : (.ok (some application), after) ∈ support
      ((callback source setup checks wire route representation created credential (.inr (.finish index (some packet)))).run before))
    (absent : ¬ MldsaTranscriptAuth.Issued (RegistrationResponseExecutor.trial true pending packet
      (RegistrationSigningShared.historyFor (PqxdhRefinement.absBytes pending.binding.server_pin.public_key)
        (RegistrationNativeMldsaShared.nativeProject before.1)))) :
    CacheHasCollision after.1.server.world.world.1.primitive.2 ∨
      ∃ ordinal, ordinal < before.2.attempts ∧ BornKey source before.2 ordinal credential.publicKey ∧
        ∃ forgery, observe source credential.publicKey (.inr (.finish index (some packet))) before (.ok (some application)) after = some forgery ∧
          Good source credential.publicKey after forgery := by
  obtain ⟨ordinal, earlier, born⟩ := born_key source before.2 provenance credential fallback safe.server
  have supportedOriginal := original source setup checks wire route representation created credential (.inr (.finish index (some packet))) trivial
    before (.ok (some application), after) supported
  rcases RegistrationNativeMldsaTypedOrigin.finish setup checks wire route representation created credential credential.publicKey index owner pending oneTime packet
    before.1 after.1 application selected phase supportedOriginal keyProtected safe.cached absent with candidate | collision
  · obtain ⟨forgery, chosen⟩ := candidate
    exact Or.inr ⟨ordinal, earlier, born, forgery, chosen,
      RegistrationNativeMldsaTableStop.captured source setup checks wire route representation created credential credential.publicKey fallback
        (.inr (.finish index (some packet))) before (.ok (some application), after) forgery safe supported chosen⟩
  · exact Or.inl collision

end Actual
end BeaconcryptCore.Computational.RegistrationNativeMldsaProtectedCoverage
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaProtectedCoverage.born_key' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaProtectedCoverage.born_key


/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaProtectedCoverage.finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaProtectedCoverage.finish

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaProtectedCoverage.born_key_fin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaProtectedCoverage.born_key_fin
