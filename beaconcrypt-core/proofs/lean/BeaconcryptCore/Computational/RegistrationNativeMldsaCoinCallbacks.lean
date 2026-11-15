-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaCoinCreate
import BeaconcryptCore.Computational.RegistrationNativeMldsaCoinBundle
import BeaconcryptCore.Computational.RegistrationNativeMldsaCoinAccept
import BeaconcryptCore.Computational.RegistrationNativeMldsaCoinServer
import BeaconcryptCore.Computational.RegistrationNativeMldsaCoinRecords
import BeaconcryptCore.Computational.RegistrationNativeMldsaCoinFinish
import BeaconcryptCore.Computational.RegistrationNativeKemSourceBills

/-! Literal ordinary-uniform bills for the original free native callback classes. Each bill comes from its actual source controller and retains every raw capability reply and failed prefix. KEM receipts constrain only their concrete primitive algorithms. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaCoinCallbacks
attribute [local irreducible] RegistrationNativeExperiment.handler
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeMldsa (Source Credential)
open RegistrationNativeMldsaCoinPrimitives (IsCoin ordinary)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι} {source : Source}

def bill (qKeygen qEncap qDecap : Nat) (kind : Fin 12) : Nat :=
  match kind.val with
  | 0 => 1
  | 1 => 128 + qKeygen
  | 2 => 416
  | 3 => RegistrationNativeMldsaCoinAccept.bill qEncap
  | 4 => 512
  | 5 => 192 + 9 * qDecap
  | 6 => 0
  | _ => 64

def allowance (qKeygen qEncap qDecap : Nat) : Nat :=
  ∑ kind : Fin 12, bill qKeygen qEncap qDecap kind

/-- The finite class allowance is an explicit polynomial in the three concrete KEM primitive draw caps. -/
theorem allowance_eq (qKeygen qEncap qDecap : Nat) :
    allowance qKeygen qEncap qDecap = 2369 + qKeygen + 9 * qEncap + 9 * qDecap := by
  simp [allowance, bill, Fin.sum_univ_succ, RegistrationNativeMldsaCoinAccept.bill]
  omega

private theorem bill_le (qKeygen qEncap qDecap : Nat) (kind : Fin 12) :
    bill qKeygen qEncap qDecap kind ≤ allowance qKeygen qEncap qDecap :=
  Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ kind)

theorem nonfinish (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : Credential source)
    (kem : RegistrationNativeKemSourceBills.Caps setup) (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (excluded : RegistrationNativeRawAdapter.kind query ≠ (5 : Fin 12))
    (before : RegistrationNativeExperiment.State n KemSK source) :
    ((RegistrationNativeMldsaProfile.handler setup checks wire route representation created credential query).run before).IsQueryBoundP IsCoin
      (bill kem.keygen kem.encapsulate kem.decapsulate (RegistrationNativeRawAdapter.kind query)) := by
  cases query with
  | inl coin =>
      apply ordinary _ 1
      simp only [RegistrationNativeExperiment.handler, RegistrationNativeExperiment.world, RegistrationNativeExperiment.server,
        StateT.run, IsTotalQueryBound, isQueryBound_map_iff, PqxdhRecordLiftWorld.effects]
      exact RegistrationNativeMldsaCoinPrimitives.sampled _ 1 (by simp [IsTotalQueryBound]) _
  | inr query => cases query with
    | create edPin mlPin keyId =>
        exact RegistrationNativeMldsaCoinCreate.create setup checks representation created kem.keygen kem.keygen_bound edPin mlPin keyId before
    | bundle index => exact RegistrationNativeMldsaCoinBundle.sourceBundle setup checks representation created wire index before
    | accept packet =>
        exact RegistrationNativeMldsaCoinAccept.handler source setup checks wire route representation created credential
          kem.encapsulate kem.encapsulate_bound packet before
    | build index application =>
        change ((fun result => (result.1, { before with server := result.2 })) <$>
          (RegistrationNativeMldsaServer.build source credential setup (RegistrationNativeWire.ledgerCodec wire) checks wire.encodeResponse index application).run before.server).IsQueryBoundP IsCoin 512
        simpa only [isQueryBoundP_map_iff] using
          RegistrationNativeMldsaCoinServer.build source credential setup (RegistrationNativeWire.ledgerCodec wire) checks wire.encodeResponse index application before.server
    | finish index packet => exact (excluded rfl).elim
    | hmac key bytes =>
        apply ordinary _ 0
        simp only [RegistrationNativeExperiment.handler, StateT.run_pure, IsTotalQueryBound, isQueryBound_pure]
    | hash bytes =>
        apply ordinary _ 64
        simpa only [RegistrationNativeExperiment.handler, RegistrationNativeExperiment.world, RegistrationNativeExperiment.server,
          StateT.run, IsTotalQueryBound, isQueryBound_map_iff] using
          RegistrationNativeMldsaCoinPrimitives.hash bytes before.server.world.world.1
    | serverSend keyId plaintext =>
        apply ordinary _ 64
        simpa only [RegistrationNativeExperiment.handler] using
          RegistrationNativeMldsaCoinRecords.record setup wire route (.inl (.inl (plaintext, keyId))) before
    | serverRaw raw =>
        apply ordinary _ 64
        simpa only [RegistrationNativeExperiment.handler] using
          RegistrationNativeMldsaCoinRecords.record setup wire route (.inl (.inr raw)) before
    | beaconSend owner plaintext =>
        apply ordinary _ 64
        simpa only [RegistrationNativeExperiment.handler] using
          RegistrationNativeMldsaCoinRecords.record setup wire route (.inr (owner, .inl plaintext)) before
    | beaconRaw owner raw =>
        apply ordinary _ 64
        simpa only [RegistrationNativeExperiment.handler] using
          RegistrationNativeMldsaCoinRecords.record setup wire route (.inr (owner, .inr raw)) before
/-- Every actual free native callback, including finish, has the derived finite ordinary-uniform allowance under narrow concrete KEM primitive receipts. -/
theorem handler (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : Credential source)
    (kem : RegistrationNativeKemSourceBills.Caps setup) (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : RegistrationNativeExperiment.State n KemSK source) :
    ((RegistrationNativeMldsaProfile.handler setup checks wire route representation created credential query).run before).IsQueryBoundP IsCoin
      (allowance kem.keygen kem.encapsulate kem.decapsulate) := by
  by_cases excluded : RegistrationNativeRawAdapter.kind query ≠ (5 : Fin 12)
  · exact (nonfinish setup checks wire route representation created credential kem query excluded before).mono
      (bill_le kem.keygen kem.encapsulate kem.decapsulate _)
  · have selected : RegistrationNativeRawAdapter.kind query = (5 : Fin 12) := not_not.mp excluded
    cases query with
    | inl coin => cases selected
    | inr query => cases query with
      | finish owner packet =>
        exact (RegistrationNativeMldsaCoinFinish.handler source setup checks wire route representation created credential
          kem.decapsulate kem.decapsulate_bound owner packet before).mono
            (bill_le kem.keygen kem.encapsulate kem.decapsulate (5 : Fin 12))
      | _ => cases selected

end BeaconcryptCore.Computational.RegistrationNativeMldsaCoinCallbacks
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCoinCallbacks.allowance_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCoinCallbacks.allowance_eq
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCoinCallbacks.nonfinish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCoinCallbacks.nonfinish

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCoinCallbacks.handler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCoinCallbacks.handler
