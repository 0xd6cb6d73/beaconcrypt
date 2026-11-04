-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterInterface
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLowSpec
/-- Only the trusted secrecy-ledger compiler emits these private refused attempts. Public adversaries retain the Slice-only interface. -/
inductive Refused where
  | serverSend (keyId :U64) (bytes :Pqxdh.Bytes) (oversized :¬bytes.length≤Usize.max)
  | beaconSend (owner :Nat) (bytes :Pqxdh.Bytes) (oversized :¬bytes.length≤Usize.max)

abbrev RefusedSpec :OracleSpec Refused :=fun _=>Option RawCtxSourceSend.Encrypted
abbrev Spec :=RegistrationNativePlatformPublicAdapterInterface.Spec+RefusedSpec

def nativeQuery :Spec.Domain →RegistrationNativeInterface.Spec.Domain
  | .inl query=>RegistrationNativePlatformPublicAdapterInterface.nativeCore query
  | .inr (.serverSend key bytes _)=>.inr (.serverSend key bytes)
  | .inr (.beaconSend owner bytes _)=>.inr (.beaconSend owner bytes)

def publicQuery (query :RegistrationNativePlatformPublicAdapterInterface.Spec.Domain) :
    OracleComp Spec (RegistrationNativePlatformPublicAdapterInterface.Spec.Range query) :=Spec.query (.inl query)

def nativeAdapter :QueryImpl Spec (OracleComp RegistrationNativeInterface.Spec)
  | .inl query=>RegistrationNativePlatformPublicAdapterInterface.adapter query
  | .inr (.serverSend key bytes _)=>RegistrationNativeInterface.Spec.query (.inr (.serverSend key bytes))
  | .inr (.beaconSend owner bytes _)=>RegistrationNativeInterface.Spec.query (.inr (.beaconSend owner bytes))

theorem public_native (query :RegistrationNativePlatformPublicAdapterInterface.Spec.Domain) :
    simulateQ nativeAdapter (publicQuery query)=RegistrationNativePlatformPublicAdapterInterface.adapter query :=by
  rw [publicQuery,simulateQ_spec_query]
  rfl

theorem server_native (key :U64) (bytes :Pqxdh.Bytes) (oversized :¬bytes.length≤Usize.max) :
    nativeAdapter (.inr (.serverSend key bytes oversized))=
      (RegistrationNativeInterface.Spec.query (.inr (.serverSend key bytes)) :OracleComp RegistrationNativeInterface.Spec _) :=rfl

theorem beacon_native (owner :Nat) (bytes :Pqxdh.Bytes) (oversized :¬bytes.length≤Usize.max) :
    nativeAdapter (.inr (.beaconSend owner bytes oversized))=
      (RegistrationNativeInterface.Spec.query (.inr (.beaconSend owner bytes)) :OracleComp RegistrationNativeInterface.Spec _) :=rfl
end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLowSpec
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLowSpec.public_native' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLowSpec.public_native
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLowSpec.server_native' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLowSpec.server_native
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLowSpec.beacon_native' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLowSpec.beacon_native
