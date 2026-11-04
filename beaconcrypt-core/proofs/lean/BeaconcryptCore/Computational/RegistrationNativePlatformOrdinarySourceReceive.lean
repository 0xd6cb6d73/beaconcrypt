-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeReceiveDispatch
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryWorldReceive
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryExperiment
/-! Actual extracted receive loops execute at the current ordinary World boundary. The canonical writer is unreachable on receive; all native primitive, owner, raw-attempt and common-platform poststates remain literal. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceReceive
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeWire (Wire ledgerCodec)
open RegistrationNativePlatformOrdinaryExperiment (canonicalWire)
variable {n : Nat} {Platform E I KemSK : Type} {base : OracleSpec I}
noncomputable def server (setup : Setup base KemSK) (wire : Wire)
    (erased : Array U8 357#usize) (route : RawCtxServerRouting.SenderDecoder) (raw : Pqxdh.Bytes) :
    RegistrationNativePlatformOrdinaryWorld.M n Platform (Option RawCtxWholeOwner.Decrypted) :=
  RegistrationNativePlatformOrdinaryWorld.liftWorld
    (RegistrationNativeReceiveDispatch.serverRaw setup (canonicalWire wire) erased route raw)
noncomputable def beacon (setup : Setup base KemSK) (wire : Wire)
    (erased : Array U8 357#usize) (index : Nat) (raw : Pqxdh.Bytes) :
    RegistrationNativePlatformOrdinaryWorld.M n Platform (Option RawCtxWholeOwner.Decrypted) :=
  RegistrationNativePlatformOrdinaryWorld.liftWorld
    (RegistrationNativeReceiveDispatch.beaconRaw setup (canonicalWire wire) erased index raw)
/-- Current Server receive executes the extracted stateful receive controller on its original reached primitive and owner state. -/
theorem server_source (setup : Setup base KemSK) (wire : Wire)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (length : RegistrationNativeExtractedReceive.AeadLength setup.source.crypto)
    (erased : Array U8 357#usize) (route : RawCtxServerRouting.SenderDecoder) (raw : Pqxdh.Bytes) :
    server (n:=n) setup wire erased route raw =
      RegistrationNativePlatformOrdinaryWorld.serverStep setup (ledgerCodec wire) reserve route (.inr raw) := by
  rw [server, RegistrationNativeReceiveDispatch.server_native setup (canonicalWire wire) length erased route raw]
  exact (RegistrationNativePlatformOrdinaryWorldReceive.server setup (ledgerCodec wire) reserve route raw).symm
/-- Current Beacon receive executes the extracted stateful receive controller, including absent and inactive cases. -/
theorem beacon_source (setup : Setup base KemSK) (wire : Wire)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (length : RegistrationNativeExtractedReceive.AeadLength setup.source.crypto)
    (erased : Array U8 357#usize) (index : Nat) (raw : Pqxdh.Bytes) :
    beacon (n:=n) setup wire erased index raw =
      RegistrationNativePlatformOrdinaryWorld.beaconStep setup (ledgerCodec wire) reserve index (.inr raw) := by
  rw [beacon, RegistrationNativeReceiveDispatch.beacon_native setup (canonicalWire wire) length erased index raw]
  exact (RegistrationNativePlatformOrdinaryWorldReceive.beacon setup (ledgerCodec wire) reserve index raw).symm
end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceReceive

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceReceive.server_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceReceive.server_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceReceive.beacon_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceReceive.beacon_source
