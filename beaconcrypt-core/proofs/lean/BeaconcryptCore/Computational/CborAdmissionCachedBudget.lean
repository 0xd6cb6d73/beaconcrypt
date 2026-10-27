-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentCompileBudget

/-! A record command whose addressed kernel has already been preloaded performs no further source14 kernel read. Its only possible source query is the existing single commitment hash, so admission's prefetch preserves the original per-command reveal/read budget. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborAdmissionCachedBudget
open PqxdhServerAuthExperiment
open PqxdhDeploymentCompile (Local Kernel peerKernel ownerKernel)
open PqxdhDeploymentCompileBudget (unit local_bound logged_bound server_hashes beacon_hashes)
open PqxdhRegistrationJointRevealCosts (SourceKind sourceKind)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

theorem server_cached (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (kind : SourceKind)
    (query : RawCtxServerMixed.SourceSpec.Domain) (copies : Local) (keyId : Std.U64) (kernel : Kernel)
    (target : PqxdhDeploymentCompile.serverTarget route query = some keyId)
    (cached : copies.peers keyId = some kernel) :
    ((PqxdhDeploymentCompile.serverLocal setup codec route query).run copies).IsQueryBoundP
      (fun request => sourceKind (KemSK := KemSK) request = kind) (unit kind (.inl 7)) := by
  rw [PqxdhDeploymentCompileRecords.serverLocal_some setup codec route query copies keyId target]
  simp only [peerKernel, cached, pure_bind, isQueryBoundP_map_iff]
  simpa only [Nat.mul_one, PqxdhDeploymentNative.logged] using local_bound setup codec kind _ 1
    (logged_bound _ _ 1 [] (server_hashes (fun _ => setup.serverKeyId) route codec.frameRead query
      (PqxdhDeploymentCompile.localServer codec copies.log keyId (some kernel) copies.serverRaw)))

theorem beacon_cached (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (kind : SourceKind) (index : Nat) (query : RawCtxMixedOwner.SourceSpec.Domain)
    (copies : Local) (kernel : Kernel) (cached : copies.owners index = some kernel) :
    ((PqxdhDeploymentCompile.beaconLocal setup codec index query).run copies).IsQueryBoundP
      (fun request => sourceKind (KemSK := KemSK) request = kind) (unit kind (.inl 7)) := by
  by_cases inside : index < copies.log.owners.length
  case pos =>
    rw [PqxdhDeploymentCompileRecords.beaconLocal_present setup codec index query copies inside]
    simp only [ownerKernel, cached, pure_bind, isQueryBoundP_map_iff]
    simpa only [Nat.mul_one, PqxdhDeploymentNative.logged] using local_bound setup codec kind _ 1
      (logged_bound _ _ 1 [] (beacon_hashes codec.frameRead query
        (PqxdhDeploymentCompile.localOwner codec copies.log index (some kernel) (copies.ownerRaw index))))
  case neg =>
    rw [PqxdhDeploymentCompileRecords.beaconLocal_absent setup codec index query copies inside]
    trivial

end BeaconcryptCore.Computational.CborAdmissionCachedBudget

/-- info: 'BeaconcryptCore.Computational.CborAdmissionCachedBudget.server_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborAdmissionCachedBudget.server_cached
/-- info: 'BeaconcryptCore.Computational.CborAdmissionCachedBudget.beacon_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborAdmissionCachedBudget.beacon_cached
