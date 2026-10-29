-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemSwitchTotal
import BeaconcryptCore.Computational.RegistrationNativeKemFullSource

/-! The original native raw/secrecy compiler supplies the online candidate provider's totality obligations from its existing public adversary budget. No caller supplies a private-KEM capacity, reveal or admissibility certificate. The exact native auxiliary state, complete live pool, histories, returned original ledger and first-getter phase are retained. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemFullSwitch
open PqxdhKemIndCca
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhDeploymentInterface (Budget FreshBounds Mode)
open RegistrationNativeKemServerState (State)
variable {ι KemSK Value : Type} {base : OracleSpec ι} {n : Nat} {mlSource : RegistrationNativeMldsa.Source}

/-- Full actual native online candidate execution is the concrete total reserved provider on the same complete source output, pool and current local state. -/
theorem program_source (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
    (bounds : FreshBounds) (mode : Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (budget : Budget) (bounded : RegistrationNativeInterface.Respects budget work) (parsed : Nat)
    (selected : Fin budget.capacity) (chosen : MlKem768PublicKey × KemSK) (others : Fin budget.create → MlKem768PublicKey × KemSK)
    (real : Bool) (localState : State n mlSource) :
    let pairs := List.ofFn (selected.insertNth chosen others)
    Prod.map id (RegistrationNativeKemSwitchReserved.project pairs) <$>
      (((simulateQ (RegistrationNativeKemSwitchSource.source setup.baseImpl setup.kem
        (RegistrationNativeKemParsedRouting.other setup checks wire route representation created credential)
        selected.val pairs chosen.1 real)
        (RegistrationNativeKemFullSource.program setup checks wire created.server.server.metadata.sender bounds mode work parsed)).run).run
          ((localState, PqxdhDynamicKemRouter.empty), none)) =
      (fun result => (some result.1, result.2)) <$>
        (simulateQ (RegistrationNativeKemSwitchReserved.source setup.baseImpl setup.kem
          (RegistrationNativeKemParsedRouting.other setup checks wire route representation created credential)
          selected.val pairs chosen.1 real)
          (RegistrationNativeKemFullSource.program setup checks wire created.server.server.metadata.sender bounds mode work parsed)).run
            ((localState, PqxdhLiveKemBirth.empty), none) := by
  dsimp only
  have native := RegistrationNativeKemSwitchTotal.program_source setup.baseImpl setup.kem
    (RegistrationNativeKemParsedRouting.other setup checks wire route representation created credential)
    selected.val (List.ofFn (selected.insertNth chosen others)) chosen.1 real
    (RegistrationNativeKemFullSource.program setup checks wire created.server.server.metadata.sender bounds mode work parsed) budget.create
    (RegistrationNativeKemFullSource.creates setup checks wire created.server.server.metadata.sender bounds mode work budget bounded parsed)
    (RegistrationNativeKemFullSource.no_reveal setup checks wire created.server.server.metadata.sender bounds mode work parsed)
    ((localState, PqxdhDynamicKemRouter.empty), none) rfl (by simp [PqxdhDynamicKemRouter.empty])
  exact native

/-- Actual complete native candidate execution has no outer stop; ordinary missing handles and KEM rejection remain inner optional replies. -/
theorem no_halt (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
    (bounds : FreshBounds) (mode : Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (budget : Budget) (bounded : RegistrationNativeInterface.Respects budget work) (parsed : Nat)
    (selected : Fin budget.capacity) (chosen : MlKem768PublicKey × KemSK) (others : Fin budget.create → MlKem768PublicKey × KemSK)
    (real : Bool) (localState : State n mlSource)
    (result : Option (Value × RegistrationNativeLedger.State) × RegistrationNativeKemSwitchSource.Switched (State n mlSource) KemSK)
    (supported : result ∈ support (((simulateQ (RegistrationNativeKemSwitchSource.source setup.baseImpl setup.kem
      (RegistrationNativeKemParsedRouting.other setup checks wire route representation created credential)
      selected.val (List.ofFn (selected.insertNth chosen others)) chosen.1 real)
      (RegistrationNativeKemFullSource.program setup checks wire created.server.server.metadata.sender bounds mode work parsed)).run).run
        ((localState, PqxdhDynamicKemRouter.empty), none))) : result.1.isSome = true := by
  have mapped : Prod.map id (RegistrationNativeKemSwitchReserved.project (List.ofFn (selected.insertNth chosen others))) result ∈ support
      (Prod.map id (RegistrationNativeKemSwitchReserved.project (List.ofFn (selected.insertNth chosen others))) <$>
        (((simulateQ (RegistrationNativeKemSwitchSource.source setup.baseImpl setup.kem
          (RegistrationNativeKemParsedRouting.other setup checks wire route representation created credential)
          selected.val (List.ofFn (selected.insertNth chosen others)) chosen.1 real)
          (RegistrationNativeKemFullSource.program setup checks wire created.server.server.metadata.sender bounds mode work parsed)).run).run
            ((localState, PqxdhDynamicKemRouter.empty), none))) := by
    rw [support_map]
    exact ⟨result, supported, rfl⟩
  rw [program_source setup checks wire route representation created credential bounds mode work budget bounded parsed selected chosen others real localState,
    support_map] at mapped
  obtain ⟨reply, _reached, same⟩ := mapped
  exact congrArg (fun value => value.1.isSome) same.symm

end BeaconcryptCore.Computational.RegistrationNativeKemFullSwitch
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemFullSwitch.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemFullSwitch.program_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemFullSwitch.no_halt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemFullSwitch.no_halt
