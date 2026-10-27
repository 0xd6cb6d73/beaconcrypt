import BeaconcryptCore.Computational.PqxdhKemCoordinateController
import BeaconcryptCore.Computational.PqxdhServerRelatedRootConsumer

/-!
The KEM-coordinate controller is consumed by the actual ordered Server raw preparation and Beacon InitSent owner preparation. These clients retain every source parser, point conversion, allocation, DH check and optional exit. Concrete interpretation exposes actual KEM replies while preserving the original private continuation and state; arbitrary replies are a strengthened authentication-only interface, not a root-secrecy game.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhKemControllerSource
open PqxdhKemCoordinateController
open PqxdhBeaconPhase2Preparation (Bytes Word32)
variable {Reader E I D X Response A Result : Type}

def serverLift : QueryImpl (PqxdhServerRootPreparation.Spec Reader E Word32)
    (OracleComp (NativeSpec Reader E I D X Response)) := fun query =>
  (NativeSpec Reader E I D X Response).query (.inl query)

def beaconLift : QueryImpl (PqxdhBeaconPhase2Preparation.Spec I D Handle X Response)
    (OracleComp (NativeSpec Reader E I D X Response)) := fun query =>
  (NativeSpec Reader E I D X Response).query (.inr query)

/-- The literal Server prefix supplies the actual ciphertext and KEM coordinate, while preserving every earlier signature, reservation and allocation effect. -/
def server (raw : Bytes) : OracleComp (ControlledSpec Reader E I D X Response)
    (Option (PqxdhServerRootPreparation.Inputs Reader E Word32)) :=
  simulateQ compiler (simulateQ serverLift (PqxdhServerRootPreparation.collect raw))

/-- The original owner preparation includes inactive rejection and terminal abort. Its assigned-ID getter and pin/core checks remain after decapsulation and all four DH calls. -/
noncomputable def beacon (raw : Bytes) (owner : PqxdhBeaconPhase2Preparation.State I D Handle) :
    OracleComp (ControlledSpec Reader E I D X Response)
      (Option (PqxdhBeaconPhase2Preparation.Prepared Response) × PqxdhBeaconPhase2Preparation.State I D Handle) :=
  simulateQ compiler (simulateQ beaconLift (PqxdhBeaconPhase2Preparation.owner raw owner))

set_option backward.isDefEq.respectTransparency false in
/-- Every original Server prefix result and complete interpreter poststate feed the same evaluated continuation after erasing only the added disclosure audit. -/
theorem server_source
    (native : QueryImpl (NativeSpec Reader E I D X Response) (StateT A ProbComp))
    (raw : Bytes) (state : State A)
    (next : Option (PqxdhServerRootPreparation.Inputs Reader E Word32) × A → ProbComp Result) :
    ((simulateQ (impl (concrete native) native) (server raw)).run state >>= fun result =>
      next (result.1, result.2.1)) =
        ((simulateQ (fun query => native (.inl query)) (PqxdhServerRootPreparation.collect raw)).run state.1 >>= next) := by
  rw [server, continuation_source]
  congr 1
  rw [← QueryImpl.simulateQ_compose]
  have same : native ∘ₛ serverLift = (fun query => native (.inl query)) := by
    funext query
    exact simulateQ_spec_query native (.inl query)
  rw [same]

set_option backward.isDefEq.respectTransparency false in
/-- The actual Beacon owner, including terminal abort and outer identity-ID update, reaches precisely the same full continuation under concrete controller interpretation. -/
theorem beacon_source
    (native : QueryImpl (NativeSpec Reader E I D X Response) (StateT A ProbComp))
    (raw : Bytes) (owner : PqxdhBeaconPhase2Preparation.State I D Handle) (state : State A)
    (next : (Option (PqxdhBeaconPhase2Preparation.Prepared Response) × PqxdhBeaconPhase2Preparation.State I D Handle) × A → ProbComp Result) :
    ((simulateQ (impl (concrete native) native) (beacon raw owner)).run state >>= fun result =>
      next (result.1, result.2.1)) =
        ((simulateQ (fun query => native (.inr query)) (PqxdhBeaconPhase2Preparation.owner raw owner)).run state.1 >>= next) := by
  rw [beacon, continuation_source]
  congr 1
  rw [← QueryImpl.simulateQ_compose]
  have same : native ∘ₛ beaconLift = (fun query => native (.inr query)) := by
    funext query
    exact simulateQ_spec_query native (.inr query)
  rw [same]

def nativeBoth
    (serverNative : QueryImpl (PqxdhServerRootPreparation.Spec Reader E Word32) (StateT A ProbComp))
    (beaconNative : QueryImpl (PqxdhBeaconPhase2Preparation.Spec I D Handle X Response) (StateT A ProbComp)) :
    QueryImpl (NativeSpec Reader E I D X Response) (StateT A ProbComp)
  | .inl query => serverNative query
  | .inr query => beaconNative query

/-- The actual native root/clearing/consumption continuation follows the controller-observed raw prefix. The extra audit is erased only at the stated observation boundary. -/
noncomputable def serverRoot
    (native : QueryImpl (NativeSpec Reader E I D X Response)
      (StateT (PqxdhServerRelatedRootConsumer.State A) ProbComp))
    (kdf : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (hmac : PqxdhSecretInputKdf.HmacSha512)
    (aux : QueryImpl PqxdhServerRelatedRootConsumer.AuxSpec (StateT A ProbComp))
    (control : pqxdh.ServerState) (binding : pqxdh.ServerBinding) (raw : Bytes)
    (initial : State (PqxdhServerRelatedRootConsumer.State A)) :
    ProbComp (RustM (Option PqxdhServerRelatedRootConsumer.Returned) × PqxdhServerRelatedRootConsumer.State A) :=
  ((simulateQ (impl (concrete native) native) (server raw)).run initial) >>= fun result =>
    match result.1 with
    | none => pure (ok none, result.2.1)
    | some input => (PqxdhServerRelatedRootConsumer.source kdf hmac aux control binding input).run result.2.1

set_option backward.isDefEq.respectTransparency false in
/-- The concrete controller consumes the existing complete source root helper, including core rejection, erasure and registration consumption, with the same full family history/cache and local poststate. -/
theorem server_root_source
    (kdf : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (hmac : PqxdhSecretInputKdf.HmacSha512)
    (joint : PqxdhJointIdentity.Primitives) (seed : PqxdhJointIdentity.IdentitySeed)
    (preImpl : QueryImpl (PqxdhServerRootPreparation.Spec Reader E Unit)
      (StateT (PqxdhServerRelatedRootConsumer.State A) ProbComp))
    (visit : Word32 → StateT (PqxdhServerRelatedRootConsumer.State A) ProbComp Unit)
    (beaconNative : QueryImpl (PqxdhBeaconPhase2Preparation.Spec I D Handle X Response)
      (StateT (PqxdhServerRelatedRootConsumer.State A) ProbComp))
    (aux : QueryImpl PqxdhServerRelatedRootConsumer.AuxSpec (StateT A ProbComp))
    (control : pqxdh.ServerState) (binding : pqxdh.ServerBinding) (raw : Bytes)
    (initial : State (PqxdhServerRelatedRootConsumer.State A)) :
    serverRoot (nativeBoth (PqxdhServerStaticDhSource.nativeImpl joint seed preImpl visit) beaconNative)
      kdf hmac aux control binding raw initial =
        (PqxdhServerRelatedRootConsumer.nativeStage kdf hmac joint seed preImpl visit aux control binding raw).run initial.1 := by
  have complete := server_source (nativeBoth (PqxdhServerStaticDhSource.nativeImpl joint seed preImpl visit) beaconNative)
    raw initial (fun result : Option (PqxdhServerRootPreparation.Inputs Reader E Word32) × PqxdhServerRelatedRootConsumer.State A => match result.1 with
    | none => pure (ok none, result.2)
    | some input => (PqxdhServerRelatedRootConsumer.source kdf hmac aux control binding input).run result.2)
  refine complete.trans ?_
  simp only [PqxdhServerRelatedRootConsumer.nativeStage, StateT.run_bind, nativeBoth]
  apply bind_congr
  rintro ⟨none | input, state⟩ <;> rfl

end BeaconcryptCore.Computational.PqxdhKemControllerSource

/-- info: 'BeaconcryptCore.Computational.PqxdhKemControllerSource.server_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhKemControllerSource.server_source

/-- info: 'BeaconcryptCore.Computational.PqxdhKemControllerSource.beacon_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhKemControllerSource.beacon_source

/-- info: 'BeaconcryptCore.Computational.PqxdhKemControllerSource.server_root_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhKemControllerSource.server_root_source
