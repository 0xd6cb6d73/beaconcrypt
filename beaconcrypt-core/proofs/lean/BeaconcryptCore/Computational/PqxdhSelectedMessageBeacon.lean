import BeaconcryptCore.Computational.RawCtxSelectedMessageFamily
import BeaconcryptCore.Computational.PqxdhInitialNativeInitializer
import BeaconcryptCore.Computational.RawCtxGenericNativeCalls

/-!
The actual attempted Beacon finish uses opaque selected message material while retaining its complete preparation, response getter, original initializer and terminal source phase. The private selected KDF changes only message-material representation; every initializer returns its actual known kernel. The mathematical source interpreter supplies the secret only to the original cryptographic backend, never to the compiled owner.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhSelectedMessageBeacon
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame PqxdhInitialBeaconAmbient
open RawCtxSelectedMessageKey RawCtxSelectedMessageReveals RawCtxSelectedMessageDriver
open RawCtxSelectedMessageKdf
open RawCtxSelectedParentTable RawCtxSelectedParentEntry
variable {I D K X Response Shared A N C : Type}

abbrev NativeKernel := RawCtxPendingOwnerQueries.Kernel RatchetChain

def interpretKernel (key : RootOutput) (kernel : RawCtxSelectedMessageReveals.Kernel) : NativeKernel :=
  (nativeKernel key kernel).refined

def knownKernel (kernel : NativeKernel) : RawCtxSelectedMessageReveals.Kernel :=
  RawCtxSelectedMessageRevealInitialization.fromKernel ⟨kernel⟩

/-- Original initializer kernels keep every directional chain, cached material and control field, including arbitrary byte aliases. -/
theorem known_roundtrip (key : RootOutput) (kernel : NativeKernel) :
    interpretKernel key (knownKernel kernel) = kernel :=
  congrArg ConcreteRatchetKernel.refined (RawCtxSelectedMessageRevealInitialization.kernel_roundtrip key ⟨kernel⟩)

variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)

noncomputable def nativeCalls : RawCtxChainOwner.Calls NativeKernel (Base A) :=
  RawCtxGenericNativeCalls.calls (RawCtxFunctionalFamily.native source writer (privateTable prior parent target (response key nonce next)))

noncomputable def materialCalls : RawCtxChainOwner.Calls RawCtxSelectedMessageReveals.Kernel (Base A) :=
  RawCtxSelectedMessageFamily.calls
    (receiveServices source writer prior parent key target nonce next)
    (sendServices source writer prior parent key target nonce next) parent target nonce next

/-- The complete actual native receive and its shared-state effects are preserved by the concrete selected-material driver. -/
theorem receive_map (kernel : RawCtxSelectedMessageReveals.Kernel) (sequence : Std.U64) (context : RawCtxWholeOwner.OpenContext) :
    (nativeCalls (A := A) source writer prior parent key target nonce next).receive (interpretKernel key kernel) sequence context =
      Prod.map (interpretKernel key) id <$>
        (materialCalls source writer prior parent key target nonce next).receive kernel sequence context := by
  have actual := (RawCtxGenericNativeCalls.receive_realized
    (RawCtxFunctionalFamily.native (A := A) source writer (privateTable prior parent target (response key nonce next)))
      (interpretKernel key kernel) sequence context).symm.trans
        (RawCtxSelectedMessageDriver.receive_source source writer prior parent key target nonce next kernel sequence context)
  have projected := congrArg (fun work => Prod.map ConcreteRatchetKernel.refined id <$> work) actual
  simp only [Functor.map_map, Prod.map_def, id_eq, Prod.mk.eta, interpretKernel] at projected
  exact (id_map _).symm.trans projected

noncomputable def knownInitial
    (initial : PqxdhBeaconPhase2Shared.Secrets Shared → Ambient A N C (Option NativeKernel))
    (secrets : PqxdhBeaconPhase2Shared.Secrets Shared) :
    Ambient A N C (Option RawCtxSelectedMessageReveals.Kernel) := Option.map knownKernel <$> initial secrets

/-- Every actual attempted finish retains the original preparation, optional response, repeated initializer, first raw receive, terminal phase and full ambient effects. -/
theorem owner_source
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (Ambient A N C))
    (application : Response → Ambient A N C (Option Pqxdh.Bytes))
    (initial : PqxdhBeaconPhase2Shared.Secrets Shared → Ambient A N C (Option NativeKernel))
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (state : RawCtxGenericRoleStorage.BeaconState RawCtxSelectedMessageReveals.Kernel I D K) :
    PqxdhInitialGenericBeacon.owner pre
      (liftCalls (nativeCalls source writer prior parent key target nonce next)) application initial decode raw
      (RawCtxGenericRoleStorage.mapBeacon (interpretKernel key) state) =
    Prod.map id (RawCtxGenericRoleStorage.mapBeacon (interpretKernel key)) <$>
      PqxdhInitialGenericBeacon.owner pre
        (liftCalls (materialCalls source writer prior parent key target nonce next)) application
        (knownInitial initial) decode raw state := by
  apply PqxdhInitialGenericBeacon.owner_map
  · intro kernel sequence context
    simp only [liftCalls, receive_map, lift_map]
  · intro secrets
    simp only [knownInitial, Functor.map_map, Option.map_map, Function.comp_def, known_roundtrip]
    change initial secrets = Option.map id <$> initial secrets
    simp only [Option.map_id, id_map]

end BeaconcryptCore.Computational.PqxdhSelectedMessageBeacon

/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedMessageBeacon.known_roundtrip' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedMessageBeacon.known_roundtrip

/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedMessageBeacon.receive_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedMessageBeacon.receive_map

/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedMessageBeacon.owner_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedMessageBeacon.owner_source
