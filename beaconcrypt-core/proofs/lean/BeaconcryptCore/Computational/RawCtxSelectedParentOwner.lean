import BeaconcryptCore.Computational.RawCtxSelectedParentCalls
import BeaconcryptCore.Computational.RawCtxGenericOwnerMap
import BeaconcryptCore.Computational.RawCtxSelectedPublicTrace

/-!
The same retained private KDF table is interpreted through complete original owner and public schedules. Actual public HKDF evaluation remains the real fixed source on both sides, with the same public coins and shared commitment cache. Every owner field and optional reply is retained; only the private chain representation changes. An arbitrary prior private table describes an intermediate operational game, not a claim that independently replaced values equal the public function.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedParentOwner
open RawCtxSelectedParentCalls RawCtxSelectedParentEntry RawCtxSelectedParentTable RawCtxSelectedChain
open PqxdhJointKdfGame PqxdhSecretInputKdf

abbrev Owner (Chain Metadata : Type) := RawCtxChainOwner.State (Kernel Chain) Metadata

def mapOwner {Metadata : Type} (target : RootOutput) : Owner Slot Metadata → Owner RatchetChain Metadata :=
  RawCtxGenericOwnerMap.mapOwner (nativeKernel target)

noncomputable def publicImpl {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) :=
  RawCtxProtocolBackend.backend (Auxiliary := Auxiliary) source writer ∘ₛ RawCtxServerServices.publicLift

noncomputable def nativeOwner {Metadata Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (target : RootOutput) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder) :=
  RawCtxGenericOwnerMap.publicOwner (Metadata := Metadata)
    (nativeCalls (Auxiliary := Auxiliary) source writer prior entry target) (publicImpl source writer) sender decode

noncomputable def labelOwner {Metadata Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (response : RatchetKdfResponse) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder) :=
  RawCtxGenericOwnerMap.publicOwner (Metadata := Metadata)
    (labelCalls (Auxiliary := Auxiliary) source writer prior entry response) (publicImpl source writer) sender decode

/-- Each original record/public operation preserves every owner field and the full actual shared primitive computation. -/
theorem step_map {Metadata Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (target : RootOutput) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (query : RawCtxSelectedPublicTrace.SourceSpec.Domain) (state : Owner Slot Metadata) :
    (nativeOwner (Auxiliary := Auxiliary) source writer prior entry target sender decode query).run (mapOwner target state) =
      Prod.map id (mapOwner target) <$>
        (labelOwner source writer prior entry (childResponse prior entry target) sender decode query).run state := by
  have law := RawCtxGenericOwnerMap.public_schedule_map (nativeKernel target)
    (labelCalls (Auxiliary := Auxiliary) source writer prior entry (childResponse prior entry target))
    (nativeCalls source writer prior entry target) (receive_map source writer prior entry target)
    (send_map source writer prior entry target) (publicImpl source writer) sender decode
    (RawCtxSelectedPublicTrace.SourceSpec.query query) state
  simpa only [simulateQ_spec_query, nativeOwner, labelOwner, mapOwner] using law

/-- The complete adaptive owner/public continuation retains original responses and full state through the concrete private interpretation. -/
theorem schedule_map {Metadata Auxiliary Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (target : RootOutput) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp RawCtxSelectedPublicTrace.SourceSpec Result) (state : Owner Slot Metadata) :
    (simulateQ (nativeOwner (Auxiliary := Auxiliary) source writer prior entry target sender decode) client).run (mapOwner target state) =
      Prod.map id (mapOwner target) <$>
        (simulateQ (labelOwner source writer prior entry (childResponse prior entry target) sender decode) client).run state :=
  RawCtxGenericOwnerMap.public_schedule_map (nativeKernel target) _ _
    (receive_map source writer prior entry target) (send_map source writer prior entry target)
    (publicImpl source writer) sender decode client state

end BeaconcryptCore.Computational.RawCtxSelectedParentOwner

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentOwner.step_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentOwner.step_map

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentOwner.schedule_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentOwner.schedule_map
