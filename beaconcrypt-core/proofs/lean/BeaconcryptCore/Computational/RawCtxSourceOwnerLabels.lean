import BeaconcryptCore.Computational.RawCtxOwnerLabels
import BeaconcryptCore.Computational.RawCtxSourceFamilyPath

/-!
The literal selective-table source family carries privately attached owner labels through its actual native callbacks. The complete source equality retains every role, raw attempt, reveal history and shared primitive state. An attached label is an actual route index, not a proof of a unique cryptographic installation at that route. Registration replacement and installation origins remain outside this no-install LIVE suffix.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSourceOwnerLabels
open RawCtxOwnerLabels PqxdhJointKdfGame
open RawCtxProtocolReveals (Owner)
variable {A M P I D K Result : Type} {S B : Nat}

abbrev Kernel (S B : Nat) := Labelled RawCtxSourceFamilyPath.Kernel S B
abbrev LiveState (M P I D K : Type) (S B : Nat) := RawCtxGenericFamilyLive.State (Kernel S B) M P I D K S B

noncomputable def impl (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder) :
    QueryImpl (RawCtxProtocolReveals.SourceSpec S B)
      (StateT (LiveState M P I D K S B) (StateT (RawCtxSourceFamilyPath.State A) ProbComp)) :=
  RawCtxGenericFamilyLive.impl
    (calls (fun _ => RawCtxGenericNativeCalls.calls (RawCtxSourceSendPath.native source writer stage)))
    (RawCtxPendingSelectiveFamily.backend source writer stage ∘ₛ RawCtxServerServices.publicLift)
    (reader (RawCtxGenericFamilyRead.nativeReader ConcreteRatchetKernel.mk)) sender route decode

def initial (entry : RawCtxProtocolReveals.State M P I D K S B) : LiveState M P I D K S B :=
  (attach (RawCtxGenericRoleFamily.fromRoles ConcreteRatchetKernel.refined entry.1), entry.2)

def native (entry : LiveState M P I D K S B) : RawCtxProtocolReveals.State M P I D K S B :=
  RawCtxGenericFamilyLive.nativeState (ConcreteRatchetKernel.mk ∘ Prod.snd) entry

/-- The whole literal original family execution is the erasure of its route-labelled source execution, with the same complete primitive state and every optional reply. -/
theorem source (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (entry : RawCtxProtocolReveals.State M P I D K S B) (state : RawCtxSourceFamilyPath.State A) :
    RawCtxSelectiveChainGame.family source writer stage S B sender route decode client entry state.1 state.2 =
      Prod.map (Prod.map id native) id <$>
        (((simulateQ (impl source writer stage sender route decode) client).run (initial entry)).run state) := by
  rw [RawCtxPendingSelectiveFamily.source_program]
  simp only [RawCtxPendingSelectiveFamily.handler, RawCtxPendingSelectiveFamily.program,
    RawCtxPendingFamilyNative.program_interpretation]
  rw [RawCtxOwnerLabels.schedule_source]
  simp only [StateT.run_map, Functor.map_map]
  congr 1
  funext result
  simp only [Prod.map_def, id_eq, RawCtxGenericFamilyLive.nativeState,
    RawCtxGenericFamilyLive.mapState, RawCtxGenericRoleFamily.compose, native]

/-- The original source's complete supported result has a route-labelled realization whose every reached owner lookup carries precisely that route. -/
theorem source_labels (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (entry : RawCtxProtocolReveals.State M P I D K S B) (state : RawCtxSourceFamilyPath.State A)
    (result : (Result × RawCtxProtocolReveals.State M P I D K S B) × RawCtxSourceFamilyPath.State A)
    (supported : result ∈ support (RawCtxSelectiveChainGame.family source writer stage S B
      sender route decode client entry state.1 state.2)) :
    ∃ labelled, labelled ∈ support
      (((simulateQ (impl source writer stage sender route decode) client).run (initial entry)).run state) ∧
      Prod.map (Prod.map id native) id labelled = result ∧
      ∀ owner kernel, RawCtxGenericRoleFamily.selectedKernel owner labelled.1.2.1 = some kernel → kernel.1 = owner := by
  rw [RawCtxSourceOwnerLabels.source, support_map] at supported
  obtain ⟨labelled, reached, equal⟩ := supported
  refine ⟨labelled, reached, equal, ?_⟩
  intro owner kernel present
  exact RawCtxOwnerLabels.schedule_owner _ _ _ sender route decode client
    (RawCtxGenericRoleFamily.fromRoles ConcreteRatchetKernel.refined entry.1) entry.2 state labelled reached owner kernel present

end BeaconcryptCore.Computational.RawCtxSourceOwnerLabels

/-- info: 'BeaconcryptCore.Computational.RawCtxSourceOwnerLabels.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceOwnerLabels.source

/-- info: 'BeaconcryptCore.Computational.RawCtxSourceOwnerLabels.source_labels' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceOwnerLabels.source_labels
