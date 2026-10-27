import BeaconcryptCore.Computational.RawCtxFamilyStateInvariant
import BeaconcryptCore.Computational.RawCtxSourcePathCalls

/-!
The actual selective-table family interpreter preserves the selected installed sender's complete executed cache path from its initial chain. Every callback contract is derived from the source receive/send and real public/read interpreters. The initializer supplies the initial path; the original no-install LIVE schedule retains it across other owners, rejected operations and complete history updates. This is source publication provenance, not a secrecy or cost transfer.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSourceFamilyPath
open RawCtxCursorLineage PqxdhJointKdfGame PqxdhSecretInputKdf
variable {A M P I D K Result : Type} {S B : Nat}

abbrev Kernel := RawCtxPendingOwnerQueries.Kernel RatchetChain
abbrev State (A : Type) := RawCtxPendingSelectiveFamily.State A
abbrev Roles (M P I D K : Type) (S B : Nat) := RawCtxGenericRoleFamily.Roles Kernel M P I D K S B
abbrev LiveState (M P I D K : Type) (S B : Nat) := RawCtxGenericFamilyLive.State Kernel M P I D K S B

def Good (root : RootOutput) (selected : RawCtxProtocolReveals.Owner S B)
    (roles : Roles M P I D K S B) (state : State A) : Prop :=
  ∀ kernel, RawCtxGenericRoleFamily.selectedKernel selected roles = some kernel →
    RawCtxSourceSendPath.Path root ⟨kernel⟩ state.2.1

private theorem actual_rules (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (stage : Nat) (root : RootOutput) :
    RawCtxFamilyStateInvariant.Rules
      (RawCtxGenericNativeCalls.calls (RawCtxSourceSendPath.native (A := A) source writer stage))
      (fun before after => Extends before.2.1 after.2.1)
      (fun kernel state => RawCtxSourceSendPath.Path root ⟨kernel⟩ state.2.1) where
  refl := fun _ _ _ known => known
  trans := fun _ _ _ first later _ _ known => later _ _ (first _ _ known)
  mono := fun kernel _ _ extension valid => RawCtxSourceSendPath.path_extends root ⟨kernel⟩ _ _ valid extension
  receive := fun entry target context state result supported =>
    let checked := RawCtxSourcePathCalls.receive_call source writer stage entry target context state result supported
    ⟨checked.1, checked.2 root⟩
  send := fun entry context state result supported =>
    let checked := RawCtxSourcePathCalls.send_call source writer stage entry context state result supported
    ⟨checked.1, checked.2 root⟩

private theorem reader_extends
    (query : (RawCtxGenericFamilyRead.ReadSpec Kernel S B).Domain) (state : State A)
    (result : (RawCtxGenericFamilyRead.ReadSpec Kernel S B).Range query × State A)
    (supported : result ∈ support ((RawCtxGenericFamilyRead.nativeReader (m := StateT (State A) ProbComp) ConcreteRatchetKernel.mk query).run state)) :
    Extends state.2.1 result.2.2.1 := by
  simp only [RawCtxGenericFamilyRead.nativeReader, StateT.run_pure, mem_support_pure_iff] at supported
  subst result
  exact fun _ _ known => known

noncomputable def impl (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder) :
    QueryImpl (RawCtxProtocolReveals.SourceSpec S B) (StateT (LiveState M P I D K S B) (StateT (State A) ProbComp)) :=
  RawCtxGenericFamilyLive.impl
    (RawCtxGenericNativeCalls.calls (RawCtxSourceSendPath.native source writer stage))
    (RawCtxPendingSelectiveFamily.backend source writer stage ∘ₛ RawCtxServerServices.publicLift)
    (RawCtxGenericFamilyRead.nativeReader ConcreteRatchetKernel.mk) sender route decode

/-- Every actual source request preserves the selected sender path, deriving all callback contracts from the concrete interpreter. -/
theorem step (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (root : RootOutput) (selected : RawCtxProtocolReveals.Owner S B)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : (RawCtxProtocolReveals.SourceSpec S B).Domain) (entry : LiveState M P I D K S B)
    (state : State A) (valid : Good root selected entry.1 state)
    (result : ((RawCtxProtocolReveals.SourceSpec S B).Range query × LiveState M P I D K S B) × State A)
    (supported : result ∈ support (((impl source writer stage sender route decode query).run entry).run state)) :
    Extends state.2.1 result.2.2.1 ∧ Good root selected result.1.2.1 result.2 := by
  have checked := RawCtxFamilyStateInvariant.live _ _ _ (actual_rules source writer stage root)
    _ (RawCtxSourcePathCalls.public_extends source writer stage) _ reader_extends sender route decode
    query entry state result supported selected
  exact ⟨checked.1, checked.2 valid⟩

/-- The same complete adaptive actual source schedule retains all original cache bindings and the selected sender's path. -/
theorem schedule (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (root : RootOutput) (selected : RawCtxProtocolReveals.Owner S B)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result) (entry : LiveState M P I D K S B)
    (state : State A) (valid : Good root selected entry.1 state)
    (result : (Result × LiveState M P I D K S B) × State A)
    (supported : result ∈ support (((simulateQ (impl source writer stage sender route decode) client).run entry).run state)) :
    Extends state.2.1 result.2.2.1 ∧ Good root selected result.1.2.1 result.2 := by
  have checked := RawCtxFamilyStateInvariant.schedule _ _ _ (actual_rules source writer stage root)
    _ (RawCtxSourcePathCalls.public_extends source writer stage) _ reader_extends sender route decode
    client entry state result supported selected
  exact ⟨checked.1, checked.2 valid⟩

def NativeGood (root : RootOutput) (selected : RawCtxProtocolReveals.Owner S B)
    (roles : RawCtxProtocolReveals.Roles M P I D K S B) (state : State A) : Prop :=
  ∀ kernel, RawCtxProtocolReveals.selectedKernel selected roles = some kernel →
    RawCtxSourceSendPath.Path root kernel state.2.1

private theorem native_good (root : RootOutput) (selected : RawCtxProtocolReveals.Owner S B)
    (roles : Roles M P I D K S B) (state : State A) :
    NativeGood root selected (RawCtxGenericRoleFamily.nativeRoles ConcreteRatchetKernel.mk roles) state ↔
      Good root selected roles state := by
  constructor
  · intro h kernel present
    exact h ⟨kernel⟩ (by simp only [RawCtxGenericRoleFamily.native_selected, present, Option.map_some])
  · intro h kernel present
    rw [RawCtxGenericRoleFamily.native_selected] at present
    obtain ⟨original, found, rfl⟩ := Option.map_eq_some_iff.mp present
    exact h original found

/-- The original native source family preserves its actual initialized sender path in the same final private cache, without any supplied callback invariant. -/
theorem source (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (root : RootOutput) (selected : RawCtxProtocolReveals.Owner S B)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (entry : RawCtxProtocolReveals.State M P I D K S B) (state : State A)
    (valid : NativeGood root selected entry.1 state)
    (result : (Result × RawCtxProtocolReveals.State M P I D K S B) × State A)
    (supported : result ∈ support (RawCtxSelectiveChainGame.family source writer stage S B
      sender route decode client entry state.1 state.2)) :
    Extends state.2.1 result.2.2.1 ∧ NativeGood root selected result.1.2.1 result.2 := by
  rw [RawCtxPendingSelectiveFamily.source_program, support_map] at supported
  obtain ⟨original, reached, rfl⟩ := supported
  have initial : Good root selected (RawCtxGenericRoleFamily.fromRoles ConcreteRatchetKernel.refined entry.1) state := by
    apply (native_good root selected _ state).mp
    simpa only [RawCtxGenericRoleFamily.roundtrip ConcreteRatchetKernel.refined ConcreteRatchetKernel.mk (fun _ => rfl)] using valid
  have reached' : original ∈ support (((simulateQ (impl source writer stage sender route decode) client).run
      (RawCtxGenericRoleFamily.fromRoles ConcreteRatchetKernel.refined entry.1, entry.2)).run state) := by
    simpa only [RawCtxPendingSelectiveFamily.handler, RawCtxPendingSelectiveFamily.program,
      RawCtxPendingFamilyNative.program_interpretation, impl, RawCtxSourceSendPath.native] using reached
  have preserved := schedule source writer stage root selected sender route decode client
    (RawCtxGenericRoleFamily.fromRoles ConcreteRatchetKernel.refined entry.1, entry.2) state initial original reached'
  exact ⟨preserved.1, (native_good root selected _ _).mpr preserved.2⟩

end BeaconcryptCore.Computational.RawCtxSourceFamilyPath

/-- info: 'BeaconcryptCore.Computational.RawCtxSourceFamilyPath.step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceFamilyPath.step

/-- info: 'BeaconcryptCore.Computational.RawCtxSourceFamilyPath.schedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceFamilyPath.schedule

/-- info: 'BeaconcryptCore.Computational.RawCtxSourceFamilyPath.source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceFamilyPath.source
