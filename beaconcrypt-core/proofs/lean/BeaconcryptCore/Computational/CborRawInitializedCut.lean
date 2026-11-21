-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawCutPrefix
import BeaconcryptCore.Computational.CborRawMiddleStart
import BeaconcryptCore.Computational.CborRawCompileCaps

/-! The initialized raw compiler reaches item 2's actual selected-accept cut through one annotated source prefix. Fresh reconstruction and allocation control follow from the real Server constructor. The stopped KEM router uses that same prefix and preserves every original accept ordinal, failure reply, continuation, private pool and runtime state. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.CborRawInitializedCut
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Spec)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhDeploymentIdealCut (CutCE scanCE sourceInit opaqueRest)
open PqxdhRegistrationJointAcceptCut (scan)
open PqxdhRegistrationJointRevealCosts (SourceKind sourceKind)
open PqxdhDeploymentIdealPoolSource (PoolOwned PoolPrefix routerOf)
open PqxdhRegistrationJointGeneratedFinish (encodeState)
variable {ι KemSK Reader Response A Y : Type} {baseSpec : OracleSpec ι}

section Prefix
variable (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks) {count : Nat}
    (target : Target count) (parameters : Params KemSK count)
    (created : PqxdhLiveServerConstruction.Created Unit)

noncomputable def compilerCut : CutCE Y × CborAdmissionCompiler.Local →
    PqxdhRegistrationJointAcceptCut.Cut KemSK (Y × CborAdmissionCompiler.Local) :=
  CborRawCompileCut.cut (CborRawCompile.compileImpl setup wire parse) CborRawCompileCut.logAccept

noncomputable def commonPrefix (pool : PqxdhRegistrationJointPreparation.Pool KemSK)
    (work : OracleComp Spec Y) :
    ProbComp ((CutCE Y × CborAdmissionCompiler.Local) × PqxdhRegistrationJointSchedule.State KemSK) :=
  (simulateQ (CborRawCutPrefix.source setup wire parse checks created.seed
      created.server.server.metadata.identityIndex (parameters.pool target))
    (CborRawCompile.compile setup wire parse (scanCE work target.accept))).run (sourceInit created pool)

/-- The raw prefix's complete invariant starts at the actual generated or imported constructor outcome, without an initial-state simulation assumption. -/
theorem initial_good (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (before after : PqxdhRegistrationJointServerPrefix.State KemSK A)
    (born : (some created, after) ∈ support
      ((PqxdhRegistrationJointServerBirth.source setup.joint ensureInit setup.serverKeyId supplied).run before)) :
    CborAdmissionCompiler.Good setup (CborRawCompile.sourceCodec wire parse)
      (CborAdmissionCompiler.Local.empty setup.serverKeyId) (PqxdhRegistrationSchedule.initial created) := by
  have native := (PqxdhRegistrationJointServerBirth.source_constructor setup.joint ensureInit setup.serverKeyId
    supplied before after created born).2
  obtain ⟨seed, shape, _⟩ := PqxdhLiveServerConstruction.construct_origin setup.joint ensureInit
    before.1.1.seeds.length setup.serverKeyId supplied before.2 after.2 created native
  exact CborAdmissionCompileStep.good_initial setup (CborRawCompile.sourceCodec wire parse)
    (PqxdhRegistrationSchedule.initial created) (by rw [shape]; rfl) (by rw [shape]; rfl)
    (by intro keyId; rw [shape]; rfl) rfl (fun _ => rfl)

/-- Every reached common-prefix outcome carries the full raw reconstruction and allocation invariant. -/
theorem cut_good
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (CborRawCompile.sourceCodec wire parse))
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack (CborRawCompile.sourceCodec wire parse))
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (before after : PqxdhRegistrationJointServerPrefix.State KemSK A)
    (born : (some created, after) ∈ support
      ((PqxdhRegistrationJointServerBirth.source setup.joint ensureInit setup.serverKeyId supplied).run before))
    (work : OracleComp Spec Y)
    (value : (CutCE Y × CborAdmissionCompiler.Local) × PqxdhRegistrationJointSchedule.State KemSK)
    (supported : value ∈ support (commonPrefix setup wire parse checks target parameters created after.1 work)) :
    CborAdmissionCompiler.Good setup (CborRawCompile.sourceCodec wire parse) value.1.2
      (PqxdhRegistrationJointSchedule.source value.2) :=
  CborRawCutPrefix.good_program setup wire parse checks created.seed created.server.server.metadata.identityIndex
    (parameters.pool target) phase1 phase2 (scanCE work target.accept)
    (CborAdmissionCompiler.Local.empty setup.serverKeyId) (sourceInit created after.1)
    (initial_good setup wire parse created ensureInit supplied before after born) value supported

/-- The native raw pool prefix is the exact complete-state image of the same annotated prefix used by the KEM router. -/
theorem native_prefix (lengths : RawCtxSourcePublication.BodyLength setup.source.crypto)
    (parser : CborRawCanonicalBuild.CanonicalReadBack (CborTaggedSimulation.boundaryWire wire parse))
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (CborRawCompile.sourceCodec wire parse))
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack (CborRawCompile.sourceCodec wire parse))
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (before after : PqxdhRegistrationJointServerPrefix.State KemSK A)
    (born : (some created, after) ∈ support
      ((PqxdhRegistrationJointServerBirth.source setup.joint ensureInit setup.serverKeyId supplied).run before))
    (work : OracleComp Spec Y) :
    (fun value => (value.1.1, CborAdmissionCompiler.merge value.1.2
      (PqxdhRegistrationJointSchedule.source value.2))) <$>
        commonPrefix setup wire parse checks target parameters created after.1 work =
      (simulateQ (CborRawPoolCompiler.native setup wire parse checks created.seed (parameters.pool target))
        (scanCE work target.accept)).run (PqxdhDeploymentNative.initial created) := by
  have simulated := CborRawCutPrefix.native_program setup wire parse checks created.seed
    created.server.server.metadata.identityIndex (parameters.pool target) lengths parser phase1 phase2
    (scanCE work target.accept) (CborAdmissionCompiler.Local.empty setup.serverKeyId) (sourceInit created after.1)
    (initial_good setup wire parse created ensureInit supplied before after born)
  have erased : PqxdhRegistrationJointSchedule.source (sourceInit created after.1) =
      PqxdhRegistrationSchedule.initial created := rfl
  simpa only [commonPrefix, CborRawCompile.compile, CborAdmissionCompiler.merge,
    CborAdmissionCompiler.Local.empty, PqxdhDeploymentCompile.merge_empty, erased,
    PqxdhDeploymentNative.initial] using simulated

/-- The selected-first router's source scan is the same common prefix, including complete failures and current private pools. -/
theorem stopped_prefix (pool : PqxdhRegistrationJointPreparation.Pool KemSK)
    (empty : pool.2 = PqxdhLiveKemBirth.empty)
    (slot : pool.1.seeds[created.server.server.metadata.identityIndex]? = some created.seed)
    (work : OracleComp Spec Y) (budget : SourceKind → Nat)
    (certified : ∀ kind, (scan (CborRawCompile.compile setup wire parse work) target.accept).IsQueryBoundP
      (fun query => sourceKind (KemSK := KemSK) query = kind) (budget kind))
    (unreadIdentity : budget (.inr 0) = 0) (unreadKem : budget (.inr 1) = 0)
    (room : budget (.inl 1) ≤ (parameters.pool target).length) :
    ((simulateQ (PqxdhDynamicKemJointRouter.stopped setup.baseImpl setup.joint setup.kem target.kem.val
        (parameters.pool target))
      (simulateQ (PqxdhRegistrationJointKemEncapsulation.actual setup)
        (PqxdhRegistrationJointKemEncapsulation.commands setup (CborRawCompile.sourceCodec wire parse) checks
          created.server.server.metadata.identityIndex (setup.joint.publicKeys created.seed)
          (scan (CborRawCompile.compile setup wire parse work) target.accept) ([], fun _ => none)
          (PqxdhRegistrationSchedule.initial created).shared))).run).run
          (pool.1, PqxdhDynamicKemRouter.empty) =
      (fun value => (some (((compilerCut setup wire parse value.1, ((encodeState setup value.2).owners, (encodeState setup value.2).inits)),
        value.2.shared)), (value.2.pool.1, routerOf value.2.pool.2))) <$>
        commonPrefix setup wire parse checks target parameters created pool work := by
  have owned : PoolOwned created.seed created.server.server.metadata.identityIndex (sourceInit created pool) :=
    ⟨⟨PqxdhRegistrationJointSchedule.initial_owned pool _, slot⟩,
      by simp [sourceInit, PqxdhRegistrationJointSchedule.initial, empty, PqxdhLiveKemBirth.empty]⟩
  have prefixed : PoolPrefix (parameters.pool target) (sourceInit created pool).pool.2 := by
    simp [sourceInit, PqxdhRegistrationJointSchedule.initial, empty, PqxdhLiveKemBirth.empty, PoolPrefix]
  have routerEmpty : PqxdhDynamicKemRouter.empty = routerOf (sourceInit created pool).pool.2 := by
    simp only [sourceInit, PqxdhRegistrationJointSchedule.initial, empty]
    rfl
  rw [PqxdhRegistrationJointKemEncapsulation.commands_actual, routerEmpty]
  have stopped := CborRawCutPrefix.stopped_scan setup wire parse checks created.seed
    created.server.server.metadata.identityIndex (parameters.pool target) target.kem.val work target.accept
    (CborAdmissionCompiler.Local.empty setup.serverKeyId) (sourceInit created pool) owned prefixed budget
    certified unreadIdentity unreadKem
    (by simpa [sourceInit, PqxdhRegistrationJointSchedule.initial, empty, PqxdhLiveKemBirth.empty] using room)
  simpa only [commonPrefix, compilerCut, CborRawCompile.compile, sourceInit,
    PqxdhRegistrationJointSchedule.initial, encodeState, List.map_nil] using stopped

end Prefix

section Initialized
variable (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks) {count : Nat}
    (target : Target count) (parameters : Params KemSK count)

/-- The complete initialized opaque prephase factors through the derived raw common prefix. Initialization, rejection, raw accept ordinals, both private pools and the caller runtime are retained exactly. -/
theorem item2_prefix (ensureInit : StateT A ProbComp Bool)
    (decision : Y × CborAdmissionCompiler.Local → Bool) (work : OracleComp Spec Y) (runtime : A)
    (budget : SourceKind → Nat)
    (certified : ∀ kind, (scan (CborRawCompile.compile setup wire parse work) target.accept).IsQueryBoundP
      (fun query => sourceKind (KemSK := KemSK) query = kind) (budget kind))
    (unreadIdentity : budget (.inr 0) = 0) (unreadKem : budget (.inr 1) = 0)
    (room : budget (.inl 1) ≤ (parameters.pool target).length) :
    PqxdhDeploymentIdealParams.preOpaquePool (Reader := Reader) setup (CborRawCompile.sourceCodec wire parse)
      checks ensureInit none decision (CborRawCompile.compile setup wire parse work) runtime count target.kem
      target.accept parameters.chosen parameters.others =
      (PqxdhRegistrationJointServerBirth.source setup.joint ensureInit setup.serverKeyId none).run
        ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime) >>= fun born =>
        (match born.1 with
        | none => pure (.failed born.2)
        | some created =>
          (commonPrefix setup wire parse checks target parameters created born.2.1 work >>= fun value =>
            ((simulateQ (PqxdhDynamicKemJointRouter.stopped setup.baseImpl setup.joint setup.kem target.kem.val
                (parameters.pool target))
              (opaqueRest setup (CborRawCompile.sourceCodec wire parse) checks
                created.server.server.metadata.identityIndex created.publicIdentity
                (PqxdhRegistrationJointAcceptCutTag.decideTag decision)
                ((compilerCut setup wire parse value.1, ((encodeState setup value.2).owners, (encodeState setup value.2).inits)), value.2.shared))).run).run
                  (value.2.pool.1, routerOf value.2.pool.2)) >>= fun result =>
            pure (.ready (PqxdhRegistrationJointServerBirth.encode created) parameters.others result.1 result.2 born.2.2)) := by
  unfold PqxdhDeploymentIdealParams.preOpaquePool
  rw [PqxdhRegistrationJointServerBirth.client_source, bind_map_left]
  refine bind_congr_of_forall_mem_support _ fun born member => ?_
  rcases born with ⟨_ | created, after⟩
  · rfl
  · dsimp only [Option.map_some]
    have publicSame := PqxdhRegistrationJointInitializedAccept.source_public setup.joint ensureInit setup.serverKeyId
      none _ after created member
    have slot := PqxdhRegistrationJointServerBirth.source_owned setup.joint ensureInit setup.serverKeyId none
      _ after created member
    have installed := (PqxdhRegistrationJointServerBirth.source_constructor setup.joint ensureInit setup.serverKeyId
      none _ after created member).1
    have empty : after.1.2 = PqxdhLiveKemBirth.empty := by rw [installed]; rfl
    refine congrArg (fun program => program >>= _) ?_
    change ((simulateQ (PqxdhDynamicKemJointRouter.stopped setup.baseImpl setup.joint setup.kem target.kem.val
        (parameters.pool target))
      (PqxdhRegistrationJointKemRawOpaque.opaqueScan (Reader := Reader) setup (CborRawCompile.sourceCodec wire parse)
        checks created.server.server.metadata.identityIndex created.publicIdentity
        (PqxdhRegistrationJointAcceptCutTag.decideTag decision) (CborRawCompile.compile setup wire parse work)
        target.accept ([], fun _ => none) (PqxdhRegistrationSchedule.initial created).shared)).run).run
          (after.1.1, PqxdhDynamicKemRouter.empty) = _
    rw [PqxdhDeploymentIdealCut.opaqueScan_split, simulateQ_bind, OptionT.run_bind, Option.elimM,
      StateT.run_bind, publicSame, stopped_prefix setup wire parse checks target parameters created after.1 empty
        slot work budget certified unreadIdentity unreadKem room, bind_map_left, ← publicSame]
    rfl

end Initialized
end BeaconcryptCore.Computational.CborRawInitializedCut

/-- info: 'BeaconcryptCore.Computational.CborRawInitializedCut.cut_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawInitializedCut.cut_good

/-- info: 'BeaconcryptCore.Computational.CborRawInitializedCut.native_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawInitializedCut.native_prefix

/-- info: 'BeaconcryptCore.Computational.CborRawInitializedCut.item2_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawInitializedCut.item2_prefix

-- Exact dependency observations for all public helper theorems.

/-- info: 'BeaconcryptCore.Computational.CborRawInitializedCut.initial_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawInitializedCut.initial_good

/-- info: 'BeaconcryptCore.Computational.CborRawInitializedCut.stopped_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawInitializedCut.stopped_prefix
