-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawInitializedCut

/-! Source ownership, actual KEM pool prefixes, creation residuals and owner positions are derived on the same initialized raw common prefix. These proofs use the original source-pool query semantics and the exact raw cut equation; they do not assume a relation between completed games. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.CborRawCutRelations
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Spec)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhDeploymentIdealCut (CutCE scanCE sourceInit PoolIndexed scan_residual sourcePool_keys query_indexed)
open PqxdhRegistrationJointAcceptCut (Cut scan)
open CborRawInitializedCut (commonPrefix compilerCut)
variable {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}
section Cut
variable (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks) {count : Nat}
    (t : Target count) (p : Params KemSK count) (created : PqxdhLiveServerConstruction.Created Unit)

theorem cut_owned {Y : Type} (pool : PqxdhRegistrationJointPreparation.Pool KemSK)
    (empty : pool.2 = PqxdhLiveKemBirth.empty)
    (slot : pool.1.seeds[created.server.server.metadata.identityIndex]? = some created.seed) (work : OracleComp Spec Y)
    (reached : (CutCE Y × CborAdmissionCompiler.Local) × PqxdhRegistrationJointSchedule.State KemSK)
    (member : reached ∈ support (commonPrefix setup wire parse checks t p created pool work)) :
    PqxdhDeploymentIdealPoolSource.PoolOwned created.seed created.server.server.metadata.identityIndex reached.2 := by
  have start : PqxdhDeploymentIdealPoolSource.PoolOwned created.seed created.server.server.metadata.identityIndex
      (sourceInit created pool) :=
    ⟨⟨PqxdhRegistrationJointSchedule.initial_owned pool _, slot⟩,
      by simp [sourceInit, PqxdhRegistrationJointSchedule.initial, empty, PqxdhLiveKemBirth.empty]⟩
  exact (PqxdhServerAuthExperiment.run_rel (PqxdhDeploymentIdealPoolSource.sourcePool setup (CborRawCompile.sourceCodec wire parse) checks created.seed
      created.server.server.metadata.identityIndex (p.pool t))
    (fun before after => PqxdhDeploymentIdealPoolSource.PoolOwned created.seed
      created.server.server.metadata.identityIndex before → PqxdhDeploymentIdealPoolSource.PoolOwned created.seed
        created.server.server.metadata.identityIndex after)
    (fun _ owned => owned) (fun _ _ _ left right owned => right (left owned))
    (fun query before after supported owned => PqxdhDeploymentIdealPoolSource.query_poolOwned setup (CborRawCompile.sourceCodec wire parse) checks
      created.seed created.server.server.metadata.identityIndex (p.pool t) query before after owned supported)
    _ _ reached member) start


theorem cut_prefix {Y : Type} (pool : PqxdhRegistrationJointPreparation.Pool KemSK)
    (empty : pool.2 = PqxdhLiveKemBirth.empty)
    (slot : pool.1.seeds[created.server.server.metadata.identityIndex]? = some created.seed) (work : OracleComp Spec Y)
    (budget : PqxdhRegistrationJointRevealCosts.SourceKind → ℕ)
    (certified : ∀ source, (scan (CborRawCompile.compile setup wire parse work) t.accept).IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source))
    (room : budget (.inl 1) ≤ (p.pool t).length)
    (reached : (CutCE Y × CborAdmissionCompiler.Local) × PqxdhRegistrationJointSchedule.State KemSK)
    (member : reached ∈ support (commonPrefix setup wire parse checks t p created pool work)) :
    PqxdhDeploymentIdealPoolSource.PoolPrefix (p.pool t) reached.2.pool.2 ∧
      reached.2.pool.2.keys.length ≤ budget (.inl 1) := by
  have owned : PqxdhDeploymentIdealPoolSource.PoolOwned created.seed created.server.server.metadata.identityIndex
      (sourceInit created pool) :=
    ⟨⟨PqxdhRegistrationJointSchedule.initial_owned pool _, slot⟩,
      by simp [sourceInit, PqxdhRegistrationJointSchedule.initial, empty, PqxdhLiveKemBirth.empty]⟩
  have certified' : ∀ source, (CborRawCompile.compile setup wire parse (scanCE work t.accept)).IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source) := by
    intro source
    have bound := certified source
    rw [show CborRawCompile.compile setup wire parse work =
        (simulateQ (CborRawCompile.compileImpl setup wire parse) work).run (CborAdmissionCompiler.Local.empty setup.serverKeyId) from rfl, CborRawCompileCut.raw_compile_scan,
      isQueryBoundP_map_iff] at bound
    exact bound
  have creations := PqxdhRegistrationJointKemCommands.creations setup (CborRawCompile.sourceCodec wire parse) checks
    created.server.server.metadata.identityIndex (setup.joint.publicKeys created.seed)
    (CborRawCompile.compile setup wire parse (scanCE work t.accept)) budget certified'
    ((PqxdhRegistrationJointGeneratedFinish.encodeState setup (sourceInit created pool)).owners,
      (PqxdhRegistrationJointGeneratedFinish.encodeState setup (sourceInit created pool)).inits)
    (sourceInit created pool).shared
  have image := PqxdhDeploymentIdealPoolSource.kemCommands_reserved setup (CborRawCompile.sourceCodec wire parse) checks created.seed
    created.server.server.metadata.identityIndex (p.pool t)
    (CborRawCompile.compile setup wire parse (scanCE work t.accept)) (sourceInit created pool) owned
  have mapped : (((reached.1, ((PqxdhRegistrationJointGeneratedFinish.encodeState setup reached.2).owners,
        (PqxdhRegistrationJointGeneratedFinish.encodeState setup reached.2).inits)),
      reached.2.shared), reached.2.pool) ∈ support ((simulateQ (PqxdhDeploymentIdealPoolSource.reservedAt setup (p.pool t))
        (PqxdhRegistrationJointKemCommands.program setup (CborRawCompile.sourceCodec wire parse) checks created.server.server.metadata.identityIndex
          (setup.joint.publicKeys created.seed) (CborRawCompile.compile setup wire parse (scanCE work t.accept))
          ((PqxdhRegistrationJointGeneratedFinish.encodeState setup (sourceInit created pool)).owners,
      (PqxdhRegistrationJointGeneratedFinish.encodeState setup (sourceInit created pool)).inits)
          (sourceInit created pool).shared)).run (sourceInit created pool).pool) := by
    rw [image, support_map]
    exact ⟨reached, member, rfl⟩
  have prefixed := PqxdhDeploymentIdealPoolSource.reserved_program_prefix setup (p.pool t) _ _ creations
    (sourceInit created pool).pool.1 (sourceInit created pool).pool.2
    (by simp [sourceInit, PqxdhRegistrationJointSchedule.initial, empty, PqxdhLiveKemBirth.empty,
      PqxdhDeploymentIdealPoolSource.PoolPrefix])
    (by simpa [sourceInit, PqxdhRegistrationJointSchedule.initial, empty, PqxdhLiveKemBirth.empty] using room) _ mapped
  refine ⟨prefixed.1, ?_⟩
  simpa [sourceInit, PqxdhRegistrationJointSchedule.initial, empty, PqxdhLiveKemBirth.empty] using prefixed.2



theorem cut_residual {Y : Type} (pool : PqxdhRegistrationJointPreparation.Pool KemSK)
    (empty : pool.2 = PqxdhLiveKemBirth.empty) (work : OracleComp Spec Y)
    (budget : PqxdhRegistrationJointRevealCosts.SourceKind → ℕ)
    (whole : ∀ source, (CborRawCompile.compile setup wire parse work).IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source))
    (reached : (CutCE Y × CborAdmissionCompiler.Local) × PqxdhRegistrationJointSchedule.State KemSK)
    (member : reached ∈ support (commonPrefix setup wire parse checks t p created pool work)) :
    reached.2.pool.2.keys.length ≤ budget (.inl 1) ∧
      ∀ raw next, compilerCut setup wire parse reached.1 = .pending raw next → ∀ reply source,
        (next reply).IsQueryBoundP
          (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source)
          (Function.update budget (.inl 1) (budget (.inl 1) - reached.2.pool.2.keys.length) source) := by
  have scanned : (compilerCut setup wire parse reached.1, reached.2) ∈ support
      ((simulateQ (PqxdhDeploymentIdealPoolSource.sourcePool setup (CborRawCompile.sourceCodec wire parse) checks created.seed
          created.server.server.metadata.identityIndex (p.pool t))
        (scan (CborRawCompile.compile setup wire parse work) t.accept)).run (sourceInit created pool)) := by
    rw [show CborRawCompile.compile setup wire parse work =
        (simulateQ (CborRawCompile.compileImpl setup wire parse) work).run (CborAdmissionCompiler.Local.empty setup.serverKeyId) from rfl,
      CborRawCompileCut.raw_compile_scan, simulateQ_map, StateT.run_map, support_map]
    exact ⟨reached, member, rfl⟩
  have start : (sourceInit created pool).pool.2.keys.length = 0 := by
    simp [sourceInit, PqxdhRegistrationJointSchedule.initial, empty, PqxdhLiveKemBirth.empty]
  have creations := scan_residual _ (fun state : PqxdhRegistrationJointSchedule.State KemSK => state.pool.2.keys.length)
    (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = .inl 1)
    (fun query state result supported => (sourcePool_keys setup (CborRawCompile.sourceCodec wire parse) checks created.seed
      created.server.server.metadata.identityIndex (p.pool t) query state result supported).le)
    _ t.accept _ (whole (.inl 1)) _ _ scanned
  simp only [start, Nat.zero_add] at creations
  refine ⟨creations.1, fun raw next pending reply source => ?_⟩
  by_cases kind : source = .inl 1
  · subst kind
    simpa only [Function.update_self] using creations.2 raw next pending reply
  · have other := scan_residual _ (fun _ : PqxdhRegistrationJointSchedule.State KemSK => 0)
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source)
      (fun _ _ _ _ => Nat.zero_le _) _ t.accept _ (whole source) _ _ scanned
    simpa only [Function.update_of_ne kind, Nat.zero_add, Nat.sub_zero] using other.2 raw next pending reply


theorem cut_indexed {Y : Type} (pool : PqxdhRegistrationJointPreparation.Pool KemSK)
    (empty : pool.2 = PqxdhLiveKemBirth.empty)
    (slot : pool.1.seeds[created.server.server.metadata.identityIndex]? = some created.seed) (work : OracleComp Spec Y)
    (reached : (CutCE Y × CborAdmissionCompiler.Local) × PqxdhRegistrationJointSchedule.State KemSK)
    (member : reached ∈ support (commonPrefix setup wire parse checks t p created pool work)) :
    PoolIndexed reached.2 := by
  have start : PqxdhDeploymentIdealPoolSource.PoolOwned created.seed created.server.server.metadata.identityIndex
      (sourceInit created pool) ∧ PoolIndexed (sourceInit created pool) :=
    ⟨⟨⟨PqxdhRegistrationJointSchedule.initial_owned pool _, slot⟩,
      by simp [sourceInit, PqxdhRegistrationJointSchedule.initial, empty, PqxdhLiveKemBirth.empty]⟩,
      by simp [PoolIndexed, sourceInit, PqxdhRegistrationJointSchedule.initial]⟩
  exact ((PqxdhServerAuthExperiment.run_rel (PqxdhDeploymentIdealPoolSource.sourcePool setup (CborRawCompile.sourceCodec wire parse) checks created.seed
      created.server.server.metadata.identityIndex (p.pool t))
    (fun before after => PqxdhDeploymentIdealPoolSource.PoolOwned created.seed
        created.server.server.metadata.identityIndex before ∧ PoolIndexed before →
      PqxdhDeploymentIdealPoolSource.PoolOwned created.seed created.server.server.metadata.identityIndex after ∧
        PoolIndexed after)
    (fun _ facts => facts) (fun _ _ _ left right facts => right (left facts))
    (fun query before after supported facts =>
      ⟨PqxdhDeploymentIdealPoolSource.query_poolOwned setup (CborRawCompile.sourceCodec wire parse) checks created.seed
        created.server.server.metadata.identityIndex (p.pool t) query before after facts.1 supported,
      query_indexed setup (CborRawCompile.sourceCodec wire parse) checks created.seed created.server.server.metadata.identityIndex (p.pool t) query
        before after facts.1 facts.2 supported⟩)
    _ _ reached member) start).2

end Cut
end BeaconcryptCore.Computational.CborRawCutRelations

/-- info: 'BeaconcryptCore.Computational.CborRawCutRelations.cut_owned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawCutRelations.cut_owned

/-- info: 'BeaconcryptCore.Computational.CborRawCutRelations.cut_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawCutRelations.cut_prefix

/-- info: 'BeaconcryptCore.Computational.CborRawCutRelations.cut_residual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawCutRelations.cut_residual

/-- info: 'BeaconcryptCore.Computational.CborRawCutRelations.cut_indexed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawCutRelations.cut_indexed
