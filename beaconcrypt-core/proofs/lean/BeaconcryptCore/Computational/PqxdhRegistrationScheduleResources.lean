-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationScheduleCosts
import BeaconcryptCore.Computational.PqxdhRegistrationScheduleExecution

/-! The joint raw registration scheduler's finite source-query partition and complete interpreted uniform bill. Every attempted API request remains present, including runtime/parser refusal and missing or spent handles. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationSchedule
open PqxdhJointIdentity PqxdhJointGapDh PqxdhServerAuthExperiment PqxdhServerAuthNative
open PqxdhServerAuthSourceCosts
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A Result : Type}

/-- Coins, constructor attempts, bundle attempts, accepts, builds, finishes, public HMAC, public hash and current-kernel reads, respectively. Labels classify work; no request is removed from execution. -/
def sourceKind : Spec.Domain → Fin 9
  | .inl _ => 0
  | .inr (.create _ _) => 1
  | .inr (.bundle _) => 2
  | .inr (.accept _) => 3
  | .inr (.build _ _) => 4
  | .inr (.finish _ _) => 5
  | .inr (.hmac _ _) => 6
  | .inr (.hash _) => 7
  | .inr (.reveal _) => 8

/-- Raw initialization and parse failures still occupy the constructor-attempt coordinate. -/
def surfaceKind : SurfaceSpec.Domain → Fin 9
  | .inl _ => 0
  | .inr (.create _ _) => 1
  | .inr (.call request) => sourceKind (.inr request.val)

/-- Concrete callback costs include all source and interpreted primitive base draws. A zero read allowance means no uniform-oracle request, not zero local work. -/
def uniformCost (caps : KemCaps) (qInit : Nat) : Fin 9 → Nat :=
  ![1, qInit + 64 + caps.keygenCost, 32, 96 + caps.encapsCost, 64,
    69 * max 64 caps.decapsCost, 64, 64, 0]

/-- The actual typed internal scheduler has the advertised per-attempt bill, preserving complete shared and owner state on every optional result. -/
theorem handler_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (seed : IdentitySeed) (qInit : Nat)
    (query : Spec.Domain) (state : State KemSK) :
    ((handler setup codec checks seed query).run state).IsTotalQueryBound (uniformCost caps qInit (sourceKind query)) := by
  rcases query with coin | request
  · simp [handler, uniformCost, sourceKind, StateT.run_lift, IsTotalQueryBound]
  · cases request with
    | accept raw =>
        simpa [handler, onShared, uniformCost, sourceKind, StateT.run, IsTotalQueryBound, isQueryBound_map_iff] using
          accept_uniform setup codec checks caps bounded seed observationScalar raw state.shared
    | create pin keyId =>
        exact (create_uniform setup caps bounded pin keyId state).mono (by simp [uniformCost, sourceKind])
    | bundle index =>
        simpa [handler, uniformCost, sourceKind] using bundle_uniform setup codec index state
    | build index payload =>
        simpa [handler, onShared, uniformCost, sourceKind, StateT.run, IsTotalQueryBound, isQueryBound_map_iff] using
          build_uniform setup codec checks index payload state.shared
    | finish index raw =>
        simpa [handler, uniformCost, sourceKind] using finish_uniform setup codec caps bounded index raw state
    | hmac key message =>
        simpa [handler, onShared, uniformCost, sourceKind, StateT.run, IsTotalQueryBound, isQueryBound_map_iff] using
          hmac_uniform setup seed observationScalar key message state.shared
    | hash bytes =>
        simpa [handler, onShared, uniformCost, sourceKind, StateT.run, IsTotalQueryBound, isQueryBound_map_iff] using
          hash_uniform bytes state.shared
    | reveal keyId =>
        change (pure _ : ProbComp _).IsTotalQueryBound 0
        trivial

/-- The actual raw public surface charges initialization on every constructor attempt and retains each original operation's complete bill. -/
theorem surface_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (seed : IdentitySeed)
    (ensureInit : StateT A ProbComp Bool) (qInit : Nat)
    (initBound : ∀ runtime, (ensureInit.run runtime).IsTotalQueryBound qInit)
    (query : SurfaceSpec.Domain) (state : A × State KemSK) :
    ((surfaceHandler setup codec checks seed ensureInit query).run state).IsTotalQueryBound
      (uniformCost caps qInit (surfaceKind query)) := by
  rcases query with coin | (⟨bytes, keyId⟩ | request)
  · simpa only [surfaceHandler, onProtocol, StateT.run, surfaceKind, sourceKind,
      IsTotalQueryBound, isQueryBound_map_iff] using
      handler_uniform setup codec checks caps bounded seed qInit (.inl coin) state.2
  · simpa [surfaceHandler, surfaceKind, uniformCost] using
      rawCreate_uniform setup checks caps bounded ensureInit qInit initBound bytes keyId state
  · simpa only [surfaceHandler, onProtocol, StateT.run, surfaceKind,
      IsTotalQueryBound, isQueryBound_map_iff] using
      handler_uniform setup codec checks caps bounded seed qInit (.inr request.val) state.2

/-- The finite class certificate quantifies every possible adaptive reply. It counts attempted public requests rather than successful outputs or log entries. -/
def UniformBounded (work : OracleComp SurfaceSpec Result) (budget : Fin 9 → Nat) : Prop :=
  ∀ kind, work.IsQueryBoundP (fun query => surfaceKind query = kind) (budget kind)

/-- Every complete adaptive raw registration schedule retains its full source/interpreted primitive work under the concrete nine-class sum. -/
theorem surface_program_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (seed : IdentitySeed)
    (ensureInit : StateT A ProbComp Bool) (qInit : Nat)
    (initBound : ∀ runtime, (ensureInit.run runtime).IsTotalQueryBound qInit)
    (work : OracleComp SurfaceSpec Result) (budget : Fin 9 → Nat) (certified : UniformBounded work budget)
    (state : A × State KemSK) :
    ((simulateQ (surfaceHandler setup codec checks seed ensureInit) work).run state).IsTotalQueryBound
      (∑ kind, uniformCost caps qInit kind * budget kind) := by
  exact (isQueryBoundP_true_iff _ _).mp
    (FinitePartitionQueryBounds.weighted_bound surfaceKind (uniformCost caps qInit) budget
      (surfaceHandler setup codec checks seed ensureInit) (fun _ => True) work certified
      (fun query before => (surface_uniform setup codec checks caps bounded seed ensureInit qInit initBound query before).isQueryBoundP)
      state)

/-- The complete actual experiment includes its Server initialization and supplied/generated-seed branch before the entire adaptive raw scheduler. No constructor prefix or runtime callback is outside this bill. -/
theorem surfaceExperiment_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (ensureInit : StateT A ProbComp Bool)
    (qInit : Nat) (initBound : ∀ runtime, (ensureInit.run runtime).IsTotalQueryBound qInit)
    (supplied : Option Pqxdh.Bytes) (adversary : PublicIdentity → Std.U64 → OracleComp SurfaceSpec Result)
    (budget : Fin 9 → Nat) (certified : ∀ identity keyId, UniformBounded (adversary identity keyId) budget)
    (runtime : A) :
    (surfaceExperiment setup codec checks ensureInit supplied adversary runtime).IsTotalQueryBound
      (qInit + (if supplied.isNone then 32 else 0) + ∑ kind, uniformCost caps qInit kind * budget kind) := by
  unfold surfaceExperiment
  apply isTotalQueryBound_bind
    (PqxdhLiveServerConstruction.construct_uniform setup.joint ensureInit qInit initBound 0 setup.serverKeyId supplied runtime)
  rintro ⟨created, initializedRuntime⟩
  cases created with
  | none => trivial
  | some created =>
      simpa only [surfaceExecute, IsTotalQueryBound, isQueryBound_map_iff] using
        surface_program_uniform setup codec checks caps bounded created.seed ensureInit qInit initBound
          (adversary created.publicIdentity created.server.server.metadata.sender) budget (certified _ _) (initializedRuntime, initial created)

/-- Expanded cumulative bill: every public attempt is charged, and the source KEM costs already include their declared base-interpreter randomness. -/
theorem uniform_bill (caps : KemCaps) (qInit : Nat) (budget : Fin 9 → Nat) :
    (∑ kind, uniformCost caps qInit kind * budget kind) =
      budget 0 + (qInit + 64 + caps.keygenCost) * budget 1 + 32 * budget 2 +
      (96 + caps.encapsCost) * budget 3 + 64 * budget 4 +
      (69 * max 64 caps.decapsCost) * budget 5 + 64 * budget 6 + 64 * budget 7 := by
  simp [uniformCost, Fin.sum_univ_succ, Nat.add_assoc]

end BeaconcryptCore.Computational.PqxdhRegistrationSchedule

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationSchedule.handler_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationSchedule.handler_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationSchedule.surface_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationSchedule.surface_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationSchedule.surface_program_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationSchedule.surface_program_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationSchedule.surfaceExperiment_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationSchedule.surfaceExperiment_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationSchedule.uniform_bill' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationSchedule.uniform_bill
