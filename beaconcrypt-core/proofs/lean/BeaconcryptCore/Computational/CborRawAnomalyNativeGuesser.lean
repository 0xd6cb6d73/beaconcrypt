-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawAnomalyOracle

/-! The actual native raw pool game, with only the selected owner's finish answered by its pre-challenge decapsulation oracle. Creation still consumes the challenger's indexed pool, records retain their actual optional writer and native admission, and every other private primitive runs on the guesser's own coins. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawAnomalyNativeGuesser
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhDeploymentIdealKeySwap (swapNative Holds Swaps withChosen pool_withChosen onNative_swaps)
open PqxdhDeploymentNative (State)
open PqxdhDeploymentInterface (Spec)
open PqxdhKemIndCca (MlKemCCAOracleSpec)
open PqxdhPrivateKemSource (ccaCoins)
open PqxdhDeploymentIdealAnomalyGuesser (interp interp_coins)
variable {ι KemSK Reader Response X : Type} {baseSpec : OracleSpec ι}

noncomputable def native (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks) {count : Nat}
    (target : Target count) (parameters : Params KemSK count) (created : PqxdhLiveServerConstruction.Created Unit) :
    QueryImpl Spec (StateT (State KemSK) (OracleComp (MlKemCCAOracleSpec baseSpec)))
  | .inr (.finish owner raw) => fun state =>
      if owner = target.kem.val then (CborRawAnomalyOracle.rawFinish setup wire parse owner raw).run state
      else ccaCoins ((CborRawPoolCompiler.native setup wire parse checks created.seed (parameters.pool target)
        (.inr (.finish owner raw))).run state)
  | query => fun state => ccaCoins
      ((CborRawPoolCompiler.native setup wire parse checks created.seed (parameters.pool target) query).run state)

private theorem pool_create (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks) {count : Nat}
    (target : Target count) (parameters : Params KemSK count) (created : PqxdhLiveServerConstruction.Created Unit)
    (new : KemSK) (pin : Pqxdh.Bytes) (keyId : Std.U64) :
    Swaps (swapNative target.kem.val new) (fun state => Holds target.kem.val parameters.chosen.2 state.native.owners)
      (CborRawPoolCompiler.native setup wire parse checks created.seed (parameters.pool target) (.inr (.create pin keyId)))
      (CborRawPoolCompiler.native setup wire parse checks created.seed ((withChosen parameters new).pool target) (.inr (.create pin keyId))) := by
  intro state held
  rw [pool_withChosen]
  cases parsed : PqxdhDeploymentInterface.parsePin pin with
  | none =>
      refine ⟨?_, ?_⟩
      · simp only [CborRawPoolCompiler.native, PqxdhDeploymentIdealPool.deploymentPool, parsed, StateT.run_pure, map_pure, Prod.map, id_eq]
      · intro result supported
        simp only [CborRawPoolCompiler.native, PqxdhDeploymentIdealPool.deploymentPool, parsed,
          StateT.run_pure, mem_support_pure_iff] at supported
        cases supported
        exact held
  | some word =>
      have step := onNative_swaps target.kem.val parameters.chosen.2 new _ _
        (PqxdhDeploymentIdealKeySwap.createPool_swaps setup target.kem.val parameters.chosen.2 new
          (parameters.pool target) word keyId (by rw [PqxdhDeploymentIdealParams.pool_length]; exact target.kem.isLt)
          (fun keys found => by rw [PqxdhDeploymentIdealParams.pool_kem, Option.some.injEq] at found; subst keys; rfl)) state held
      refine ⟨?_, ?_⟩
      · simp only [CborRawPoolCompiler.native, PqxdhDeploymentIdealPool.deploymentPool, parsed,
          StateT.run_map, step.1, Functor.map_map, Prod.map, id_eq]
      · intro result supported
        simp only [CborRawPoolCompiler.native, PqxdhDeploymentIdealPool.deploymentPool, parsed,
          StateT.run_map, support_map] at supported
        obtain ⟨inner, reached, rfl⟩ := supported
        exact step.2 inner reached

private theorem pool_coin (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks)
    (seed : PqxdhJointIdentity.IdentitySeed) (pool : List (PqxdhLiveKemReservation.Pair KemSK))
    (coin : Nat) (state : State KemSK) :
    (CborRawPoolCompiler.native setup wire parse checks seed pool (.inl coin)).run state =
      (fun reply => (reply, state)) <$> (unifSpec.query coin : ProbComp _) := rfl

private theorem pool_other (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks)
    (seed : PqxdhJointIdentity.IdentitySeed) (pool : List (PqxdhLiveKemReservation.Pair KemSK))
    (command : PqxdhDeploymentInterface.Command)
    (other : ∀ pin keyId, command ≠ .create pin keyId) :
    CborRawPoolCompiler.native setup wire parse checks seed pool (.inr command) =
      CborProductionBoundary.handler setup wire parse checks seed (.inr command) := by
  cases command
  case create pin keyId => exact False.elim (other pin keyId rfl)
  all_goals rfl

private theorem native_selected_run (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks) {count : Nat}
    (target : Target count) (parameters : Params KemSK count) (created : PqxdhLiveServerConstruction.Created Unit)
    (raw : Pqxdh.Bytes) (state : State KemSK) :
    (native setup wire parse checks target parameters created (.inr (.finish target.kem.val raw))).run state =
      (CborRawAnomalyOracle.rawFinish setup wire parse target.kem.val raw).run state := by
  change (if target.kem.val = target.kem.val then _ else _) = _
  rw [ite_eq_left rfl]

private theorem native_lift_run (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks) {count : Nat}
    (target : Target count) (parameters : Params KemSK count) (created : PqxdhLiveServerConstruction.Created Unit)
    (query : Spec.Domain) (state : State KemSK)
    (notSelected : ∀ raw, query ≠ .inr (.finish target.kem.val raw)) :
    (native setup wire parse checks target parameters created query).run state = ccaCoins
      ((CborRawPoolCompiler.native setup wire parse checks created.seed (parameters.pool target) query).run state) := by
  rcases query with coin | command
  · rfl
  · cases command
    case finish owner raw =>
      change (if owner = target.kem.val then _ else _) = _
      rw [ite_eq_right (fun same => notSelected raw (by rw [same]))]
    all_goals rfl

/-- Every actual raw native operation is realized under the chosen secret's pre-challenge oracle, retaining all replies and complete source fields. -/
theorem query_interp (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks) {count : Nat}
    (target : Target count) (parameters : Params KemSK count) (created : PqxdhLiveServerConstruction.Created Unit)
    (new : KemSK) (query : Spec.Domain) (state : State KemSK)
    (held : Holds target.kem.val parameters.chosen.2 state.native.owners) :
    simulateQ (interp setup parameters.chosen.2)
        ((native setup wire parse checks target (withChosen parameters new) created query).run (swapNative target.kem.val new state)) =
      Prod.map id (swapNative target.kem.val new) <$>
        (CborRawPoolCompiler.native setup wire parse checks created.seed (parameters.pool target) query).run state ∧
    ∀ result ∈ support ((CborRawPoolCompiler.native setup wire parse checks created.seed (parameters.pool target) query).run state),
      Holds target.kem.val parameters.chosen.2 result.2.native.owners := by
  rcases query with coin | command
  · rw [native_lift_run setup wire parse checks target (withChosen parameters new) created (.inl coin)
      (swapNative target.kem.val new state) (fun _ same => by cases same), interp_coins, pool_coin, pool_coin]
    refine ⟨by simp only [Functor.map_map, Prod.map, id_eq], ?_⟩
    intro result supported
    rw [support_map] at supported
    obtain ⟨reply, _, rfl⟩ := supported
    exact held
  · by_cases selected : ∃ raw, command = .finish target.kem.val raw
    · obtain ⟨raw, rfl⟩ := selected
      rw [native_selected_run, pool_other setup wire parse checks created.seed (parameters.pool target)
        (.finish target.kem.val raw) (fun _ _ same => by cases same)]
      exact CborRawAnomalyOracle.rawFinish_interp setup wire parse checks created target.kem.val parameters.chosen.2 new raw state held
    · rw [native_lift_run setup wire parse checks target (withChosen parameters new) created (.inr command)
        (swapNative target.kem.val new state) (fun raw same => selected ⟨raw, Sum.inr.inj same⟩), interp_coins]
      by_cases creating : ∃ pin keyId, command = .create pin keyId
      · obtain ⟨pin, keyId, rfl⟩ := creating
        exact pool_create setup wire parse checks target parameters created new pin keyId state held
      · rw [pool_other setup wire parse checks created.seed ((withChosen parameters new).pool target) command
          (fun pin keyId same => creating ⟨pin, keyId, same⟩),
          pool_other setup wire parse checks created.seed (parameters.pool target) command
            (fun pin keyId same => creating ⟨pin, keyId, same⟩)]
        exact CborRawAnomalyNativeSwap.handler_other setup wire parse checks created.seed target.kem.val parameters.chosen.2 new command
          (fun pin keyId same => creating ⟨pin, keyId, same⟩) (fun raw same => selected ⟨raw, same⟩) state held

/-- The same original adaptive native program has the exact original output and secret-replaced native poststate under the CCA oracle. -/
theorem program_interp (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks) {count : Nat}
    (target : Target count) (parameters : Params KemSK count) (created : PqxdhLiveServerConstruction.Created Unit)
    (new : KemSK) (work : OracleComp Spec X) (state : State KemSK)
    (held : Holds target.kem.val parameters.chosen.2 state.native.owners) :
    simulateQ (interp setup parameters.chosen.2)
      ((simulateQ (native setup wire parse checks target (withChosen parameters new) created) work).run
        (swapNative target.kem.val new state)) =
      Prod.map id (swapNative target.kem.val new) <$>
        (simulateQ (CborRawPoolCompiler.native setup wire parse checks created.seed (parameters.pool target)) work).run state := by
  rw [PqxdhRegistrationJointKemEntryFactor.simulateQ_mapRun]
  exact (PqxdhDeploymentIdealAnomalyGuesser.simulate_swaps
    (CborRawPoolCompiler.native setup wire parse checks created.seed (parameters.pool target))
    (PqxdhRegistrationJointKemEntryFactor.mapRun (interp setup parameters.chosen.2)
      (native setup wire parse checks target (withChosen parameters new) created))
    (swapNative target.kem.val new) (fun state => Holds target.kem.val parameters.chosen.2 state.native.owners)
    (fun _ => False) (fun query _ current invariant => by
      simpa only [PqxdhRegistrationJointKemEntryFactor.mapRun_run] using
        query_interp setup wire parse checks target parameters created new query current invariant)
    work (isQueryBoundP_false work 0) state held).1

end BeaconcryptCore.Computational.CborRawAnomalyNativeGuesser

/-- info: 'BeaconcryptCore.Computational.CborRawAnomalyNativeGuesser.query_interp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawAnomalyNativeGuesser.query_interp
/-- info: 'BeaconcryptCore.Computational.CborRawAnomalyNativeGuesser.program_interp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawAnomalyNativeGuesser.program_interp
