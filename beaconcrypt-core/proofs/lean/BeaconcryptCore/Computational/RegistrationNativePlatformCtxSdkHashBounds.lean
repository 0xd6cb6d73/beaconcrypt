-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformCtxCompletionHashBounds
import BeaconcryptCore.Computational.RegistrationNativePlatformCtxSdk
/-! The literal moved-token SDK preserves the physical hash allowance through pin lookup, occupancy, public reservation, completion and commit. All source failures retain their actual reached prefix. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformCtxSdkHashBounds
open BeaconcryptCore.Refinement
open RegistrationNativePlatformCtxLeafHashBounds (Bounded)
open RegistrationNativePlatformCtxBirthdayBudget (IsHash)
open RegistrationNativePlatformCtxRunner (M)
open RegistrationNativePlatformCompletionSdk
open RegistrationServerFrontendCompiler (State)
open RegistrationServerRootCompiler (Local)
open PqxdhServerAuthExperiment (Setup Codec)
variable {n : Nat} {I KemSK Reader Response Platform E S A B Encoded : Type} {base : OracleSpec I}

private theorem pure_bound (value : A) (cap : Nat) : Bounded (pure value : M S Platform A) cap :=
  fun _ _ => isQueryBoundP_pure _ _ _
private theorem bind_bound (work : M S Platform A) (next : A → M S Platform B)
    (first later : Nat) (bounded : Bounded work first) (rest : ∀ value, Bounded (next value) later) :
    Bounded (work >>= next) (first + later) := by
  intro before previous
  rw [StateT.run_bind, StateT.run_bind]
  exact isQueryBoundP_bind (bounded before previous) (fun result _ => rest result.1.1 result.1.2 result.2)

private theorem map_apply {T X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT T m X) (before : T) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

private theorem world (work : M (Local n) Platform A) (cap : Nat) (bounded : Bounded work cap) :
    Bounded (RegistrationNativePlatformServerSdk.world work) cap := by
  intro before previous
  simpa only [RegistrationNativePlatformServerSdk.world, StateT.run, map_apply,
    isQueryBoundP_map_iff] using bounded before.world previous

private theorem commit (result : RustM (RegistrationWorldServerCompletion.Result Encoded)) :
    Bounded (RegistrationNativePlatformServerSdk.commit (n := n) (m := StateT Platform (OracleComp RegistrationNativePlatformCtxBackend.Spec)) result) 0 := by
  intro before previous
  cases result with
  | fail error | div => exact isQueryBoundP_pure _ _ _
  | ok reply => cases reply <;> exact isQueryBoundP_pure _ _ _

private theorem from_initial (finish : Completion n (StateT Platform (OracleComp RegistrationNativePlatformCtxBackend.Spec)) Encoded)
    (bounded : ∀ control pending, Bounded (finish control pending) 9)
    (control : pqxdh.ServerState) (pending : registration.ServerInitialKdf) :
    Bounded (fromInitial finish control pending) 9 := by
  unfold fromInitial
  exact bind_bound _ _ 9 0 (world _ 9 (bounded control pending)) commit

private theorem after_occupancy
    (deriveAd : AdHash n (StateT Platform (OracleComp RegistrationNativePlatformCtxBackend.Spec)))
    (hashed : ∀ pending, Bounded (deriveAd pending) 1)
    (reserve : M (State n) Platform Bool) (reserved : Bounded reserve 0)
    (finish : Completion n (StateT Platform (OracleComp RegistrationNativePlatformCtxBackend.Spec)) Encoded)
    (bounded : ∀ control pending, Bounded (finish control pending) 9)
    (control : pqxdh.ServerState) (lookup : peer.CompletionLookup) (occupied : Bool) :
    Bounded (afterOccupancy deriveAd reserve finish control lookup occupied) 10 := by
  unfold afterOccupancy
  cases lookup.resume occupied with
  | fail error | div => exact pure_bound _ _
  | ok reply => cases reply with
    | Err state => exact pure_bound _ _
    | Ok pending =>
      apply bind_bound _ _ 1 9 (hashed pending)
      intro result
      cases result with
      | fail error | div => exact pure_bound _ _
      | ok reply => cases reply with
        | Err state => exact pure_bound _ _
        | Ok initial =>
          apply bind_bound _ _ 0 9 reserved
          intro admitted
          cases admitted with
          | false => exact pure_bound _ _
          | true => exact from_initial finish bounded control initial

private theorem after_pin
    (deriveAd : AdHash n (StateT Platform (OracleComp RegistrationNativePlatformCtxBackend.Spec)))
    (hashed : ∀ pending, Bounded (deriveAd pending) 1)
    (reserve : M (State n) Platform Bool) (reserved : Bounded reserve 0)
    (present : U64 → M (State n) Platform Bool) (presence : ∀ key, Bounded (present key) 0)
    (finish : Completion n (StateT Platform (OracleComp RegistrationNativePlatformCtxBackend.Spec)) Encoded)
    (bounded : ∀ control pending, Bounded (finish control pending) 9)
    (control : pqxdh.ServerState) (token : peer.ConsumedRegistration) (application : Slice U8)
    (pin : RustM (core.option.Option session.ServerAuthenticationPin)) :
    Bounded (afterPin deriveAd reserve present finish control token application pin) 10 := by
  unfold afterPin
  cases pin with
  | fail error | div => exact pure_bound _ _
  | ok optional => cases optional with
    | none => exact pure_bound _ _
    | some pin =>
      simp only
      cases peer.begin_completion_lookup control pin token application with
      | fail error | div => exact pure_bound _ _
      | ok reply => cases reply with
        | Err state => exact pure_bound _ _
        | Ok lookup =>
          simp only
          cases lookup.request with
          | fail error | div => exact pure_bound _ _
          | ok keyId =>
            simp only
            split
            · exact bind_bound _ _ 0 10 (presence keyId)
                (fun occupied => after_occupancy deriveAd hashed reserve reserved finish bounded control lookup occupied)
            · exact pure_bound _ _

private theorem complete_bound
    (deriveAd : AdHash n (StateT Platform (OracleComp RegistrationNativePlatformCtxBackend.Spec)))
    (hashed : ∀ pending, Bounded (deriveAd pending) 1)
    (pin : M (State n) Platform (RustM (core.option.Option session.ServerAuthenticationPin))) (pinned : Bounded pin 0)
    (reserve : M (State n) Platform Bool) (reserved : Bounded reserve 0)
    (present : U64 → M (State n) Platform Bool) (presence : ∀ key, Bounded (present key) 0)
    (finish : Completion n (StateT Platform (OracleComp RegistrationNativePlatformCtxBackend.Spec)) Encoded)
    (bounded : ∀ control pending, Bounded (finish control pending) 9)
    (token : peer.ConsumedRegistration) (application : Slice U8) :
    Bounded (complete deriveAd pin reserve present finish token application) 10 := by
  unfold complete
  apply bind_bound _ _ 0 10
  · intro before previous
    exact isQueryBoundP_pure _ _ _
  · intro before
    exact bind_bound _ _ 0 10 pinned
      (fun selected => after_pin deriveAd hashed reserve reserved present presence finish bounded before.control token application selected)

private theorem sdk_bound
    (deriveAd : AdHash n (StateT Platform (OracleComp RegistrationNativePlatformCtxBackend.Spec)))
    (hashed : ∀ pending, Bounded (deriveAd pending) 1)
    (pin : M (State n) Platform (RustM (core.option.Option session.ServerAuthenticationPin))) (pinned : Bounded pin 0)
    (reserve : M (State n) Platform Bool) (reserved : Bounded reserve 0)
    (present : U64 → M (State n) Platform Bool) (presence : ∀ key, Bounded (present key) 0)
    (finish : Completion n (StateT Platform (OracleComp RegistrationNativePlatformCtxBackend.Spec)) Encoded)
    (bounded : ∀ control pending, Bounded (finish control pending) 9)
    (handle : Nat) (application : Option (Slice U8)) :
    Bounded (build deriveAd pin reserve present finish handle application) 10 := by
  intro before previous
  simp only [build, StateT.run]
  cases RegistrationServerSdkSource.take handle before with
  | mk selected current => cases selected with
    | none => exact isQueryBoundP_pure _ _ _
    | some token => cases application with
      | none => exact isQueryBoundP_pure _ _ _
      | some application => exact complete_bound deriveAd hashed pin pinned reserve reserved present presence finish bounded token application current previous

private theorem pin_zero : Bounded (RegistrationNativePlatformCtxSdk.pin (n := n) : M _ Platform _) 0 := by
  intro before previous
  apply world _ 0 _ before previous
  apply RegistrationNativePlatformCtxLeafHashBounds.private_work
  intro current
  simp only [RegistrationNativePlatformCtxPin.pin, StateT.run_pure, isQueryBoundP_pure]

private theorem ad_hash (pending : registration.ServerAdHash) :
    Bounded (RegistrationNativePlatformCtxSdk.adHash (n := n) pending : M _ Platform _) 1 := by
  unfold RegistrationNativePlatformCtxSdk.adHash RegistrationServerAdHash.runWith
  cases pending.request with
  | fail error | div => exact pure_bound _ _
  | ok request =>
    simp only [bind_assoc, pure_bind]
    exact bind_bound _ _ 1 0
      (world _ 1 (RegistrationNativePlatformCtxLeafHashBounds.private_work _ 1
        (RegistrationNativePlatformCtxLeafHashBounds.effects _)))
      (fun _ => pure_bound _ 0)

/-- Pure pin selection also satisfies the retained conservative one-request allowance. -/
theorem pin : Bounded (RegistrationNativePlatformCtxSdk.pin (n := n) : M _ Platform _) 1 := by
  intro before previous
  exact (pin_zero before previous).mono (by decide)

/-- Occupancy lookup has no CTX request; it keeps its literal native capability result. -/
theorem present (keyId : U64) :
    Bounded (RegistrationNativePlatformCtxSdk.present (n := n) keyId : M _ Platform _) 0 := by
  apply world _ 0
  apply RegistrationNativePlatformCtxLeafHashBounds.private_work
  intro before
  simp only [RegistrationNativePlatformCtxLocal.effects, RegistrationNativePlatformCtxEffects.program,
    StateT.run, isQueryBoundP_map_iff]
  exact RegistrationNativePlatformCtxLeafHashBounds.coins _

variable [sealPrimitive : AdapterSealPrimitive.Operations]
/-- The literal complete source SDK build uses at most ten physical CTX calls, including its actual AD hash and every failed prefix. -/
theorem build_bound (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : sealPrimitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (reserve : StateT Platform ProbComp Bool) (handle : Nat) (application : Option (Slice U8)) :
    Bounded (RegistrationNativePlatformCtxSdk.build (n := n) setup codec view failure allocation erased sign helper writer reserve handle application) 10 := by
  apply sdk_bound _ ad_hash _ pin_zero _ (RegistrationNativePlatformCtxLeafHashBounds.public_work reserve) _ present
  exact RegistrationNativePlatformCtxCompletionHashBounds.completion setup codec view failure allocation erased sign helper writer
end BeaconcryptCore.Computational.RegistrationNativePlatformCtxSdkHashBounds

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxSdkHashBounds.pin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxSdkHashBounds.pin

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxSdkHashBounds.present' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxSdkHashBounds.present

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxSdkHashBounds.build_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxSdkHashBounds.build_bound
