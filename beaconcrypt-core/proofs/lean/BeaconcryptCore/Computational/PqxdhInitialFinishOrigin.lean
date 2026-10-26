import BeaconcryptCore.Computational.PqxdhInitialGenericBeacon

/-!
The original Beacon finish privately records a marker derived from its actual prepared initializer request only when that same source finish publishes successfully. The marker is not returned to the original client. Failed preparation, initialization, first receive, authentication and inactive phases keep their original results. Erasing the marker is literal program equality, so the instrumentation cannot create a successful installation or replace its session origin by its owner index.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialFinishOrigin
open RawCtxGenericRoleStorage PqxdhBeaconPhase2Shared PqxdhInitialGenericBeacon
variable {Kernel Other Origin I D K X Response Shared : Type}

abbrev Result (Kernel Origin I D K : Type) :=
  (Option Pqxdh.Bytes × BeaconState Kernel I D K) × Option Origin

def tag (origin : Origin) (result : Option Pqxdh.Bytes × BeaconState Kernel I D K) : Result Kernel Origin I D K :=
  (result, result.1.map (fun _ => origin))

section Effects
variable {m : Type → Type*} [Monad m]

noncomputable def owner (mark : Secrets Shared → Origin)
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) m)
    (calls : RawCtxChainOwner.Calls Kernel m) (application : Response → m (Option Pqxdh.Bytes))
    (initial : Secrets Shared → m (Option Kernel)) (decode : RawCtxReceive.FrameDecoder)
    (raw : Pqxdh.Bytes) (state : BeaconState Kernel I D K) : m (Result Kernel Origin I D K) :=
  match state.beacon.phase with
  | .initSent control prekey oneTime kem => do
      let prepared ← simulateQ pre (PqxdhBeaconPhase2Shared.prepare control state.beacon.identity prekey oneTime kem raw)
      match prepared with
      | none => pure (finish control state none, none)
      | some prepared => do
          let staged ← tail calls application initial decode prepared
          pure (tag (mark prepared.root) (finish control state staged))
  | _ => pure ((none, state), none)

variable [LawfulMonad m]

/-- Erasing only the private installation marker recovers the exact complete original finish program. -/
theorem erase (mark : Secrets Shared → Origin)
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) m)
    (calls : RawCtxChainOwner.Calls Kernel m) (application : Response → m (Option Pqxdh.Bytes))
    (initial : Secrets Shared → m (Option Kernel)) (decode : RawCtxReceive.FrameDecoder)
    (raw : Pqxdh.Bytes) (state : BeaconState Kernel I D K) :
    Prod.fst <$> owner mark pre calls application initial decode raw state =
      PqxdhInitialGenericBeacon.owner pre calls application initial decode raw state := by
  unfold owner PqxdhInitialGenericBeacon.owner
  cases phase : state.beacon.phase
  case initSent control prekey oneTime kem =>
    simp only [map_bind]
    apply bind_congr
    intro prepared
    cases prepared with
    | none => simp only [map_pure]
    | some prepared => simp only [map_bind, map_pure, tag]
  all_goals simp only [map_pure]

/-- The same actual initializer marker is retained under the private kernel interpretation, including complete first-receive and publication effects. -/
theorem owner_map (interpret : Kernel → Other) (mark : Secrets Shared → Origin)
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) m)
    (calls : RawCtxChainOwner.Calls Kernel m) (otherCalls : RawCtxChainOwner.Calls Other m)
    (receiveMap : ∀ entry target context, otherCalls.receive (interpret entry) target context =
      Prod.map interpret id <$> calls.receive entry target context)
    (application : Response → m (Option Pqxdh.Bytes))
    (initial : Secrets Shared → m (Option Kernel)) (otherInitial : Secrets Shared → m (Option Other))
    (initialMap : ∀ secrets, otherInitial secrets = Option.map interpret <$> initial secrets)
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes) (state : BeaconState Kernel I D K) :
    owner mark pre otherCalls application otherInitial decode raw (mapBeacon interpret state) =
      Prod.map (Prod.map id (mapBeacon interpret)) id <$> owner mark pre calls application initial decode raw state := by
  unfold owner
  simp only [mapBeacon]
  cases phase : state.beacon.phase
  case initSent control prekey oneTime kem =>
    simp only [mapPhase, map_bind]
    apply bind_congr
    intro prepared
    cases prepared with
    | none => simp only [map_pure]; rfl
    | some prepared =>
      dsimp only
      rw [tail_map interpret calls otherCalls receiveMap application initial otherInitial initialMap]
      simp only [bind_map_left, map_bind, map_pure]
      apply bind_congr
      intro staged
      apply congrArg pure
      change tag (mark prepared.root) (finish control (mapBeacon interpret state) (staged.map (mapStaged interpret))) = _
      rw [finish_map]
      rfl
  all_goals simp only [mapPhase, map_pure, Prod.map, mapBeacon, phase, id_eq]

end Effects

/-- Every recorded installation marker comes from the actual supported preparation and full first-receive tail that published this exact returned Beacon state. -/
theorem origin {State : Type} (mark : Secrets Shared → Origin)
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (StateT State ProbComp))
    (calls : RawCtxChainOwner.Calls Kernel (StateT State ProbComp))
    (application : Response → StateT State ProbComp (Option Pqxdh.Bytes))
    (initial : Secrets Shared → StateT State ProbComp (Option Kernel)) (decode : RawCtxReceive.FrameDecoder)
    (raw : Pqxdh.Bytes) (entry : BeaconState Kernel I D K) (before : State)
    (result : Result Kernel Origin I D K × State)
    (supported : result ∈ support ((owner mark pre calls application initial decode raw entry).run before))
    (marker : Origin) (recorded : result.1.2 = some marker) :
    ∃ control prekey oneTime kem, ∃ (prepared : Prepared Response Shared) (atTail : State) (staged : Option (Staged Kernel)),
      entry.beacon.phase = .initSent control prekey oneTime kem ∧
      (some prepared, atTail) ∈ support ((simulateQ pre
        (PqxdhBeaconPhase2Shared.prepare control entry.beacon.identity prekey oneTime kem raw)).run before) ∧
      (staged, result.2) ∈ support ((tail calls application initial decode prepared).run atTail) ∧
      result.1.1 = finish control entry staged ∧ result.1.1.1.isSome = true ∧ marker = mark prepared.root := by
  unfold owner at supported
  cases phase : entry.beacon.phase
  case initSent control prekey oneTime kem =>
    simp only [phase, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨prepared, preReached, rest⟩ := supported
    cases preparedFound : prepared.1 with
    | none =>
      simp only [preparedFound, StateT.run_pure, mem_support_pure_iff] at rest
      subst result
      cases recorded
    | some pending =>
      simp only [preparedFound, StateT.run_bind, mem_support_bind_iff] at rest
      obtain ⟨staged, tailReached, final⟩ := rest
      simp only [StateT.run_pure, mem_support_pure_iff] at final
      subst result
      simp only [tag] at recorded
      obtain ⟨bytes, published, markerEq⟩ := Option.map_eq_some_iff.mp recorded
      exact ⟨control, prekey, oneTime, kem, pending, prepared.2, staged.1, rfl,
        by simpa only [← preparedFound] using preReached, tailReached, rfl,
        by simp only [tag, published, Option.isSome_some], markerEq.symm⟩
  all_goals
    simp only [phase, StateT.run_pure, mem_support_pure_iff] at supported
    subst result
    cases recorded

/-- An installation marker is present exactly when that same original finish returns its successful application reply. -/
theorem published {State : Type} (mark : Secrets Shared → Origin)
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (StateT State ProbComp))
    (calls : RawCtxChainOwner.Calls Kernel (StateT State ProbComp))
    (application : Response → StateT State ProbComp (Option Pqxdh.Bytes))
    (initial : Secrets Shared → StateT State ProbComp (Option Kernel)) (decode : RawCtxReceive.FrameDecoder)
    (raw : Pqxdh.Bytes) (entry : BeaconState Kernel I D K) (before : State)
    (result : Result Kernel Origin I D K × State)
    (supported : result ∈ support ((owner mark pre calls application initial decode raw entry).run before)) :
    result.1.2.isSome = result.1.1.1.isSome := by
  unfold owner at supported
  cases phase : entry.beacon.phase
  case initSent control prekey oneTime kem =>
    simp only [phase, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨prepared, preReached, rest⟩ := supported
    cases preparedFound : prepared.1 with
    | none =>
      simp only [preparedFound, StateT.run_pure, mem_support_pure_iff] at rest
      subst result
      rfl
    | some pending =>
      simp only [preparedFound, StateT.run_bind, mem_support_bind_iff] at rest
      obtain ⟨staged, tailReached, final⟩ := rest
      simp only [StateT.run_pure, mem_support_pure_iff] at final
      subst result
      simp only [tag, Option.isSome_map]
  all_goals
    simp only [phase, StateT.run_pure, mem_support_pure_iff] at supported
    subst result
    rfl

end BeaconcryptCore.Computational.PqxdhInitialFinishOrigin

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialFinishOrigin.erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialFinishOrigin.erase


/-- info: 'BeaconcryptCore.Computational.PqxdhInitialFinishOrigin.owner_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialFinishOrigin.owner_map


/-- info: 'BeaconcryptCore.Computational.PqxdhInitialFinishOrigin.origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialFinishOrigin.origin


/-- info: 'BeaconcryptCore.Computational.PqxdhInitialFinishOrigin.published' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialFinishOrigin.published
