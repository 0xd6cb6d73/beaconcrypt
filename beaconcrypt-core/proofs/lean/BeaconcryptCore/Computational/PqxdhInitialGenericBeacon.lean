import BeaconcryptCore.Computational.PqxdhInitialFusedOwner
import BeaconcryptCore.Computational.RawCtxGenericOwnerMap
import BeaconcryptCore.Computational.RawCtxGenericRoleStorage

/-!
The first Beacon receive retains the original response getter, exact sequence-one and eight-byte binding checks, pinned-server checks and complete publication while making only the private kernel representation generic. Its private initializer returns an optional kernel, never a raw root. Preparation, role identities, private key fields, failed states and all ambient callback effects remain in source order.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialGenericBeacon
open RawCtxGenericRoleStorage PqxdhBeaconPhase2Shared
variable {Kernel Other I D K Response Shared : Type}

structure Staged (Kernel : Type) where
  authenticated : pqxdh.AuthenticatedBeaconRegistration
  associatedData : Array Std.U8 281#usize
  kernel : Kernel
  opened : RawCtxWholeOwner.Decrypted

def mapStaged (interpret : Kernel → Other) (staged : Staged Kernel) : Staged Other :=
  ⟨staged.authenticated, staged.associatedData, interpret staged.kernel, staged.opened⟩

noncomputable def afterOpening (candidate : pqxdh.BeaconRegistrationCandidate) (kernel : Kernel)
    (reply : core.option.Option RawCtxWholeOwner.Decrypted) : Option (Staged Kernel) :=
  match reply with
  | .None => none
  | .Some opened =>
      if opened.sequence ≠ 1#u64 then none
      else if length : 8 < opened.plaintext.length then
        match PqxdhBeaconPhase2Publication.normalAuthenticate candidate opened.keyId
          (BeaconcryptCore.Refinement.ProtocolComposition.plaintextBinding opened.plaintext length) with
        | .Err _ => none
        | .Ok authenticated => some ⟨authenticated, candidate.associated_data, kernel, opened⟩
      else none

def localOwner (candidate : pqxdh.BeaconRegistrationCandidate) (kernel : Kernel) : RawCtxChainOwner.State Kernel Unit :=
  ⟨kernel, candidate.server_binding.identity_key_id, PqxdhRefinement.absBytes candidate.associated_data, (), 0⟩

def abort (control : pqxdh.BeaconInitSent) (state : BeaconState Kernel I D K) : BeaconState Kernel I D K :=
  { state with beacon := { state.beacon with
      identityKeyId := control.expected_server_binding.identity_key_id
      phase := .aborted ⟨control.expected_server_binding.identity_key_id⟩ } }

def publish (state : BeaconState Kernel I D K) (staged : Staged Kernel) : Pqxdh.Bytes × BeaconState Kernel I D K :=
  (staged.opened.plaintext.drop 8, { state with beacon := { state.beacon with
    identityKeyId := staged.authenticated.candidate.assigned_key_id
    phase := .established
      ⟨staged.authenticated.candidate.server_binding, staged.authenticated.candidate.assigned_key_id⟩
      staged.associatedData staged.kernel } })

noncomputable def finish (control : pqxdh.BeaconInitSent) (state : BeaconState Kernel I D K)
    (staged : Option (Staged Kernel)) : Option Pqxdh.Bytes × BeaconState Kernel I D K :=
  match staged with
  | none => (none, abort control state)
  | some staged =>
      if control.expected_server_binding.identity_key_id ≠ staged.authenticated.candidate.server_binding.identity_key_id then
        (none, abort control state)
      else if PqxdhRefinement.absBytes state.beacon.serverIdentity ≠
          PqxdhRefinement.absBytes staged.authenticated.candidate.server_binding.identity_public_key then
        (none, abort control state)
      else let result := publish state staged; (some result.1, result.2)

/-- Changing the private kernel representation preserves the original sequence-one, plaintext-prefix and authentication branches exactly. -/
theorem opening_map (interpret : Kernel → Other) (candidate : pqxdh.BeaconRegistrationCandidate)
    (kernel : Kernel) (reply : core.option.Option RawCtxWholeOwner.Decrypted) :
    afterOpening candidate (interpret kernel) reply = (afterOpening candidate kernel reply).map (mapStaged interpret) := by
  cases reply with
  | none => rfl
  | some opened =>
      simp only [afterOpening]
      split
      · rfl
      · split
        · split <;> rfl
        · rfl

/-- Terminal abort and successful publication preserve every source field while changing only the private kernel representation. -/
theorem finish_map (interpret : Kernel → Other) (control : pqxdh.BeaconInitSent)
    (state : BeaconState Kernel I D K) (staged : Option (Staged Kernel)) :
    finish control (mapBeacon interpret state) (staged.map (mapStaged interpret)) =
      Prod.map id (mapBeacon interpret) (finish control state staged) := by
  cases staged with
  | none => rfl
  | some staged =>
      simp only [finish, Option.map_some, mapStaged, mapBeacon]
      split_ifs <;> simp_all [abort, publish, mapBeacon, mapPhase, Prod.map]

section Effects
variable {m : Type → Type*} [Monad m]

noncomputable def afterInitial (calls : RawCtxChainOwner.Calls Kernel m)
    (application : Response → m (Option Pqxdh.Bytes)) (decode : RawCtxReceive.FrameDecoder)
    (pending : Prepared Response Shared) (kernel : Kernel) : m (Option (Staged Kernel)) := do
  let raw ← application pending.response
  match raw with
  | none => pure none
  | some raw => do
      let result ← (RawCtxChainOwner.rawReceive calls decode raw).run (localOwner (clearedMetadata pending.metadata) kernel)
      pure (afterOpening (clearedMetadata pending.metadata) result.2.kernel result.1)

noncomputable def tail (calls : RawCtxChainOwner.Calls Kernel m)
    (application : Response → m (Option Pqxdh.Bytes)) (initialImpl : Secrets Shared → m (Option Kernel))
    (decode : RawCtxReceive.FrameDecoder) (pending : Prepared Response Shared) : m (Option (Staged Kernel)) := do
  let kernel ← initialImpl pending.root
  match kernel with
  | none => pure none
  | some kernel => afterInitial calls application decode pending kernel

noncomputable def owner {X : Type}
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) m)
    (calls : RawCtxChainOwner.Calls Kernel m) (application : Response → m (Option Pqxdh.Bytes))
    (initialImpl : Secrets Shared → m (Option Kernel)) (decode : RawCtxReceive.FrameDecoder)
    (raw : Pqxdh.Bytes) (state : BeaconState Kernel I D K) : m (Option Pqxdh.Bytes × BeaconState Kernel I D K) :=
  match state.beacon.phase with
  | .initSent control prekey oneTime kem => do
      let prepared ← simulateQ pre (PqxdhBeaconPhase2Shared.prepare control state.beacon.identity prekey oneTime kem raw)
      match prepared with
      | none => pure (finish control state none)
      | some prepared => do
          let staged ← tail calls application initialImpl decode prepared
          pure (finish control state staged)
  | _ => pure (none, state)

variable [LawfulMonad m]

/-- The original application callback and entire first raw receive preserve their optional plaintext and ambient effects under the kernel representation map. -/
theorem afterInitial_map (interpret : Kernel → Other) (calls : RawCtxChainOwner.Calls Kernel m)
    (otherCalls : RawCtxChainOwner.Calls Other m)
    (receiveMap : ∀ entry target context, otherCalls.receive (interpret entry) target context =
      Prod.map interpret id <$> calls.receive entry target context)
    (application : Response → m (Option Pqxdh.Bytes)) (decode : RawCtxReceive.FrameDecoder)
    (pending : Prepared Response Shared) (kernel : Kernel) :
    afterInitial otherCalls application decode pending (interpret kernel) =
      Option.map (mapStaged interpret) <$> afterInitial calls application decode pending kernel := by
  simp only [afterInitial, map_bind]
  apply bind_congr
  intro raw
  cases raw with
  | none => simp only [map_pure, Option.map_none]
  | some raw =>
      dsimp only
      rw [show localOwner (clearedMetadata pending.metadata) (interpret kernel) =
        RawCtxGenericOwnerMap.mapOwner interpret (localOwner (clearedMetadata pending.metadata) kernel) from rfl,
        RawCtxGenericOwnerMap.raw_map interpret calls otherCalls receiveMap]
      simp only [bind_map_left, map_bind, map_pure]
      apply bind_congr
      intro result
      exact congrArg pure (opening_map interpret _ _ _)

/-- The optional private initializer remains in source order, and its entire application/receive continuation maps the kernel representation. -/
theorem tail_map (interpret : Kernel → Other) (calls : RawCtxChainOwner.Calls Kernel m)
    (otherCalls : RawCtxChainOwner.Calls Other m)
    (receiveMap : ∀ entry target context, otherCalls.receive (interpret entry) target context =
      Prod.map interpret id <$> calls.receive entry target context)
    (application : Response → m (Option Pqxdh.Bytes))
    (initialImpl : Secrets Shared → m (Option Kernel))
    (otherInitial : Secrets Shared → m (Option Other))
    (initialMap : ∀ secrets, otherInitial secrets = Option.map interpret <$> initialImpl secrets)
    (decode : RawCtxReceive.FrameDecoder) (pending : Prepared Response Shared) :
    tail otherCalls application otherInitial decode pending =
      Option.map (mapStaged interpret) <$> tail calls application initialImpl decode pending := by
  simp only [tail, initialMap, bind_map_left, map_bind]
  apply bind_congr
  intro kernel
  cases kernel with
  | none => simp only [Option.map_none, map_pure]
  | some kernel => exact afterInitial_map interpret calls otherCalls receiveMap application decode pending kernel

/-- Complete original preparation, failures and publication preserve every phase and state field under the private-kernel map. -/
theorem owner_map {X : Type} (interpret : Kernel → Other)
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) m)
    (calls : RawCtxChainOwner.Calls Kernel m) (otherCalls : RawCtxChainOwner.Calls Other m)
    (receiveMap : ∀ entry target context, otherCalls.receive (interpret entry) target context =
      Prod.map interpret id <$> calls.receive entry target context)
    (application : Response → m (Option Pqxdh.Bytes))
    (initialImpl : Secrets Shared → m (Option Kernel))
    (otherInitial : Secrets Shared → m (Option Other))
    (initialMap : ∀ secrets, otherInitial secrets = Option.map interpret <$> initialImpl secrets)
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes) (state : BeaconState Kernel I D K) :
    owner pre otherCalls application otherInitial decode raw (mapBeacon interpret state) =
      Prod.map id (mapBeacon interpret) <$> owner pre calls application initialImpl decode raw state := by
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
      rw [tail_map interpret calls otherCalls receiveMap application initialImpl otherInitial initialMap]
      simp only [bind_map_left, map_bind, map_pure]
      apply bind_congr
      intro staged
      exact congrArg pure (finish_map interpret control state staged)
  all_goals simp only [mapPhase, map_pure, Prod.map, mapBeacon, phase, id_eq]

end Effects

end BeaconcryptCore.Computational.PqxdhInitialGenericBeacon
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialGenericBeacon.opening_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialGenericBeacon.opening_map

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialGenericBeacon.finish_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialGenericBeacon.finish_map

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialGenericBeacon.afterInitial_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialGenericBeacon.afterInitial_map

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialGenericBeacon.tail_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialGenericBeacon.tail_map

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialGenericBeacon.owner_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialGenericBeacon.owner_map
