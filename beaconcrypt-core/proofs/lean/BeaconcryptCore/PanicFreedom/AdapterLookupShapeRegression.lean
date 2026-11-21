-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.PanicFreedom.AdapterPublicOrdinary

/-! An adversarial external map interpretation satisfies the reached borrow-shape contract while its unused shape-changing updates expose an invalid remote. The actual extracted public operations retain their normal rejection and returned-state guarantees. This model tests the safety interface; it makes no native container-correspondence claim. -/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.PanicFreedom.AdapterLookupShapeRegression
open Refinement AdapterNormal AdapterPublicOrdinary beaconcrypt_public_wrapper

@[instance_reducible] private def platform : PublicWrapperPlatform.Platform where
  Arc := fun T => T
  arcView := id
  Hasher := Unit
  HashState := Unit
  Allocator := Unit
  Map := fun _ V _ _ => core.option.Option V × core.option.Option V
  Set := fun _ _ _ => Unit
  Occupied := fun _ _ _ _ => Unit
  Vacant := fun _ _ _ _ => Unit
  ReserveError := Unit

attribute [local instance] platform

private def restore {V : Type} (selected hidden replacement : core.option.Option V) :
    core.option.Option V × core.option.Option V :=
  match selected, replacement with
  | none, none => (none, hidden)
  | some _, some changed => (some changed, hidden)
  | _, _ => (hidden, hidden)

private theorem restore_first {V : Type} (selected hidden replacement : core.option.Option V)
    (shape : SameOptionShape selected replacement) :
    (restore selected hidden replacement).1 = replacement := by
  cases selected <;> cases replacement <;> simp_all [SameOptionShape, restore]

@[instance_reducible] private def lookup [PublicWrapperPlatform.Allocator] : AdapterPublicOrdinaryPlatform.LookupOperations where
  get _ _ _ _ _ _ map _ := ok map.1
  getMut _ _ _ _ _ _ map _ := ok (map.1, restore map.1 map.2)

attribute [local instance] lookup

variable [PublicWrapperPlatform.Material] [AdapterInitEdPrimitive.Operations]
variable [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations]
variable [PublicWrapperPlatform.ContainerOperations]

private theorem valid_map_iff (map : PeerMap) : ValidMap map ↔ ValidOptionalRemote map.1 :=
  ⟨fun valid remote same => valid 0#u64 remote (congrArg ok same),
    fun valid _ remote returned => valid remote (RustM.ok.inj returned)⟩

/-- Only updates with the selected borrow shape are constrained by the safety interface. -/
theorem lookup_contracts : LookupContracts where
  get _ _ := ⟨_, rfl⟩
  getMut map _ valid :=
    ⟨(map.1, restore map.1 map.2), rfl, (valid_map_iff map).mp valid,
      fun replacement shape replacementValid =>
        (valid_map_iff _).mpr ((restore_first map.1 map.2 replacement shape).symm ▸ replacementValid)⟩

private def invalidRemote (remote : Remote) : Remote :=
  { remote with peer := { remote.peer with ratchet := ⟨⟨none⟩⟩ } }

omit [PublicWrapperPlatform.Material] [PublicWrapperPlatform.Allocator]
    [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
private theorem invalid_remote (remote : Remote) : ¬ ValidRemote (invalidRemote remote) :=
  fun ⟨_, impossible⟩ => by cases impossible

/-- A shape-changing update can expose an empty slot without violating the revised contract. -/
theorem shape_change_invalid (remote : Remote) :
    ¬ ValidMap (restore (some remote) (some (invalidRemote remote)) none) :=
  fun valid => invalid_remote remote ((valid_map_iff _).mp valid (invalidRemote remote) rfl)

/-- The former all-shapes external lens law is false in this otherwise admissible model. -/
theorem unrestricted_lens_law_false (remote : Remote) :
    ¬ (∀ replacement, ValidOptionalRemote replacement →
      ValidMap (restore (some remote) (some (invalidRemote remote)) replacement)) :=
  fun law => shape_change_invalid remote (law none (fun _ impossible => by cases impossible))

private def selectedServer (self : server.Server) (remote : Remote) : server.Server :=
  { self with known_ids := (some remote, some (invalidRemote remote)) }

private theorem selected_valid (self : server.Server) (remote : Remote) (valid : ValidRemote remote) :
    ValidServer (selectedServer self remote) :=
  (valid_map_iff _).mpr (fun _ same => by cases same; exact valid)

/-- The actual manager lens retains its stronger guarantee for every valid optional manager. -/
theorem borrow_preserves (self : server.Server) (remote : Remote) (key : U64) (valid : ValidRemote remote) :
    Ensures (beaconcrypt_public_ordinary.server.Server.ratchet_manager_mut (selectedServer self remote) key)
      (fun result => ValidOptionalManager result.1 ∧
        ∀ replacement, ValidOptionalManager replacement → ValidServer (result.2 replacement)) :=
  ratchet_manager_mut_preserves lookup_contracts _ key (selected_valid self remote valid)

variable [beaconcrypt_record_send.ratchet.Operations]

/-- The native public rejection restores the present remote and never uses the unsafe shape change. -/
theorem empty_message_rejects (self : server.Server) (remote : Remote) (key : U64) :
    beaconcrypt_public_ordinary.server.Server.encrypt_message (selectedServer self remote) (Slice.new U8) key =
      ok (none, selectedServer self remote) := rfl

/-- Native rejection returns a valid server even though the unused shape-changing lens is unsafe. -/
theorem empty_message_preserves (self : server.Server) (remote : Remote) (key : U64)
    (valid : ValidRemote remote) :
    Ensures (beaconcrypt_public_ordinary.server.Server.encrypt_message (selectedServer self remote) (Slice.new U8) key)
      (fun result => result.1 = none ∧ ValidServer result.2) :=
  ⟨_, empty_message_rejects self remote key, rfl, selected_valid self remote valid⟩

private def repeatEmpty (key : U64) : Nat → server.Server → RustM server.Server
  | 0, self => ok self
  | count + 1, self => do
    let (_, changed) ← beaconcrypt_public_ordinary.server.Server.encrypt_message self (Slice.new U8) key
    repeatEmpty key count changed

/-- Every finite sequence of these native rejections returns the same object. -/
theorem repeated_rejections (self : server.Server) (remote : Remote) (key : U64) (count : Nat) :
    repeatEmpty key count (selectedServer self remote) = ok (selectedServer self remote) :=
  Nat.rec rfl
    (fun _ previous => by simpa only [repeatEmpty, empty_message_rejects, bind_tc_ok, uncurry] using previous)
    count

/-- Rejection preserves the exact public valid-object invariant for every finite repetition count. -/
theorem repeated_rejections_preserve (self : server.Server) (remote : Remote) (key : U64)
    (count : Nat) (valid : ValidRemote remote) :
    Ensures (repeatEmpty key count (selectedServer self remote)) ValidServer :=
  ⟨_, repeated_rejections self remote key count, selected_valid self remote valid⟩

end BeaconcryptCore.PanicFreedom.AdapterLookupShapeRegression
