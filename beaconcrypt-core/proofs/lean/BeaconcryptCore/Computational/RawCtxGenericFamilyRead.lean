import BeaconcryptCore.Computational.RawCtxGenericRoleFamily

/-!
A private typed read request retains the original finite-family owner and read kind together with the actual optional selected kernel. Its dependent reply is exactly the original source optional current chain or skipped material. The native reader forwards the extracted lookup result and rejects absent kernels. Kernel representation conversion preserves this whole reply. Reads contribute one read-interface attempt and no additional uniform requests, without claiming zero deterministic lookup or copying work.

The actual family frontend must supply the selected kernel and retain the original read history. The read payload is private interpreter state, not an adversary-visible secret. Hidden-input masking and freshness require their own consuming reader and source correspondence; these representation statements do not supply them. Snapshots and persistence are excluded.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxGenericFamilyRead
open RawCtxGenericRoleFamily RawCtxProtocolReveals

def requestOwner {serverCount beaconCount : Nat} : Request serverCount beaconCount → Owner serverCount beaconCount
  | .sendChain owner | .receiveChain owner | .skippedKey owner _ => owner

abbrev ReadInput (Kernel : Type) (serverCount beaconCount : Nat) :=
  Request serverCount beaconCount × Option Kernel

def ReadSpec (Kernel : Type) (serverCount beaconCount : Nat) : OracleSpec (ReadInput Kernel serverCount beaconCount) :=
  fun request => (RevealSpec serverCount beaconCount).Range request.1

noncomputable def nativeValue {Kernel : Type} {serverCount beaconCount : Nat}
    (interpret : Kernel → ConcreteRatchetKernel) :
    (input : ReadInput Kernel serverCount beaconCount) → (ReadSpec Kernel serverCount beaconCount).Range input
  | (.sendChain _, none) => .None
  | (.sendChain _, some kernel) => .Some (interpret kernel).refined.send_chain
  | (.receiveChain _, none) => .None
  | (.receiveChain _, some kernel) => .Some (interpret kernel).refined.receive_chain
  | (.skippedKey _ _, none) => .None
  | (.skippedKey _ sequence, some kernel) => RawCtxProtocolReveals.skippedKey (interpret kernel) sequence

noncomputable def nativeReader {Kernel : Type} {serverCount beaconCount : Nat} {m : Type → Type*} [Monad m]
    (interpret : Kernel → ConcreteRatchetKernel) : QueryImpl (ReadSpec Kernel serverCount beaconCount) m :=
  fun input => pure (nativeValue interpret input)

/-- The typed family read returns the actual source optional value at the original requested owner. -/
theorem source_value {Kernel Metadata PeerMetadata Identity DhPair KemPair : Type} {serverCount beaconCount : Nat}
    (interpret : Kernel → ConcreteRatchetKernel) (request : Request serverCount beaconCount)
    (roles : RawCtxGenericRoleFamily.Roles Kernel Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount) :
    nativeValue interpret (request, RawCtxGenericRoleFamily.selectedKernel (requestOwner request) roles) =
      reveal request (nativeRoles interpret roles) := by
  cases request with
  | sendChain owner =>
      simp only [nativeValue, requestOwner, reveal, native_selected]
      cases RawCtxGenericRoleFamily.selectedKernel owner roles <;> rfl
  | receiveChain owner =>
      simp only [nativeValue, requestOwner, reveal, native_selected]
      cases RawCtxGenericRoleFamily.selectedKernel owner roles <;> rfl
  | skippedKey owner sequence =>
      simp only [nativeValue, requestOwner, reveal, native_selected]
      cases RawCtxGenericRoleFamily.selectedKernel owner roles <;> rfl

/-- Private representation conversion leaves every actual optional read value unchanged. -/
theorem map_value {Kernel Other : Type} {serverCount beaconCount : Nat}
    (convert : Kernel → Other) (interpret : Other → ConcreteRatchetKernel)
    (input : ReadInput Kernel serverCount beaconCount) :
    nativeValue interpret (input.1, input.2.map convert) = nativeValue (interpret ∘ convert) input := by
  rcases input with ⟨request, kernel⟩
  cases request <;> cases kernel <;> rfl

/-- The actual native read makes no uniform request; its deterministic lookup and copying remain actual work. -/
theorem native_uniform {Kernel : Type} {serverCount beaconCount : Nat}
    (interpret : Kernel → ConcreteRatchetKernel) (input : ReadInput Kernel serverCount beaconCount) :
    (nativeReader (m := ProbComp) interpret input).IsTotalQueryBound 0 := by
  trivial

/-- Each forwarded live-read attempt spends one read-interface query, including rejection and repetition. -/
theorem query_total {Kernel : Type} {serverCount beaconCount : Nat}
    (input : ReadInput Kernel serverCount beaconCount) :
    (liftM ((ReadSpec Kernel serverCount beaconCount).query input) :
      OracleComp (ReadSpec Kernel serverCount beaconCount) _).IsTotalQueryBound 1 := by
  exact (isQueryBound_query_iff _ _ _ _).mpr (by decide)

end BeaconcryptCore.Computational.RawCtxGenericFamilyRead

/-- info: 'BeaconcryptCore.Computational.RawCtxGenericFamilyRead.source_value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxGenericFamilyRead.source_value

/-- info: 'BeaconcryptCore.Computational.RawCtxGenericFamilyRead.map_value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxGenericFamilyRead.map_value

/-- info: 'BeaconcryptCore.Computational.RawCtxGenericFamilyRead.native_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxGenericFamilyRead.native_uniform

/-- info: 'BeaconcryptCore.Computational.RawCtxGenericFamilyRead.query_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxGenericFamilyRead.query_total

