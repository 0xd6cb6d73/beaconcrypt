-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterSealStateful
import BeaconcryptCore.Refinement.AdapterSealTag

/-! A typed native AEAD reply supplies its actual sixteen-byte tag. The source dispatcher still executes the original optional/result gates and tag conversion, while its allocator remains a separate dynamic request. This bridge retains all primitive/allocator failures and shared state; it assumes no source, parser or security conclusion. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Refinement.AdapterSealNative
variable [primitives : AdapterSealPrimitive.Operations]

abbrev NativeReply := RustM (core.result.Result (alloc.vec.Vec U8 × Std.Array U8 16#usize) primitives.Error)
abbrev SourceReply := RustM (core.result.Result (alloc.vec.Vec U8 × alloc.vec.Vec U8) primitives.Error)
abbrev Output := core.option.Option (alloc.vec.Vec U8 × Std.Array U8 16#usize)

def embed (result : NativeReply) : SourceReply := do
  let reply ← result
  match reply with
  | .Err error => .ok (.Err error)
  | .Ok (ciphertext, tag) => .ok (.Ok (ciphertext, Std.Array.to_slice tag))

def finish (result : NativeReply) : RustM Output := do
  let reply ← result
  match reply with
  | .Err _ => .ok .none
  | .Ok value => .ok (.some value)

def sourceTail (result : SourceReply) : RustM Output := do
  let reply ← result
  let optional ← core.result.Result.ok reply
  match optional with
  | .none => .ok .none
  | .some (ciphertext, tag) =>
      let bytes ← alloc.vec.Vec.as_slice tag
      let adapted ← core.Array.Insts.CoreConvertTryFromShared0SliceTryFromSliceError.try_from
        16#usize core.U8.Insts.CoreMarkerCopy bytes
      let optional ← core.result.Result.ok adapted
      match optional with
      | .none => .ok .none
      | .some tag => .ok (.some (ciphertext, tag))

theorem tag_exact (result : NativeReply) : sourceTail (embed result) = finish result := by
  cases result with
  | fail error => rfl
  | div => rfl
  | ok reply =>
      cases reply with
      | Err error => rfl
      | Ok pair =>
          rcases pair with ⟨ciphertext, tag⟩
          change (do
            let adapted ← core.Array.Insts.CoreConvertTryFromShared0SliceTryFromSliceError.try_from
              16#usize core.U8.Insts.CoreMarkerCopy (Std.Array.to_slice tag)
            let optional ← core.result.Result.ok adapted
            match optional with
            | .none => .ok .none
            | .some tag => .ok (.some (ciphertext, tag)) : RustM Output) = _
          rw [AdapterSealTag.try_from_array]
          rfl

inductive Request where
  | reserve (before : alloc.vec.Vec U8) (capacity : Usize)
  | aead (plaintext : Slice U8) (associated : core.option.Option (Slice U8))
      (nonce : primitives.Nonce) (key : primitives.Key)

abbrev Spec (E : Type) : OracleSpec Request
  | .reserve _ _ => RustM (core.result.Result Unit E × alloc.vec.Vec U8)
  | .aead _ _ _ _ => NativeReply

def native {E : Type} : QueryImpl (AdapterSealRequestMonad.Spec E) (OracleComp (Spec E))
  | .reserve before capacity => (Spec E).query (.reserve before capacity)
  | .aead plaintext associated nonce key => embed <$>
      ((Spec E).query (.aead plaintext associated nonce key) : OracleComp (Spec E) NativeReply)

def source (E : Type) (request : record_effects.AeadSealRequest) : OracleComp (Spec E) (RustM Output) :=
  simulateQ native (AdapterSealRequestExtraction.execute (E := E) (m := AdapterSealRequestMonad.Program E) request).run

def continueWith {E A : Type} (result : RustM A)
    (next : A → OracleComp (Spec E) (RustM Output)) : OracleComp (Spec E) (RustM Output) :=
  match result with
  | .ok value => next value
  | .fail error => pure (.fail error)
  | .div => pure .div

def joined (E : Type) (prefixBytes : Std.Array U8 8#usize) (application : Slice U8) :
    OracleComp (Spec E) (RustM (core.option.Option (alloc.vec.Vec U8))) :=
  simulateQ native (AdapterSealRequestMonad.Lifted.join (E := E) (m := AdapterSealRequestMonad.Program E)
    (Std.Array.make 2#usize [Std.Array.to_slice prefixBytes, application])).run

def aead (E : Type) (plaintext : Slice U8) (associated : Std.Array U8 151#usize)
    (nonce : primitives.Nonce) (key : primitives.Key) : OracleComp (Spec E) (RustM Output) :=
  finish <$> ((Spec E).query (.aead plaintext (.some (Std.Array.to_slice associated)) nonce key) :
    OracleComp (Spec E) NativeReply)

def execute (E : Type) (request : record_effects.AeadSealRequest) : OracleComp (Spec E) (RustM Output) :=
  continueWith (AdapterSealRequestMonad.Lifted.key (m := RustM) request.key) fun key =>
    continueWith (AdapterSealRequestMonad.Lifted.nonce (m := RustM) request.nonce) fun nonce =>
      match request.plaintext with
      | .Single plaintext => aead E plaintext request.associated_data nonce key
      | .Prefixed prefixBytes application => do
          let result ← joined E prefixBytes application
          continueWith result fun optional => match optional with
          | .none => pure (.ok .none)
          | .some plaintext => aead E plaintext request.associated_data nonce key

private def aeadProgram (E : Type) (plaintext : Slice U8) (associated : Std.Array U8 151#usize)
    (nonce : primitives.Nonce) (key : primitives.Key) : AdapterSealRequestMonad.Program E Output := do
  let associated ← AdapterSealRequestMonad.Lifted.arraySlice associated
  let reply ← AdapterSealRequestMonad.Operations.aead (E := E) plaintext (core.option.Option.Some associated) nonce key
  let optional ← AdapterSealRequestMonad.Lifted.resultOk reply
  let branch ← AdapterSealRequestMonad.Lifted.branch optional
  match branch with
  | .Continue value =>
      let bytes ← AdapterSealRequestMonad.Lifted.slice value.2
      let adapted ← AdapterSealRequestMonad.Lifted.tag bytes
      let optional ← AdapterSealRequestMonad.Lifted.resultOk adapted
      let branch ← AdapterSealRequestMonad.Lifted.branch optional
      match branch with
      | .Continue tag => pure (core.option.Option.Some (value.1, tag))
      | .Break residual => AdapterSealRequestMonad.Lifted.fromResidual residual
  | .Break residual => AdapterSealRequestMonad.Lifted.fromResidual residual

private theorem aead_body (E : Type) (plaintext : Slice U8) (associated : Std.Array U8 151#usize)
    (nonce : primitives.Nonce) (key : primitives.Key) :
    simulateQ native (aeadProgram E plaintext associated nonce key).run = aead E plaintext associated nonce key := by
  unfold aeadProgram
  simp only [AdapterSealRequestMonad.Lifted.arraySlice, core.array.Array.as_slice,
    rust_primitives.slice.array_as_slice,
    AdapterSealRequestMonad.Program.run_bind, AdapterSealRequestMonad.Program.run_lift, pure_bind]
  simp only [AdapterSealRequestMonad.Operations.aead, AdapterSealRequestMonad.Program.query,
    simulateQ_bind, simulateQ_spec_query, native, bind_map_left]
  unfold aead
  rw [← bind_pure_comp]
  apply bind_congr
  intro result
  cases result with
  | fail error => rfl
  | div => rfl
  | ok reply =>
      cases reply with
      | Err error => rfl
      | Ok pair =>
          rcases pair with ⟨ciphertext, tag⟩
          simp only [embed, AdapterSealRequestMonad.Lifted.resultOk,
            AdapterSealRequestMonad.Lifted.branch, AdapterSealRequestMonad.Lifted.slice,
            AdapterSealRequestMonad.Lifted.tag, AdapterSealRequestMonad.Lifted.fromResidual,
            AdapterSealRequestMonad.Program.run_lift, pure_bind]
          simp only [bind_tc_ok, core.result.Result.ok,
            core.option.Option.Insts.CoreOpsTry_traitTry.branch, alloc.vec.Vec.as_slice,
            core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
            rust_primitives.sequence.seq_to_slice,
            AdapterSealRequestMonad.Program.run_bind, AdapterSealRequestMonad.Program.run_lift,
            pure_bind]
          rw [AdapterSealTag.try_from_array]
          rfl

theorem source_native (E : Type) (request : record_effects.AeadSealRequest) : source E request = execute E request := by
  unfold source AdapterSealRequestExtraction.execute execute
  simp only [AdapterSealRequestMonad.Lifted.key, AdapterSealRequestMonad.Lifted.nonce,
    AdapterSealRequestMonad.Program.run_bind,
    pure_bind, AdapterRecordRequestMonad.liftRust]
  cases core.convert.Into.Blanket.into
      beaconcrypt_crypto.crypto_aead.chacha20poly1305_ietf.Key.Insts.CoreConvertFromArrayU832 request.key with
  | fail error => rfl
  | div => rfl
  | ok key =>
      cases core.convert.Into.Blanket.into
          beaconcrypt_crypto.crypto_aead.chacha20poly1305_ietf.Nonce.Insts.CoreConvertFromArrayU812 request.nonce with
      | fail error => rfl
      | div => rfl
      | ok nonce =>
          dsimp only [continueWith]
          cases request.plaintext with
          | Single plaintext =>
              dsimp only
              change simulateQ native (aeadProgram E plaintext request.associated_data nonce key).run = _
              exact aead_body E plaintext request.associated_data nonce key
          | Prefixed prefixBytes application =>
              dsimp only
              simp only [AdapterSealRequestMonad.Lifted.arraySlice, core.array.Array.as_slice,
                rust_primitives.slice.array_as_slice, AdapterSealRequestMonad.Program.run_bind,
                AdapterSealRequestMonad.Program.run_lift, pure_bind, simulateQ_bind]
              unfold joined
              apply bind_congr
              intro result
              cases result with
              | fail error => rfl
              | div => rfl
              | ok optional =>
                  cases optional with
                  | none => rfl
                  | some plaintext =>
                      simp only [AdapterSealRequestMonad.Lifted.branch,
                        core.option.Option.Insts.CoreOpsTry_traitTry.branch,
                        core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
                        AdapterSealRequestMonad.Lifted.protect, zeroize.Zeroizing.new,
                        AdapterSealRequestMonad.Lifted.optionRef, core.option.Option.as_ref,
                        AdapterSealRequestMonad.Lifted.deref, zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
                        AdapterSealRequestMonad.Lifted.slice, alloc.vec.Vec.as_slice,
                        rust_primitives.sequence.seq_to_slice,
                        AdapterSealRequestMonad.Program.run_bind, AdapterSealRequestMonad.Program.run_lift,
                        pure_bind]
                      change simulateQ native (aeadProgram E plaintext request.associated_data nonce key).run = _
                      exact aead_body E plaintext request.associated_data nonce key

theorem shared {E σ ι : Type} {base : OracleSpec ι}
    (implementation : QueryImpl (Spec E) (StateT σ (OracleComp base)))
    (request : record_effects.AeadSealRequest) :
    AdapterSealStateful.execute (implementation ∘ₛ native) request =
      simulateQ implementation (execute E request) := by
  unfold AdapterSealStateful.execute
  rw [QueryImpl.simulateQ_compose]
  exact congrArg (simulateQ implementation) (source_native E request)

theorem shared_joint {E σ ι : Type} {base : OracleSpec ι}
    (implementation : QueryImpl (Spec E) (StateT σ (OracleComp base)))
    (request : record_effects.AeadSealRequest) (before : σ) :
    (AdapterSealStateful.execute (implementation ∘ₛ native) request).run before =
      (simulateQ implementation (execute E request)).run before := by
  rw [shared]

theorem shared_continuation {E σ ι Value : Type} {base : OracleSpec ι}
    (implementation : QueryImpl (Spec E) (StateT σ (OracleComp base)))
    (request : record_effects.AeadSealRequest)
    (next : RustM Output → StateT σ (OracleComp base) Value) (before : σ) :
    ((AdapterSealStateful.execute (implementation ∘ₛ native) request >>= next).run before) = (do
      let result ← (simulateQ implementation (execute E request)).run before
      (next result.1).run result.2) := by
  rw [shared, StateT.run_bind]

end BeaconcryptCore.Refinement.AdapterSealNative

/-- info: 'BeaconcryptCore.Refinement.AdapterSealNative.tag_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterSealNative.tag_exact

/-- info: 'BeaconcryptCore.Refinement.AdapterSealNative.source_native' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterSealNative.source_native

/-- info: 'BeaconcryptCore.Refinement.AdapterSealNative.shared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterSealNative.shared

/-- info: 'BeaconcryptCore.Refinement.AdapterSealNative.shared_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterSealNative.shared_joint

/-- info: 'BeaconcryptCore.Refinement.AdapterSealNative.shared_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterSealNative.shared_continuation
