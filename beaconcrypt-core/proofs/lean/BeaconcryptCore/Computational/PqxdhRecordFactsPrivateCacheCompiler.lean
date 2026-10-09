-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheServices

/-! Internal expansion of the actual hidden-record services into keyed and base-only requests. These requests are compiler plumbing, not additional adversarial capabilities. -/
open OracleComp OracleSpec
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheCompiler
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftIdeal (CtxPrivate KeyMode KeyedSpec onBase)
open PqxdhRecordLiftProtocol (Private Service ServiceSpec)
open PqxdhRecordFactsPrivateCacheFamily (uncountedKeyed observeFamily)
open PqxdhRecordFactsPrivateCacheServices (MixedSpec mixed erased)
open CtxRomAuth AdaptiveCtxReceive LazyOracleDiscard
variable {n : Nat}

/-- These internal operations expose the base state only to the trusted service compiler. -/
inductive BaseService (n : Nat) where
  | read
  | pending (frames : PqxdhRecordLiftLoggedAdapters.Frames)
  | service (query : Service n)

abbrev BaseSpec (n : Nat) : OracleSpec (BaseService n)
  | .read => Private n
  | .pending _ => Unit
  | .service query => (ServiceSpec n).Range query

/-- Literal base read, literal writer-buffer replacement, or the supplied source base service. -/
noncomputable def base (impl : QueryImpl (ServiceSpec n) (StateT (Private n) ProbComp)) :
    QueryImpl (BaseSpec n) (StateT (Private n) ProbComp)
  | .read => fun state => pure (state, state)
  | .pending frames => fun state => pure ((), { state with pending := frames })
  | .service q => impl q

/-- Inject a hidden coordinate request into the internal mixed interface. -/
def injectKey : QueryImpl (KeyedSpec n) (OracleComp (MixedSpec n (BaseSpec n))) :=
  fun q => (MixedSpec n (BaseSpec n)).query (.inl q)

/-- Compile each exact hidden service; every other source service remains one literal base call. -/
noncomputable def compile (writer : RawCtxMixedShared.Writer) (replace : Pqxdh.Bytes → Pqxdh.Bytes) :
    QueryImpl (ServiceSpec n) (OracleComp (MixedSpec n (BaseSpec n)))
  | .opening pending => do
      let state ← (MixedSpec n (BaseSpec n)).query (.inr .read)
      simulateQ injectKey (PqxdhRecordLiftIdeal.hiddenOpening
        (PqxdhRecordLiftProtocol.cachedSeeds state) state.chain pending)
  | .sealing pending => do
      let state ← (MixedSpec n (BaseSpec n)).query (.inr .read)
      let result ← simulateQ injectKey
        ((PqxdhRecordLiftIdeal.hiddenSealing writer state.chain replace pending).run state.pending)
      let _ ← (MixedSpec n (BaseSpec n)).query (.inr (.pending result.2))
      pure result.1
  | query => (MixedSpec n (BaseSpec n)).query (.inr (.service query))

/-- Injecting an arbitrary adaptive keyed program does not change its interpreter or continuation. -/
theorem inject_program (modes : Label n → KeyMode) (decode : RawDecoder) (crypto : Pqxdh.Crypto)
    (impl : QueryImpl (ServiceSpec n) (StateT (Private n) ProbComp)) {Result : Type}
    (client : OracleComp (KeyedSpec n) Result) :
    simulateQ (mixed modes decode crypto (base impl)) (simulateQ injectKey client) =
      simulateQ (uncountedKeyed modes decode crypto) client := by
  rw [← QueryImpl.simulateQ_compose]
  congr 1
  ext query
  simp only [QueryImpl.apply_compose, injectKey, simulateQ_spec_query, mixed]

private theorem apply_bind {σ α β : Type} (work : StateT σ ProbComp α)
    (next : α → StateT σ ProbComp β) (state : σ) :
    (work >>= next) state = (work state >>= fun result => next result.1 result.2) := rfl

/-- The compiled opening uses the current exact seeds/table and returns the actual optional plaintext with its entire private poststate. -/
theorem compile_opening (modes : Label n → KeyMode) (decode : RawDecoder) (crypto : Pqxdh.Crypto)
    (impl : QueryImpl (ServiceSpec n) (StateT (Private n) ProbComp))
    (writer : RawCtxMixedShared.Writer) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (pending : PqxdhRecordLiftProtocol.Opening n) (state : CtxPrivate n) :
    (simulateQ (mixed modes decode crypto (base impl))
      (compile writer replace (.opening pending))).run state =
    (simulateQ (uncountedKeyed modes decode crypto)
      (PqxdhRecordLiftIdeal.hiddenOpening (PqxdhRecordLiftProtocol.cachedSeeds state.base)
        state.base.chain pending)).run state := by
  simp only [compile, simulateQ_bind, simulateQ_spec_query, mixed, base,
    StateT.run, apply_bind, onBase, map_pure, pure_bind, inject_program]

/-- The compiled seal retains the literal frame buffer even when the writer returns failure, and changes no other base field on buffer reinstallation. -/
theorem compile_sealing (modes : Label n → KeyMode) (decode : RawDecoder) (crypto : Pqxdh.Crypto)
    (impl : QueryImpl (ServiceSpec n) (StateT (Private n) ProbComp))
    (writer : RawCtxMixedShared.Writer) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (pending : PqxdhRecordLiftProtocol.Sealing n) (state : CtxPrivate n) :
    (simulateQ (mixed modes decode crypto (base impl))
      (compile writer replace (.sealing pending))).run state =
    ((simulateQ (uncountedKeyed modes decode crypto)
      ((PqxdhRecordLiftIdeal.hiddenSealing writer state.base.chain replace pending).run state.base.pending)).run state
      >>= fun result => pure (result.1.1, { result.2 with base := { result.2.base with pending := result.1.2 } })) := by
  simp only [compile, simulateQ_bind, simulateQ_spec_query, simulateQ_pure, mixed, base,
    StateT.run, apply_bind, onBase, map_pure, pure_bind, inject_program]
  rfl

/-- Every service agrees with the corresponding original CTX service shape; no assumption about the supplied base service is used. -/
theorem compile_service (modes : Label n → KeyMode) (decode : RawDecoder) (crypto : Pqxdh.Crypto)
    (impl : QueryImpl (ServiceSpec n) (StateT (Private n) ProbComp))
    (writer : RawCtxMixedShared.Writer) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (query : Service n) (state : CtxPrivate n) :
    (simulateQ (mixed modes decode crypto (base impl)) (compile writer replace query)).run state =
    ((match query with
      | .opening pending => fun current =>
          (simulateQ (uncountedKeyed modes decode crypto)
            (PqxdhRecordLiftIdeal.hiddenOpening (PqxdhRecordLiftProtocol.cachedSeeds current.base)
              current.base.chain pending)).run current
      | .sealing pending => fun current => do
          let result ← (simulateQ (uncountedKeyed modes decode crypto)
            ((PqxdhRecordLiftIdeal.hiddenSealing writer current.base.chain replace pending).run current.base.pending)).run current
          pure (result.1.1, { result.2 with base := { result.2.base with pending := result.1.2 } })
      | other => onBase (impl other)) : StateT (CtxPrivate n) ProbComp ((ServiceSpec n).Range query)).run state := by
  cases query with
  | opening pending => exact compile_opening modes decode crypto impl writer replace pending state
  | sealing pending => exact compile_sealing modes decode crypto impl writer replace pending state
  | _ => simp only [compile, simulateQ_spec_query, mixed, base]

/-- The erased service is the same compiler with only discarded raw private-cache completions removed. -/
noncomputable def erasedInterpreter (modes : Label n → KeyMode) (decode : RawDecoder) (crypto : Pqxdh.Crypto)
    (impl : QueryImpl (ServiceSpec n) (StateT (Private n) ProbComp))
    (writer : RawCtxMixedShared.Writer) (replace : Pqxdh.Bytes → Pqxdh.Bytes) :
    QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp) :=
  erased modes decode crypto (base impl) ∘ₛ compile writer replace

/-- Discarding private suffix-cache completions preserves complete adaptive source-service observations, including the returned result, base state and every coordinate's local history. -/
theorem compiled_observation (modes : Label n → KeyMode) (decode : RawDecoder) (crypto : Pqxdh.Crypto)
    (impl : QueryImpl (ServiceSpec n) (StateT (Private n) ProbComp))
    (writer : RawCtxMixedShared.Writer) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (supported : ∀ label, modes label ≠ .real) {Result : Type}
    (client : OracleComp (ServiceSpec n) Result) (state : CtxPrivate n) :
    LawEq (Prod.map id observeFamily <$>
      (simulateQ (mixed modes decode crypto (base impl)) (simulateQ (compile writer replace) client)).run state)
      (Prod.map id observeFamily <$>
        (simulateQ (erasedInterpreter modes decode crypto impl writer replace) client).run state) := by
  simpa only [erasedInterpreter, QueryImpl.simulateQ_compose] using
    PqxdhRecordFactsPrivateCacheServices.mixed_observation modes decode crypto (base impl) supported
      (simulateQ (compile writer replace) client) state

end BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheCompiler

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheCompiler.inject_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheCompiler.inject_program

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheCompiler.compile_opening' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheCompiler.compile_opening

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheCompiler.compile_sealing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheCompiler.compile_sealing

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheCompiler.compile_service' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheCompiler.compile_service

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheCompiler.compiled_observation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheCompiler.compiled_observation
