import BeaconcryptCore.Computational.PqxdhInitialGenericPost
import BeaconcryptCore.Computational.RawCtxPendingFamilyLiveQueries

/-!
The complete source post schedule compiles to explicit pending receive/send, live-read, preparation, application, initializer and selector requests. Frontend state contains only the full role family, controls and consumed identifiers. Shared primitives, the private identity interpreter and initializer cache stay in the interpreter, so no copied ambient state becomes stale. These source equations retain the complete original post continuation and add no secrecy premise.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialPendingPost
open PqxdhInitialGenericBeacon
variable {ι Chain Kernel M P I D K X Response Shared Result : Type}
variable {extra : OracleSpec ι} {S B : Nat}

section Interpretation
variable {κ : Type} {spec : OracleSpec κ} {m : Type → Type} [Monad m] [LawfulMonad m]

/-- The actual first raw receive and application getter commute with the same primitive interpreter, retaining all optional replies and effects. -/
theorem after_interpretation (impl : QueryImpl spec m)
    (calls : RawCtxChainOwner.Calls Kernel (OracleComp spec))
    (application : Response → OracleComp spec (Option Pqxdh.Bytes))
    (decode : RawCtxReceive.FrameDecoder)
    (pending : PqxdhBeaconPhase2Shared.Prepared Response Shared) (kernel : Kernel) :
    simulateQ impl (afterInitial calls application decode pending kernel) =
      afterInitial (RawCtxGenericOwnerInterpretation.interpretedCalls impl calls)
        (fun reply => simulateQ impl (application reply)) decode pending kernel := by
  simp only [afterInitial, simulateQ_bind]
  apply bind_congr
  intro raw
  cases raw with
  | none => exact simulateQ_pure _ _
  | some raw =>
      simp only [bind_pure_comp, simulateQ_map,
        RawCtxGenericOwnerInterpretation.raw_interpretation]

/-- Initializer replies remain before the complete first-receive tail under the same interpreter. -/
theorem tail_interpretation (impl : QueryImpl spec m)
    (calls : RawCtxChainOwner.Calls Kernel (OracleComp spec))
    (application : Response → OracleComp spec (Option Pqxdh.Bytes))
    (initial : PqxdhBeaconPhase2Shared.Secrets Shared → OracleComp spec (Option Kernel))
    (decode : RawCtxReceive.FrameDecoder)
    (pending : PqxdhBeaconPhase2Shared.Prepared Response Shared) :
    simulateQ impl (tail calls application initial decode pending) =
      tail (RawCtxGenericOwnerInterpretation.interpretedCalls impl calls)
        (fun reply => simulateQ impl (application reply))
        (fun secrets => simulateQ impl (initial secrets)) decode pending := by
  simp only [tail, simulateQ_bind]
  apply bind_congr
  intro kernel
  cases kernel with
  | none => exact simulateQ_pure _ _
  | some kernel => exact after_interpretation impl calls application decode pending kernel

/-- Every active or inactive Beacon attempt preserves full preparation, first receive and publication under literal source interpretation. -/
theorem owner_interpretation (impl : QueryImpl spec m)
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (OracleComp spec))
    (calls : RawCtxChainOwner.Calls Kernel (OracleComp spec))
    (application : Response → OracleComp spec (Option Pqxdh.Bytes))
    (initial : PqxdhBeaconPhase2Shared.Secrets Shared → OracleComp spec (Option Kernel))
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (state : RawCtxGenericRoleStorage.BeaconState Kernel I D K) :
    simulateQ impl (owner pre calls application initial decode raw state) =
      owner (impl ∘ₛ pre) (RawCtxGenericOwnerInterpretation.interpretedCalls impl calls)
        (fun reply => simulateQ impl (application reply))
        (fun secrets => simulateQ impl (initial secrets)) decode raw state := by
  unfold owner
  cases phase : state.beacon.phase
  case initSent control prekey oneTime kem =>
    simp only [simulateQ_bind, ← QueryImpl.simulateQ_compose]
    apply bind_congr
    intro prepared
    cases prepared with
    | none => exact simulateQ_pure _ _
    | some prepared =>
        simp only [bind_pure_comp, simulateQ_map, tail_interpretation]
  all_goals exact simulateQ_pure _ _

end Interpretation
abbrev KernelOf (Chain : Type) := RawCtxPendingOwnerQueries.Kernel Chain
abbrev External (extra : OracleSpec ι) (Chain I D K X Response Shared : Type) :=
  PqxdhBeaconPhase2Shared.Spec I D K X Response Shared +
    ((Response →ₒ Option Pqxdh.Bytes) +
      ((PqxdhBeaconPhase2Shared.Secrets Shared →ₒ Option (KernelOf Chain)) +
        (extra + PqxdhServerRegistrationPublication.AuxSpec)))
abbrev Spec (extra : OracleSpec ι) (Chain I D K X Response Shared : Type) (S B : Nat) :=
  RawCtxPendingFamilyLiveQueries.Spec Chain S B + External extra Chain I D K X Response Shared

structure Front (Chain M P I D K : Type) (S B : Nat) where
  roles : RawCtxGenericFamilyLive.State (KernelOf Chain) M P I D K S B
  controls : Fin S → pqxdh.ServerState
  consumed : Fin S → List Pqxdh.Bytes

def liveForward : QueryImpl (RawCtxPendingFamilyLiveQueries.Spec Chain S B)
    (OracleComp (Spec extra Chain I D K X Response Shared S B)) :=
  fun query => (Spec extra Chain I D K X Response Shared S B).query (.inl query)
def primitiveForward : QueryImpl (RawCtxPendingOwnerQueries.Spec Chain)
    (OracleComp (Spec extra Chain I D K X Response Shared S B)) :=
  fun query => (Spec extra Chain I D K X Response Shared S B).query (.inl (.inl query))
def preForward : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared)
    (OracleComp (Spec extra Chain I D K X Response Shared S B)) :=
  fun query => (Spec extra Chain I D K X Response Shared S B).query (.inr (.inl query))
def applicationForward (reply : Response) :
    OracleComp (Spec extra Chain I D K X Response Shared S B) (Option Pqxdh.Bytes) :=
  (Spec extra Chain I D K X Response Shared S B).query (.inr (.inr (.inl reply)))
def initialForward (secrets : PqxdhBeaconPhase2Shared.Secrets Shared) :
    OracleComp (Spec extra Chain I D K X Response Shared S B) (Option (KernelOf Chain)) :=
  (Spec extra Chain I D K X Response Shared S B).query (.inr (.inr (.inr (.inl secrets))))
def selectorForward : QueryImpl extra (OracleComp (Spec extra Chain I D K X Response Shared S B)) :=
  fun query => (Spec extra Chain I D K X Response Shared S B).query (.inr (.inr (.inr (.inr (.inl query)))))
def auxForward : QueryImpl PqxdhServerRegistrationPublication.AuxSpec
    (OracleComp (Spec extra Chain I D K X Response Shared S B)) :=
  fun query => (Spec extra Chain I D K X Response Shared S B).query (.inr (.inr (.inr (.inr (.inr query)))))

noncomputable def calls : RawCtxChainOwner.Calls (KernelOf Chain)
    (OracleComp (Spec extra Chain I D K X Response Shared S B)) :=
  RawCtxGenericOwnerInterpretation.interpretedCalls primitiveForward RawCtxPendingOwnerQueries.calls

def install (index : Fin B) (before : Front Chain M P I D K S B)
    (updated : RawCtxGenericRoleStorage.BeaconState (KernelOf Chain) I D K) : Front Chain M P I D K S B :=
  { before with roles := ((before.roles.1.1, Function.update before.roles.1.2 index updated),
      RawCtxProtocolReveals.tick before.roles.2) }

noncomputable def compiler (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) :
    QueryImpl (PqxdhInitialGenericPost.Spec extra S B)
      (StateT (Front Chain M P I D K S B) (OracleComp (Spec extra Chain I D K X Response Shared S B)))
  | .inl (.inl query) => fun before => do
      let result ← simulateQ liveForward ((RawCtxPendingFamilyLiveQueries.compiler sender route decode query).run before.roles)
      pure (result.1, { before with roles := result.2 })
  | .inl (.inr query) => fun before => do
      let reply ← selectorForward query
      pure (reply, before)
  | .inr (.finish index raw) => fun before => do
      let result ← owner preForward calls applicationForward initialForward decode raw (before.roles.1.2 index)
      pure (result.1, install index before result.2)

section Run
variable {m : Type → Type} [Monad m] [LawfulMonad m]

def handler
    (primitive : QueryImpl (RawCtxPendingOwnerQueries.Spec Chain) m)
    (reader : QueryImpl (RawCtxGenericFamilyRead.ReadSpec (KernelOf Chain) S B) m)
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) m)
    (application : Response → m (Option Pqxdh.Bytes))
    (initial : PqxdhBeaconPhase2Shared.Secrets Shared → m (Option (KernelOf Chain)))
    (selector : QueryImpl extra m) (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec m) :
    QueryImpl (Spec extra Chain I D K X Response Shared S B) m
  | .inl query => RawCtxPendingFamilyLiveQueries.handler primitive reader query
  | .inr (.inl query) => pre query
  | .inr (.inr (.inl reply)) => application reply
  | .inr (.inr (.inr (.inl secrets))) => initial secrets
  | .inr (.inr (.inr (.inr (.inl query)))) => selector query
  | .inr (.inr (.inr (.inr (.inr query)))) => aux query

noncomputable def interpreted
    (primitive : QueryImpl (RawCtxPendingOwnerQueries.Spec Chain) m)
    (reader : QueryImpl (RawCtxGenericFamilyRead.ReadSpec (KernelOf Chain) S B) m)
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) m)
    (application : Response → m (Option Pqxdh.Bytes))
    (initial : PqxdhBeaconPhase2Shared.Secrets Shared → m (Option (KernelOf Chain)))
    (selector : QueryImpl extra m)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder) :
    QueryImpl (PqxdhInitialGenericPost.Spec extra S B) (StateT (Front Chain M P I D K S B) m)
  | .inl (.inl query) => fun before => do
      let result ← (RawCtxGenericFamilyLive.impl
        (RawCtxGenericOwnerInterpretation.interpretedCalls primitive RawCtxPendingOwnerQueries.calls)
        (fun request => simulateQ primitive (RawCtxPendingOwnerQueries.publicForward request)) reader
        sender route decode query).run before.roles
      pure (result.1, { before with roles := result.2 })
  | .inl (.inr query) => fun before => do
      let reply ← selector query
      pure (reply, before)
  | .inr (.finish index raw) => fun before => do
      let result ← owner pre
        (RawCtxGenericOwnerInterpretation.interpretedCalls primitive RawCtxPendingOwnerQueries.calls)
        application initial decode raw (before.roles.1.2 index)
      pure (result.1, install index before result.2)

variable
    (primitive : QueryImpl (RawCtxPendingOwnerQueries.Spec Chain) m)
    (reader : QueryImpl (RawCtxGenericFamilyRead.ReadSpec (KernelOf Chain) S B) m)
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) m)
    (application : Response → m (Option Pqxdh.Bytes))
    (initial : PqxdhBeaconPhase2Shared.Secrets Shared → m (Option (KernelOf Chain)))
    (selector : QueryImpl extra m) (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec m)

private theorem calls_handler :
    RawCtxGenericOwnerInterpretation.interpretedCalls
      (handler primitive reader pre application initial selector aux) calls =
      RawCtxGenericOwnerInterpretation.interpretedCalls primitive RawCtxPendingOwnerQueries.calls := by
  have forwarding : handler primitive reader pre application initial selector aux ∘ₛ primitiveForward = primitive := by
    funext query
    simp [QueryImpl.compose, primitiveForward, handler, OracleSpec.query,
      RawCtxPendingFamilyLiveQueries.handler]
  simp only [calls, RawCtxGenericOwnerInterpretation.interpretedCalls, ← QueryImpl.simulateQ_compose, forwarding]

/-- Each original record, selector or attempted finish compiles to the same explicit callback sequence and complete frontend state. -/
theorem step_interpretation
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : (PqxdhInitialGenericPost.Spec extra S B).Domain)
    (before : Front Chain M P I D K S B) :
    simulateQ (handler primitive reader pre application initial selector aux)
      ((compiler sender route decode query).run before) =
      (interpreted primitive reader pre application initial selector sender route decode query).run before := by
  rcases query with (query | query) | query
  · simp only [compiler, interpreted, StateT.run, bind_pure_comp, simulateQ_map,
      ← QueryImpl.simulateQ_compose]
    have forwarding : handler primitive reader pre application initial selector aux ∘ₛ liveForward =
        RawCtxPendingFamilyLiveQueries.handler primitive reader := by
      funext request
      simp [QueryImpl.compose, liveForward, handler, OracleSpec.query]
    rw [forwarding]
    exact congrArg (fun work => (fun result => (result.1, { before with roles := result.2 })) <$> work)
      (RawCtxPendingFamilyLiveQueries.step_interpretation primitive reader sender route decode query before.roles)
  · simp [compiler, interpreted, StateT.run, bind_pure_comp, simulateQ_map,
      selectorForward, handler, OracleSpec.query]
  · cases query with
    | finish index raw =>
        simp only [compiler, interpreted, StateT.run, bind_pure_comp, simulateQ_map,
          owner_interpretation, calls_handler]
        have forwarding : handler primitive reader pre application initial selector aux ∘ₛ preForward = pre := by
          funext request
          simp [QueryImpl.compose, preForward, handler, OracleSpec.query]
        rw [forwarding]
        simp [applicationForward, initialForward, handler, OracleSpec.query]

/-- The full original adaptive post client remains present after every pending callback, including later selectors and new Beacon finishes. -/
theorem program_interpretation
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (PqxdhInitialGenericPost.Spec extra S B) Result)
    (before : Front Chain M P I D K S B) :
    simulateQ (handler primitive reader pre application initial selector aux)
      ((simulateQ (compiler sender route decode) client).run before) =
      (simulateQ (interpreted primitive reader pre application initial selector sender route decode) client).run before := by
  induction client using OracleComp.inductionOn generalizing before with
  | pure result => simp only [simulateQ_pure, StateT.run_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      rw [step_interpretation]
      exact bind_congr fun reply => ih reply.1 reply.2

end Run
end BeaconcryptCore.Computational.PqxdhInitialPendingPost

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPendingPost.after_interpretation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPendingPost.after_interpretation

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPendingPost.tail_interpretation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPendingPost.tail_interpretation

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPendingPost.owner_interpretation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPendingPost.owner_interpretation

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPendingPost.step_interpretation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPendingPost.step_interpretation

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPendingPost.program_interpretation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPendingPost.program_interpretation
