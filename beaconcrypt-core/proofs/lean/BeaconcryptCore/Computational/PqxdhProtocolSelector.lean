import BeaconcryptCore.Computational.PqxdhRegistrationProtocolState

/-!
Twelve statements compile an arbitrary adaptive public record/public/reveal and identity/CCA program into the retained private Phase-1 prefix. Full interpreter equalities keep the original source generation order and complete native and joint-identity poststate. Internal native randomness uses the existing private CCA coin route; only public transcript and requested replies reach Program.main. Selective restrictions exclude those coins only under an explicit predicate, while PqxdhProtocolQueryBounds counts them in the full ledger. Existing native role objects are fixed before the fresh target identity and KEM generation; this compiler does not install that fresh Beacon or model replicated registrations.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhProtocolSelector
open PqxdhPrivateKemSource PqxdhPrivateSourceCoins PqxdhKemIndCca
open PqxdhEd25519EufCma PqxdhJointIdentity PqxdhPhase1AcceptanceOracle

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK : Type}
variable {M P I D K A : Type} {S B : Nat}

abbrev State := PqxdhRegistrationProtocolState.State M P I D K A S B
abbrev ProtocolSpec := RawCtxProtocolReveals.SourceSpec S B
abbrev Spec (baseSpec : OracleSpec ι) (S B : Nat) :=
  RawCtxProtocolReveals.SourceSpec S B + SelectorSpec baseSpec

/-- Internal sampler calls use the existing CCA coin channel, never a public source-coin request. -/
def coins {Result : Type} (work : ProbComp Result) : OracleComp (SelectorSpec baseSpec) Result :=
  simulateQ (fun coin => (SelectorSpec baseSpec).query (.inr (.inl (.inl coin)))) work

/-- Original local evaluation turns those internal calls into the private channel with no protocol-state exposure. -/
theorem local_coins {Result : Type} (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK) (work : ProbComp Result) :
    simulateQ (localSelector baseImpl kem secret) (coins work) = localCoins work := by
  induction work using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query next ih =>
      simp only [coins, localCoins, simulateQ_bind, simulateQ_spec_query]
      change (do let answer ← (PrivateSourceSpec.query (.inl query) : OracleComp PrivateSourceSpec _)
                 simulateQ (localSelector baseImpl kem secret) (coins (next answer))) = _
      simp only [ih, localCoins]
      rfl

/-- The public program receives only actual operation replies; the complete reached role state stays in the compiler. -/
noncomputable def compiler
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (senderId : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder) :
    QueryImpl (Spec baseSpec S B)
      (StateT (State (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B))
        (OracleComp (SelectorSpec baseSpec))) :=
  fun query state => match query with
  | .inl request => coins ((PqxdhRegistrationProtocolState.sourceImpl source writer senderId route decode request).run state)
  | .inr request => do
      let answer ← (SelectorSpec baseSpec).query request
      pure (answer, state)

/-- The actual local identity/CCA interpreter used by the existing full private-prefix source. -/
def selectorImpl (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK) :
    QueryImpl (SelectorSpec baseSpec) (StateT (BareState count) ProbComp) :=
  privateImpl attachedVerify primitives count ∘ₛ localSelector baseImpl kem secret

/-- Primitive coins preserve the complete joint signing/DH/reveal/identity state and its original public log. -/
theorem selector_coins {Result : Type}
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK)
    (work : ProbComp Result) (state : BareState count) :
    (simulateQ (selectorImpl attachedVerify primitives count baseImpl kem secret) (coins work)).run state =
      (fun result => (result, state)) <$> work := by
  rw [selectorImpl, QueryImpl.simulateQ_compose, local_coins]
  exact private_local_complete attachedVerify primitives count work state

/-- Direct source execution interleaves the actual record/public/reveal and identity/CCA handlers, retaining both private states. -/
noncomputable def directImpl
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (senderId : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK) :
    QueryImpl (Spec baseSpec S B)
      (StateT (State (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B) × BareState count) ProbComp) :=
  fun query state => match query with
  | .inl request => do
      let result ← (PqxdhRegistrationProtocolState.sourceImpl source writer senderId route decode request).run state.1
      pure (result.1, (result.2, state.2))
  | .inr request => do
      let result ← (selectorImpl attachedVerify primitives count baseImpl kem secret request).run state.2
      pure (result.1, (state.1, result.2))

/-- Compilation is a complete interpreter equality, without exposing the role state to the requesting program. -/
theorem compiler_interpretation
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (senderId : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK) :
    ((selectorImpl attachedVerify primitives count baseImpl kem secret).mapStateTBase
      (compiler (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B)
        source writer senderId route decode)).flattenStateT =
      directImpl source writer senderId route decode attachedVerify primitives count baseImpl kem secret := by
  funext query state
  cases query with
  | inl request =>
      change (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ (selectorImpl attachedVerify primitives count baseImpl kem secret)
          (coins ((PqxdhRegistrationProtocolState.sourceImpl source writer senderId route decode request).run state.1))).run state.2 = _
      rw [selector_coins]
      simp only [Functor.map_map, directImpl, StateT.run, bind_pure_comp]
  | inr request =>
      simp only [QueryImpl.flattenStateT, QueryImpl.mapStateTBase, compiler, directImpl,
        StateT.run, StateT.mk, bind_pure_comp, simulateQ_map, simulateQ_spec_query]
      simpa only [StateT.run, Functor.map_map, OracleSpec.add_apply_inr, OracleSpec.Range] using
        congrArg (Functor.map (fun x => (x.1.1, (x.1.2, x.2))))
          (StateT.run_map (fun a => (a, state.1))
            (selectorImpl attachedVerify primitives count baseImpl kem secret request) state.2)

/-- The arbitrary adaptive prefix transports its full source roles, primitive cache and joint identity history together. -/
theorem compiler_complete {Result : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (senderId : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK)
    (client : OracleComp (Spec baseSpec S B) Result)
    (state : State (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B))
    (identities : BareState count) :
    (simulateQ (selectorImpl attachedVerify primitives count baseImpl kem secret)
      ((simulateQ (compiler source writer senderId route decode) client).run state)).run identities =
      (fun result => ((result.1, result.2.1), result.2.2)) <$>
        (simulateQ (directImpl source writer senderId route decode attachedVerify primitives count baseImpl kem secret)
          client).run (state, identities) := by
  rw [simulateQ_mapStateTBase_run_eq_map_flattenStateT, compiler_interpretation]

/-- Only the public transcript and requested operation replies reach the requesting program. -/
structure Program (baseSpec : OracleSpec ι) (Context : Type) (S B : Nat) where
  Selection : Type
  main : PqxdhEd25519EufCma.Phase1PublicTranscript Context →
    OracleComp (Spec baseSpec S B) (PqxdhEd25519EufCma.Phase1Candidate × Selection)

/-- Compile the same reached native state into the existing private prefix result; it is never an argument to Program.main. -/
noncomputable def selected {Context : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (senderId : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (program : Program baseSpec Context S B)
    (initial : State (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B)) :
    Selector baseSpec Context where
  State := program.Selection × State (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B)
  main transcript := (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ (compiler source writer senderId route decode) (program.main transcript)).run initial

/-- Instantiating the existing selector retains the exact reached native state and complete private identity state in the original source prefix. -/
theorem selected_complete {Context : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (senderId : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (program : Program baseSpec Context S B)
    (initial : State (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK)
    (transcript : Phase1PublicTranscript Context) (identities : BareState count) :
    (simulateQ (privateImpl attachedVerify primitives count)
      (simulateQ (localSelector baseImpl kem secret)
        ((selected source writer senderId route decode program initial).main transcript))).run identities =
      (fun result => ((result.1.1, (result.1.2, result.2.1)), result.2.2)) <$>
        (simulateQ (directImpl source writer senderId route decode attachedVerify primitives count baseImpl kem secret)
          (program.main transcript)).run (initial, identities) := by
  rw [← QueryImpl.simulateQ_compose]
  change (simulateQ (selectorImpl attachedVerify primitives count baseImpl kem secret) _).run identities = _
  simp only [selected, simulateQ_map, StateT.run_map]
  rw [compiler_complete]
  simp only [Functor.map_map]

/-- A selective ordinary class excludes internal protocol coins only when its explicit predicate says so. -/
theorem coins_excluded {Result : Type} (predicate : (SelectorSpec baseSpec).Domain → Prop)
    [DecidablePred predicate] (excluded : ∀ coin, ¬ predicate (.inr (.inl (.inl coin))))
    (work : ProbComp Result) : (coins (baseSpec := baseSpec) work).IsQueryBoundP predicate 0 := by
  induction work using OracleComp.inductionOn with
  | pure value => simp [coins]
  | query_bind query next ih =>
      change OracleComp.IsQueryBoundP (do
        let answer ← ((SelectorSpec baseSpec).query (.inr (.inl (.inl query))) : OracleComp (SelectorSpec baseSpec) _)
        coins (next answer)) predicate 0
      rw [isQueryBoundP_query_bind_iff]
      exact ⟨by simp [excluded query], fun answer => by simpa only [if_neg (excluded query)] using ih answer⟩

def SelectorClass (predicate : (SelectorSpec baseSpec).Domain → Prop) : (Spec baseSpec S B).Domain → Prop
  | .inl _ => False
  | .inr query => predicate query

instance (predicate : (SelectorSpec baseSpec).Domain → Prop) [DecidablePred predicate] :
    DecidablePred (SelectorClass (S := S) (B := B) predicate)
  | .inl _ => isFalse id
  | .inr query => inferInstanceAs (Decidable (predicate query))

/-- Actual native work is retained while excluded source-service caps count every forwarded original attempt. -/
theorem compiler_bound {Result : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (senderId : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (predicate : (SelectorSpec baseSpec).Domain → Prop) [DecidablePred predicate]
    (excluded : ∀ coin, ¬ predicate (.inr (.inl (.inl coin))))
    (client : OracleComp (Spec baseSpec S B) Result) (budget : Nat)
    (bounded : client.IsQueryBoundP (SelectorClass predicate) budget)
    (state : State (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B)) :
    ((simulateQ (compiler source writer senderId route decode) client).run state).IsQueryBoundP predicate budget := by
  apply bounded.simulateQ_run_StateT_of_step _ state
  intro query before
  cases query with
  | inl request => exact coins_excluded predicate excluded _
  | inr request =>
      simp only [compiler, StateT.run, bind_pure_comp, isQueryBoundP_map_iff, SelectorClass]
      exact (isQueryBoundP_query_iff _ _ _).mpr (by intro present; simp [present])

/-- Source signing/creation restrictions on the public program transfer structurally to the exact existing selector. -/
theorem selected_source_bound {Context : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (senderId : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (program : Program baseSpec Context S B)
    (initial : State (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B))
    (predicate : SourceSpec.Domain → Prop) [DecidablePred predicate]
    (transcript : Phase1PublicTranscript Context) (budget : Nat)
    (bounded : (program.main transcript).IsQueryBoundP
      (SelectorClass (PqxdhPrivateKemQueryBounds.SelectorSource (baseSpec := baseSpec) predicate)) budget) :
    ((selected source writer senderId route decode program initial).main transcript).IsQueryBoundP
      (PqxdhPrivateKemQueryBounds.SelectorSource (baseSpec := baseSpec) predicate) budget := by
  simpa only [selected, isQueryBoundP_map_iff] using
    compiler_bound source writer senderId route decode
      (PqxdhPrivateKemQueryBounds.SelectorSource (baseSpec := baseSpec) predicate)
      (by intro coin; simp [PqxdhPrivateKemQueryBounds.SelectorSource])
      (program.main transcript) budget bounded initial

/-- Each real mixed step preserves registration allocation and consumed history; record material and cache effects still occur. -/
theorem direct_step_controls
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (senderId : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK)
    (query : (Spec baseSpec S B).Domain)
    (state : State (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B) × BareState count)
    (result : (Spec baseSpec S B).Range query ×
      (State (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B) × BareState count))
    (present : result ∈ support
      ((directImpl source writer senderId route decode attachedVerify primitives count baseImpl kem secret query).run state)) :
    result.2.1.controls = state.1.controls ∧ result.2.1.consumed = state.1.consumed := by
  cases query with
  | inl request =>
      simp only [directImpl, StateT.run, bind_pure_comp, support_map] at present
      obtain ⟨original, present, rfl⟩ := present
      exact PqxdhRegistrationProtocolState.source_controls source writer senderId route decode
        ((RawCtxProtocolReveals.SourceSpec S B).query request : OracleComp (RawCtxProtocolReveals.SourceSpec S B) _) state.1 original
        (by simpa only [simulateQ_spec_query, StateT.run] using present)
  | inr request =>
      simp only [directImpl, StateT.run, bind_pure_comp, support_map] at present
      obtain ⟨original, _, rfl⟩ := present
      exact ⟨rfl, rfl⟩

/-- The entire actual adaptive mixed prefix preserves registration controls and consumed history, while retaining all other source effects. -/
theorem direct_controls {Result : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (senderId : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK)
    (client : OracleComp (Spec baseSpec S B) Result)
    (state : State (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B) × BareState count)
    (result : Result × (State (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B) × BareState count))
    (present : result ∈ support ((simulateQ
      (directImpl source writer senderId route decode attachedVerify primitives count baseImpl kem secret) client).run state)) :
    result.2.1.controls = state.1.controls ∧ result.2.1.consumed = state.1.consumed := by
  induction client using OracleComp.inductionOn generalizing state result with
  | pure value =>
      have equal := OracleComp.eq_of_mem_support_pure (value, state) present
      rw [equal]
      exact ⟨rfl, rfl⟩
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, support_bind,
        Set.mem_iUnion, exists_prop] at present
      obtain ⟨intermediate, step, rest⟩ := present
      have first := direct_step_controls source writer senderId route decode attachedVerify primitives
        count baseImpl kem secret query state intermediate step
      have last := ih intermediate.1 intermediate.2 result rest
      exact ⟨last.1.trans first.1, last.2.trans first.2⟩

set_option backward.isDefEq.respectTransparency false in
/-- Original creation, private prekey/KEM/one-time generation and signing retain the reached native controls/history without an added selector premise. -/
theorem program_controls
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (senderId : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (setup : PqxdhStatefulPhase1EufCma.StatefulPhase1Setup baseSpec)
    (program : Program baseSpec setup.Context S B)
    (initial : State (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (result : Option (PqxdhPrivateCandidateAcceptance.Outcome (PqxdhPrivatePhase1Prefix.Retained setup KemSK
      (program.Selection × State (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B)))) × BareState count)
    (present : result ∈ support (privateRun attachedVerify primitives count
      (PqxdhPrivatePhase1Prefix.program baseImpl kem setup
        (selected source writer senderId route decode program initial)))) :
    ∃ output, result.1 = some output ∧ output.context.selection.2.controls = initial.controls ∧
      output.context.selection.2.consumed = initial.consumed := by
  rw [PqxdhPrivatePhase1Prefix.program_complete] at present
  simp only [mem_support_bind_iff] at present
  obtain ⟨seed, _, generated, _, selectedResult, selectedSupport, finished⟩ := present
  obtain rfl := eq_of_mem_support_pure _ finished
  rw [selected_complete, support_map] at selectedSupport
  obtain ⟨original, originalSupport, rfl⟩ := selectedSupport
  have preserved := direct_controls source writer senderId route decode attachedVerify primitives count
    baseImpl kem generated.secret _ _ original originalSupport
  exact ⟨_, rfl, preserved.1, preserved.2⟩


/-- Erasing only the target KEM secret preserves the reached controls and consumed history established by the complete source prefix. -/
theorem erased_program_controls
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (senderId : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (setup : PqxdhStatefulPhase1EufCma.StatefulPhase1Setup baseSpec)
    (program : Program baseSpec setup.Context S B)
    (initial : State (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (result : Option (PqxdhPrivateCandidateAcceptance.Outcome (PqxdhPrivatePhase1Prefix.Retained setup KemSK
      (program.Selection × State (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B)))) × BareState count)
    (present : result ∈ support (privateRun attachedVerify primitives count
      (PqxdhPrivatePhase1Prefix.program baseImpl kem setup
        (selected source writer senderId route decode program initial)))) :
    ∃ output, result.1.map PqxdhPrivateRootSource.eraseOutput = some output ∧
      output.context.selection.2.controls = initial.controls ∧
      output.context.selection.2.consumed = initial.consumed := by
  obtain ⟨output, presentOutput, controls, consumed⟩ := program_controls source writer senderId route decode
    setup program initial attachedVerify primitives count baseImpl kem result present
  exact ⟨PqxdhPrivateRootSource.eraseOutput output, by simp only [presentOutput, Option.map_some], controls, consumed⟩

end BeaconcryptCore.Computational.PqxdhProtocolSelector

/--
info: 'BeaconcryptCore.Computational.PqxdhProtocolSelector.local_coins' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhProtocolSelector.local_coins

/--
info: 'BeaconcryptCore.Computational.PqxdhProtocolSelector.selector_coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhProtocolSelector.selector_coins

/--
info: 'BeaconcryptCore.Computational.PqxdhProtocolSelector.compiler_interpretation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhProtocolSelector.compiler_interpretation

/--
info: 'BeaconcryptCore.Computational.PqxdhProtocolSelector.compiler_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhProtocolSelector.compiler_complete

/--
info: 'BeaconcryptCore.Computational.PqxdhProtocolSelector.selected_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhProtocolSelector.selected_complete

/--
info: 'BeaconcryptCore.Computational.PqxdhProtocolSelector.coins_excluded' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhProtocolSelector.coins_excluded

/--
info: 'BeaconcryptCore.Computational.PqxdhProtocolSelector.compiler_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhProtocolSelector.compiler_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhProtocolSelector.selected_source_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhProtocolSelector.selected_source_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhProtocolSelector.direct_step_controls' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhProtocolSelector.direct_step_controls

/--
info: 'BeaconcryptCore.Computational.PqxdhProtocolSelector.direct_controls' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhProtocolSelector.direct_controls

/--
info: 'BeaconcryptCore.Computational.PqxdhProtocolSelector.program_controls' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhProtocolSelector.program_controls

/--
info: 'BeaconcryptCore.Computational.PqxdhProtocolSelector.erased_program_controls' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhProtocolSelector.erased_program_controls
