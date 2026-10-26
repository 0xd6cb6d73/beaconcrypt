import BeaconcryptCore.Computational.PqxdhProtocolSelector

/-!
Five complete-program equalities instantiate the previously arbitrary accepted-root Plan with the actual native state reached by the compiled selector. Accepted response construction resumes the same record/public/reveal scheduler after installing the actual optional result and primitive poststate. Early completion maps the modeled registration errors to the source Option API. Source branch and Server-field lemmas separately justify unchanged rejection history and exact accepted consumption; this Plan definition alone does not establish those facts. The reduction interface gains no KEM shared-secret argument.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhProtocolRegistration
open PqxdhPrivateAcceptedRoot
open PqxdhServerRegistrationPublication (NativeSpec AuxSpec Response)

variable {ι : Type} {baseSpec : OracleSpec ι}
variable {M P I D K A : Type} {S B : Nat}

abbrev State := PqxdhRegistrationProtocolState.State M P I D K A S B

/-- Internal record/registration work uses the existing private CCA coin route in the source continuation. -/
def coins {Result : Type} (work : ProbComp Result) : OracleComp (CorrelatedSpec baseSpec) Result :=
  simulateQ (fun coin => ((CorrelatedSpec baseSpec).query (.inl (.inr (.inl (.inl (.inl coin))))) :
    OracleComp (CorrelatedSpec baseSpec) _)) work

theorem coins_bind {α β : Type} (work : ProbComp α) (next : α → ProbComp β) :
    coins (baseSpec := baseSpec) (work >>= next) = (coins work >>= fun value => coins (next value)) :=
  simulateQ_bind _ work next

noncomputable def nativeImpl
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (aux : QueryImpl AuxSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp)) :
    QueryImpl NativeSpec
      (StateT (State (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B)) ProbComp) :=
  fun query state => do
    let result ← (PqxdhRegistrationProtocolState.registrationImpl source writer aux query).run state.primitive
    pure (result.1, { state with primitive := result.2 })

noncomputable def liftedImpl
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (aux : QueryImpl AuxSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp)) :
    QueryImpl NativeSpec
      (StateT (State (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B))
        (OracleComp (CorrelatedSpec baseSpec))) :=
  fun query state => coins ((nativeImpl source writer aux query).run state)

/-- The complete native callback program is lifted without dropping any role or primitive state. -/
theorem lifted_complete {Result : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (aux : QueryImpl AuxSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (client : OracleComp NativeSpec Result)
    (state : State (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B)) :
    (simulateQ (liftedImpl (baseSpec := baseSpec) source writer aux) client).run state =
      coins ((simulateQ (nativeImpl source writer aux) client).run state) := by
  induction client using OracleComp.inductionOn generalizing state with
  | pure value => rfl
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, coins_bind]
      simp only [liftedImpl, StateT.run]
      exact bind_congr (fun result => ih result.1 result.2)

/-- Callback execution changes the same shared primitive state, retaining all role, control and consumed fields jointly. -/
theorem native_complete {Result : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (aux : QueryImpl AuxSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (client : OracleComp NativeSpec Result)
    (state : State (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B)) :
    (simulateQ (nativeImpl source writer aux) client).run state =
      (fun result => (result.1, { state with primitive := result.2 })) <$>
        (simulateQ (PqxdhRegistrationProtocolState.registrationImpl source writer aux) client).run state.primitive := by
  have complete := map_run_simulateQ_eq_of_query_map_eq
    (PqxdhRegistrationProtocolState.registrationImpl source writer aux)
    (nativeImpl source writer aux) (fun primitive => { state with primitive := primitive })
    (fun query before => by
      simp only [nativeImpl, StateT.run, map_eq_bind_pure_comp]
      apply bind_congr
      intro result
      rfl) client state.primitive
  exact complete.symm

abbrev Output (setup : PqxdhStatefulPhase1EufCma.StatefulPhase1Setup baseSpec) (Selection : Type) :=
  Option (PqxdhPrivateCandidateAcceptance.Outcome (PqxdhPrivatePhase1Prefix.Retained setup Unit
    (Selection × State (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B))))

/-- The only fallback is the untouched entry state for rejection before the selector ran. -/
def reached {setup : PqxdhStatefulPhase1EufCma.StatefulPhase1Setup baseSpec} {Selection : Type}
    (initial : State (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B))
    (output : Output (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B) setup Selection) : State (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B) :=
  match output with
  | none => initial
  | some output => output.context.selection.2

def choice {setup : PqxdhStatefulPhase1EufCma.StatefulPhase1Setup baseSpec} {Selection : Type}
    (output : Output (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B) setup Selection) :
    Option Selection := output.map (fun result => result.context.selection.1)

/-- Native post-state is retained before only the requested API result is exposed to the continued program. -/
def afterBuilder (index : Fin S)
    (result : RustM (Option Response × PqxdhServerRegistrationPublication.State M P (List Pqxdh.Bytes)) ×
      State (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B)) :
    RustM (Option Response) × State (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B) :=
  PqxdhRegistrationProtocolState.reinstall index result.2 (result.1, result.2.primitive)

/-- A concrete Plan extracts the actual selected state produced by the source compiler and resumes the same role scheduler. -/
noncomputable def plan {Selection : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (aux : QueryImpl AuxSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (senderId : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (setup : PqxdhStatefulPhase1EufCma.StatefulPhase1Setup baseSpec)
    (index : Fin S) (metadata : P)
    (initial : State (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B))
    (post : Option Selection → RustM (Option Response) → OracleComp (RawCtxProtocolReveals.SourceSpec S B) Bool) :
    PqxdhAcceptedRegistration.Plan baseSpec setup
      (Selection × State (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B))
      M P (List Pqxdh.Bytes) (State (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B)) where
  inputs output ready :=
    let state := PqxdhRegistrationProtocolState.consume index ready (reached initial output)
    let selected := PqxdhRegistrationProtocolState.input senderId index metadata state
    ⟨selected.binding, selected.state, metadata, state⟩
  impl := liftedImpl source writer aux
  completed output _ := coins (Prod.fst <$>
    (simulateQ (PqxdhRegistrationProtocolState.sourceImpl source writer senderId route decode)
      (post (choice output) (ok none))).run (reached initial output))
  next output result :=
    let updated := afterBuilder index result
    coins (Prod.fst <$>
      (simulateQ (PqxdhRegistrationProtocolState.sourceImpl source writer senderId route decode)
        (post (choice output) updated.1)).run updated.2)

/-- The full private primitive context is merely re-associated; no prior role state is restored over a real update. -/
theorem afterBuilder_restored (index : Fin S)
    (state : State (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B))
    (result : RustM (Option Response × PqxdhServerRegistrationPublication.State M P (List Pqxdh.Bytes)) ×
      RawCtxSharedPrimitive.SharedState A) :
    afterBuilder index (result.1, { state with primitive := result.2 }) =
      PqxdhRegistrationProtocolState.reinstall index state result := by
  rcases result with ⟨result, primitive⟩
  cases result <;> rfl

/-- The concrete private Plan runs the reached source builder, installs its real result and resumes the same source role scheduler. -/
theorem accepted_run {Selection : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (aux : QueryImpl AuxSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (senderId : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (setup : PqxdhStatefulPhase1EufCma.StatefulPhase1Setup baseSpec)
    (index : Fin S) (metadata : P)
    (initial : State (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B))
    (post : Option Selection → RustM (Option Response) → OracleComp (RawCtxProtocolReveals.SourceSpec S B) Bool)
    (output : Output (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B) setup Selection)
    (ready : Ready) :
    ((plan source writer aux senderId route decode setup index metadata initial post).continuation source).accepted output ready =
      coins (do
        let result ← (PqxdhRegistrationProtocolState.build source writer aux senderId index metadata ready).run (reached initial output)
        Prod.fst <$> (simulateQ (PqxdhRegistrationProtocolState.sourceImpl source writer senderId route decode)
          (post (choice output) result.1)).run result.2) := by
  dsimp only [PqxdhAcceptedRegistration.Plan.continuation, PqxdhAcceptedRegistration.registrationContinuation, plan]
  rw [lifted_complete, native_complete, ← coins_bind]
  simp only [bind_map_left, afterBuilder_restored, PqxdhRegistrationProtocolState.build, StateT.run]

end BeaconcryptCore.Computational.PqxdhProtocolRegistration

/--
info: 'BeaconcryptCore.Computational.PqxdhProtocolRegistration.coins_bind' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhProtocolRegistration.coins_bind

/--
info: 'BeaconcryptCore.Computational.PqxdhProtocolRegistration.lifted_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhProtocolRegistration.lifted_complete

/--
info: 'BeaconcryptCore.Computational.PqxdhProtocolRegistration.native_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhProtocolRegistration.native_complete

/--
info: 'BeaconcryptCore.Computational.PqxdhProtocolRegistration.afterBuilder_restored' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhProtocolRegistration.afterBuilder_restored

/--
info: 'BeaconcryptCore.Computational.PqxdhProtocolRegistration.accepted_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhProtocolRegistration.accepted_run
