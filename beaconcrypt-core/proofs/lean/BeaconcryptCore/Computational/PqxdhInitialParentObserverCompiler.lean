import BeaconcryptCore.Computational.PqxdhInitialParentBuilderContext
import BeaconcryptCore.Computational.PqxdhInitialRootAudit
import BeaconcryptCore.Computational.RawCtxFamilyPendingCompiler

/-!
The complete pending builder/post program lowers to the existing primitive/read interface plus its original external services. An initializer returns its exact privately audited input and native optional kernel; a pure audit query records that input and both returned chains before the known-label kernel is used. This is an executable source adapter, with two callbacks per initializer and at most one for every other input. The original full outside PostSpec client and its effects are unchanged.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialParentObserverCompiler
open PqxdhSecretInputKdf PqxdhInitialPendingPost RawCtxSelectedChain
variable {ι I D K X Response Shared Result Srv Bcn : Type} {extra : OracleSpec ι} {S B : Nat}

abbrev InitialReply := RootOutput × Option (KernelOf RatchetChain)
abbrev External (extra : OracleSpec ι) (I D K X Response Shared : Type) :=
  PqxdhBeaconPhase2Shared.Spec I D K X Response Shared +
    ((Response →ₒ Option Pqxdh.Bytes) +
      ((PqxdhBeaconPhase2Shared.Secrets Shared →ₒ InitialReply) +
        (extra + PqxdhServerRegistrationPublication.AuxSpec)))
abbrev AuditSpec := InitialReply →ₒ Option (KernelOf RatchetChain)
abbrev Spec (extra : OracleSpec ι) (I D K X Response Shared : Type) :=
  RawCtxSelectedLiveCompiler.Spec + (External extra I D K X Response Shared + AuditSpec)

def candidates (reply : InitialReply) : List RootOutput := reply.1 ::
  match reply.2 with
  | none => []
  | some kernel => [RawCtxSelectedQueryTrace.rootVector kernel.send_chain,
      RawCtxSelectedQueryTrace.rootVector kernel.receive_chain]

def oldForward : QueryImpl RawCtxSelectedLiveCompiler.Spec
    (OracleComp (Spec extra I D K X Response Shared)) :=
  fun query => (Spec extra I D K X Response Shared).query (.inl query)

def externalForward : QueryImpl (External extra I D K X Response Shared)
    (OracleComp (Spec extra I D K X Response Shared)) :=
  fun query => (Spec extra I D K X Response Shared).query (.inr (.inl query))

def audit (reply : InitialReply) : OracleComp (Spec extra I D K X Response Shared) (Option (KernelOf RatchetChain)) :=
  (Spec extra I D K X Response Shared).query (.inr (.inr reply))

noncomputable def compiler : QueryImpl
    (PqxdhInitialPendingPost.Spec extra Slot I D K X Response Shared S B)
    (OracleComp (Spec extra I D K X Response Shared))
  | .inl query => simulateQ oldForward (RawCtxFamilyPendingCompiler.live query)
  | .inr (.inl query) => externalForward (.inl query)
  | .inr (.inr (.inl reply)) => externalForward (.inr (.inl reply))
  | .inr (.inr (.inr (.inl secrets))) => do
      let reply ← externalForward (.inr (.inr (.inl secrets)))
      let kernel ← audit reply
      pure (Option.map RawCtxSelectedFamilyContext.knownKernel kernel)
  | .inr (.inr (.inr (.inr (.inl query)))) => externalForward (.inr (.inr (.inr (.inl query))))
  | .inr (.inr (.inr (.inr (.inr query)))) => externalForward (.inr (.inr (.inr (.inr query))))

variable {m : Type → Type} [Monad m] [LawfulMonad m]

def handler (old : QueryImpl RawCtxSelectedLiveCompiler.Spec m)
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) m)
    (application : Response → m (Option Pqxdh.Bytes))
    (initial : PqxdhBeaconPhase2Shared.Secrets Shared → m InitialReply)
    (selector : QueryImpl extra m) (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec m) :
    QueryImpl (Spec extra I D K X Response Shared) m
  | .inl query => old query
  | .inr (.inl (.inl query)) => pre query
  | .inr (.inl (.inr (.inl reply))) => application reply
  | .inr (.inl (.inr (.inr (.inl secrets)))) => initial secrets
  | .inr (.inl (.inr (.inr (.inr (.inl query))))) => selector query
  | .inr (.inl (.inr (.inr (.inr (.inr query))))) => aux query
  | .inr (.inr reply) => pure reply.2

/-- Every initializer audit includes its actual input and no more than the two returned native chain values. -/
theorem candidates_bound (reply : InitialReply) : (candidates reply).length ≤ 3 := by
  rcases reply with ⟨root, kernel⟩
  cases kernel <;> simp [candidates]

/-- The initializer input remains in the actual candidate log even if kernel construction fails. -/
theorem input_recorded (reply : InitialReply) : reply.1 ∈ candidates reply := by
  simp only [candidates, List.mem_cons, true_or]

/-- Forwarding the original primitive/read interface preserves every callback of its supplied interpreter. -/
theorem old_handler (old : QueryImpl RawCtxSelectedLiveCompiler.Spec m)
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) m)
    (application : Response → m (Option Pqxdh.Bytes))
    (initial : PqxdhBeaconPhase2Shared.Secrets Shared → m InitialReply)
    (selector : QueryImpl extra m) (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec m) :
    handler old pre application initial selector aux ∘ₛ oldForward = old := by
  funext query
  exact simulateQ_spec_query _ _

/-- Removing the pure audit callback gives exactly the full original pending interpreter, including the native initializer reply mapped to known kernels. -/
theorem compiler_handler (old : QueryImpl RawCtxSelectedLiveCompiler.Spec m)
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) m)
    (application : Response → m (Option Pqxdh.Bytes))
    (initial : PqxdhBeaconPhase2Shared.Secrets Shared → m InitialReply)
    (selector : QueryImpl extra m) (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec m) :
    handler old pre application initial selector aux ∘ₛ compiler (S := S) (B := B) =
      PqxdhInitialPendingPost.handler
        (old ∘ₛ RawCtxFamilyPendingCompiler.primitive)
        (old ∘ₛ RawCtxFamilyReadCompiler.compiler) pre application
        (fun secrets => (fun reply => Option.map RawCtxSelectedFamilyContext.knownKernel reply.2) <$> initial secrets)
        selector aux := by
  funext query
  rcases query with query | (query | (reply | (secrets | (query | query))))
  · simp only [QueryImpl.compose, compiler, ← QueryImpl.simulateQ_compose, old_handler]
    cases query <;> rfl
  · exact simulateQ_spec_query _ _
  · exact simulateQ_spec_query _ _
  · simp [QueryImpl.compose, compiler, externalForward, audit, handler,
      PqxdhInitialPendingPost.handler]
  · exact simulateQ_spec_query _ _
  · exact simulateQ_spec_query _ _

/-- The entire original pending builder/post continuation keeps all replies and effects after adding only the private audit instrumentation. -/
theorem program_source (old : QueryImpl RawCtxSelectedLiveCompiler.Spec m)
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) m)
    (application : Response → m (Option Pqxdh.Bytes))
    (initial : PqxdhBeaconPhase2Shared.Secrets Shared → m InitialReply)
    (selector : QueryImpl extra m) (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec m)
    (client : OracleComp (PqxdhInitialPendingPost.Spec extra Slot I D K X Response Shared S B) Result) :
    simulateQ (handler old pre application initial selector aux) (simulateQ compiler client) =
      simulateQ (PqxdhInitialPendingPost.handler
        (old ∘ₛ RawCtxFamilyPendingCompiler.primitive)
        (old ∘ₛ RawCtxFamilyReadCompiler.compiler) pre application
        (fun secrets => (fun reply => Option.map RawCtxSelectedFamilyContext.knownKernel reply.2) <$> initial secrets)
        selector aux) client := by
  rw [← QueryImpl.simulateQ_compose, compiler_handler]

/-- All replies are charged: one callback for ordinary source inputs, at most one for a read, and initializer lookup plus its private audit. -/
theorem compiler_bound (query : (PqxdhInitialPendingPost.Spec extra Slot I D K X Response Shared S B).Domain) :
    (compiler query).IsTotalQueryBound 2 := by
  rcases query with (query | read) | (query | (reply | (secrets | (query | query))))
  · rcases query with (pending | opening) | ((pending | sealing) | (coin | (hash | view)))
    all_goals simp only [compiler, RawCtxFamilyPendingCompiler.live,
      RawCtxPendingFamilyLiveQueries.handler, RawCtxFamilyPendingCompiler.primitive,
      QueryImpl.compose, RawCtxPendingOwnerQueries.erase]
    all_goals exact (isQueryBound_query_iff _ _ _ _).mpr (by decide)
  · rcases read with ⟨request, kernel⟩
    cases request <;> cases kernel
    all_goals simp only [compiler, RawCtxFamilyPendingCompiler.live,
      RawCtxPendingFamilyLiveQueries.handler, RawCtxFamilyReadCompiler.compiler]
    all_goals first | trivial | exact (isQueryBound_query_iff _ _ _ _).mpr (by decide)
  · exact (isQueryBound_query_iff _ _ _ _).mpr (by decide)
  · exact (isQueryBound_query_iff _ _ _ _).mpr (by decide)
  · change ((externalForward (.inr (.inr (.inl secrets))) :
        OracleComp (Spec extra I D K X Response Shared) InitialReply) >>= fun reply =>
        audit reply >>= fun kernel => pure (Option.map RawCtxSelectedFamilyContext.knownKernel kernel)).IsTotalQueryBound 2
    apply isTotalQueryBound_bind (n₁ := 1) (n₂ := 1)
      ((isQueryBound_query_iff _ _ _ _).mpr (by decide))
    intro reply
    exact isTotalQueryBound_bind (n₁ := 1) (n₂ := 0)
      ((isQueryBound_query_iff _ _ _ _).mpr (by decide)) (fun _ => by trivial)
  · exact (isQueryBound_query_iff _ _ _ _).mpr (by decide)
  · exact (isQueryBound_query_iff _ _ _ _).mpr (by decide)

/-- The concrete audit lowering doubles at most the original all-reply pending callback budget; no ambient work is declared free. -/
theorem program_bound
    (client : OracleComp (PqxdhInitialPendingPost.Spec extra Slot I D K X Response Shared S B) Result)
    (budget : Nat) (bounded : client.IsTotalQueryBound budget) :
    (simulateQ compiler client).IsTotalQueryBound (2 * budget) := by
  induction client using OracleComp.inductionOn generalizing budget with
  | pure value => simpa only [simulateQ_pure] using (show (pure value : OracleComp (Spec extra I D K X Response Shared) Result).IsTotalQueryBound (2 * budget) from by trivial)
  | query_bind query next ih =>
      rw [isTotalQueryBound_query_bind_iff] at bounded
      simp only [simulateQ_bind, simulateQ_spec_query]
      exact (isTotalQueryBound_bind (compiler_bound query)
        (fun reply => ih reply (budget - 1) (bounded.2 reply))).mono (by have := bounded.1; omega)

end BeaconcryptCore.Computational.PqxdhInitialParentObserverCompiler

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialParentObserverCompiler.candidates_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialParentObserverCompiler.candidates_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialParentObserverCompiler.input_recorded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialParentObserverCompiler.input_recorded

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialParentObserverCompiler.old_handler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialParentObserverCompiler.old_handler

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialParentObserverCompiler.compiler_handler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialParentObserverCompiler.compiler_handler

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialParentObserverCompiler.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialParentObserverCompiler.program_source

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialParentObserverCompiler.compiler_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialParentObserverCompiler.compiler_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialParentObserverCompiler.program_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialParentObserverCompiler.program_bound
