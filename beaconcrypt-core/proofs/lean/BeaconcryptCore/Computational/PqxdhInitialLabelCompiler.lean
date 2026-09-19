import BeaconcryptCore.Computational.PqxdhInitialRootLabelBridge

/-!
The response-only initializer interface compiles to the exact original uniform-root family and real initializer. Its full adaptive source equality retains the complete root cache and ordinary coins. The selected-response interpretation is supplied by the separate private cache reconstruction, so this compiler never treats public HKDF as a random table.
-/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialLabelCompiler
open PqxdhInitialRootLabelService PqxdhJointKdfGame PqxdhCorrelatedExpand PqxdhCorrelatedExpandHybrid
variable {Result : Type}
abbrev Spec := PqxdhInitialRootLabelService.Spec unifSpec

noncomputable def source (fixed : FixedHkdfSha512NoSaltSource) : QueryImpl Spec (OracleComp RootSpec)
  | .inl query => RootSpec.query (.inl query)
  | .inr (.known root) => pure (realInitial fixed root)
  | .inr (.family message) => realInitial fixed <$> (RootSpec.query (.inr message) : OracleComp RootSpec _)

def coins (work : ProbComp Result) : OracleComp Spec Result := OracleComp.liftComp work Spec

/-- Ordinary sampling remains the same complete computation in source order under the response-only initializer compiler. -/
theorem coins_source (fixed : FixedHkdfSha512NoSaltSource) (work : ProbComp Result) :
    simulateQ (source fixed) (coins work) = rootCoins work := by
  induction work using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query next ih =>
      simp only [coins, rootCoins, liftComp_bind, simulateQ_bind]
      change (simulateQ (source fixed) (Spec.query (.inl query)) >>= fun answer =>
        simulateQ (source fixed) (coins (next answer))) = _
      simp only [simulateQ_spec_query, source, ih]
      rfl

set_option backward.isDefEq.respectTransparency false in
/-- Each source-compiled response-only request has exactly the same reply and complete cache effect as the original private initializer service. -/
theorem source_step (fixed : FixedHkdfSha512NoSaltSource) (query : Spec.Domain) (cache : RootOracle.QueryCache) :
    (simulateQ uniformImpl (source fixed query)).run cache =
      (nativeFull fixed (QueryImpl.ofLift unifSpec ProbComp) query).run cache := by
  cases query with
  | inl query => rfl
  | inr query =>
      cases query with
      | known root => rfl
      | family message =>
          simp only [source, simulateQ_map, simulateQ_spec_query, StateT.run_map]
          rfl

/-- The complete original uniform-root/real-initializer computation is retained for every adaptive response-only client and full root cache. -/
theorem source_program (fixed : FixedHkdfSha512NoSaltSource) (client : OracleComp Spec Result)
    (cache : RootOracle.QueryCache) :
    (simulateQ uniformImpl (simulateQ (source fixed) client)).run cache =
      (simulateQ (nativeFull fixed (QueryImpl.ofLift unifSpec ProbComp)) client).run cache := by
  rw [← QueryImpl.simulateQ_compose]
  have same : uniformImpl ∘ₛ source fixed = nativeFull fixed (QueryImpl.ofLift unifSpec ProbComp) := by
    funext query cache
    exact source_step fixed query cache
  rw [same]

end BeaconcryptCore.Computational.PqxdhInitialLabelCompiler

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialLabelCompiler.coins_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialLabelCompiler.coins_source

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialLabelCompiler.source_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialLabelCompiler.source_step

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialLabelCompiler.source_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialLabelCompiler.source_program
