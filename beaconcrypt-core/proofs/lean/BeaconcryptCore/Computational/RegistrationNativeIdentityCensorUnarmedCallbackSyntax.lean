-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPublicClient
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorOperationalPrefix
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorUnarmedMain
import BeaconcryptCore.Computational.RegistrationNativeIdentityTemplatePublicPrefix
/-! Every literal callback before the public guessed bundle lowers to the ordinary recorded prefix language, with no selector or omitted marker. The property follows from actual public entry and source lowering through arbitrary replies. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorUnarmedCallbackSyntax
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativeIdentityCensorCompiler (Mode)
open RegistrationNativeIdentityCensorPrefix (SourceSpec record)
open RegistrationNativeIdentityTemplatePublicPrefix (Allowed)
variable {A S : Type}

private theorem record_query (query : SourceSpec.Domain) (before : Mode) :
    (simulateQ RegistrationNativeIdentityCensorOperational.embed ((record query).run before)).AllQueriesSatisfy Allowed := by
  cases query <;>
    simp only [record,StateT.run,RegistrationNativeIdentityCensorPrefix.embed,RegistrationNativeIdentityCensorCompiler.protocol,
      simulateQ_bind,simulateQ_spec_query,RegistrationNativeIdentityCensorOperational.embed,simulateQ_pure] <;>
    exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨by trivial,fun _=>allQueriesSatisfy_pure _ _⟩

private theorem record_program (work : OracleComp SourceSpec A) (before : Mode) :
    (simulateQ RegistrationNativeIdentityCensorOperational.embed ((simulateQ record work).run before)).AllQueriesSatisfy Allowed := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value=>
    simp only [simulateQ_pure,StateT.run_pure]
    exact allQueriesSatisfy_pure _ _
  | query_bind query next ih=>
    simp only [simulateQ_bind,simulateQ_spec_query,StateT.run_bind]
    apply allQueriesSatisfy_bind (record_query query before)
    intro result
    exact ih result.1 result.2

/-- Public entry before the guessed bundle derives the complete allowed original prefix syntax, for arbitrary actual indexed callback bodies and all replies. -/
theorem callback (selected position : Nat) (placeholder : PqxdhEd25519EufCma.Ed25519Signature)
    (frontend : QueryImpl TypedSpec (StateT S (OracleComp SourceSpec))) (query : TypedSpec.Domain) (before : S × Mode)
    (missing : before.2.target=none)
    (different : ∀ index,query=.inr (.bundle index)→before.2.bundles≠position) :
    ((RegistrationNativeIdentityCensorPublicClient.callback selected position placeholder frontend query).run before).AllQueriesSatisfy Allowed := by
  have unarmed := RegistrationNativeIdentityCensorUnarmedMain.enter position query before.2 missing different
  have sourceLaw := RegistrationNativeIdentityCensorOperationalPrefix.program selected placeholder ((frontend query).run before.1)
    (RegistrationNativeIdentityCensorCompiler.enter position query before.2) unarmed
  simp only [RegistrationNativeIdentityCensorPublicClient.callback,StateT.run,bind_pure_comp]
  dsimp only [StateT.run] at sourceLaw
  rw [sourceLaw]
  exact RegistrationNativeIdentityMainNoRevealCore.mapped _ _ _
    (record_program ((frontend query).run before.1) (RegistrationNativeIdentityCensorCompiler.enter position query before.2))

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorUnarmedCallbackSyntax
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorUnarmedCallbackSyntax.callback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorUnarmedCallbackSyntax.callback
