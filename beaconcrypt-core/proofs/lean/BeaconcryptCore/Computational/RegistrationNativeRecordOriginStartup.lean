-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeRecordOriginProgram
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginAmbient

/-! Actual native initialization performs constructor coins, ML generation, public Server import and the real ML-pin hash in one cache, while retaining every private record dictionary and writer log exactly. No initialized cache is reset or sampled in a separate pure startup. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeRecordOriginStartup
open PqxdhRecordLiftInterface (WorldSpec coinLift)
open PqxdhRecordLiftIdeal (CtxPrivate KeyMode ctxInterpreter)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordFactsOriginAmbient (Kept)
open PqxdhServerAuthExperiment (Setup Codec)
variable {n : Nat} {ι KemSK Reader Response Value : Type} {base : OracleSpec ι}

def Allowed : (WorldSpec n).Domain → Prop
  | .inl _ | .inr (.inl _) => True
  | _ => False

private theorem coins (work : ProbComp Value) : (simulateQ (coinLift (n := n)) work).AllQueriesSatisfy Allowed := by
  induction work using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, coinLift]
    exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨trivial, ih⟩

/-- The original initialization AST exposes only the actual coins, public Server import and shared pin hash. -/
theorem allowed (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKid : U64)
    (identity : PqxdhJointIdentity.PublicIdentity) :
    (RegistrationNativeHiddenStartup.start (n := n) setup source ensureInit identityIndex serverKid identity).AllQueriesSatisfy Allowed := by
  unfold RegistrationNativeHiddenStartup.start
  apply allQueriesSatisfy_bind (coins _)
  intro constructed
  cases selected : constructed.1 with
  | none => trivial
  | some created =>
    apply allQueriesSatisfy_bind (coins _)
    intro generated
    cases generated with
    | none => trivial
    | some credential =>
      dsimp only
      apply allQueriesSatisfy_bind ((allQueriesSatisfy_query_iff (spec := WorldSpec n)
        (.inl (RegistrationServerStartup.publicCreated identity identityIndex serverKid)) Allowed).mpr trivial)
      intro installed
      exact allQueriesSatisfy_bind ((allQueriesSatisfy_query_iff (spec := WorldSpec n)
        (.inr (.inl (.inr (.hash (PqxdhRefinement.absBytes credential.publicKey))))) Allowed).mpr trivial) (fun _ => trivial)

private theorem oracle_map_apply {Index S A B : Type} {spec : OracleSpec Index}
    (observe : A → B) (work : StateT S (OracleComp spec) A) (before : S) :
    (observe <$> work) before = (fun pair => (observe pair.1, pair.2)) <$> work before :=
  StateT.run_map observe work before

private theorem query_kept (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup base KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (query : (WorldSpec n).Domain) (permitted : Allowed query)
    (shell : CborRecordWorldClient.Shell) (control : PqxdhRecordLiftProtocol.Control n) (secret : CtxPrivate n)
    (result : (((WorldSpec n).Range query × CborRecordWorldClient.Shell) × PqxdhRecordLiftProtocol.Control n) × CtxPrivate n)
    (supported : result ∈ support (CborRawRecordOriginFlatten.interpret (ctxInterpreter modes replace setup codec) codec route
      ((WorldSpec n).query query) shell control secret)) : Kept secret result.2 := by
  rcases query with created | effect | record
  · simp only [CborRawRecordOriginFlatten.interpret, simulateQ_spec_query, CborRecordWorldClient.handler,
      CborRecordWorldClient.refusal, CborRecordWorldClient.forward, StateT.run, simulateQ_map, oracle_map_apply, support_map] at supported
    obtain ⟨inner, reached, rfl⟩ := supported
    exact PqxdhRecordFactsOriginAmbient.initialize_kept modes replace setup codec created control secret inner reached
  · simp only [CborRawRecordOriginFlatten.interpret, simulateQ_spec_query, CborRecordWorldClient.handler,
      CborRecordWorldClient.refusal, CborRecordWorldClient.forward, StateT.run, simulateQ_map, oracle_map_apply, support_map] at supported
    obtain ⟨inner, reached, rfl⟩ := supported
    exact PqxdhRecordFactsOriginAmbient.effects_kept modes replace setup codec effect control secret inner reached
  · exact False.elim permitted

/-- Any such literal initialization path retains all private record dictionaries while executing its real shared-cache effects. -/
theorem program_kept (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup base KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (work : OracleComp (WorldSpec n) Value) (permitted : work.AllQueriesSatisfy Allowed)
    (shell : CborRecordWorldClient.Shell) (control : PqxdhRecordLiftProtocol.Control n) (secret : CtxPrivate n)
    (result : ((Value × CborRecordWorldClient.Shell) × PqxdhRecordLiftProtocol.Control n) × CtxPrivate n)
    (supported : result ∈ support (CborRawRecordOriginFlatten.interpret (ctxInterpreter modes replace setup codec) codec route
      work shell control secret)) : Kept secret result.2 := by
  induction work using OracleComp.inductionOn generalizing shell control secret with
  | pure value =>
    rw [CborRawRecordOriginFlatten.interpret_pure, mem_support_pure_iff] at supported
    subst result
    exact Kept.refl _
  | query_bind query next ih =>
    obtain ⟨current, later⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp permitted
    rw [CborRawRecordOriginFlatten.interpret_bind, mem_support_bind_iff] at supported
    obtain ⟨middle, reached, continued⟩ := supported
    exact Kept.trans _ _ _ (query_kept modes replace setup codec route query current shell control secret middle reached)
      (ih middle.1.1.1 (later middle.1.1.1) middle.1.1.2 middle.1.2 middle.2 continued)

/-- Every supported actual native startup leaves the initially empty sealing dictionaries empty, including failed constructor and ML branches. -/
theorem empty (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup base KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKid : U64)
    (identity : PqxdhJointIdentity.PublicIdentity)
    (result : RegistrationNativeSelectiveEntropyStartup.Started n source)
    (supported : result ∈ support (CborRawRecordOriginFlatten.interpret (ctxInterpreter modes replace setup codec) codec route
      (RegistrationNativeHiddenStartup.start setup source ensureInit identityIndex serverKid identity)
      CborRecordWorldClient.initial PqxdhRecordLiftProtocol.initialControl CtxPrivate.initial)) :
    ∀ label, (result.2.keys label).1.successfulSeals = [] := by
  have kept := program_kept modes replace setup codec route _ (allowed setup source ensureInit identityIndex serverKid identity) _ _ _ _ supported
  intro label
  rw [kept.keys]
  rfl

end BeaconcryptCore.Computational.RegistrationNativeRecordOriginStartup
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRecordOriginStartup.allowed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRecordOriginStartup.allowed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRecordOriginStartup.program_kept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRecordOriginStartup.program_kept

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRecordOriginStartup.empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRecordOriginStartup.empty
