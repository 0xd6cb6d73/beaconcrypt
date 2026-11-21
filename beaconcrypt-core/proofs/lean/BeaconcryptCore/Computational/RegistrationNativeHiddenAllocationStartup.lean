-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeHiddenAllocation
import BeaconcryptCore.Computational.RegistrationNativeHiddenStartup

/-! The effectful actual native startup creates no owner and derives the initial joint allocation invariant after its constructor, Server ML generation and Server import. No pure-start or caller-owned-roster premise is used. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationStartup
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftInterface (WorldSpec coinLift)
open RegistrationNativeHiddenAllocationCore (WorldAllowed mapped)
variable {n : Nat} {ι KemSK ProviderState Reader Response Secret Value : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

private theorem coins (work : ProbComp Value) : AllQueriesSatisfy (simulateQ (coinLift (n := n)) work) WorldAllowed := by
  induction work using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, coinLift]
      exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨rfl, ih⟩

/-- Every actual startup callback is a coin or Server import, with no physical owner allocation. -/
theorem start_safe (setup : Setup base KemSK) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (identity : PqxdhJointIdentity.PublicIdentity) :
    AllQueriesSatisfy (RegistrationNativeHiddenStartup.start (n := n) setup source ensureInit identityIndex serverKeyId identity) WorldAllowed := by
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
            (.inl (RegistrationServerStartup.publicCreated identity identityIndex serverKeyId)) WorldAllowed).mpr rfl)
          intro installed
          trivial

/-- Every reached interpreted startup result belongs to its literal source AST, irrespective of private service behavior. -/
theorem interpreted_support (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (work : OracleComp (WorldSpec n) Value) (shell : CborRecordWorldClient.Shell)
    (control : PqxdhRecordLiftProtocol.Control n) (secret : Secret)
    (result : ((Value × CborRecordWorldClient.Shell) × PqxdhRecordLiftProtocol.Control n) × Secret)
    (supported : result ∈ support (CborRawRecordOriginFlatten.interpret service codec route work shell control secret)) :
    result.1.1.1 ∈ support work := by
  induction work using OracleComp.inductionOn generalizing shell control secret with
  | pure value =>
      rw [CborRawRecordOriginFlatten.interpret_pure, mem_support_pure_iff] at supported
      cases supported
      simp
  | query_bind query next ih =>
      rw [CborRawRecordOriginFlatten.interpret_bind, mem_support_bind_iff] at supported
      obtain ⟨middle, _reached, continued⟩ := supported
      rw [mem_support_bind_iff]
      exact ⟨middle.1.1.1, by simp, ih middle.1.1.1 middle.1.1.2 middle.1.2 middle.2 continued⟩

/-- Actual successful effectful startup establishes the literal empty joint roster and cursor allocation invariant. -/
theorem initialized (setup : Setup base KemSK) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (identity : PqxdhJointIdentity.PublicIdentity)
    (providerState : ProviderState)
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (secret : Secret) (started : RegistrationNativeHiddenStartup.Started source)
    (shell : CborRecordWorldClient.Shell) (control : PqxdhRecordLiftProtocol.Control n) (after : Secret)
    (supported : (((some started, shell), control), after) ∈ support
      (CborRawRecordOriginFlatten.interpret service codec route
        (RegistrationNativeHiddenStartup.start setup source ensureInit identityIndex serverKeyId identity)
        CborRecordWorldClient.initial PqxdhRecordLiftProtocol.initialControl secret)) :
    RegistrationNativeHiddenEnvironmentJoint.Holds
      ((((started.native.frontend, RegistrationNativeHiddenInterpreter.initial (n := n) (KemSK := KemSK) providerState), shell), control), after) := by
  have fields := RegistrationNativeHiddenStartup.start_fields setup source ensureInit identityIndex serverKeyId identity started
    (interpreted_support service codec route _ _ _ _ _ supported)
  have physical := RegistrationNativeHiddenAllocationCore.interpreted_program service codec route _ _ _ _ _
    (start_safe setup ensureInit identityIndex serverKeyId identity) supported
  have empty : control.owners = [] := List.length_eq_zero_iff.mp physical
  refine ⟨by simp only [fields.1, empty, List.length_nil], ?_, ?_⟩
  · intro index owner found
    simp only [fields.1, List.getElem?_nil] at found
    cases found
  · have domain := RegistrationNativeHiddenJointCursorWorld.program_domain service codec route
      (RegistrationNativeHiddenStartup.start setup source ensureInit identityIndex serverKeyId identity)
      CborRecordWorldClient.initial PqxdhRecordLiftProtocol.initialControl secret
      (((some started, shell), control), after) supported (RegistrationNativeHiddenJointCursor.initial _)
    exact RegistrationNativeHiddenJointCursor.absent shell control.owners domain

end BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationStartup
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationStartup.start_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationStartup.start_safe
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationStartup.interpreted_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationStartup.interpreted_support
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationStartup.initialized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationStartup.initialized
