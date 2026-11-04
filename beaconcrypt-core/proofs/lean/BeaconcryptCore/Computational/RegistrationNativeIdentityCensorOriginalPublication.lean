-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPublicationSource
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxOrdinary

/-! The honest physical-source interpretation of the literal Main publication closes to the original Core controller and exact mutable source writer. The equation is derived from the actual scoped dictionary and its per-operation state transformers; no controller or writer-purity law is supplied. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorOriginalPublication
open PqxdhServerAuthExperiment (Setup Checks)
variable {n : Nat} {I KemSK Platform E A B Q : Type} {base : OracleSpec I} {queries : OracleSpec Q} {mlSource : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (checks : Checks)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
variable (index : Nat) (owner : RegistrationNativeIdentityFrontend.Owner mlSource)
variable (reserve : Usize → StateT Platform ProbComp (core.result.Result Unit E))
local notation "Main" => RegistrationNativePlatformIdentityCtxMain.beacon (n := n) (Platform := Platform) (source := mlSource) setup checks representation created
local notation "run(" work ")" => RegistrationNativePlatformIdentityCtxMain.interpret setup.joint work
local notation "external(" work ")" => Main (RegistrationNativePlatformIdentityProgram.external work)
local notation "action(" query ")" => Main (RegistrationNativePlatformIdentityProgram.native
  (RegistrationNativeIdentityFrontend.outgoing (n := n) (Auxiliary := RegistrationServerRoleBackend.State) setup mlSource index owner query))
local notation "callback" => (fun query => run(action(query)))
local notation "encoder" => (fun fields => run(external(RegistrationNativeIdentityCensorConcreteWriter.encode reserve fields)))

private theorem original_program
    (impl : QueryImpl queries (RegistrationNativePlatformIdentityCtxMain.M n KemSK Platform mlSource))
    (work : OracleComp queries A) :
    run(simulateQ impl work) = simulateQ (fun query => run(impl query)) work := by
  induction work using OracleComp.inductionOn with
  | pure value => simpa only [simulateQ_pure] using RegistrationNativePlatformIdentityCtxOrdinary.interpret_pure setup.joint value
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, RegistrationNativePlatformIdentityCtxOrdinary.interpret_bind, ih]

private theorem external_pure (value : A) : external((pure value : StateT Platform ProbComp A)) = pure value := by
  funext before
  change (external((pure value : StateT Platform ProbComp A))).run before = (pure value : RegistrationNativePlatformIdentityCtxMain.M n KemSK Platform mlSource A).run before
  rw [RegistrationNativeIdentityCensorExternalSource.native setup checks representation created]
  simp only [StateT.run_pure, simulateQ_pure, map_pure]

private theorem external_bind (work : StateT Platform ProbComp A) (next : A → StateT Platform ProbComp B) :
    external(work >>= next) = (do let value ← external(work); external(next value)) := by
  funext before
  change (external(work >>= next)).run before = ((do let value ← external(work); external(next value)) : RegistrationNativePlatformIdentityCtxMain.M n KemSK Platform mlSource B).run before
  simp only [RegistrationNativeIdentityCensorExternalSource.native, StateT.run_bind, simulateQ_bind, map_bind, bind_map_left]

private theorem external_program (impl : QueryImpl queries (StateT Platform ProbComp)) (work : OracleComp queries A) :
    run(external(simulateQ impl work)) = simulateQ (fun query => run(external(impl query))) work := by
  induction work using OracleComp.inductionOn with
  | pure value => rw [simulateQ_pure, external_pure, RegistrationNativePlatformIdentityCtxOrdinary.interpret_pure, simulateQ_pure]
  | query_bind query next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, external_bind, RegistrationNativePlatformIdentityCtxOrdinary.interpret_bind]
    simp only [ih, simulateQ_bind, simulateQ_spec_query]

/-- Literal honest-source binding through the actual NoKem Main publication and complete concrete source encoder, retaining all pool/cache/journal/native/P state. -/
theorem source (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin) (mldsa : Array U8 1952#usize) :
    run(Main (simulateQ
      (RegistrationNativePlatformIdentityPublication.callback (n := n) (Auxiliary := RegistrationServerRoleBackend.State)
        setup index owner (RegistrationNativePlatformConcreteSource.writer reserve))
      (RegistrationNativePlatformWriter.begin E control inputs coins pin mldsa))) =
      RegistrationNativePlatformBeaconPublication.begin callback encoder control inputs coins pin mldsa := by
  rw [RegistrationNativePlatformIdentityCtxOutgoingFold.publication, original_program,
    RegistrationNativePlatformWriter.begin_interpret]
  have writerEq : (fun fields => simulateQ
      (fun query => run(Main (RegistrationNativePlatformIdentityPublication.callback setup index owner (RegistrationNativePlatformConcreteSource.writer reserve) (.inr query))))
      (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestExtraction.encodeInit (E := E)
        (m := BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Program E)
        (RegistrationNativePlatformWriter.initPacket fields)).run) = encoder := by
    funext fields
    change simulateQ (fun query => run(external(RegistrationNativePlatformConcreteSource.writer reserve query))) _ = _
    exact (external_program setup checks representation created (RegistrationNativePlatformConcreteSource.writer reserve) _).symm
  rw [writerEq]
  rfl

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorOriginalPublication

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorOriginalPublication.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorOriginalPublication.source
