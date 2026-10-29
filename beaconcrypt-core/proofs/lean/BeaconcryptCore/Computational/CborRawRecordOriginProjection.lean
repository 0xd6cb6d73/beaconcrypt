-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawRecordOriginFlatten

/-! Startup coins preserve the actual public cursor shell, while Server installation performs its literal public initialization update. Dropping only that shell retains the exact original generic private-service execution. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawRecordOriginProjection
open PqxdhRecordLiftInterface (Environment WorldSpec coinLift)
open PqxdhRecordLiftProtocol (ServiceSpec Control initialControl)
open PqxdhServerAuthExperiment (Codec)
open CborRawRecordOriginFlatten (startup install interpret)
variable {n : Nat} {Reader Response E S X : Type}

/-- Actual startup coin calls retain the entire cursor shell, for every draw and continuation. -/
theorem coin_shell (work : ProbComp X) (shell : CborRecordWorldClient.Shell) :
    (simulateQ (CborRecordWorldClient.handler (n := n)) (simulateQ coinLift work)).run shell =
      (fun result => (result, shell)) <$> simulateQ coinLift work := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind, coinLift, simulateQ_spec_query, StateT.run_bind, map_bind]
      rw [show (CborRecordWorldClient.handler (n := n) (.inr (.inl (.inl query)))).run shell =
        (fun reply => (reply, shell)) <$> ((WorldSpec n).query (.inr (.inl (.inl query))) : OracleComp (WorldSpec n) _) by rfl]
      simp only [bind_map_left, ih]
      rfl


/-- Generic startup retains its exact initial shell and original complete Protocol/private outcome. -/
theorem startup_eq (service : QueryImpl (ServiceSpec n) (StateT S ProbComp))
    (env : Environment n E) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder) (secret : S) :
    startup service env codec route secret =
      (fun result => (((result.1.1, CborRecordWorldClient.initial), result.1.2), result.2)) <$>
        (simulateQ service ((simulateQ (PqxdhRecordLiftProtocol.handler codec.frameRead route)
          (simulateQ coinLift env.start)).run initialControl)).run secret := by
  rw [startup, interpret, coin_shell]
  simp only [simulateQ_map, StateT.run_map]

/-- Erasing only startup cursor metadata keeps the exact original generic service program. -/
theorem startup_project (service : QueryImpl (ServiceSpec n) (StateT S ProbComp))
    (env : Environment n E) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder) (secret : S) :
    (fun result => ((result.1.1.1, result.1.2), result.2)) <$> startup service env codec route secret =
      (simulateQ service ((simulateQ (PqxdhRecordLiftProtocol.handler codec.frameRead route)
        (simulateQ coinLift env.start)).run initialControl)).run secret := by
  rw [startup_eq]
  simp only [Functor.map_map, Prod.mk.eta, id_map']

/-- Server installation retains the literal public cursor initialization and the full original private service execution. -/
theorem install_eq (service : QueryImpl (ServiceSpec n) (StateT S ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (created : PqxdhLiveServerConstruction.Created Unit) (shell : CborRecordWorldClient.Shell)
    (control : Control n) (secret : S) :
    install service codec route created shell control secret =
      (fun result => ((CborRecordWorldClient.next (show (WorldSpec n).Domain from .inl created) () shell, result.1.2), result.2)) <$>
        (simulateQ service ((PqxdhRecordLiftProtocol.handler codec.frameRead route (.inl created)).run control)).run secret := by
  simp only [install, interpret, simulateQ_spec_query]
  rw [show (CborRecordWorldClient.handler (n := n) (.inl created)).run shell =
    CborRecordWorldClient.forward (.inl created) shell by rfl]
  simp only [CborRecordWorldClient.forward, simulateQ_map, StateT.run_map, simulateQ_spec_query, Functor.map_map, CborRecordWorldClient.next]


/-- Dropping only the cursor from installation preserves all original Protocol and private fields. -/
theorem install_project (service : QueryImpl (ServiceSpec n) (StateT S ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (created : PqxdhLiveServerConstruction.Created Unit) (shell : CborRecordWorldClient.Shell)
    (control : Control n) (secret : S) :
    (fun result => (result.1.2, result.2)) <$> install service codec route created shell control secret =
      (fun result => (result.1.2, result.2)) <$>
        (simulateQ service ((PqxdhRecordLiftProtocol.handler codec.frameRead route (.inl created)).run control)).run secret := by
  rw [install_eq]
  simp only [Functor.map_map]

end BeaconcryptCore.Computational.CborRawRecordOriginProjection

/-- info: 'BeaconcryptCore.Computational.CborRawRecordOriginProjection.coin_shell' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordOriginProjection.coin_shell
/-- info: 'BeaconcryptCore.Computational.CborRawRecordOriginProjection.startup_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordOriginProjection.startup_eq
/-- info: 'BeaconcryptCore.Computational.CborRawRecordOriginProjection.startup_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordOriginProjection.startup_project
/-- info: 'BeaconcryptCore.Computational.CborRawRecordOriginProjection.install_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordOriginProjection.install_eq
/-- info: 'BeaconcryptCore.Computational.CborRawRecordOriginProjection.install_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordOriginProjection.install_project
