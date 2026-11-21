-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetSource
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetCollector

/-! The actual Word Server controller lowers its current mutable environment into the concrete combined interpreter. This exact source plumbing retains every request, flag, World/cache effect and KEM pool/phase through authentication and collection. It exposes the actual selected getter interpreter rather than replacing it with the closed real SDK backend. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetServerExecution
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message ServerState)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordInterface (LocalSpec)
open RegistrationNativeSecretWordInterpreter (Provider)
open RegistrationServerReferenceCompiler (Environment)
variable {n : Nat} {ι KemSK Value Next : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

abbrev Auxiliary (n : Nat) (KemSK : Type) := Environment × RegistrationNativeSecretWordInterpreter.State n KemSK

noncomputable def localImpl (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
    (provider : Provider KemSK) (outer : QueryImpl Combined ProbComp) (selected : Bool) :
    QueryImpl (LocalSpec n KemSK) (StateT (RegistrationNativeSecretWordInterpreter.State n KemSK) ProbComp) :=
  RegistrationNativeSecretWordTargetSource.implementation setup wire route sign input inside provider outer ∘ₛ
    RegistrationNativeSecretWordInterface.liftLocal selected

def lower (implementation : QueryImpl (LocalSpec n KemSK)
      (StateT (RegistrationNativeSecretWordInterpreter.State n KemSK) ProbComp))
    (work : StateT Environment (OracleComp (LocalSpec n KemSK)) Value) : StateT (Auxiliary n KemSK) ProbComp Value := fun before =>
  (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ implementation (work.run before.1)).run before.2

theorem lower_run (implementation : QueryImpl (LocalSpec n KemSK)
      (StateT (RegistrationNativeSecretWordInterpreter.State n KemSK) ProbComp))
    (work : StateT Environment (OracleComp (LocalSpec n KemSK)) Value) (before : Auxiliary n KemSK) :
    (lower implementation work).run before =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ implementation (work.run before.1)).run before.2 := rfl

private theorem lower_pure (implementation : QueryImpl (LocalSpec n KemSK)
      (StateT (RegistrationNativeSecretWordInterpreter.State n KemSK) ProbComp)) (value : Value) :
    lower implementation (pure value) = pure value := by
  apply StateT.ext
  intro before
  simp only [lower_run, StateT.run_pure, simulateQ_pure, map_pure]

/-- Lowering threads every actual new environment through the next callback. -/
theorem lower_bind (implementation : QueryImpl (LocalSpec n KemSK)
      (StateT (RegistrationNativeSecretWordInterpreter.State n KemSK) ProbComp))
    (work : StateT Environment (OracleComp (LocalSpec n KemSK)) Value)
    (next : Value → StateT Environment (OracleComp (LocalSpec n KemSK)) Next) :
    lower implementation (work >>= next) = (lower implementation work >>= fun value => lower implementation (next value)) := by
  apply StateT.ext
  intro before
  simp only [lower_run, StateT.run_bind, simulateQ_bind, map_bind, bind_map_left]

/-- Actual prefix oracle programs lower query by query on the reached environment. -/
theorem lower_program {Index : Type} {spec : OracleSpec Index}
    (implementation : QueryImpl (LocalSpec n KemSK)
      (StateT (RegistrationNativeSecretWordInterpreter.State n KemSK) ProbComp))
    (compiler : QueryImpl spec (StateT Environment (OracleComp (LocalSpec n KemSK))))
    (work : OracleComp spec Value) :
    lower implementation (simulateQ compiler work) = simulateQ (fun query => lower implementation (compiler query)) work := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure, lower_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, lower_bind]
      congr 1
      funext reply
      exact ih reply

noncomputable def prefixImpl (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
    (provider : Provider KemSK) (outer : QueryImpl Combined ProbComp) :
    QueryImpl (RegistrationNativeSecretWordServerCollect.Spec registration.InitPacket Unit PqxdhJointIdentity.PeerEncoding)
      (StateT (Auxiliary n KemSK) ProbComp) := fun query =>
  lower (localImpl setup wire route sign input inside provider outer true)
    (RegistrationNativeSecretWordServerCompiler.prefixImpl setup checks query)

/-- The actual successful collector is interpreted by this same selected primitive source at every callback. -/
theorem collect_run (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
    (provider : Provider KemSK) (outer : QueryImpl Combined ProbComp)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) :
    lower (localImpl (n := n) setup wire route sign input inside provider outer true)
      (RegistrationNativeSecretWordServerCompiler.collect setup checks packet authenticated) =
      simulateQ (prefixImpl setup checks wire route sign input inside provider outer)
        (RegistrationNativeSecretWordServerCollect.collect (RegistrationRootInput.verified packet authenticated)) := by
  rw [RegistrationNativeSecretWordServerCompiler.collect, lower_program]
  rfl

attribute [local irreducible] RegistrationNativeSecretWordServerCompiler.accept

private theorem serverOpen_run (selected : Bool)
    (work : RegistrationNativeSecretWordServerCompiler.M n KemSK Value)
    (before : RegistrationNativeSecretWordMessage.State source) :
    (RegistrationNativeSecretWordFrontend.serverOpen selected work).run before =
      (fun result => (result.1.1, { before with server := result.1.2, environment := result.2 })) <$>
        simulateQ (RegistrationNativeSecretWordInterface.liftLocal selected)
          ((work.run before.server).run before.environment) := rfl

private theorem handler_accept_run (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (packet : registration.InitPacket) (before : RegistrationNativeSecretWordMessage.State source) :
    (RegistrationNativeSecretWordFrontend.handler (n := n) setup checks wire source sign
      selectedOwner selectedAccept publicPrekey (.inr (.accept packet))).run before =
      (RegistrationNativeSecretWordFrontend.serverOpen (decide (before.parsedAccepts = selectedAccept))
        (RegistrationNativeSecretWordServerCompiler.accept setup checks source.verify packet)).run
          { before with parsedAccepts := before.parsedAccepts + 1 } := by
  simp only [RegistrationNativeSecretWordFrontend.handler, StateT.run_bind,
    StateT.run_get, StateT.run_modify, pure_bind]

/-- The complete typed selected-accept source is the actual Word controller, current environment and same private provider with its literal preincrement. -/
theorem accept_run (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
    (provider : Provider KemSK) (outer : QueryImpl Combined ProbComp)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (packet : registration.InitPacket) (before : RegistrationNativeSecretWordTargetSource.State n KemSK source)
    (selected : before.1.parsedAccepts = selectedAccept) :
    (RegistrationNativeSecretWordTargetSource.typed setup checks wire route sign input inside provider outer
      selectedOwner selectedAccept publicPrekey (.inr (.accept packet))).run before =
      (fun result => (result.1.1, ({ before.1 with server := result.1.2, environment := result.2.1, parsedAccepts := before.1.parsedAccepts + 1 }, result.2.2))) <$>
        (lower (localImpl setup wire route sign input inside provider outer true)
          ((RegistrationNativeSecretWordServerCompiler.accept setup checks source.verify packet).run before.1.server)).run
            (before.1.environment, before.2) := by
  rw [RegistrationNativeSecretWordTargetSource.typed_run, handler_accept_run]
  simp only [selected, decide_true]
  rw [serverOpen_run, lower_run, simulateQ_map, StateT.run_map, ← QueryImpl.simulateQ_compose]
  simp only [Functor.map_map]
  rfl

end BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetServerExecution
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetServerExecution.lower_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetServerExecution.lower_run
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetServerExecution.lower_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetServerExecution.lower_bind
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetServerExecution.lower_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetServerExecution.lower_program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetServerExecution.collect_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetServerExecution.collect_run
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetServerExecution.accept_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetServerExecution.accept_run
