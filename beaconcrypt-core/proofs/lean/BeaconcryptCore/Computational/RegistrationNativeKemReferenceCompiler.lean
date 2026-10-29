-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationBeaconReferenceCompiler
import BeaconcryptCore.Computational.RegistrationServerReferenceCompiler
import BeaconcryptCore.Computational.RegistrationNativeKemBackend

/-! The Server related-root reference prefix shares the actual indexed KEM service with the native selected-accept compiler. Ordinary local callbacks retain their original open Env coin program; the literal encapsulation getter is forwarded instead of being sampled inside that program. The environment still contains only local ephemeral state and public request/receipt logs. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemReferenceCompiler
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationServerReferenceCompiler (Environment)
open RegistrationBeaconReferenceCompiler (indexed)
variable {ι KemSK Value : Type} {base : OracleSpec ι} {n : Nat}

abbrev Spec (n : Nat) (KemSK : Type) := RegistrationBeaconReferenceCompiler.Spec n KemSK

def lift : QueryImpl (RegistrationServerReferenceCompiler.Spec n) (OracleComp (Spec n KemSK))
  | .inl message => (Spec n KemSK).query (.inl message)
  | .inr query => (Spec n KemSK).query (.inr (.inl query))

def ordinary (work : StateT Environment (OracleComp (RegistrationServerReferenceCompiler.Spec n)) Value) :
    StateT Environment (OracleComp (Spec n KemSK)) Value := fun before => simulateQ lift (work.run before)

noncomputable def backend (setup : Setup base KemSK) (checks : Checks) :
    QueryImpl RegistrationAgreementExecutor.Spec (StateT Environment (OracleComp (Spec n KemSK)))
  | .encapsulate key => fun before => (fun reply => (reply,
      { before with requests := before.requests ++ RegistrationWorldAgreement.recorded (.encapsulate key) })) <$>
        simulateQ indexed (RegistrationNativeKemInterface.server checks (.encapsulate key))
  | .convertPublic key => ordinary (RegistrationServerReferenceCompiler.backend setup checks (.convertPublic key))
  | .convertSecret role => ordinary (RegistrationServerReferenceCompiler.backend setup checks (.convertSecret role))
  | .generate role => ordinary (RegistrationServerReferenceCompiler.backend setup checks (.generate role))
  | .decapsulate ciphertext => ordinary (RegistrationServerReferenceCompiler.backend setup checks (.decapsulate ciphertext))
  | .dh request => ordinary (RegistrationServerReferenceCompiler.backend setup checks (.dh request))
  | .root request => ordinary (RegistrationServerReferenceCompiler.backend setup checks (.root request))

def visit (point : PqxdhBeaconPhase2Preparation.Word32) : StateT Environment (OracleComp (Spec n KemSK)) Unit :=
  ordinary (RegistrationServerReferenceCompiler.visit point)

noncomputable def collect (setup : Setup base KemSK) (checks : Checks)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) :
    StateT Environment (OracleComp (Spec n KemSK))
      (Option (PqxdhServerRootPreparation.Inputs registration.InitPacket Unit PqxdhJointIdentity.PeerEncoding)) :=
  simulateQ (PqxdhServerStaticDhSource.prefixImpl setup.serverDomain
    (RegistrationAgreementInterpreter.prepImpl (backend setup checks)) visit)
    (PqxdhServerRootPreparation.collectVerified (RegistrationRootInput.verified packet authenticated))

/-- The actual native encapsulation callback forwards the checked key to the indexed service and preserves its complete chronological request marker. -/
theorem backend_encapsulation (setup : Setup base KemSK) (checks : Checks)
    (key : core.option.Option (Std.Array U8 1184#usize)) (before : Environment) :
    (backend (n := n) setup checks (.encapsulate key)).run before =
      (fun reply => (reply, { before with requests := before.requests ++ RegistrationWorldAgreement.recorded (.encapsulate key) })) <$>
        simulateQ indexed (RegistrationNativeKemInterface.server checks (.encapsulate key)) := rfl

def NonEncapsulation : RegistrationAgreementExecutor.Request → Prop
  | .encapsulate _ => False
  | _ => True

/-- Every other actual local callback retains the complete old source Env coin and log computation, rather than receiving a fabricated reply. -/
theorem backend_ordinary (setup : Setup base KemSK) (checks : Checks)
    (query : RegistrationAgreementExecutor.Request) (notKem : NonEncapsulation query) (before : Environment) :
    (backend (n := n) setup checks query).run before =
      simulateQ lift ((RegistrationServerReferenceCompiler.backend setup checks query).run before) := by
  cases query <;> first | rfl | exact notKem.elim

/-- In real mode the indexed getter is exactly the concrete native Server encapsulation, retaining its whole local state and private pool. -/
theorem encapsulation_source (setup : Setup base KemSK) (checks : Checks)
    (other : QueryImpl RegistrationNativeKemInterface.OtherSpec (StateT RegistrationServerRoleBackend.State ProbComp))
    (key : core.option.Option (Std.Array U8 1184#usize))
    (before : RegistrationServerRoleBackend.State × PqxdhLiveKemBirth.Pool KemSK) :
    (simulateQ (RegistrationNativeKemInterface.source setup.baseImpl setup.kem RegistrationNativeKemInterface.OtherSpec other)
      (RegistrationNativeKemInterface.server checks (.encapsulate key))).run before =
      (fun result => (result.1, (result.2, before.2))) <$>
        (RegistrationServerRoleBackend.localBackend setup checks (.encapsulate key)).run before.1 := by
  cases key with
  | none => simp only [RegistrationNativeKemInterface.server, simulateQ_pure, StateT.run_pure,
      RegistrationServerRoleBackend.localBackend, map_pure]
  | some key =>
      simp only [RegistrationNativeKemInterface.server, RegistrationServerRoleBackend.localBackend]
      split
      · simp only [RegistrationNativeKemInterface.encapsulate, simulateQ_map, simulateQ_spec_query,
          RegistrationNativeKemInterface.source, StateT.run_map, StateT.run_lift, bind_pure_comp,
          PqxdhServerAuthExperiment.encapsulate, Functor.map_map, RegistrationAgreementRoot.nativeOption]
        rfl
      · simp only [simulateQ_pure, StateT.run_pure, map_pure]

/-- The actual normalized native agreement still realizes the selected-DH source prefix with this same open indexed KEM backend. -/
theorem native_collect (setup : Setup base KemSK) (checks : Checks) (seed : PqxdhJointIdentity.IdentitySeed)
    (control : pqxdh.ServerState) (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) :
    simulateQ (RegistrationAgreementInterpreter.sourceImpl setup.joint seed (backend (n := n) setup checks) visit)
        (RegistrationAgreementExecutor.server control .Fresh authenticated) =
        (show StateT Environment (OracleComp (Spec n KemSK)) (RustM agreement.AgreementEffect) from do
      let input ← simulateQ (PqxdhServerStaticDhSource.nativeImpl setup.joint seed
        (RegistrationAgreementInterpreter.prepImpl (backend setup checks)) visit)
        (PqxdhServerRootPreparation.collectVerified (RegistrationRootInput.verified packet authenticated))
      match input with
      | none => pure (.ok (.Rejected .None))
      | some input =>
          simulateQ (RegistrationAgreementInterpreter.sourceImpl setup.joint seed (backend setup checks) visit)
            (RegistrationAgreementRoot.finish control authenticated input)) :=
  RegistrationAgreementInterpreter.server_source setup.joint seed (backend setup checks) visit control packet authenticated

end BeaconcryptCore.Computational.RegistrationNativeKemReferenceCompiler

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemReferenceCompiler.backend_encapsulation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemReferenceCompiler.backend_encapsulation
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemReferenceCompiler.backend_ordinary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemReferenceCompiler.backend_ordinary
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemReferenceCompiler.encapsulation_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemReferenceCompiler.encapsulation_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemReferenceCompiler.native_collect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemReferenceCompiler.native_collect
