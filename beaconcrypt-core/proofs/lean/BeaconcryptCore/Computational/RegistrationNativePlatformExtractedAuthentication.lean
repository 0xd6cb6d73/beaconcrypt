-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformAuthentication
import BeaconcryptCore.Computational.RegistrationNativePlatformSourceAccept
/-! Actual extracted Init and response authentication execute against the current shared World interpreter and arbitrary persistent outer monad. The source law retains the complete World state and only erases the authentication executor's analysis Event list from its reply. No controller, profile or security equation is a caller premise. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformExtractedAuthentication
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Codec)
variable [ed : AdapterInitEdPrimitive.Operations]
variable {n : Nat} {I KemSK Reader Response : Type} {base : OracleSpec I}
variable {m : Type →Type} [Monad m] [LawfulMonad m]
variable (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)

noncomputable def init (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket) :=
  simulateQ (AdapterPublicWrapperChildren.initQueries (RegistrationNativePlatformAuthentication.source (n:=n) coins setup codec route verify))
    (AdapterInitAuthenticationSourceLoop.authenticate (m:=AdapterInitAuthenticationRequestMonad.Program) pin packet).run

/-- Actual extracted Init authentication consumes the same World effects; only its analysis-only event list is projected from the reply. -/
theorem init_source (functional : RegistrationNativePlatformAuthentication.EdFunctional setup.source.crypto)
    (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket) :
    init (n:=n) coins setup codec route verify pin packet=
      AdapterInitAuthenticationDriver.observe <$>
        simulateQ (RegistrationNativePlatformAuthentication.core coins setup codec route verify)
          (RegistrationAuthenticationExecutor.begin pin packet) :=
  RegistrationNativePlatformAuthentication.init_source coins setup codec route verify functional pin packet

/-- The same actual Init source execution retains its full arbitrary before/after World and outer platform state. -/
theorem init_world (functional : RegistrationNativePlatformAuthentication.EdFunctional setup.source.crypto)
    (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket) (before : PqxdhRecordLiftWorld.State n) :
    (init coins setup codec route verify pin packet).run before=
      (fun result=>(AdapterInitAuthenticationDriver.observe result.1,result.2)) <$>
        simulateQ coins ((RegistrationWorldAuthentication.begin setup codec route verify pin packet).run before) :=
  RegistrationNativePlatformAuthentication.init_world coins setup codec route verify functional pin packet before

noncomputable def response (pending : registration.BeaconPending) (packet : Option registration.ResponsePacket) :=
  simulateQ (AdapterPublicWrapperChildren.response (RegistrationNativePlatformAuthentication.source (n:=n) coins setup codec route verify))
    (AdapterAuthenticationRequestExtraction.authenticate (m:=AdapterAuthenticationRequestMonad.Program) pending packet).run

/-- The checked lifted extracted response controller is exactly the current response child, including every optional or failed result. -/
theorem response_source (pending : registration.BeaconPending) (packet : Option registration.ResponsePacket) :
    response (n:=n) coins setup codec route verify pending packet=
      simulateQ (RegistrationNativePlatformAuthentication.core coins setup codec route verify)
        (RegistrationResponseExecutor.begin pending packet) :=
  RegistrationNativePlatformAuthentication.response_source coins setup codec route verify pending packet

/-- No cache or counter is reset when the actual response source is interpreted from a reached World state. -/
theorem response_world (pending : registration.BeaconPending) (packet : Option registration.ResponsePacket)
    (before : PqxdhRecordLiftWorld.State n) :
    (response coins setup codec route verify pending packet).run before=
      simulateQ coins ((simulateQ (RegistrationWorldAuthentication.implementation setup codec route verify)
        (RegistrationResponseExecutor.begin pending packet)).run before) :=
  RegistrationNativePlatformAuthentication.response_world coins setup codec route verify pending packet before

/-- Current typed acceptance's authentication child has the same full source result after erasing only its analysis reply events. -/
noncomputable def authenticate (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket) :
    StateT (RegistrationServerFrontendCompiler.State n) m
      (RustM (core.option.Option registration.AuthenticatedInit)) := fun before=>
  (fun result=>(result.1,{before with world:={before.world with world:=(result.2,before.world.world.2)}})) <$>
    (init coins setup codec route verify pin packet).run before.world.world.1

theorem authenticate_source (functional : RegistrationNativePlatformAuthentication.EdFunctional setup.source.crypto)
    (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket) :
    authenticate (n:=n) coins setup codec route verify pin packet=
      AdapterInitAuthenticationDriver.observe <$>
        RegistrationNativePlatformSourceAccept.authenticate coins setup codec route verify pin packet := by
  funext before
  change (authenticate coins setup codec route verify pin packet).run before=
    (AdapterInitAuthenticationDriver.observe <$>
      RegistrationNativePlatformSourceAccept.authenticate coins setup codec route verify pin packet).run before
  rw [StateT.run_map]
  change (fun result=>(result.1,{before with world:={before.world with world:=(result.2,before.world.world.2)}})) <$>
    (init coins setup codec route verify pin packet).run before.world.world.1 = _
  rw [init_world coins setup codec route verify functional pin packet]
  simp only [RegistrationNativePlatformSourceAccept.authenticate,StateT.run,Functor.map_map]


variable (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))

noncomputable def afterPin (reserve : StateT (RegistrationServerFrontendCompiler.State n) m Bool)
    (packet : registration.InitPacket) (result : RustM (core.option.Option session.ServerAuthenticationPin)) :
    StateT (RegistrationServerFrontendCompiler.State n) m (RustM (Option Nat)) :=
  match result with
  | .fail error=>pure (.fail error)
  | .div=>pure .div
  | .ok .None=>pure (.ok none)
  | .ok (.Some pin)=>do
      let checked←authenticate coins setup codec route verify pin packet
      match checked with
      | .fail error=>pure (.fail error)
      | .div=>pure .div
      | .ok .None=>pure (.ok none)
      | .ok (.Some accepted)=>RegistrationNativePlatformServerSdk.afterAuthentication coins setup checks reserve representation created packet accepted

/-- The original accept continuation sees the actual extracted authentication result on the same reached state. -/
theorem afterPin_source (functional : RegistrationNativePlatformAuthentication.EdFunctional setup.source.crypto)
    (reserve : StateT (RegistrationServerFrontendCompiler.State n) m Bool)
    (packet : registration.InitPacket) (result : RustM (core.option.Option session.ServerAuthenticationPin)) :
    afterPin coins setup codec route verify checks representation created reserve packet result=
      RegistrationNativePlatformSourceAccept.afterPin coins setup codec checks reserve route verify representation created packet result := by
  cases result with
  | fail error | div=>rfl
  | ok result=>
    cases result with
    | none=>rfl
    | some pin=>
      simp only [afterPin,RegistrationNativePlatformSourceAccept.afterPin]
      rw [authenticate_source coins setup codec route verify functional pin packet]
      rw [bind_map_left]
      apply congrArg (fun next=>RegistrationNativePlatformSourceAccept.authenticate coins setup codec route verify pin packet >>= next)
      funext checked
      cases checked with
      | fail error | div=>rfl
      | ok checked=>
        rcases checked with ⟨events,state⟩
        cases state <;> rfl

noncomputable def acceptWith
    (pin : StateT (RegistrationServerFrontendCompiler.State n) m (RustM (core.option.Option session.ServerAuthenticationPin)))
    (reserve : StateT (RegistrationServerFrontendCompiler.State n) m Bool) (packet : registration.InitPacket) :=do
  let current←pin
  afterPin coins setup codec route verify checks representation created reserve packet current

noncomputable def accept (reserve : m Bool) (packet : registration.InitPacket) :
    StateT (RegistrationServerFrontendCompiler.State n) m (RustM (Option Nat)) :=
  acceptWith coins setup codec route verify checks representation created
    (RegistrationNativePlatformSourceBuild.pin coins) (StateT.lift reserve) packet

theorem accept_source (functional : RegistrationNativePlatformAuthentication.EdFunctional setup.source.crypto)
    (reserve : m Bool) (packet : registration.InitPacket) :
    accept (n:=n) coins setup codec route verify checks representation created reserve packet=
      RegistrationNativePlatformSourceAccept.accept coins setup codec checks reserve route verify representation created packet := by
  unfold accept acceptWith RegistrationNativePlatformSourceAccept.accept RegistrationNativePlatformSourceAccept.acceptWith
  congr 1
  funext current
  exact afterPin_source coins setup codec route verify checks representation created functional _ packet current

end BeaconcryptCore.Computational.RegistrationNativePlatformExtractedAuthentication

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedAuthentication.init_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedAuthentication.init_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedAuthentication.init_world' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedAuthentication.init_world

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedAuthentication.response_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedAuthentication.response_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedAuthentication.response_world' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedAuthentication.response_world

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedAuthentication.authenticate_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedAuthentication.authenticate_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedAuthentication.afterPin_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedAuthentication.afterPin_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedAuthentication.accept_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedAuthentication.accept_source
