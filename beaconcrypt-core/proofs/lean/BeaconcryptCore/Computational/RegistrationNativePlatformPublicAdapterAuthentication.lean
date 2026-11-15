-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLeaves
import BeaconcryptCore.Refinement.AdapterPublicServerAuthenticationPrefix
/-! The actual Server pin recomputation and mandatory authentication use only the retained physical backend. Literal source operands and all shared-cache effects remain exact. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuthentication
open BeaconcryptCore.Refinement
open RegistrationNativePlatformSdkReification (Backend backend worldBackend)
variable {n : Nat} {I KemSK Reader Response : Type} {base : OracleSpec I}
variable {source : RegistrationNativeMldsa.Source}
variable (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))

noncomputable def hash (bytes : Pqxdh.Bytes) : StateT (Backend n KemSK) ProbComp CtxRomAuth.CtxDigest :=
  RegistrationNativePlatformSdkReification.backendLeaf setup checks representation created (.inr (.inl bytes))

theorem hash_source (bytes : Pqxdh.Bytes) (before : RegistrationNativeExperiment.State n KemSK source) :
    Prod.map id backend <$>
      (AdapterPublicServerWorldLens.world (n:=n) (KemSK:=KemSK) (mlSource:=source)
        (PqxdhRecordLiftWorld.effects (n:=n) (.inr (.hash bytes)))).run before=
      (hash setup checks representation created bytes).run (backend before) := by
  have same:=RegistrationNativePlatformSdkReification.hash_backend (n:=n) (source:=source) setup checks representation created bytes before
  change (Prod.map id backend <$> (RegistrationNativeExperiment.world
    (PqxdhRecordLiftWorld.effects (n:=n) (.inr (.hash bytes)))).run before : ProbComp (CtxRomAuth.CtxDigest×Backend n KemSK))=
    (hash setup checks representation created bytes).run (backend before) at same
  rw [AdapterPublicAgreementNativeWorldMap.world_run] at same
  rw [AdapterPublicServerWorldLens.world_run]
  exact same

noncomputable def pinHash : QueryImpl RegistrationNativeServerPinRecompute.Spec (StateT (Backend n KemSK) ProbComp) :=fun request=>do
  let digest←hash setup checks representation created (RegistrationInputs.hashBytes request)
  pure (.ok (.Some (RegistrationAuthenticationShared.digestArray digest)))

noncomputable def pin (binding : pqxdh.ServerBinding) (publicKey : Std.Array U8 1952#usize) :=
  simulateQ (pinHash (n:=n) setup checks representation created) (RegistrationNativeServerPinRecompute.program binding publicKey)

theorem pin_source (binding : pqxdh.ServerBinding) (publicKey : Std.Array U8 1952#usize)
    (before : RegistrationNativeExperiment.State n KemSK source) :
    Prod.map id backend <$>
      (AdapterPublicServerWorldLens.world (RegistrationNativeServerPinRecompute.native binding publicKey)).run before=
      (pin setup checks representation created binding publicKey).run (backend before) := by
  unfold RegistrationNativeServerPinRecompute.native pin
  rw [AdapterPublicServerWorldLens.simulate_world]
  apply OracleComp.map_run_simulateQ_eq_of_query_map_eq
  intro request state
  unfold RegistrationNativeServerPinRecompute.nativeHash pinHash
  simp only [AdapterPublicServerWorldLens.world_run,bind_pure_comp,StateT.run_map,Functor.map_map]
  have same:=congrArg (fun work=>(fun result=>(RustM.ok (core.option.Option.Some
    (RegistrationAuthenticationShared.digestArray result.1)),result.2)) <$>work)
    (hash_source setup checks representation created (RegistrationInputs.hashBytes request) state)
  simp only [AdapterPublicServerWorldLens.world_run,Functor.map_map,Prod.map,id_eq] at same ⊢
  convert same using 1
  rfl

noncomputable def callbacks (verify : MldsaTranscriptAuth.Verify) :
    QueryImpl RegistrationAuthenticationExecutor.Spec (StateT (Backend n KemSK) ProbComp)
  | .hash request=>do
    let digest←hash setup checks representation created (RegistrationInputs.hashBytes request)
    pure (.Some (RegistrationAuthenticationShared.digestArray digest))
  | .mldsa request=>pure (RegistrationAuthenticationShared.verifyMldsa verify request)
  | .ed25519 request=>pure (RegistrationAuthenticationShared.verifyEd25519 setup.source.crypto request)

noncomputable def authenticate (verify : MldsaTranscriptAuth.Verify)
    (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket) :=
  simulateQ (callbacks (n:=n) setup checks representation created verify) (RegistrationAuthenticationExecutor.begin pin packet)

theorem authenticate_source (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket)
    (before : RegistrationNativeExperiment.State n KemSK source) :
    Prod.map id backend <$>
      (AdapterPublicServerWorldLens.world (RegistrationWorldAuthentication.begin setup codec route verify pin packet)).run before=
      (authenticate setup checks representation created verify pin packet).run (backend before) := by
  unfold RegistrationWorldAuthentication.begin RegistrationWorldAuthentication.program authenticate
  rw [←QueryImpl.simulateQ_compose,AdapterPublicServerWorldLens.simulate_world]
  apply OracleComp.map_run_simulateQ_eq_of_query_map_eq
  intro query state
  cases query with
  | mldsa request | ed25519 request=>
    simp only [callbacks,QueryImpl.apply_compose,RegistrationWorldAuthentication.callbacks,simulateQ_pure,
      AdapterPublicServerWorldLens.pure_world,StateT.run_pure,map_pure]
    rfl
  | hash request=>
    simp only [callbacks,QueryImpl.apply_compose,RegistrationWorldAuthentication.callbacks,simulateQ_map,
      simulateQ_spec_query,PqxdhRecordLiftWorld.handler,AdapterPublicServerWorldLens.world_run,
      bind_pure_comp,StateT.run_map,Functor.map_map]
    have same:=congrArg (fun work=>(fun result=>(core.option.Option.Some
      (RegistrationAuthenticationShared.digestArray result.1),result.2)) <$>work)
      (hash_source setup checks representation created (RegistrationInputs.hashBytes request) state)
    simp only [AdapterPublicServerWorldLens.world_run,Functor.map_map,Prod.map,id_eq] at same ⊢
    convert same using 1 <;> rfl

noncomputable def afterPin (verify : MldsaTranscriptAuth.Verify) (control : pqxdh.ServerState)
    (packet : registration.InitPacket) (reply : RegistrationNativeServerPinRecompute.PinReply) :
    StateT (Backend n KemSK) ProbComp (RustM (core.option.Option peer.RegistrationLookup)) :=
  match reply with
  | .fail error=>pure (.fail error)
  | .div=>pure .div
  | .ok .None=>pure (.ok .None)
  | .ok (.Some pin)=>AdapterPublicServerAuthentication.observed control <$>
      authenticate setup checks representation created verify pin packet

noncomputable def prefixProgram (verify : MldsaTranscriptAuth.Verify) (control : pqxdh.ServerState)
    (binding : pqxdh.ServerBinding) (publicKey : Std.Array U8 1952#usize) (packet : registration.InitPacket) :=do
  let reply←pin (n:=n) setup checks representation created binding publicKey
  afterPin setup checks representation created verify control packet reply

theorem pin_platform {P : Type} (coins : QueryImpl unifSpec (StateT P ProbComp))
    (binding : pqxdh.ServerBinding) (publicKey : Std.Array U8 1952#usize)
    (before : RegistrationNativeExperiment.State n KemSK source) :
    Prod.map id backend <$>
      (AdapterPublicServerWorldLens.world
        (RegistrationNativePlatformInterpret.state coins (RegistrationNativeServerPinRecompute.native binding publicKey))).run before=
      simulateQ coins ((pin setup checks representation created binding publicKey).run (backend before)) := by
  have same:=congrArg (simulateQ coins) (pin_source setup checks representation created binding publicKey before)
  simp only [AdapterPublicServerWorldLens.world_run,simulateQ_map] at same ⊢
  convert same using 1
  rfl

variable [ed : AdapterInitEdPrimitive.Operations]

theorem afterPin_platform {P : Type} (coins : QueryImpl unifSpec (StateT P ProbComp))
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (verify : MldsaTranscriptAuth.Verify)
    (edLaws : RegistrationNativePlatformAuthentication.EdFunctional setup.source.crypto)
    (control : pqxdh.ServerState) (packet : registration.InitPacket)
    (reply : RegistrationNativeServerPinRecompute.PinReply) (before : RegistrationNativeExperiment.State n KemSK source) :
    Prod.map id backend <$>
      (AdapterPublicServerWorldLens.world
        (AdapterPublicServerAuthentication.afterPin
          (RegistrationNativePlatformAuthentication.native coins setup codec route verify edLaws) control packet reply)).run before=
      simulateQ coins ((afterPin setup checks representation created verify control packet reply).run (backend before)) := by
  rw [AdapterPublicServerWorldLens.world_run,AdapterPublicServerAuthenticationPrefix.after_pin_run]
  cases reply with
  | fail error | div=>simp only [afterPin,StateT.run_pure,map_pure,simulateQ_pure];rfl
  | ok optional=>cases optional with
    | none=>simp only [afterPin,StateT.run_pure,map_pure,simulateQ_pure];rfl
    | some pin=>
      simp only [afterPin,StateT.run_map,simulateQ_map,Functor.map_map]
      have same:=congrArg (fun work=>simulateQ coins ((fun result=>(AdapterPublicServerAuthentication.observed control result.1,result.2)) <$>work))
        (authenticate_source setup checks representation created codec route verify pin packet before)
      simp only [AdapterPublicServerWorldLens.world_run,simulateQ_map,Functor.map_map,Prod.map,id_eq] at same ⊢
      convert same using 1

theorem prefix_source {P : Type} (coins : QueryImpl unifSpec (StateT P ProbComp))
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (verify : MldsaTranscriptAuth.Verify)
    (edLaws : RegistrationNativePlatformAuthentication.EdFunctional setup.source.crypto)
    (control : pqxdh.ServerState) (binding : pqxdh.ServerBinding)
    (publicKey : Std.Array U8 1952#usize) (packet : registration.InitPacket)
    (before : RegistrationNativeExperiment.State n KemSK source) :
    Prod.map id backend <$>
      (AdapterPublicServerWorldLens.world (AdapterPublicServerAuthenticationPrefix.program coins setup codec route verify edLaws
        control binding publicKey packet)).run before=
      simulateQ coins ((prefixProgram setup checks representation created verify control binding publicKey packet).run (backend before)) := by
  unfold AdapterPublicServerAuthenticationPrefix.program prefixProgram
  rw [AdapterPublicServerWorldLens.bind_world]
  simp only [StateT.run_bind,map_bind,simulateQ_bind]
  rw [←pin_platform setup checks representation created coins binding publicKey before,bind_map_left]
  apply bind_congr
  rintro ⟨reply,current⟩
  exact afterPin_platform setup checks representation created coins codec route verify edLaws control packet reply current

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuthentication

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuthentication.hash_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuthentication.hash_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuthentication.pin_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuthentication.pin_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuthentication.authenticate_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuthentication.authenticate_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuthentication.pin_platform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuthentication.pin_platform

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuthentication.afterPin_platform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuthentication.afterPin_platform

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuthentication.prefix_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuthentication.prefix_source
