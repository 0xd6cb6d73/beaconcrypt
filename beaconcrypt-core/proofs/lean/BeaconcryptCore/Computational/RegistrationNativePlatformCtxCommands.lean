-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformCtxContext
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainAmbient
/-! Literal public environment and four ordinary record commands expose shared CTX queries while retaining the same outer native context and persistent platform state. Owner lookup uses only the existing public World handle. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformCtxCommands
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Codec Checks)
open RegistrationNativePlatformCtxContext (M Full interpret realize)
open PqxdhRecordLiftInterface (RecordQuery WorldSpec)
open RegistrationNativeRawAdapter (TypedSpec)
variable {n : Nat} {I KemSK Reader Response Platform E : Type} {base : OracleSpec I}

noncomputable def record (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (route : RawCtxServerRouting.SenderDecoder) (owners : List Nat) :
    (query : RecordQuery) → M n KemSK Platform ((PqxdhRecordLiftInterface.RecordSpec .O).Range query)
  | .inl query => RegistrationNativePlatformCtxContext.guarded setup codec reserve route (.inr (.inr (.inl query)))
  | .inr (index, .inl plaintext) => match owners[index]? with
      | none => pure none
      | some selected => RegistrationNativePlatformCtxContext.guarded setup codec reserve route (.inr (.inr (.inr (selected, .inl plaintext))))
  | .inr (index, .inr raw) => match owners[index]? with
      | none => pure .None
      | some selected => RegistrationNativePlatformCtxContext.guarded setup codec reserve route (.inr (.inr (.inr (selected, .inr raw))))

noncomputable def nativeRecord (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (route : RawCtxServerRouting.SenderDecoder) (owners : List Nat) :
    (query : RecordQuery) → StateT (RegistrationNativeIdentityWorld.Context n KemSK × Platform) ProbComp ((PqxdhRecordLiftInterface.RecordSpec .O).Range query)
  | .inl query => RegistrationNativePlatformCtxContext.nativeWorld (RegistrationNativePlatformOrdinaryWorld.guarded setup codec reserve route (.inr (.inr (.inl query))))
  | .inr (index, .inl plaintext) => match owners[index]? with
      | none => pure none
      | some selected => RegistrationNativePlatformCtxContext.nativeWorld (RegistrationNativePlatformOrdinaryWorld.guarded setup codec reserve route (.inr (.inr (.inr (selected, .inl plaintext)))))
  | .inr (index, .inr raw) => match owners[index]? with
      | none => pure .None
      | some selected => RegistrationNativePlatformCtxContext.nativeWorld (RegistrationNativePlatformOrdinaryWorld.guarded setup codec reserve route (.inr (.inr (.inr (selected, .inr raw)))))

private theorem state_pure_apply {S X : Type} {m : Type → Type} [Monad m]
    (value : X) (before : S) : (pure value : StateT S m X) before = pure (value, before) := rfl

private theorem pure_source {A : Type} (value : A) (before : Full n KemSK Platform) :
    Prod.map id realize <$> (interpret (pure value : M n KemSK Platform A)).run before =
      (pure value : StateT (RegistrationNativeIdentityWorld.Context n KemSK × Platform) ProbComp A).run (realize before) := by
  simp only [RegistrationNativePlatformCtxContext.interpret, StateT.run, state_pure_apply, simulateQ_pure, map_pure, Prod.map_def, id_eq]

/-- Every real ordinary route keeps its actual hash requests, frame writer failures, public handle lookup and full Context/P result. -/
theorem record_source (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (route : RawCtxServerRouting.SenderDecoder) (owners : List Nat) (query : RecordQuery) (before : Full n KemSK Platform) :
    Prod.map id realize <$> (interpret (record setup codec reserve route owners query)).run before =
      (nativeRecord setup codec reserve route owners query).run (realize before) := by
  cases query with
  | inl query => exact RegistrationNativePlatformCtxContext.guarded_source setup codec reserve route (.inr (.inr (.inl query))) before
  | inr query =>
    rcases query with ⟨index, query⟩
    cases query with
    | inl plaintext => cases found : owners[index]? with
      | none => simpa only [record, nativeRecord, found] using pure_source (n := n) (none : Option RawCtxSourceSend.Encrypted) before
      | some selected => simpa only [record, nativeRecord, found] using RegistrationNativePlatformCtxContext.guarded_source setup codec reserve route (.inr (.inr (.inr (selected, .inl plaintext)))) before
    | inr raw => cases found : owners[index]? with
      | none => simpa only [record, nativeRecord, found] using pure_source (n := n) (core.option.Option.None : core.option.Option RawCtxWholeOwner.Decrypted) before
      | some selected => simpa only [record, nativeRecord, found] using RegistrationNativePlatformCtxContext.guarded_source setup codec reserve route (.inr (.inr (.inr (selected, .inr raw)))) before

noncomputable def command (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (route : RawCtxServerRouting.SenderDecoder) (owners : List Nat) :
    (query : TypedSpec.Domain) → M n KemSK Platform (TypedSpec.Range query)
  | .inl coin => RegistrationNativePlatformCtxContext.guarded setup codec reserve route (.inr (.inl (.inl coin)))
  | .inr (.hmac key message) => pure (setup.hmac.eval key message)
  | .inr (.hash bytes) => RegistrationNativePlatformCtxContext.guarded setup codec reserve route (.inr (.inl (.inr (.hash bytes))))
  | .inr (.serverSend keyId plaintext) => record setup codec reserve route owners (.inl (.inl (plaintext, keyId)))
  | .inr (.serverRaw raw) => record setup codec reserve route owners (.inl (.inr raw))
  | .inr (.beaconSend index plaintext) => record setup codec reserve route owners (.inr (index, .inl plaintext))
  | .inr (.beaconRaw index raw) => record setup codec reserve route owners (.inr (index, .inr raw))
  | .inr (.create ..) => pure (.ok none)
  | .inr (.bundle ..) => pure (.ok none)
  | .inr (.accept ..) => pure (.ok none)
  | .inr (.build ..) => pure (.ok none)
  | .inr (.finish ..) => pure (.ok none)

noncomputable def nativeCommand (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (route : RawCtxServerRouting.SenderDecoder) (owners : List Nat) :
    (query : TypedSpec.Domain) → StateT (RegistrationNativeIdentityWorld.Context n KemSK × Platform) ProbComp (TypedSpec.Range query)
  | .inl coin => (fun query => RegistrationNativePlatformCtxContext.nativeWorld (RegistrationNativePlatformOrdinaryWorld.guarded setup codec reserve route query)) (.inr (.inl (.inl coin)))
  | .inr (.hmac key message) => pure (setup.hmac.eval key message)
  | .inr (.hash bytes) => (fun query => RegistrationNativePlatformCtxContext.nativeWorld (RegistrationNativePlatformOrdinaryWorld.guarded setup codec reserve route query)) (.inr (.inl (.inr (.hash bytes))))
  | .inr (.serverSend keyId plaintext) => nativeRecord setup codec reserve route owners (.inl (.inl (plaintext, keyId)))
  | .inr (.serverRaw raw) => nativeRecord setup codec reserve route owners (.inl (.inr raw))
  | .inr (.beaconSend index plaintext) => nativeRecord setup codec reserve route owners (.inr (index, .inl plaintext))
  | .inr (.beaconRaw index raw) => nativeRecord setup codec reserve route owners (.inr (index, .inr raw))
  | .inr (.create ..) => pure (.ok none)
  | .inr (.bundle ..) => pure (.ok none)
  | .inr (.accept ..) => pure (.ok none)
  | .inr (.build ..) => pure (.ok none)
  | .inr (.finish ..) => pure (.ok none)

/-- The ordinary dictionary has the exact same joint native/cache and P interpretation through every reply. Its five registration branches are supplied separately by the final dispatcher. -/
theorem command_source (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (route : RawCtxServerRouting.SenderDecoder) (owners : List Nat) (query : TypedSpec.Domain) (before : Full n KemSK Platform) :
    Prod.map id realize <$> (interpret (command setup codec reserve route owners query)).run before =
      (nativeCommand setup codec reserve route owners query).run (realize before) := by
  cases query with
  | inl coin => exact RegistrationNativePlatformCtxContext.guarded_source setup codec reserve route (.inr (.inl (.inl coin))) before
  | inr query => cases query with
    | hmac key message => exact pure_source _ before
    | hash bytes => exact RegistrationNativePlatformCtxContext.guarded_source setup codec reserve route (.inr (.inl (.inr (.hash bytes)))) before
    | serverSend keyId plaintext => exact record_source setup codec reserve route owners (.inl (.inl (plaintext, keyId))) before
    | serverRaw raw => exact record_source setup codec reserve route owners (.inl (.inr raw)) before
    | beaconSend index plaintext => exact record_source setup codec reserve route owners (.inr (index, .inl plaintext)) before
    | beaconRaw index raw => exact record_source setup codec reserve route owners (.inr (index, .inr raw)) before
    | create edPin mlPin keyId => exact pure_source _ before
    | bundle index => exact pure_source _ before
    | accept packet => exact pure_source _ before
    | build handle application => exact pure_source _ before
    | finish index packet => exact pure_source _ before

private theorem state_map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

private theorem native_world {A : Type} {source : RegistrationNativeMldsa.Source}
    (work : RegistrationNativePlatformOrdinaryWorld.M n Platform A)
    (owners : RegistrationNativeIdentityFrontend.State source)
    (before : RegistrationNativeIdentityWorld.Context n KemSK × Platform) :
    (fun result => (result.1.1, (RegistrationNativeIdentityWorld.project result.1.2, result.2))) <$>
      ((RegistrationNativePlatformOrdinaryExperiment.world work).run
        (RegistrationNativeIdentityMainOrdinary.attach (RegistrationNativePlatformIdentityMainAmbient.dummyOwners owners) before.1)).run before.2 =
      (RegistrationNativePlatformCtxContext.nativeWorld work).run before := by
  simp only [RegistrationNativePlatformOrdinaryExperiment.world, RegistrationNativePlatformOrdinaryExperiment.replaceWorld,
    RegistrationNativeIdentityWorld.project, RegistrationNativeIdentityMainOrdinary.attach,
    RegistrationNativePlatformCtxContext.nativeWorld, RegistrationNativePlatformCtxContext.attach,
    StateT.run, state_map_apply, Functor.map_map, Prod.map_def, id_eq]

private theorem state_lift_apply {S X : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : m X) (before : S) :
    (StateT.lift work : StateT S m X) before = (fun value => (value, before)) <$> work := by
  change (do let value ← work; pure (value, before)) = _
  rw [bind_pure_comp]

private theorem lifted_world {A : Type} {source : RegistrationNativeMldsa.Source}
    (work : StateT (PqxdhRecordLiftWorld.State n) ProbComp A) :
    RegistrationNativePlatformExperiment.liftNative (RegistrationNativePlatformMldsaProgram.coins (Platform := Platform))
      (RegistrationNativeExperiment.world (KemSK := KemSK) (mlSource := source) work) =
      RegistrationNativePlatformOrdinaryExperiment.world (RegistrationNativePlatformOrdinaryWorld.liftWorld work) := by
  funext before previous
  simp only [RegistrationNativePlatformExperiment.liftNative, RegistrationNativePlatformMldsaProgram.lift_coins,
    RegistrationNativeExperiment.world, RegistrationNativeExperiment.server,
    RegistrationNativePlatformOrdinaryWorld.liftWorld, RegistrationNativePlatformOrdinaryExperiment.world,
    RegistrationNativePlatformOrdinaryExperiment.replaceWorld, StateT.run, state_map_apply, state_lift_apply, Functor.map_map, Prod.map_def, id_eq]

private theorem native_pure {A : Type} {source : RegistrationNativeMldsa.Source} (value : A)
    (owners : RegistrationNativeIdentityFrontend.State source)
    (before : RegistrationNativeIdentityWorld.Context n KemSK × Platform) :
    (fun result => (result.1.1, (RegistrationNativeIdentityWorld.project result.1.2, result.2))) <$>
      ((pure value : RegistrationNativePlatformOrdinaryExperiment.M n KemSK source Platform A).run
        (RegistrationNativeIdentityMainOrdinary.attach (RegistrationNativePlatformIdentityMainAmbient.dummyOwners owners) before.1)).run before.2 =
      pure (value, before) := by
  simp only [StateT.run_pure, map_pure, RegistrationNativeIdentityWorld.project,
    RegistrationNativeIdentityMainOrdinary.attach]

private theorem record_literal {source : RegistrationNativeMldsa.Source}
    (setup : Setup base KemSK)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (route : RawCtxServerRouting.SenderDecoder) (wire : RegistrationNativeWire.Wire)
    (owners : RegistrationNativeIdentityFrontend.State source) (query : RecordQuery)
    (before : RegistrationNativeIdentityWorld.Context n KemSK × Platform) :
    (fun result => (result.1.1, (RegistrationNativeIdentityWorld.project result.1.2, result.2))) <$>
      ((RegistrationNativePlatformOrdinaryExperiment.record setup wire reserve route query source).run
        (RegistrationNativeIdentityMainOrdinary.attach (RegistrationNativePlatformIdentityMainAmbient.dummyOwners owners) before.1)).run before.2 =
      (nativeRecord setup (RegistrationNativeWire.ledgerCodec wire) reserve route (owners.map (fun selected => selected.worldOwner)) query).run before := by
  cases query with
  | inl query => cases query with
    | inl pair =>
      simp only [RegistrationNativePlatformOrdinaryExperiment.record, nativeRecord]
      exact native_world (RegistrationNativePlatformOrdinaryWorld.guarded setup (RegistrationNativeWire.ledgerCodec wire) reserve route (.inr (.inr (.inl (.inl pair))))) owners before
    | inr raw =>
      simp only [RegistrationNativePlatformOrdinaryExperiment.record, nativeRecord]
      exact native_world (RegistrationNativePlatformOrdinaryWorld.guarded setup (RegistrationNativeWire.ledgerCodec wire) reserve route (.inr (.inr (.inl (.inr raw))))) owners before
  | inr query =>
    rcases query with ⟨index, query⟩
    cases query with
    | inl plaintext => cases found : owners[index]? with
      | none =>
        simp only [RegistrationNativePlatformOrdinaryExperiment.record, nativeRecord,
          RegistrationNativeIdentityMainOrdinary.attach, RegistrationNativePlatformIdentityMainAmbient.dummyOwners,
          StateT.run, List.getElem?_map, found, Option.map_none, state_pure_apply]
        exact native_pure (n := n) (none : Option RawCtxSourceSend.Encrypted) owners before
      | some selected =>
        simp only [RegistrationNativePlatformOrdinaryExperiment.record, nativeRecord,
          RegistrationNativeIdentityMainOrdinary.attach, RegistrationNativePlatformIdentityMainAmbient.dummyOwners,
          StateT.run, List.getElem?_map, found, Option.map_some, RegistrationNativeIdentityFrontend.restore]
        exact native_world (RegistrationNativePlatformOrdinaryWorld.guarded setup (RegistrationNativeWire.ledgerCodec wire) reserve route (.inr (.inr (.inr (selected.worldOwner, .inl plaintext))))) owners before
    | inr raw => cases found : owners[index]? with
      | none =>
        simp only [RegistrationNativePlatformOrdinaryExperiment.record, nativeRecord,
          RegistrationNativeIdentityMainOrdinary.attach, RegistrationNativePlatformIdentityMainAmbient.dummyOwners,
          StateT.run, List.getElem?_map, found, Option.map_none, state_pure_apply]
        exact native_pure (n := n) (core.option.Option.None : core.option.Option RawCtxWholeOwner.Decrypted) owners before
      | some selected =>
        simp only [RegistrationNativePlatformOrdinaryExperiment.record, nativeRecord,
          RegistrationNativeIdentityMainOrdinary.attach, RegistrationNativePlatformIdentityMainAmbient.dummyOwners,
          StateT.run, List.getElem?_map, found, Option.map_some, RegistrationNativeIdentityFrontend.restore]
        exact native_world (RegistrationNativePlatformOrdinaryWorld.guarded setup (RegistrationNativeWire.ledgerCodec wire) reserve route (.inr (.inr (.inr (selected.worldOwner, .inr raw))))) owners before

private theorem guarded_effect (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (route : RawCtxServerRouting.SenderDecoder) (query : (PqxdhRecordLiftInterface.EnvEffects n).Domain) :
    RegistrationNativePlatformOrdinaryWorld.guarded setup codec reserve route (.inr (.inl query)) =
      RegistrationNativePlatformOrdinaryWorld.liftWorld (PqxdhRecordLiftWorld.effects query) := rfl

private theorem lifted_pure {A : Type} {source : RegistrationNativeMldsa.Source} (value : A) :
    RegistrationNativePlatformExperiment.liftNative (RegistrationNativePlatformMldsaProgram.coins (Platform := Platform))
      (pure value : RegistrationNativeExperiment.M n KemSK source A) =
      (pure value : RegistrationNativePlatformOrdinaryExperiment.M n KemSK source Platform A) := by
  funext before previous
  simp only [RegistrationNativePlatformExperiment.liftNative, StateT.run, state_pure_apply, simulateQ_pure]

def IsOrdinary : TypedSpec.Domain → Prop
  | .inr (.create ..) | .inr (.bundle ..) | .inr (.accept ..) | .inr (.build ..) | .inr (.finish ..) => False
  | _ => True

variable [primitive : AdapterSealPrimitive.Operations]
variable {source : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
variable (keys : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))

private theorem handler_uniform (coin : unifSpec.Domain) :
    RegistrationNativePlatformOrdinaryExperiment.handler (n := n) setup checks wire route representation created source credential keys failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer (Sum.inl coin) =
      RegistrationNativePlatformExperiment.liftNative RegistrationNativePlatformMldsaProgram.coins
        (RegistrationNativeExperiment.world (PqxdhRecordLiftWorld.effects (.inl coin))) := rfl

private theorem handler_hash (bytes : Pqxdh.Bytes) :
    RegistrationNativePlatformOrdinaryExperiment.handler (n := n) setup checks wire route representation created source credential keys failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer (Sum.inr (.hash bytes)) =
      RegistrationNativePlatformExperiment.liftNative RegistrationNativePlatformMldsaProgram.coins
        (RegistrationNativeExperiment.world (PqxdhRecordLiftWorld.effects (.inr (.hash bytes)))) := rfl

private theorem handler_hmac (key : PqxdhSecretInputKdf.HmacBlock) (message : Pqxdh.Bytes) :
    RegistrationNativePlatformOrdinaryExperiment.handler (n := n) setup checks wire route representation created source credential keys failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer (Sum.inr (.hmac key message)) =
      RegistrationNativePlatformExperiment.liftNative RegistrationNativePlatformMldsaProgram.coins
        (pure (setup.hmac.eval key message)) := rfl

private theorem handler_server_send (keyId : U64) (plaintext : Pqxdh.Bytes) :
    RegistrationNativePlatformOrdinaryExperiment.handler (n := n) setup checks wire route representation created source credential keys failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer (Sum.inr (.serverSend keyId plaintext)) =
      RegistrationNativePlatformOrdinaryExperiment.record setup wire reserveFrame route (.inl (.inl (plaintext, keyId))) source := rfl

private theorem handler_server_raw (raw : Pqxdh.Bytes) :
    RegistrationNativePlatformOrdinaryExperiment.handler (n := n) setup checks wire route representation created source credential keys failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer (Sum.inr (.serverRaw raw)) =
      RegistrationNativePlatformOrdinaryExperiment.record setup wire reserveFrame route (.inl (.inr raw)) source := rfl

private theorem handler_beacon_send (index : Nat) (plaintext : Pqxdh.Bytes) :
    RegistrationNativePlatformOrdinaryExperiment.handler (n := n) setup checks wire route representation created source credential keys failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer (Sum.inr (.beaconSend index plaintext)) =
      RegistrationNativePlatformOrdinaryExperiment.record setup wire reserveFrame route (.inr (index, .inl plaintext)) source := rfl

private theorem handler_beacon_raw (index : Nat) (raw : Pqxdh.Bytes) :
    RegistrationNativePlatformOrdinaryExperiment.handler (n := n) setup checks wire route representation created source credential keys failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer (Sum.inr (.beaconRaw index raw)) =
      RegistrationNativePlatformOrdinaryExperiment.record setup wire reserveFrame route (.inr (index, .inr raw)) source := rfl

attribute [local irreducible] RegistrationNativePlatformIdentityMainAmbient.command

private theorem command_literal (owners : RegistrationNativeIdentityFrontend.State source) (query : TypedSpec.Domain)
    (allowed : IsOrdinary query) (before : RegistrationNativeIdentityWorld.Context n KemSK × Platform) :
    (RegistrationNativePlatformIdentityMainAmbient.command setup checks wire route representation created credential keys failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer query owners).run before =
      (nativeCommand setup (RegistrationNativeWire.ledgerCodec wire) reserveFrame route (owners.map (fun selected => selected.worldOwner)) query).run before := by
  cases query with
  | inl coin =>
    simp only [RegistrationNativePlatformIdentityMainAmbient.command, handler_uniform,
      StateT.run, lifted_world, nativeCommand, guarded_effect]
    exact native_world _ owners before
  | inr query => cases query with
    | hmac key message =>
      simp only [RegistrationNativePlatformIdentityMainAmbient.command, handler_hmac,
        StateT.run, lifted_pure, nativeCommand]
      exact native_pure _ owners before
    | hash bytes =>
      simp only [RegistrationNativePlatformIdentityMainAmbient.command, handler_hash,
        StateT.run, lifted_world, nativeCommand, guarded_effect]
      exact native_world _ owners before
    | serverSend keyId plaintext =>
      simp only [RegistrationNativePlatformIdentityMainAmbient.command, handler_server_send, StateT.run, nativeCommand]
      exact record_literal setup reserveFrame route wire owners (.inl (.inl (plaintext, keyId))) before
    | serverRaw raw =>
      simp only [RegistrationNativePlatformIdentityMainAmbient.command, handler_server_raw, StateT.run, nativeCommand]
      exact record_literal setup reserveFrame route wire owners (.inl (.inr raw)) before
    | beaconSend index plaintext =>
      simp only [RegistrationNativePlatformIdentityMainAmbient.command, handler_beacon_send, StateT.run, nativeCommand]
      exact record_literal setup reserveFrame route wire owners (.inr (index, .inl plaintext)) before
    | beaconRaw index raw =>
      simp only [RegistrationNativePlatformIdentityMainAmbient.command, handler_beacon_raw, StateT.run, nativeCommand]
      exact record_literal setup reserveFrame route wire owners (.inr (index, .inr raw)) before
    | create edPin mlPin keyId | bundle index | accept packet | build handle application | finish index packet => cases allowed

/-- Every literal nonregistration Context command has its original complete source/P distribution; the final dispatcher supplies each registration branch separately. -/
theorem runtime_source (owners : RegistrationNativeIdentityFrontend.State source) (query : TypedSpec.Domain)
    (allowed : IsOrdinary query) (before : Full n KemSK Platform) :
    Prod.map id realize <$> (interpret (command setup (RegistrationNativeWire.ledgerCodec wire) reserveFrame route
      (owners.map (fun selected => selected.worldOwner)) query)).run before =
      (RegistrationNativePlatformIdentityMainAmbient.command setup checks wire route representation created credential keys failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer query owners).run (realize before) := by
  exact (command_source setup (RegistrationNativeWire.ledgerCodec wire) reserveFrame route
    (owners.map (fun selected => selected.worldOwner)) query before).trans
      (command_literal setup checks wire route representation created credential keys failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer owners query allowed (realize before)).symm
end BeaconcryptCore.Computational.RegistrationNativePlatformCtxCommands

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxCommands.record_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxCommands.record_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxCommands.command_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxCommands.command_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxCommands.runtime_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxCommands.runtime_source
