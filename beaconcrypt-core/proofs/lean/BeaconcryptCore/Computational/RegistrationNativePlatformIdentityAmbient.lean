-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryExperiment
import BeaconcryptCore.Computational.RegistrationNativeIdentityMainOld

/-! Actual current-runtime callbacks other than Beacon create/bundle/finish depend on a Beacon roster only through public World owner handles. Replacing private Ed seed fields leaves those callbacks' complete native/platform execution unchanged, while restoring the chosen roster literally. The source writer, allocator, private counters and failure outcomes are preserved. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityAmbient
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeWire (Wire)
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativeBeaconFrontend (Owner)
variable {n : Nat} {ι KemSK Platform E Value Next : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

local notation "Native" => RegistrationNativeExperiment.State n KemSK source

def nonBeacon : TypedSpec.Domain → Prop
  | .inr (.create ..) | .inr (.bundle ..) | .inr (.finish ..) => False
  | _ => True

def replace (owners : List (Owner source)) (before : Native) : Native := { before with beacons := owners }

private theorem bind_apply {S A B : Type} {m : Type → Type} [Monad m]
    (work : StateT S m A) (next : A → StateT S m B) (before : S) :
    (work >>= next) before = (do let result ← work before; next result.1 result.2) := rfl
private theorem pure_apply {S A : Type} {m : Type → Type} [Monad m] (value : A) (before : S) :
    (pure value : StateT S m A) before = pure (value, before) := rfl
private theorem modify_apply {S : Type} {m : Type → Type} [Monad m] (change : S → S) (before : S) :
    (modify change : StateT S m Unit) before = pure ((), change before) := rfl

variable [primitives : AdapterSealPrimitive.Operations]

variable (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))

omit primitives in
private theorem record_roster (query : PqxdhRecordLiftInterface.RecordQuery) (before : Native)
    (owners : List (Owner source)) (same : before.beacons.map Owner.worldOwner = owners.map Owner.worldOwner) :
    Prod.map id (replace owners) <$>
      (RegistrationNativePlatformOrdinaryExperiment.record setup wire reserveFrame route query source).run before =
      (RegistrationNativePlatformOrdinaryExperiment.record setup wire reserveFrame route query source).run (replace owners before) := by
  cases query with
  | inl query =>
    simp only [RegistrationNativePlatformOrdinaryExperiment.record, RegistrationNativePlatformOrdinaryExperiment.world,
      StateT.run, Functor.map_map, Prod.map, id_eq, replace,
      RegistrationNativePlatformOrdinaryExperiment.replaceWorld]
  | inr query =>
    rcases query with ⟨index, query⟩
    have found := congrArg (fun values : List Nat => values[index]?) same
    simp only [List.getElem?_map] at found
    cases left : before.beacons[index]? with
    | none =>
      have right : owners[index]? = none := by
        cases right : owners[index]? with
        | none => rfl
        | some owner => simp only [left, right, Option.map_none, Option.map_some] at found; cases found
      cases query <;> simp only [RegistrationNativePlatformOrdinaryExperiment.record, StateT.run,
        replace, left, right, map_pure, Prod.map, id_eq]
    | some owner =>
      obtain ⟨other, right, ownerEq⟩ : ∃ other, owners[index]? = some other ∧ owner.worldOwner = other.worldOwner := by
        cases right : owners[index]? with
        | none => simp only [left, right, Option.map_none, Option.map_some] at found; cases found
        | some other =>
          refine ⟨other, rfl, ?_⟩
          simpa only [left, right, Option.map_some, Option.some.injEq] using found
      cases query <;> simp only [RegistrationNativePlatformOrdinaryExperiment.record, StateT.run,
        replace, left, right, RegistrationNativePlatformOrdinaryExperiment.world,
        Functor.map_map, Prod.map, id_eq, RegistrationNativePlatformOrdinaryExperiment.replaceWorld]
      all_goals rw [ownerEq]

omit primitives in
private theorem trusted_roster
    (query : (RegistrationNativeBeaconFrontend.Trusted n KemSK).Domain) (before : Native) (owners : List (Owner source)) :
    Prod.map id (replace owners) <$>
      (RegistrationNativeExperiment.trusted setup checks representation created source query).run before =
      (RegistrationNativeExperiment.trusted setup checks representation created source query).run (replace owners before) := by
  have first := RegistrationNativeIdentityMainOld.trusted_source setup checks representation created before.beacons query
    (RegistrationNativeIdentityWorld.project before)
  have second := RegistrationNativeIdentityMainOld.trusted_source setup checks representation created owners query
    (RegistrationNativeIdentityWorld.project before)
  have same := congrArg (fun distribution => Prod.map id (replace owners) <$> distribution) first
  simp only [Functor.map_map, Prod.map, id_eq, replace, RegistrationNativeIdentityMainOrdinary.attach,
    RegistrationNativeIdentityWorld.project] at same second
  exact same.symm.trans second

omit primitives in
private theorem lifted_roster
    (query : (RegistrationNativeBeaconFrontend.Trusted n KemSK).Domain) (before : Native) (owners : List (Owner source)) :
    Prod.map id (replace owners) <$>
      (RegistrationNativePlatformExperiment.liftNative (RegistrationNativePlatformMldsaProgram.coins (Platform := Platform))
        (RegistrationNativeExperiment.trusted setup checks representation created source query)).run before =
      (RegistrationNativePlatformExperiment.liftNative (RegistrationNativePlatformMldsaProgram.coins (Platform := Platform))
        (RegistrationNativeExperiment.trusted setup checks representation created source query)).run (replace owners before) := by
  have same := congrArg (fun distribution => simulateQ (RegistrationNativePlatformMldsaProgram.coins (Platform := Platform)) distribution)
    (trusted_roster setup checks representation created query before owners)
  simpa only [RegistrationNativePlatformExperiment.liftNative, StateT.run, simulateQ_map] using same

omit primitives in
private theorem afterParsed_roster
    (work : StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) Value)
    (before : Native) (owners : List (Owner source)) :
    Prod.map id (replace owners) <$>
      ((do
        modify fun current : Native => { current with parsedAccepts := current.parsedAccepts + 1 }
        RegistrationNativePlatformExperiment.server work).run before) =
      ((do
        modify fun current : Native => { current with parsedAccepts := current.parsedAccepts + 1 }
        RegistrationNativePlatformExperiment.server work).run (replace owners before)) := by
  simp only [bind_apply, modify_apply, pure_bind, RegistrationNativePlatformExperiment.server,
    StateT.run, Functor.map_map, Prod.map, id_eq, replace]

omit primitives in
private theorem server_result_roster
    (work : StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) Value)
    (observe : Value → Next) (before : Native) (owners : List (Owner source)) :
    Prod.map id (replace owners) <$>
      ((do let value ← RegistrationNativePlatformExperiment.server work; pure (observe value)).run before) =
      ((do let value ← RegistrationNativePlatformExperiment.server work; pure (observe value)).run (replace owners before)) := by
  simp only [RegistrationNativePlatformExperiment.server, bind_apply, StateT.run,
    Functor.map_map, Prod.map, id_eq, replace, pure_apply, bind_pure_comp]

omit primitives in
private theorem lifted_pure (value : Value) (before : Native) (owners : List (Owner source)) :
    Prod.map id (replace owners) <$>
      (RegistrationNativePlatformExperiment.liftNative (RegistrationNativePlatformMldsaProgram.coins (Platform := Platform))
        (pure value : StateT Native ProbComp Value)).run before =
      (RegistrationNativePlatformExperiment.liftNative (RegistrationNativePlatformMldsaProgram.coins (Platform := Platform))
        (pure value : StateT Native ProbComp Value)).run (replace owners before) := by
  rfl

attribute [local irreducible] RegistrationNativePlatformSourceAccept.accept RegistrationNativePlatformSourceSeal.build

/-- Every actual non-Beacon callback preserves private-roster substitution through the same current native/P run, including dynamic writer failure. -/
theorem handler (query : TypedSpec.Domain) (allowed : nonBeacon query) (before : Native)
    (owners : List (Owner source)) (same : before.beacons.map Owner.worldOwner = owners.map Owner.worldOwner) :
    Prod.map id (replace owners) <$>
      (RegistrationNativePlatformOrdinaryExperiment.handler setup checks wire route representation created source credential view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer query).run before =
      (RegistrationNativePlatformOrdinaryExperiment.handler setup checks wire route representation created source credential view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer query).run (replace owners before) := by
  cases query with
  | inl coin => exact lifted_roster (Platform := Platform) setup checks representation created (.inl (.inl coin)) before owners
  | inr query => cases query with
    | create edPin mlPin keyId | bundle index | finish index packet => cases allowed
    | serverSend keyId plaintext => exact record_roster setup wire route reserveFrame (.inl (.inl (plaintext, keyId))) before owners same
    | serverRaw raw => exact record_roster setup wire route reserveFrame (.inl (.inr raw)) before owners same
    | beaconSend index plaintext => exact record_roster setup wire route reserveFrame (.inr (index, .inl plaintext)) before owners same
    | beaconRaw index raw => exact record_roster setup wire route reserveFrame (.inr (index, .inr raw)) before owners same
    | accept packet =>
      exact afterParsed_roster
        (RegistrationNativePlatformSourceAccept.accept RegistrationNativePlatformMldsaProgram.coins setup
          (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire))
          checks reserveRegistration route source.verify representation created packet) before owners
    | build session application =>
      exact server_result_roster
        (RegistrationNativePlatformSourceSeal.build RegistrationNativePlatformMldsaProgram.coins setup
          (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)) view failure allocation erased reservePeer
          (RegistrationNativeMldsa.owned source credential) helper writer session application)
        (fun result : RustM (Option (U64 × alloc.vec.Vec U8)) => (do let optional ← result; .ok (optional.map fun value => (value.1, TranscriptAuthParts.absSlice value.2)) : RustM (Option (U64 × Pqxdh.Bytes)))) before owners
    | hmac key message => exact lifted_pure (Platform := Platform) (setup.hmac.eval key message) before owners
    | hash bytes => exact lifted_roster (Platform := Platform) setup checks representation created (.inl (.inr (.hash bytes))) before owners


end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityAmbient
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityAmbient.handler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityAmbient.handler
