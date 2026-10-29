-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeProviderBeaconCaps

/-! Post-agreement completion retains every provider coordinate. Its actual source108 opening, aborts and kernel installation use no KEM callback; the root memo is read at the freshly returned name. No real KEM interpretation is substituted into the preceding agreement. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeProviderBeaconContinuation
open PqxdhServerAuthExperiment (Setup)
open PqxdhJointIdentity (IdentitySeed)
open PqxdhJointGapDh (ScalarBytes)
open PqxdhRecordLiftInterface (EnvEffects)
open RegistrationNativeProviderInterpreter (Provider)
open RegistrationNativeProviderCallbacks (NativeState implementation program_free)
open RegistrationNativeProviderBeaconAgreement (trusted)
open RegistrationNativeProviderBeaconCaps (abort_zero complete_zero factored_zero)
open RegistrationBeaconReferenceCompiler (SelectedOwner eraseOwner Spec effect trustedLift)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationBeaconReferenceNativeContinuation (view sourceAfter afterPrepared)
open RegistrationBeaconReferenceNativePreparation (restored)
variable {n : Nat} {ι KemSK ProviderState Auxiliary Value : Type} {base : OracleSpec ι}
variable {mlSource : RegistrationNativeMldsa.Source}

private theorem abort_projection (owner current : RegistrationNativeBeaconFrontend.Owner mlSource)
    (env : EnvState Auxiliary) (value : Value) :
    view <$>
      (((RegistrationBeaconReferenceNativeOwner.abort owner *> pure value :
        RegistrationBeaconReferenceNativeOwner.M n KemSK Auxiliary mlSource Value).run current).run env) =
      simulateQ RegistrationBeaconReferenceNativeRecord.environment
        (((RegistrationBeaconReferenceCompletion.abort (QueryImpl.id' (EnvEffects n)) (eraseOwner owner) *> pure value :
          RegistrationBeaconReferenceCompletion.M (target := EnvEffects n) (Auxiliary := Auxiliary)
            mlSource Value).run (eraseOwner current)).run (RegistrationBeaconReferenceNativeRecord.erase env)) := by
  simp only [RegistrationBeaconReferenceNativeOwner.abort, RegistrationBeaconReferenceCompletion.abort,
    seqRight_eq_bind, StateT.run_lift, bind_pure_comp, StateT.run_map,
    RegistrationBeaconReferenceNativeRecord.environment, simulateQ_map, simulateQ_spec_query,
    QueryImpl.id'_apply, Functor.map_map, view]
  rfl

private theorem public_abort (owner current : SelectedOwner mlSource) (env : EnvState Auxiliary) (value : Value) :
    (((RegistrationBeaconReferenceFinish.abort owner *> pure value :
      RegistrationBeaconReferenceCompletion.M (target := Spec n KemSK) (Auxiliary := Auxiliary)
        mlSource Value).run current).run env) =
      simulateQ effect
        (((RegistrationBeaconReferenceCompletion.abort (QueryImpl.id' (EnvEffects n)) owner *> pure value :
          RegistrationBeaconReferenceCompletion.M (target := EnvEffects n) (Auxiliary := Auxiliary)
            mlSource Value).run current).run env) := by
  simp only [RegistrationBeaconReferenceFinish.abort, RegistrationBeaconReferenceCompletion.abort,
    seqRight_eq_bind, StateT.run_map, StateT.run_lift, bind_pure_comp,
    simulateQ_map, simulateQ_spec_query, QueryImpl.id'_apply]

theorem abort_native (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : IdentitySeed) (scalar : ScalarBytes) (provider : Provider KemSK ProviderState)
    (owner current : RegistrationNativeBeaconFrontend.Owner mlSource) (env : EnvState Auxiliary)
    (value : Value) (before : NativeState n KemSK ProviderState) :
    (simulateQ (implementation setup wire route sign seed scalar provider false)
      (((RegistrationBeaconReferenceFinish.abort (eraseOwner owner) *> pure value :
        RegistrationBeaconReferenceCompletion.M (target := Spec n KemSK) (Auxiliary := Auxiliary)
          mlSource Value).run (eraseOwner current)).run (RegistrationBeaconReferenceNativeRecord.erase env))).run before =
      Prod.map view id <$>
        (simulateQ (trusted setup wire route sign seed scalar provider)
          (((RegistrationBeaconReferenceNativeOwner.abort owner *> pure value :
            RegistrationBeaconReferenceNativeOwner.M n KemSK Auxiliary mlSource Value).run current).run env)).run before := by
  rw [public_abort]
  have source := congrArg (fun work => (simulateQ (trusted setup wire route sign seed scalar provider) work).run before)
    (abort_projection (n := n) (KemSK := KemSK) owner current env value)
  simp only [simulateQ_map, StateT.run_map, ← QueryImpl.simulateQ_compose] at source
  have lowered : trusted (n := n) setup wire route sign seed scalar provider ∘ₛ
      RegistrationBeaconReferenceNativeRecord.environment =
      implementation setup wire route sign seed scalar provider false ∘ₛ effect := by
    funext query
    simp only [trusted, QueryImpl.apply_compose, RegistrationBeaconReferenceNativeRecord.environment,
      simulateQ_spec_query, trustedLift]
  rw [lowered, QueryImpl.simulateQ_compose] at source
  simpa only [Prod.map_def, id_eq] using source.symm

theorem complete_missing (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : IdentitySeed) (scalar : ScalarBytes) (provider : Provider KemSK ProviderState)
    (owner current : SelectedOwner mlSource) (env : EnvState Auxiliary)
    (ready : RegistrationBeaconReferenceRoot.Ready) (before : NativeState n KemSK ProviderState)
    (missing : before.1.extra.1 ready.reference = none) :
    (simulateQ (implementation setup wire route sign seed scalar provider false)
      (((RegistrationBeaconReferenceFinish.complete setup.source owner ready :
        RegistrationBeaconReferenceCompletion.M (target := Spec n KemSK) (Auxiliary := Auxiliary)
          mlSource (RustM (Option Pqxdh.Bytes))).run current).run env)).run before =
      (simulateQ (implementation setup wire route sign seed scalar provider false)
        (((RegistrationBeaconReferenceFinish.abort owner *> pure (.ok none) :
          RegistrationBeaconReferenceCompletion.M (target := Spec n KemSK) (Auxiliary := Auxiliary)
            mlSource (RustM (Option Pqxdh.Bytes))).run current).run env)).run before := by
  rw [program_free setup wire route sign seed scalar provider false _ (complete_zero setup.source owner current ready env),
    program_free setup wire route sign seed scalar provider false _ (abort_zero owner current env _)]
  exact congrArg (fun distribution => (fun result => (result.1, (result.2, before.2))) <$> distribution)
    (RegistrationNativeOrdinaryFinishSourceContinuation.complete_missing setup wire route sign seed scalar
      owner current env ready before.1 missing)

/-- The complete prepared-root opening and installation are the actual native source108 controller, with arbitrary provider state framed exactly. -/
theorem complete_native (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : IdentitySeed) (scalar : ScalarBytes) (provider : Provider KemSK ProviderState)
    (owner current : SelectedOwner mlSource) (env : EnvState Auxiliary)
    (ready : RegistrationBeaconReferenceRoot.Ready) (root : PqxdhSecretInputKdf.RootOutput)
    (before : NativeState n KemSK ProviderState) (prepared : before.1.extra.1 ready.reference = some root) :
    (simulateQ (implementation setup wire route sign seed scalar provider false)
      (((RegistrationBeaconReferenceFinish.complete setup.source owner ready :
        RegistrationBeaconReferenceCompletion.M (target := Spec n KemSK) (Auxiliary := Auxiliary)
          mlSource (RustM (Option Pqxdh.Bytes))).run current).run env)).run before =
      (simulateQ (trusted setup wire route sign seed scalar provider)
        (((RegistrationBeaconReferenceNativeKnown.factored setup wire owner ready.descriptor root :
          RegistrationBeaconReferenceCompletion.M (target := RegistrationNativeBeaconFrontend.Trusted n KemSK)
            (Auxiliary := Auxiliary) mlSource (RustM (Option Pqxdh.Bytes))).run current).run env)).run before := by
  rw [program_free setup wire route sign seed scalar provider false _ (complete_zero setup.source owner current ready env),
    trusted, QueryImpl.simulateQ_compose,
    program_free setup wire route sign seed scalar provider false _ (factored_zero setup wire owner current env ready root)]
  have old := RegistrationNativeOrdinaryFinishSourceNative.complete_native setup wire route sign seed scalar
    owner current env ready root before.1 prepared
  simpa only [RegistrationNativeOrdinaryFinishSourceNative.trusted, QueryImpl.simulateQ_compose] using
    congrArg (fun distribution => (fun result => (result.1, (result.2, before.2))) <$> distribution) old

/-- Every post-agreement result reconstructs its native continuation, retaining absent roots, all failures and complete provider state. -/
theorem continuation_native (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : IdentitySeed) (scalar : ScalarBytes) (provider : Provider KemSK ProviderState)
    (owner current : RegistrationNativeBeaconFrontend.Owner mlSource) (env : EnvState Auxiliary)
    (authenticated : registration.AuthenticatedResponse)
    (result : RustM (Option RegistrationBeaconReferenceRoot.Ready)) (erased : Std.Array U8 357#usize)
    (before : NativeState n KemSK ProviderState) :
    (simulateQ (implementation setup wire route sign seed scalar provider false)
      (((afterPrepared setup.source (eraseOwner owner) result :
        RegistrationBeaconReferenceCompletion.M (target := Spec n KemSK) (Auxiliary := Auxiliary)
          mlSource (RustM (Option Pqxdh.Bytes))).run (eraseOwner current)).run
            (RegistrationBeaconReferenceNativeRecord.erase env))).run before =
      Prod.map view id <$>
        (simulateQ (trusted setup wire route sign seed scalar provider)
          (((sourceAfter setup wire owner (restored before.1.extra.1 authenticated result) :
            RegistrationBeaconReferenceNativeOwner.M n KemSK Auxiliary mlSource (RustM (Option Pqxdh.Bytes))).run current).run env)).run before := by
  cases result with
  | fail error | div => exact abort_native setup wire route sign seed scalar provider owner current env _ before
  | ok result => cases result with
    | none => exact abort_native setup wire route sign seed scalar provider owner current env _ before
    | some ready =>
        cases memo : before.1.extra.1 ready.reference with
        | none =>
            simp only [afterPrepared, restored, memo, sourceAfter]
            rw [complete_missing setup wire route sign seed scalar provider (eraseOwner owner) (eraseOwner current)
              (RegistrationBeaconReferenceNativeRecord.erase env) ready before memo]
            exact abort_native setup wire route sign seed scalar provider owner current env _ before
        | some root =>
            simp only [afterPrepared, restored, memo, sourceAfter]
            rw [complete_native setup wire route sign seed scalar provider
              (eraseOwner owner) (eraseOwner current) (RegistrationBeaconReferenceNativeRecord.erase env) ready root before memo]
            have actual := congrArg (fun work => (simulateQ (trusted setup wire route sign seed scalar provider) work).run before)
              (RegistrationBeaconReferenceNativeKnown.post_root (n := n) (KemSK := KemSK) setup wire erased owner current
                ready.descriptor root env)
            simpa only [simulateQ_map, StateT.run_map, Prod.map_def, id_eq,
              RegistrationBeaconReferenceRoot.atRoot, view] using actual.symm

end BeaconcryptCore.Computational.RegistrationNativeProviderBeaconContinuation

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderBeaconContinuation.abort_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderBeaconContinuation.abort_native
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderBeaconContinuation.complete_missing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderBeaconContinuation.complete_missing
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderBeaconContinuation.complete_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderBeaconContinuation.complete_native
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderBeaconContinuation.continuation_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderBeaconContinuation.continuation_native
