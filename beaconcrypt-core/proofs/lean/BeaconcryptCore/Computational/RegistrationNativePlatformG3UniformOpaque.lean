-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformOpaqueAfter
import BeaconcryptCore.Computational.RegistrationNativePlatformG3RecordProviderSource
/-! A genuine uniform KEM profile and the actual warmed startup are shared by both sides of the complete record-observer comparison. The same provider, platform state and source failures remain literal, and the repeated-role audit is the one from that uniform source run. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

namespace BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformOpaque
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePlatformPublicRecordOpaqueInitialized (Context prior)
variable {I KemSK Platform E Value : Type} {base : OracleSpec I}
variable [primitive : AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64) (selectedAccept : Nat)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (decision : Value × RegistrationNativeLedger.State → RegistrationNativePlatformPublicWorldObservation.RecordView → Bool)

abbrev Prefix (source : RegistrationNativeMldsa.Source) (n : Nat) (KemSK : Type) :=
  Context source n × RegistrationNativeSecretWordAliasOuter.Profile KemSK × PqxdhKemIndCca.MlKemSharedSecret

noncomputable def warmPrior (budget : PqxdhDeploymentInterface.Budget) (selected : Fin (budget.create + 1)) :
    ProbComp (Prefix source (budget.cap 4 + budget.cap 5) KemSK) := do
  let context ← prior setup source ensureInit identityIndex serverKeyId budget
  let profile ← RegistrationNativeG3NativeRepeatUniformBound.prior setup.baseImpl setup.kem budget.create selected
  let candidate ← $ᵗ PqxdhKemIndCca.MlKemSharedSecret
  pure (context, profile, candidate)

noncomputable def knownAt (budget : PqxdhDeploymentInterface.Budget) (selected : Fin (budget.create + 1))
    (previous : Platform) (packet : Prefix source (budget.cap 4 + budget.cap 5) KemSK) : ProbComp (Bool × Platform) :=
  match packet.1.2.2.2.1 with
  | none => pure (false,previous)
  | some _ => do
    let materials ← $ᵗ RegistrationNativeG3Tables.MaterialTable (budget.cap 4 + budget.cap 5)
    RegistrationNativePlatformG3UniformOpaqueAfter.known setup checks wire route source serverKeyId (RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem selected.val packet.2.1.pairs packet.2.1.publicKey packet.2.1.challenge packet.2.2) none selected.val selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision
      budget packet.1.1 packet.1.2.1 packet.2.2 materials previous packet.1.2.2.2

noncomputable def known (budget : PqxdhDeploymentInterface.Budget) (selected : Fin (budget.create + 1))
    (previous : Platform) : ProbComp (Bool × Platform) := do
  let packet ← warmPrior setup source ensureInit identityIndex serverKeyId budget selected
  knownAt setup checks wire route source serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision budget selected previous packet

noncomputable def hiddenAt (budget : PqxdhDeploymentInterface.Budget) (selected : Fin (budget.create + 1))
    (previous : Platform) (packet : Prefix source (budget.cap 4 + budget.cap 5) KemSK) : ProbComp (Bool × Platform) :=
  match packet.1.2.2.2.1 with
  | none => pure (false,previous)
  | some _ => do
    let materials ← $ᵗ RegistrationNativeG3Tables.MaterialTable (budget.cap 4 + budget.cap 5)
    RegistrationNativePlatformG3UniformOpaqueAfter.hidden setup checks wire route source serverKeyId (RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem selected.val packet.2.1.pairs packet.2.1.publicKey packet.2.1.challenge packet.2.2) none selected.val selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision
      budget packet.1.1 packet.1.2.1 packet.2.2 materials previous packet.1.2.2.2

noncomputable def hidden (budget : PqxdhDeploymentInterface.Budget) (selected : Fin (budget.create + 1))
    (previous : Platform) : ProbComp (Bool × Platform) := do
  let packet ← warmPrior setup source ensureInit identityIndex serverKeyId budget selected
  hiddenAt setup checks wire route source serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision budget selected previous packet

noncomputable def auditAt (budget : PqxdhDeploymentInterface.Budget) (selected : Fin (budget.create + 1))
    (previous : Platform) (packet : Prefix source (budget.cap 4 + budget.cap 5) KemSK) : ProbComp (Bool) :=
  match packet.1.2.2.2.1 with
  | none => pure false
  | some _ => do
    let materials ← $ᵗ RegistrationNativeG3Tables.MaterialTable (budget.cap 4 + budget.cap 5)
    RegistrationNativePlatformG3UniformOpaqueAfter.audit setup checks wire route source serverKeyId (RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem selected.val packet.2.1.pairs packet.2.1.publicKey packet.2.1.challenge packet.2.2) none selected.val selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary
      budget packet.1.1 packet.1.2.1 packet.2.2 materials previous packet.1.2.2.2

noncomputable def audit (budget : PqxdhDeploymentInterface.Budget) (selected : Fin (budget.create + 1))
    (previous : Platform) : ProbComp (Bool) := do
  let packet ← warmPrior setup source ensureInit identityIndex serverKeyId budget selected
  auditAt setup checks wire route source serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget selected previous packet

/-- The conditional warm comparison samples fresh private cells only after actual startup succeeds. -/
theorem at_bound (budget : PqxdhDeploymentInterface.Budget) (selected : Fin (budget.create + 1))
    (previous : Platform) (packet : Prefix source (budget.cap 4 + budget.cap 5) KemSK) :
    ENNReal.ofReal (discreteDistance
      (knownAt setup checks wire route source serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision budget selected previous packet)
      (hiddenAt setup checks wire route source serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision budget selected previous packet)) ≤
      Pr{let flag ← auditAt setup checks wire route source serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget selected previous packet}[flag = true] := by
  cases success : packet.1.2.2.2.1 with
  | none =>
    simp only [knownAt,hiddenAt,auditAt,success,discreteDistance_self,ENNReal.ofReal_zero,prEvent_pure,Bool.false_eq_true,↓reduceIte]
    exact le_rfl
  | some started =>
    have compared := PqxdhExtractRomHiddenSuffix.tvDist_bind_le_probEvent
      ($ᵗ RegistrationNativeG3Tables.MaterialTable (budget.cap 4 + budget.cap 5))
      (fun materials => RegistrationNativePlatformG3UniformOpaqueAfter.known setup checks wire route source serverKeyId (RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem selected.val packet.2.1.pairs packet.2.1.publicKey packet.2.1.challenge packet.2.2) none selected.val selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision
        budget packet.1.1 packet.1.2.1 packet.2.2 materials previous packet.1.2.2.2)
      (fun materials => RegistrationNativePlatformG3UniformOpaqueAfter.hidden setup checks wire route source serverKeyId (RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem selected.val packet.2.1.pairs packet.2.1.publicKey packet.2.1.challenge packet.2.2) none selected.val selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision
        budget packet.1.1 packet.1.2.1 packet.2.2 materials previous packet.1.2.2.2)
      (fun materials => RegistrationNativePlatformG3UniformOpaqueAfter.audit setup checks wire route source serverKeyId (RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem selected.val packet.2.1.pairs packet.2.1.publicKey packet.2.1.challenge packet.2.2) none selected.val selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary
        budget packet.1.1 packet.1.2.1 packet.2.2 materials previous packet.1.2.2.2)
      (fun _ flag => flag = true)
      (fun materials _ => by
        have pointwise := ENNReal.toReal_mono (prEvent_ne_top _)
          (RegistrationNativePlatformG3UniformOpaqueAfter.bound setup checks wire route source serverKeyId (RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem selected.val packet.2.1.pairs packet.2.1.publicKey packet.2.1.challenge packet.2.2) none selected.val selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision
            budget packet.1.1 packet.1.2.1 packet.2.2 materials previous packet.1.2.2.2)
        simpa only [ENNReal.toReal_ofReal (discreteDistance_nonneg _ _)] using pointwise)
    have lifted := (ENNReal.ofReal_le_ofReal compared).trans (ENNReal.ofReal_toReal (prEvent_ne_top _)).le
    simpa only [knownAt,hiddenAt,auditAt,success,OracleComp.prEvent_bind_eq_tsum,bind_pure_comp,prEvent_map] using lifted

/-- One genuine uniform KEM context and the literal warm startup are shared by the complete record-observer comparison. -/
theorem bound (budget : PqxdhDeploymentInterface.Budget) (selected : Fin (budget.create + 1)) (previous : Platform) :
    ENNReal.ofReal (discreteDistance
      (known setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision budget selected previous)
      (hidden setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision budget selected previous)) ≤
      Pr{let flag ← audit setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget selected previous}[flag = true] := by
  have compared := PqxdhExtractRomHiddenSuffix.tvDist_bind_le_probEvent
    (warmPrior setup source ensureInit identityIndex serverKeyId budget selected)
    (knownAt setup checks wire route source serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision budget selected previous)
    (hiddenAt setup checks wire route source serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision budget selected previous)
    (auditAt setup checks wire route source serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget selected previous)
    (fun _ flag => flag = true)
    (fun packet _ => by
      have pointwise := ENNReal.toReal_mono (prEvent_ne_top _)
        (at_bound setup checks wire route source serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision budget selected previous packet)
      simpa only [ENNReal.toReal_ofReal (discreteDistance_nonneg _ _)] using pointwise)
  have lifted := (ENNReal.ofReal_le_ofReal compared).trans (ENNReal.ofReal_toReal (prEvent_ne_top _)).le
  simpa only [known,hidden,audit,OracleComp.prEvent_bind_eq_tsum,bind_pure_comp,prEvent_map] using lifted

/-- The only audit loss is the literal actual uniform-provider chronology, with the same warm prior and platform state. -/
theorem audit_source (budget : PqxdhDeploymentInterface.Budget) (selected : Fin (budget.create + 1)) (previous : Platform) :
    audit setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget selected previous =
      RegistrationNativePlatformG3UniformAudit.audit setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget selected previous := by
  unfold audit warmPrior RegistrationNativePlatformG3UniformAudit.audit
  simp only [bind_assoc,pure_bind]
  apply OracleComp.bind_congr_of_forall_mem_support
  intro context reached
  apply bind_congr
  intro profile
  apply bind_congr
  intro candidate
  cases success : context.2.2.2.1 with
  | none => simp only [auditAt,success]
  | some started =>
    have fields := RegistrationNativePlatformPublicRecordOpaqueInitialized.prior_fields setup source ensureInit identityIndex serverKeyId budget context started reached success
    simp only [auditAt,success]
    apply bind_congr
    intro materials
    have actual := RegistrationNativePlatformG3UniformOpaqueAfter.audit_source setup checks wire route source serverKeyId (RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem selected.val profile.pairs profile.publicKey profile.challenge candidate) none selected.val selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary
      budget context.1 context.2.1 candidate materials previous started context.2.2.2.2 fields.2.2.2.2
    simpa only [RegistrationNativePlatformG3UniformOpaqueAfter.audit,success,RegistrationNativeSelectiveHiddenInterpreter.initial] using actual

omit primitive in
def observation (previous : Platform) {cap : Nat}
    (result : PqxdhKemIndCca.MlKemSharedSecret × RegistrationNativePlatformG3RecordKem.Result source cap Value Platform) : Bool × Platform :=
  match result.2.2 with
  | none => (false,previous)
  | some actual => (decision actual.1.1.1 actual.2,actual.1.1.2.2)

/-- The exact complete actual uniform-provider source equals the known side of the same warm comparison. -/
theorem known_source (budget : PqxdhDeploymentInterface.Budget) (selected : Fin (budget.create + 1)) (previous : Platform) :
    observation source decision previous <$> RegistrationNativePlatformG3RecordProviderSource.game setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget selected previous =
      known setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision budget selected previous := by
  unfold RegistrationNativePlatformG3RecordProviderSource.game known warmPrior
  simp only [map_bind,bind_assoc,pure_bind]
  apply OracleComp.bind_congr_of_forall_mem_support
  intro context reached
  apply bind_congr
  intro profile
  apply bind_congr
  intro candidate
  cases success : context.2.2.2.1 with
  | none => simp only [RegistrationNativePlatformG3RecordProviderSource.full,knownAt,success,map_pure,observation,pure_bind]
  | some started =>
    have fields := RegistrationNativePlatformPublicRecordOpaqueInitialized.prior_fields setup source ensureInit identityIndex serverKeyId budget context started reached success
    simp only [RegistrationNativePlatformG3RecordProviderSource.full,knownAt,success,map_pure,bind_pure_comp,map_bind]
    apply bind_congr
    intro materials
    have actual := RegistrationNativePlatformG3UniformOpaqueAfter.known_source setup checks wire route source serverKeyId (RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem selected.val profile.pairs profile.publicKey profile.challenge candidate) none selected.val selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision
      budget context.1 context.2.1 candidate materials previous started context.2.2.2.2 fields.2.2.2.2
    simpa only [RegistrationNativePlatformG3RecordTraceKnown.full, RegistrationNativePlatformG3UniformOpaqueAfter.known,
      success,observation,RegistrationNativePlatformG3UniformOpaqueAfter.observation,Functor.map_map,RegistrationNativeSelectiveHiddenInterpreter.initial,map_bind,bind_pure_comp] using actual

/-- The genuine uniform KEM branch retains the original full record event on the known side of the same source comparison. -/
theorem conditional_source (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publication, RegistrationNativeInterface.Respects budget (adversary publication))
    (selected : Fin (budget.create + 1)) (previous : Platform) :
    RegistrationNativePlatformG3RecordUniformSource.conditional setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget selected previous
      (fun _ result => RegistrationNativePlatformG3RecordKem.observation source decision result) =ᵈ
      Prod.fst <$> known setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision budget selected previous := by
  have actual := RegistrationNativePlatformG3RecordProviderSource.conditional_source setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget bounded selected previous
    (fun _ result => RegistrationNativePlatformG3RecordKem.observation source decision result)
  have observed := congrArg (Functor.map Prod.fst) (known_source setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision budget selected previous)
  simp only [Functor.map_map] at observed
  have functions : (fun result => (observation source decision previous (cap := budget.cap 4 + budget.cap 5) result).1) =
      (fun result => RegistrationNativePlatformG3RecordKem.observation source decision result.2) := by
    funext result
    cases seen : result.2.2 <;> simp only [observation,RegistrationNativePlatformG3RecordKem.observation,seen]
  rw [functions] at observed
  exact actual.trans (by rw [observed])

noncomputable def recoveryLoss (budget : PqxdhDeploymentInterface.Budget) (selected : Fin (budget.create + 1)) (previous : Platform) : ℝ≥0∞ :=
  2 * (ENNReal.ofReal (RegistrationNativeSuffixKeyPrf.advantage setup.source
        (RegistrationNativeSuffixKeyRecovery.adversary setup.source (RegistrationNativeSecretWordRecoveryCompiler.guesses
          (RegistrationNativePlatformSecretWordInitializedAlias.actual setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation
            reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget selected previous)))) +
        (budget.cap 4 + budget.cap 5) * (256 ^ 160 : ℝ≥0∞)⁻¹ + (budget.cap 4 + budget.cap 5) * (256 ^ 32 : ℝ≥0∞)⁻¹)

/-- The complete warm known/hidden distance pays only twice one startup-inclusive recovery advantage and the two material byte-guess terms. -/
theorem loss_bound (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publication, RegistrationNativeInterface.Respects budget (adversary publication))
    (selected : Fin (budget.create + 1)) (previous : Platform) :
    ENNReal.ofReal (discreteDistance
      (known setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision budget selected previous)
      (hidden setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision budget selected previous)) ≤
      recoveryLoss setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget selected previous := by
  have loss := RegistrationNativePlatformG3UniformAudit.bound setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget bounded selected previous
  rw [← audit_source setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget selected previous] at loss
  exact (bound setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision budget selected previous).trans loss

end BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformOpaque

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformOpaque.at_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformOpaque.at_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformOpaque.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformOpaque.bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformOpaque.audit_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformOpaque.audit_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformOpaque.known_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformOpaque.known_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformOpaque.conditional_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformOpaque.conditional_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformOpaque.loss_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformOpaque.loss_bound
