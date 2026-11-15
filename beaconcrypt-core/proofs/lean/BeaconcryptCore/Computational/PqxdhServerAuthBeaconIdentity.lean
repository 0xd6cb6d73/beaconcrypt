import BeaconcryptCore.Computational.PqxdhServerAuthBeaconMetadata

/-! Actual target Beacon control and metadata identities through source admission. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete PqxdhRefinement
open BeaconcryptCore.Refinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthBeaconIdentity
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor PqxdhJointIdentity PqxdhJointGapDh
variable {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}

/-- The target identity pair as retained by an active original Beacon control. -/
def Control (server : pqxdh.ServerBinding) (beacon : PqxdhBeaconPhase2Preparation.Word32)
    (control : pqxdh.BeaconInitSent) : Prop :=
  control.expected_server_binding = server ∧ control.beacon_identity_public_key = beacon

/-- The hidden callback's functional metadata property; the concrete factor service discharges it below. -/
def TailAD {τ : Type} (services : Services Response τ) : Prop :=
  ∀ pending before result, result ∈ support ((services.hiddenAfter pending).run before) →
    ∀ staged, result.1 = some staged → staged.associatedData = pending.metadata.associatedData

/-- Uniform or real concrete factors retain the same source metadata without a condition on their sampled key bytes. -/
theorem factor_tail (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (context : Context KemSK) (value : PqxdhServerAuthKeySchedule.Output) :
    TailAD (factorServices setup codec checks context value) := by
  intro pending before result supported staged returned
  exact factor_ad setup codec pending _ before result supported staged returned

open PqxdhServerAuthCtxState PqxdhServerAuthCtxStop PqxdhSecretInputKdf
abbrev Observed := PqxdhServerAuthPublicationRecordReserve.Observed

end BeaconcryptCore.Computational.PqxdhServerAuthBeaconIdentity

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBeaconIdentity.factor_tail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBeaconIdentity.factor_tail
