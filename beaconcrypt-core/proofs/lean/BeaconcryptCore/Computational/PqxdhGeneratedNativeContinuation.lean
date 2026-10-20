import BeaconcryptCore.Computational.PqxdhGeneratedRootSource

/-!
The native mathematical execution can retain its generated KEM secret inside the private interpreter. The complete continuation theorem moves the ordinary independent KEM key generation through the actual source identity/prekey generation while retaining every subsequent source field and effect. The secret-key argument below belongs to a private `ProbComp` continuation; it is not an executable reduction interface or permission to provide the key to an adversary. A separate simulation must remove that private argument before an ordinary CCA reduction is constructed.
-/

open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhGeneratedNativeContinuation
open PqxdhEd25519EufCma PqxdhJointIdentity PqxdhJointPhase1SourceWriter PqxdhJointPhase1AcceptanceComposition
open PqxdhPhase1AcceptanceOracle PqxdhPrivateSourceCoins PqxdhPrivateCandidateAcceptance
open PqxdhPrivateKemSource PqxdhPrivatePhase1Prefix PqxdhKemIndCca PqxdhInitializerSecrecy
open PqxdhStatefulPhase1EufCma PqxdhPrivateRootSource PqxdhGeneratedPhase1Prefix PqxdhGeneratedRootSource
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK : Type}

/-- The original source prefix retains its generated secret solely for the private mathematical continuation. Public source context is represented by the existing secret-erased output and complete identity state. -/
def nativeContinued {Result : Type}
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec) (driver : Driver setup)
    (next : KemSK → Outcome (Retained setup Unit driver.State) × BareState 1 → ProbComp Result)
    (fallback : Result) : ProbComp Result := do
  let stopped ← privateRun attachedVerify primitives 1 (PqxdhGeneratedPhase1Prefix.program baseImpl kem setup driver)
  match stopped.1 with
  | none => pure fallback
  | some output => next output.context.generated.secret (eraseOutput output, stopped.2)

/-- Equality of the complete evaluated native continuation, including its actual private state and secret-key interpretation. The left side keeps source generator order; the right side samples the independent ordinary KEM key pair first. -/
theorem nativeContinued_keyfirst {Result : Type}
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec) (driver : Driver setup)
    (next : KemSK → Outcome (Retained setup Unit driver.State) × BareState 1 → ProbComp Result)
    (fallback : Result) :
    EvalDistEq (nativeContinued attachedVerify primitives baseImpl kem setup driver next fallback)
      (do let pair ← simulateQ (kemAmbientImpl baseImpl) kem.keygen
          let prepared ← evalKem baseImpl kem pair.2
            (borrowedPrefix attachedVerify primitives setup driver pair.1)
          next pair.2 prepared) := by
  have commute := generators_complete_continuation baseImpl primitives kem setup
    (fun seed generated => do
      let material := publicMaterial setup (primitives.publicKeys seed).ed25519 generated
      let bundle := signedCandidate primitives seed (primitives.publicKeys seed).ed25519 material.keyTuple
      let initial := singletonState primitives 1 seed
      let selected ← (simulateQ (privateImpl attachedVerify primitives 1)
        (simulateQ (localSelector baseImpl kem generated.secret)
          (driver.main 0 (primitives.publicKeys seed) (eraseGenerated generated) (transcript bundle material.context)))).run
        (signedGlobalState primitives seed 1 0 material.keyTuple initial.1,
         signedState primitives seed 0 material.keyTuple initial.2)
      next generated.secret
        (⟨⟨0, primitives.publicKeys seed, eraseGenerated generated, bundle, selected.1.2⟩,
          ⟨0, selected.1.1⟩, PqxdhJointPhase1Reports.sourceAccept attachedVerify selected.1.1⟩, selected.2))
  simpa only [nativeContinued, PqxdhGeneratedPhase1Prefix.program_complete, bind_assoc, pure_bind,
    PqxdhGeneratedRootSource.borrowedPrefix_evaluated, identityPreSample, eraseOutput, eraseRetained, eraseGenerated,
    publicMaterial, setupMaterial] using commute

set_option linter.deprecated false in theorem _root_.BeaconcryptCore.Computational.PqxdhGeneratedNativeContinuation.nativeContinued_keyfirst_vcvioLegacy :
    ∀ {ι : Type} {baseSpec : OracleSpec ι} {KemSK Result : Type} (attachedVerify : BeaconcryptCore.Computational.PqxdhEd25519EufCma.Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : BeaconcryptCore.Computational.PqxdhJointIdentity.Primitives) (baseImpl : QueryImpl baseSpec ProbComp) (kem : BeaconcryptCore.Computational.PqxdhKemIndCca.MlKemScheme) (setup : BeaconcryptCore.Computational.PqxdhStatefulPhase1EufCma.StatefulPhase1Setup baseSpec) (driver : BeaconcryptCore.Computational.PqxdhGeneratedPhase1Prefix.Driver setup) (next : KemSK → BeaconcryptCore.Computational.PqxdhPrivateCandidateAcceptance.Outcome (BeaconcryptCore.Computational.PqxdhPrivatePhase1Prefix.Retained setup Unit driver.State) × BeaconcryptCore.Computational.PqxdhPhase1AcceptanceOracle.BareState 1 → ProbComp Result) (fallback : Result),
      𝒮[BeaconcryptCore.Computational.PqxdhGeneratedNativeContinuation.nativeContinued attachedVerify primitives baseImpl kem setup driver next fallback] =
        𝒮[do
          let pair ← simulateQ (BeaconcryptCore.Computational.PqxdhInitializerSecrecy.kemAmbientImpl baseImpl) kem.keygen
          let prepared ← BeaconcryptCore.Computational.PqxdhPrivateKemSource.evalKem baseImpl kem pair.2 (BeaconcryptCore.Computational.PqxdhGeneratedRootSource.borrowedPrefix attachedVerify primitives setup driver pair.1)
          next pair.2 prepared] :=
  by simpa only [BeaconcryptCore.VCVioLegacy.evalSPMF_eq_iff_evalDistEq] using @BeaconcryptCore.Computational.PqxdhGeneratedNativeContinuation.nativeContinued_keyfirst

end BeaconcryptCore.Computational.PqxdhGeneratedNativeContinuation

/--
info: 'BeaconcryptCore.Computational.PqxdhGeneratedNativeContinuation.nativeContinued_keyfirst' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhGeneratedNativeContinuation.nativeContinued_keyfirst
