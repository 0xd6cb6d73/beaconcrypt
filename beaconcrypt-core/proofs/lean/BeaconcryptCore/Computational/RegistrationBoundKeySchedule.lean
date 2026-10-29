-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationSeedErasure
import BeaconcryptCore.Computational.PqxdhDeploymentHiddenLayout

/-!
The actual bound Server post-root continuation factors through the 108-byte key-schedule output and retained public source fields. Its executable descriptor contains no root or discarded initializer left chain. Associated data is taken from the actual populated native binding before sealing. The generic material/seed split therefore applies to this concrete continuation; the higher root/KEM game and slot-cache adapter remain distinct composition steps.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationBoundKeySchedule
open PqxdhSecretInputKdf (RootOutput)

/-- The actual public post-root fields, without the selected root value or a private KDF request. -/
structure PublicInitial where
  candidate : pqxdh.ServerRegistrationCandidate
  binding : session.RegistrationBinding
  application : Slice Std.U8

def publicInitial (initial : registration.ServerInitialKdf) : PublicInitial :=
  ⟨initial.candidate, initial.binding, initial.application⟩

def zero : RootOutput := List.Vector.replicate 32 0

def restore (initial : PublicInitial) : registration.ServerInitialKdf :=
  ⟨initial.candidate, initial.binding, initial.application,
    PqxdhInitialRatchetComplementarity.serverPending (PqxdhRootTableInitialization.rootArray zero)⟩

/-- The source's two supplied-reply resumes never inspect the already-consumed root request. -/
theorem root_unused (initial : registration.ServerInitialKdf) (root : Std.Array Std.U8 32#usize)
    (role : initial.pending = PqxdhInitialRatchetComplementarity.serverPending root)
    (initialResponse : pqxdh.concrete.InitialRatchetKdfResponse) (response : RatchetKdfResponse) :
    RegistrationSeedErasure.selected initial initialResponse response =
      RegistrationSeedErasure.selected (restore (publicInitial initial)) initialResponse response := by
  simp only [RegistrationSeedErasure.selected, registration.ServerInitialKdf.resume, role,
    restore, publicInitial, pqxdh.concrete.resume_initial_ratchet_kdf,
    PqxdhInitialRatchetComplementarity.serverPending]

/-- All subsequent actual AEAD/hash/write callbacks receive the original native capability at the supplied 108-byte output. -/
def factored (initial : PublicInitial) (output : PqxdhServerAuthKeySchedule.Output) :
    OracleComp RegistrationRecordPrimitives.Spec (RustM RegistrationServerRecordExecutor.Result) :=
  RegistrationServerRecordExecutor.continueResult
    (RegistrationSeedErasure.selected (restore initial)
      (RawCtxSelectedInitialConstructor.response64 (zero ++ output.2))
      (RawCtxKdfRequestTable.fullResponse output.1)) RegistrationServerRecordExecutor.fromAead

def supplied (initial : registration.ServerInitialKdf) (left right : RootOutput)
    (output : PqxdhFullSecretInputKdf.FullOutput) :
    OracleComp RegistrationRecordPrimitives.Spec (RustM RegistrationServerRecordExecutor.Result) :=
  RegistrationServerRecordExecutor.continueResult
    (RegistrationSeedErasure.selected initial (RawCtxSelectedInitialConstructor.response64 (left ++ right))
      (RawCtxKdfRequestTable.fullResponse output)) RegistrationServerRecordExecutor.fromAead

/-- Actual admission derives the role receipt; no supplied successful-kernel or AD-replacement premise is required. -/
theorem supplied_factored (control : pqxdh.ServerState) (current : session.ServerAuthenticationPin)
    (availability : pqxdh.KeyIdAvailability) (agreement : agreement.ServerAgreement) (application : Slice Std.U8)
    (initial : registration.ServerInitialKdf)
    (actual : registration.begin_server_completion control current availability agreement application = .ok (.Ok initial))
    (left right : RootOutput) (output : PqxdhFullSecretInputKdf.FullOutput) :
    supplied initial left right output = factored (publicInitial initial) (output, right) := by
  unfold supplied factored
  rw [RegistrationSeedErasure.server_left_unused control current availability agreement application initial actual
    left zero right output]
  rw [root_unused initial agreement.root.bytes
    (RegistrationSeedKernel.server_pending control current availability agreement application initial actual)]

/-- The exact consumed native kernel is the seed constructor before the remaining native seal/publication operations. -/
theorem factored_kernel (initial : PublicInitial) (material : PqxdhDeploymentHiddenLayout.Material)
    (seed : PqxdhRecordLiftSeed.Seed) :
    ∃ selected : registration.ServerRecordAead,
      RegistrationSeedErasure.selected (restore initial)
        (RawCtxSelectedInitialConstructor.response64 (zero ++ seed.2))
        (RawCtxKdfRequestTable.fullResponse (PqxdhDeploymentHiddenLayout.joinOutput material seed).1) = .ok (.Ok selected) ∧
      PqxdhRecordLiftSeed.serverKernel seed = .ok selected.pending.seal.advanced := by
  let response := RawCtxKdfRequestTable.fullResponse (PqxdhDeploymentHiddenLayout.joinOutput material seed).1
  obtain ⟨kernel, next, selected, context, kernelRun, initialResume, ratchetResume, sent⟩ :=
    RegistrationSeedKernel.source_send (restore initial)
      (RawCtxSelectedInitialConstructor.response64 (zero ++ seed.2)) response
  have supplied : PqxdhInitialReplyErasure.kernelOf false
      (RawCtxSelectedInitialConstructor.response64 (zero ++ seed.2)) = .ok kernel := kernelRun
  dsimp only [response, PqxdhDeploymentHiddenLayout.joinOutput] at sent ratchetResume
  have same := PqxdhRecordLiftSeed.server_source_parts zero material.1 seed material.2 context
    (.None : core.option.Option Unit)
  rw [supplied, bind_tc_ok, sent] at same
  obtain ⟨expected, expectedRun⟩ := PqxdhRecordLiftSeed.serverKernel_total seed
  rw [expectedRun, RawCtxMaterialInterpretation.rust_map_ok] at same
  have kernelEq : selected.pending.seal.advanced = expected := by
    simpa only [RustM.ok.injEq, Option.some.injEq, Prod.mk.injEq, and_true] using same
  refine ⟨selected, ?_, expectedRun.trans (congrArg RustM.ok kernelEq.symm)⟩
  simp only [RegistrationSeedErasure.selected, initialResume, bind_tc_ok, PqxdhDeploymentHiddenLayout.joinOutput, ratchetResume]

/-- A uniform 108-byte output is the independent material/seed experiment for this actual bound continuation, through every later interpreter and observer. -/
theorem uniform_split {Primitive Result : Type}
    (initial : PublicInitial)
    (native : QueryImpl RegistrationRecordPrimitives.Spec (StateT Primitive ProbComp))
    (state : Primitive)
    (next : (RustM RegistrationServerRecordExecutor.Result × Primitive) → ProbComp Result) :
    LazyOracleDiscard.LawEq
      (do let output ← $ᵗ PqxdhServerAuthKeySchedule.Output
          let result ← (simulateQ native (factored initial output)).run state
          next result)
      (do let material ← $ᵗ PqxdhDeploymentHiddenLayout.Material
          let seed ← $ᵗ PqxdhRecordLiftSeed.Seed
          let result ← (simulateQ native (factored initial (PqxdhDeploymentHiddenLayout.joinOutput material seed))).run state
          next result) :=
  PqxdhDeploymentHiddenLayout.uniform_split _

/-- The real bound continuation, followed by any concrete response/signing/record experiment. -/
noncomputable def trial {Primitive : Type}
    (native : QueryImpl RegistrationRecordPrimitives.Spec (StateT Primitive ProbComp))
    (post : PublicInitial → (RustM RegistrationServerRecordExecutor.Result × Primitive) → ProbComp Bool)
    (context : PublicInitial × Primitive) : PqxdhServerAuthKeySchedule.Distinguisher := fun output => do
  let result ← (simulateQ native (factored context.1 output)).run context.2
  post context.1 result

open PqxdhSecretInputKdf PqxdhServerAuthKeySchedule

/-- The existing five explicit primitive advantages for the concrete bound continuation. -/
noncomputable def keyLoss (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (distinguisher : Distinguisher) : ℝ :=
  (hmacPrfRealGame hmac (rootExpandReduction source distinguisher)).boolDistance
      (hmacPrfRandomGame (rootExpandReduction source distinguisher)) +
    (extractRealGame hmac uniform32 (initExtractReduction source hmac distinguisher)).boolDistance
      (extractUniformGame uniform32 (initExtractReduction source hmac distinguisher)) +
    (hmacPrfRealGame hmac (initExpandReduction source distinguisher)).boolDistance
      (hmacPrfRandomGame (initExpandReduction source distinguisher)) +
    (extractRealGame hmac uniform32 (stepExtractReduction hmac distinguisher)).boolDistance
      (extractUniformGame uniform32 (stepExtractReduction hmac distinguisher)) +
    (hmacPrfRealGame hmac (stepExpandReduction distinguisher)).boolDistance
      (hmacPrfRandomGame (stepExpandReduction distinguisher))

/-- The actual root-free bound service can replace its real key schedule by independent hidden seed and position-one material at the existing five-hop loss. The context is sampled before the selected PRK, and the entire later concrete source experiment is included in the constructed reductions. -/
theorem key_bound {Primitive : Type} (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (hmac : HmacSha512) (correct : PqxdhFullSecretInputKdf.SourceFullCorrect source hmac)
    (native : QueryImpl RegistrationRecordPrimitives.Spec (StateT Primitive ProbComp))
    (sample : ProbComp (PublicInitial × Primitive))
    (post : PublicInitial → (RustM RegistrationServerRecordExecutor.Result × Primitive) → ProbComp Bool) :
    (do let context ← sample
        let prk ← $ᵗ HmacBlock
        trial native post context (keySchedule source hmac prk)).boolDistance
      (do let context ← sample
          let material ← $ᵗ PqxdhDeploymentHiddenLayout.Material
          let seed ← $ᵗ PqxdhRecordLiftSeed.Seed
          trial native post context (PqxdhDeploymentHiddenLayout.joinOutput material seed)) ≤
      keyLoss source hmac (withContext sample (trial native post)) := by
  have pointwise : ∀ context : PublicInitial × Primitive,
      LazyOracleDiscard.LawEq
        (do let output ← $ᵗ Output; trial native post context output)
        (do let material ← $ᵗ PqxdhDeploymentHiddenLayout.Material
            let seed ← $ᵗ PqxdhRecordLiftSeed.Seed
            trial native post context (PqxdhDeploymentHiddenLayout.joinOutput material seed)) := by
    intro context
    exact uniform_split context.1 native context.2 (post context.1)
  have ideal : 𝒟[do let context ← sample
                     let output ← $ᵗ Output
                     trial native post context output] =
      𝒟[do let context ← sample
           let material ← $ᵗ PqxdhDeploymentHiddenLayout.Material
           let seed ← $ᵗ PqxdhRecordLiftSeed.Seed
           trial native post context (PqxdhDeploymentHiddenLayout.joinOutput material seed)] := by
    apply evalDist_bind_congr
    intro context
    exact (pointwise context).evalDist_eq
  rw [← advantage_congr rfl ideal]
  exact keySchedule_bound_context source hmac correct sample (trial native post)

end BeaconcryptCore.Computational.RegistrationBoundKeySchedule

/-- info: 'BeaconcryptCore.Computational.RegistrationBoundKeySchedule.root_unused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBoundKeySchedule.root_unused

/-- info: 'BeaconcryptCore.Computational.RegistrationBoundKeySchedule.supplied_factored' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBoundKeySchedule.supplied_factored

/-- info: 'BeaconcryptCore.Computational.RegistrationBoundKeySchedule.factored_kernel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBoundKeySchedule.factored_kernel

/-- info: 'BeaconcryptCore.Computational.RegistrationBoundKeySchedule.uniform_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBoundKeySchedule.uniform_split

/-- info: 'BeaconcryptCore.Computational.RegistrationBoundKeySchedule.key_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBoundKeySchedule.key_bound
