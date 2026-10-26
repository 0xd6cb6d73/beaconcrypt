-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordLiftSourcePrefix

/-! Complete supported first-parent prefix equality for policies differing only at a dependent child. The actual source availability certificate excludes that child before its missing parent is reached. -/
open OracleComp OracleSpec Aeneas
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordLiftPrefixPolicy
open PqxdhRecordLiftProtocol PqxdhRecordLiftFirstLookup PqxdhRecordLiftAvailability
open PqxdhRecordLiftChainState PqxdhRecordLiftChainTable PqxdhRecordLiftInterface
variable {n : Nat} {Result : Type}

/-- Only the private lookup service consults a coordinate selector. -/
def AgreesAt (left right : Coordinate (Slot n) → Bool) : (ServiceSpec n).Domain → Prop
  | .lookup coordinate => left coordinate = right coordinate
  | _ => True

/-- Equal selector decisions at the requested coordinate give the same complete private query execution. -/
theorem query_agrees {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (left right : Coordinate (Slot n) → Bool) (query : (ServiceSpec n).Domain)
    (agree : AgreesAt left right query)
    (secret : Private n) :
    (interpreter (PqxdhRecordLiftMixedWorld.policy setup.source left) setup codec query).run secret =
      (interpreter (PqxdhRecordLiftMixedWorld.policy setup.source right) setup codec query).run secret := by
  cases query with
  | lookup coordinate =>
      change left coordinate = right coordinate at agree
      have same : PqxdhRecordLiftChainOracle.lookup setup.source (cachedSeeds secret) left coordinate =
          PqxdhRecordLiftChainOracle.lookup setup.source (cachedSeeds secret) right coordinate := by
        funext state
        simp only [PqxdhRecordLiftChainOracle.lookup, agree]
      have logged : PqxdhRecordLiftLoggedAdapters.liftLookup
          (PqxdhRecordLiftChainOracle.lookup setup.source (cachedSeeds secret) left) coordinate =
          PqxdhRecordLiftLoggedAdapters.liftLookup
          (PqxdhRecordLiftChainOracle.lookup setup.source (cachedSeeds secret) right) coordinate := by
        funext state
        simp only [PqxdhRecordLiftLoggedAdapters.liftLookup, same]
      simp only [interpreter, localInterpreter, PqxdhRecordLiftOpaqueDrivers.interpreter,
        withRecord, PqxdhRecordLiftMixedWorld.policy, StateT.run, logged]
  | _ => rfl

/-- Supported query safety excludes a dependent child until the missing parent is queried, so policies differing only at that child execute the identical complete prefix. -/
theorem supported_prefix {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (left right : Coordinate (Slot n) → Bool) (parent child : Coordinate (Slot n))
    (reads : PqxdhRecordLiftMaskedReads.Reads child parent)
    (agree : ∀ coordinate, coordinate ≠ child → left coordinate = right coordinate)
    (client : OracleComp (ServiceSpec n) Result)
    (avoids : client.AllQueriesSatisfy (Avoids parent)) (secret : Private n)
    (safe : Safe (interpreter (PqxdhRecordLiftMixedWorld.policy setup.source left) setup codec)
      Allowed client secret) (missing : secret.chain parent = none) :
    (simulateQ (interpreter (PqxdhRecordLiftMixedWorld.policy setup.source left) setup codec) client).run secret =
      (simulateQ (interpreter (PqxdhRecordLiftMixedWorld.policy setup.source right) setup codec) client).run secret := by
  induction client using OracleComp.inductionOn generalizing secret with
  | pure value => rfl
  | query_bind query next ih =>
      rw [allQueriesSatisfy_query_bind_iff] at avoids
      have selected : AgreesAt left right query := by
        cases query with
        | lookup coordinate =>
            apply agree
            rintro rfl
            obtain ⟨_, output, found⟩ := safe.1.2.resolve_left reads.1
            rw [reads.2, missing] at found
            contradiction
        | _ => trivial
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      rw [← query_agrees setup codec left right query selected secret]
      exact bind_congr_of_forall_mem_support _ (fun result member =>
        ih result.1 (avoids.2 result.1) result.2 (safe.2 result member)
          ((query_other setup.source left setup codec parent query avoids.1 secret result member).trans missing))

/-- The initialized adaptive WorldSpec schedule has the same full first-parent scanner law under selectors differing only at a dependent child. Its query-safety and missing-parent facts are derived from the source. -/
theorem scan_schedule {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (left right : Coordinate (Slot n) → Bool) (parent child : Coordinate (Slot n))
    (reads : PqxdhRecordLiftMaskedReads.Reads child parent)
    (agree : ∀ coordinate, coordinate ≠ child → left coordinate = right coordinate)
    (route : RawCtxServerRouting.SenderDecoder) (client : OracleComp (WorldSpec n) Result) :
    (simulateQ (interpreter (PqxdhRecordLiftMixedWorld.policy setup.source left) setup codec)
      (scan parent (schedule codec.frameRead route client initialControl))).run initialPrivate =
    (simulateQ (interpreter (PqxdhRecordLiftMixedWorld.policy setup.source right) setup codec)
      (scan parent (schedule codec.frameRead route client initialControl))).run initialPrivate :=
  supported_prefix setup codec left right parent child reads agree _ (scan_avoids parent _) initialPrivate
    (PqxdhRecordLiftSourcePrefix.scan_schedule_safe setup codec left route client parent) rfl

/-- The exact frozen program has the same complete first-parent prefix in either source mode, with the caller result, ledger, environment state and private remainder retained. -/
theorem scan_program {ι KemSK Reader Response E X : Type} {baseSpec : OracleSpec ι}
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (left right : Coordinate (Slot n) → Bool) (parent child : Coordinate (Slot n))
    (reads : PqxdhRecordLiftMaskedReads.Reads child parent)
    (agree : ∀ coordinate, coordinate ≠ child → left coordinate = right coordinate)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E)
    (serverKid : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) :
    (simulateQ (interpreter (PqxdhRecordLiftMixedWorld.policy setup.source left) setup codec)
      (scan parent (PqxdhRecordLiftProtocol.program env setup.source.crypto codec route serverKid bounds mode adversary))).run initialPrivate =
    (simulateQ (interpreter (PqxdhRecordLiftMixedWorld.policy setup.source right) setup codec)
      (scan parent (PqxdhRecordLiftProtocol.program env setup.source.crypto codec route serverKid bounds mode adversary))).run initialPrivate :=
  scan_schedule setup codec left right parent child reads agree route
    (PqxdhRecordLiftInterface.program env setup.source.crypto codec serverKid bounds mode adversary)

/-- Proof attachment preserves the exact initialized schedule prefix equality without conditioning, including unused parent cuts. -/
theorem sampled_schedule {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (left right : Coordinate (Slot n) → Bool) (parent child : Coordinate (Slot n))
    (reads : PqxdhRecordLiftMaskedReads.Reads child parent)
    (agree : ∀ coordinate, coordinate ≠ child → left coordinate = right coordinate)
    (route : RawCtxServerRouting.SenderDecoder) (client : OracleComp (WorldSpec n) Result) :
    sampledPrefix setup.source left setup codec parent (schedule codec.frameRead route client initialControl) =
      sampledPrefix setup.source right setup codec parent (schedule codec.frameRead route client initialControl) := by
  apply (map_inj_right (f := Subtype.val) (fun h => Subtype.ext h)).mp
  rw [prefix_forget, prefix_forget]
  exact scan_schedule setup codec left right parent child reads agree route client

/-- The proof-attached sampler of either frozen environment/adversary program is the same under selectors differing only at a dependent child, retaining the caller result, ledger, environment state and private remainder. -/
theorem sampled_program {ι KemSK Reader Response E X : Type} {baseSpec : OracleSpec ι}
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (left right : Coordinate (Slot n) → Bool) (parent child : Coordinate (Slot n))
    (reads : PqxdhRecordLiftMaskedReads.Reads child parent)
    (agree : ∀ coordinate, coordinate ≠ child → left coordinate = right coordinate)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E)
    (serverKid : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) :
    sampledPrefix setup.source left setup codec parent
        (PqxdhRecordLiftProtocol.program env setup.source.crypto codec route serverKid bounds mode adversary) =
      sampledPrefix setup.source right setup codec parent
        (PqxdhRecordLiftProtocol.program env setup.source.crypto codec route serverKid bounds mode adversary) :=
  sampled_schedule setup codec left right parent child reads agree route
    (PqxdhRecordLiftInterface.program env setup.source.crypto codec serverKid bounds mode adversary)

end BeaconcryptCore.Computational.PqxdhRecordLiftPrefixPolicy

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftPrefixPolicy.query_agrees' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftPrefixPolicy.query_agrees

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftPrefixPolicy.supported_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftPrefixPolicy.supported_prefix

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftPrefixPolicy.scan_schedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftPrefixPolicy.scan_schedule

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftPrefixPolicy.scan_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftPrefixPolicy.scan_program

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftPrefixPolicy.sampled_schedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftPrefixPolicy.sampled_schedule

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftPrefixPolicy.sampled_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftPrefixPolicy.sampled_program
