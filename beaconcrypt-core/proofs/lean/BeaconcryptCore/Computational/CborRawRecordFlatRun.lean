-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawRecordOriginFlatten

/-! The literal guarded CTX world runs on its complete cursor, record control and private state below the unchanged secrecy ledger. This is the operational whole-program representation used by the fresh-message and test-bit couplings. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawRecordFlatRun
open PqxdhRecordLiftInterface (Environment)
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftIdeal (KeyMode CtxPrivate ctxInterpreter)
open PqxdhDeploymentInterface (FreshBounds Mode ModeSpec asModeO)
variable {n : Nat} {ι KemSK Reader Response E X : Type} {base : OracleSpec ι}

noncomputable def startup (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup base KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) :=
  CborRawRecordOriginFlatten.startup (ctxInterpreter modes replace setup codec) env codec route CtxPrivate.initial

noncomputable def install (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup base KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (created : PqxdhLiveServerConstruction.Created Unit) (shell : CborRecordWorldClient.Shell)
    (control : PqxdhRecordLiftProtocol.Control n) (secret : CtxPrivate n) :=
  CborRawRecordOriginFlatten.install (ctxInterpreter modes replace setup codec) codec route created shell control secret

/-- Actual raw startup, Server installation and adaptive full-ledger execution retain the entire cursor-aware private state. -/
theorem ctxRun_flat (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup base KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Aeneas.Std.U64) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) :
    PqxdhRecordLiftLaterWorlds.ctxRunOf modes replace setup codec route
      (CborRawRecordLiftBounds.client env setup.source.crypto codec serverKid bounds mode adversary) =
      (startup modes replace setup codec route env >>= fun born =>
        match born.1.1.1 with
        | none => pure ((none, born.1.2), born.2)
        | some (created, initial) =>
            install modes replace setup codec route created born.1.1.2 born.1.2 born.2 >>= fun installed =>
              (fun result => ((some (PqxdhRegistrationJointServerBirth.encode created,
                (result.1, result.2.1), result.2.2.1.1.1), result.2.2.1.2), result.2.2.2)) <$>
                (simulateQ (CborRawRecordFlat.fullImpl modes replace setup codec route env serverKid bounds)
                  (asModeO mode adversary)).run
                  (PqxdhDeploymentSecrecy.Ledger.empty, (((initial, installed.1.1), installed.1.2), installed.2))) := by
  exact CborRawRecordOriginFlatten.program_flat (ctxInterpreter modes replace setup codec) env setup.source.crypto
    codec route serverKid bounds mode adversary CtxPrivate.initial

end BeaconcryptCore.Computational.CborRawRecordFlatRun

/-- info: 'BeaconcryptCore.Computational.CborRawRecordFlatRun.ctxRun_flat' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordFlatRun.ctxRun_flat
