import BeaconcryptCore.Computational.VCVioForwardOracleComp
import VCVio.ProgramLogic.Relational.FromUnary

/-!
# Forward shim: relational program logic (VCVio pin 98dc1089)

Re-export point for the relational helpers that migrated proofs need. It brings VCVio's `OracleComp.ProgramLogic.Relational.relTriple_prod` into the project closure (module `VCVio.ProgramLogic.Relational.FromUnary`, which exists at the pin and upstream; upstream moves the lemma to `Relational.Basic` with the same statement). Two support properties combine into a relational triple through the product coupling, so project proofs no longer unfold `RelTriple` into an `SPMF` coupling. At the pin, `RelTriple` and its couplings are still defined through `SPMF`; that definition is VCVio's and is not deprecated.
-/
