-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordLiftLaterTargets

/-!
# Later fresh-message and left-or-right target statements

These are the confidentiality-only R6 forms of the frozen run-phase targets. The post phase discloses only a function of the environment state and runs through `PostSpec`; the claim and public decision may use its final output. No origin or binding target is introduced, and neither target needs a budget or a primitive contract.
-/

open OracleComp OracleSpec ENNReal CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhRecordFactsLaterTargets
open PqxdhRecordLiftInterface PqxdhRecordLiftIdeal PqxdhRecordLiftLaterWorlds
open PqxdhDeploymentInterface (Mode ModeSpec FreshBounds)
open PqxdhDeploymentLater (PostSpec)
open PqxdhServerAuthExperiment (Setup Codec)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

section Targets
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
  (route : RawCtxServerRouting.SenderDecoder) (serverKid : Std.U64) (bounds : FreshBounds)

/-- Later CE-APP fact: after any E-only disclosure and post adversary, guessing an admitted fresh message sent on a hidden handle succeeds with probability at most `2^{-min}`. The final post output determines both the claimed index and the bytes. No `Frame`, budget or contract premise. -/
def LaterFreshGuessStatement (n : Nat) : Prop :=
  ∀ {E X Out R : Type} (env : Environment n E) (reveal : E → R)
    (first : OracleComp (ModeSpec .P) X) (second : X → R → OracleComp PostSpec Out)
    (claim : Out → Option (Nat × Pqxdh.Bytes)),
  𝒟[(fun result => freshEvent claim (ctxView result)) <$>
      laterIdealRecords setup codec route env serverKid bounds .P reveal first second] {true} ≤
    ((2 ^ bounds.min : Nat) : ℝ≥0∞)⁻¹

/-- Later CE-LOR fact: after any E-only disclosure and post adversary, every public decision guesses the shared test bit with probability exactly one half of public eligibility and hiddenness of every admitted test. The public projection includes the final post output and environment state, while the secret test bit is excluded. No `Frame`, budget or contract premise. -/
def LaterLorStatement (n : Nat) : Prop :=
  ∀ {E X Out R : Type} (env : Environment n E) (reveal : E → R)
    (first : OracleComp (ModeSpec .P) X) (second : X → R → OracleComp PostSpec Out)
    (decision eligible : PublicHiding n E Out → Bool),
  𝒟[(fun result => lorGuess setup.source.crypto codec serverKid decision eligible (ctxView result)) <$>
      laterIdealRecords setup codec route env serverKid bounds .P reveal first second] {true} =
    2⁻¹ * 𝒟[(fun result => lorEligible setup.source.crypto codec serverKid eligible (ctxView result)) <$>
      laterIdealRecords setup codec route env serverKid bounds .P reveal first second] {true}

end Targets
end BeaconcryptCore.Computational.PqxdhRecordFactsLaterTargets
