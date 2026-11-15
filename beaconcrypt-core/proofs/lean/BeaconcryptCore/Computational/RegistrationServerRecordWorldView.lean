-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeWorldView
import BeaconcryptCore.Computational.RegistrationWorldAgreement

/-! The existing private instrumentation view is shared by current source callbacks without importing their separate all-request correspondence. It retains operational World, cache, protocol, auxiliary and platform state exactly as before. -/
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationServerRecordWorldSource
variable {n : Nat} {Auxiliary : Type}

def project (before : RegistrationWorldAgreement.State n Auxiliary) : RegistrationWorldAgreement.State n Auxiliary :=
  { before with recordRequests := [], world := (RegistrationNativeWorldView.project before.world.1, before.world.2) }

end BeaconcryptCore.Computational.RegistrationServerRecordWorldSource
