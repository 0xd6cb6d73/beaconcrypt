-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryDriver
/-! One actual ordinary SDK invocation retains its returned source object, complete reached native/platform state, exact writer-attempt frames and its source-entry observation. Committing that observation is separate from the current model owner finalizer. -/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryReceipt
structure Packet (Self Reply Native Platform : Type) where
  outcome : RustM (Reply ×Self)
  after : Native ×Platform
  frames : PqxdhRecordLiftLoggedAdapters.Frames
  rawBefore : Nat
  rawInvoked : Bool

def rawAfter {Self Reply Native Platform : Type} (packet : Packet Self Reply Native Platform) : Nat :=
  packet.rawBefore + if packet.rawInvoked then 1 else 0
end BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryReceipt
