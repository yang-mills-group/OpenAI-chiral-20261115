import SatinStress.U1.Certificate.F.Data

-- This file from the U1 certificate generator (`the construction notes`).
-- Proof by Lean kernel checks; no axiom for evaluation or assumption on the data.
namespace SatinStress.U1.Certificate.F
open Radix Raw Class Derivative

-- high limits only in these arithmetic-certificate files
set_option maxHeartbeats 32000000
set_option maxRecDepth 120000
set_option synthInstance.maxSize 2048

theorem issuers_T : ph4.M.issuers TT = colsTID := by decide +kernel

theorem issuers_W : ph5.M.issuers W = colsWID := by decide +kernel

theorem issuers_V : ph5.M.issuers V = colsVID := by decide +kernel

end SatinStress.U1.Certificate.F
