import SatinStress.U1.Certificate.X.Data

-- This file from the U1 certificate generator (`the construction notes`).
-- Proof by Lean kernel checks; no axiom for evaluation or assumption on the data.
namespace SatinStress.U1.Certificate.X
open Radix Raw Class Derivative

-- high limits only in these arithmetic-certificate files
set_option maxHeartbeats 32000000
set_option maxRecDepth 120000

theorem issuers_T : mixed4.M.issuers TT = colsTID := by decide +kernel

theorem issuers_W : mixed.M.issuers W = colsWID := by decide +kernel

theorem issuers_V : mixed.M.issuers V = colsVID := by decide +kernel

end SatinStress.U1.Certificate.X
