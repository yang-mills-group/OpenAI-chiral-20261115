import SatinStress.U1.Certificate.F.Data

-- This file from the U1 certificate generator (`the construction notes`).
-- Proof by Lean kernel checks; no axiom for evaluation or assumption on the data.
namespace SatinStress.U1.Certificate.F
open Radix Raw Class Derivative

-- high limits only in these arithmetic-certificate files
set_option maxHeartbeats 32000000
set_option maxRecDepth 120000

theorem V_dep_17 :
    (relation [(v17,1), (v6, 1), (v15, 1)]).denote = 0 :=
  Raw.spends vRow_all (by decide +kernel)

theorem V_dep_18 :
    (relation [(v18,1), (v7, 1), (v14, 1)]).denote = 0 :=
  Raw.spends vRow_all (by decide +kernel)

theorem V_dep_19 :
    (relation [(v19,1), (v5, 1)]).denote = 0 :=
  Raw.spends vRow_all (by decide +kernel)

theorem V_dep_20 :
    (relation [(v20,1), (v4, -1), (v15, -1)]).denote = 0 :=
  Raw.spends vRow_all (by decide +kernel)

end SatinStress.U1.Certificate.F
