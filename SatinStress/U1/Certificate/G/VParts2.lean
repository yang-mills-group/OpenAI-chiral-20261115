import SatinStress.U1.Certificate.G.Data

-- This file from the U1 certificate generator (`the construction notes`).
-- Proof by Lean kernel checks; no axiom for evaluation or assumption on the data.
namespace SatinStress.U1.Certificate.G
open Radix Raw Class Derivative

-- high limits only in these arithmetic-certificate files
set_option maxHeartbeats 32000000
set_option maxRecDepth 120000

theorem V_dep_20 :
    (relation [(v20,1), (v10, -1)]).denote = 0 :=
  Raw.spends vRow_all (by decide +kernel)

theorem V_dep_21 :
    (relation [(v21,1), (v4, 1)]).denote = 0 :=
  Raw.spends vRow_all (by decide +kernel)

theorem V_dep_22 :
    (relation [(v22,1), (v2, 1)]).denote = 0 :=
  Raw.spends vRow_all (by decide +kernel)

theorem V_dep_23 :
    (relation [(v23,1), (v1, 1)]).denote = 0 :=
  Raw.spends vRow_all (by decide +kernel)

end SatinStress.U1.Certificate.G
