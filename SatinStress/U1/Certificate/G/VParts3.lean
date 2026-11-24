import SatinStress.U1.Certificate.G.Data

-- This file from the U1 certificate generator (`the construction notes`).
-- Proof by Lean kernel checks; no axiom for evaluation or assumption on the data.
namespace SatinStress.U1.Certificate.G
open Radix Raw Class Derivative

-- high limits only in these arithmetic-certificate files
set_option maxHeartbeats 32000000
set_option maxRecDepth 120000

theorem V_dep_25 :
    (relation [(v25,1), (v3, 1), (v24, 1)]).denote = 0 :=
  Raw.spends vRow_all (by decide +kernel)

theorem V_dep_27 :
    (relation [(v27,1), (v5, 1), (v26, 1)]).denote = 0 :=
  Raw.spends vRow_all (by decide +kernel)

theorem V_dep_31 :
    (relation [(v31,1), (v29, 1), (v30, -1)]).denote = 0 :=
  Raw.spends vRow_all (by decide +kernel)

theorem V_dep_32 :
    (relation [(v32,1), (v11, 1), (v12, -1)]).denote = 0 :=
  Raw.spends vRow_all (by decide +kernel)

end SatinStress.U1.Certificate.G
