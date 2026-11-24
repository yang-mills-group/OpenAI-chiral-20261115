import GaugeFieldConstruction.Caps
import GaugeFieldConstruction.RateC
import GaugeFieldConstruction.RateG
import GaugeFieldConstruction.RateR

/-!
# Assemble totals from certifier with the needed orders of Photon, Spin letters
-/
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction.Invoice
open Cauchy Vouchers Abacus
lemma greaseC : RateC.S.toFinset=bound 3 := by decide
lemma greaseR : RateR.S.toFinset=bound 3 := by decide
lemma greaseG : RateG.S.toFinset=formG 2 := by decide
end YM.GaugeFieldConstruction.Invoice
