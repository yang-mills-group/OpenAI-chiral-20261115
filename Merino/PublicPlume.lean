import SU5SatinMarkedCurrentNovember7
import Merino.Plume.Ala
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
namespace YM.CF.Merino
open Buffered.Afterglow.Tower.VacuumSelection
universe u

/-- Unconditionally, joint election retaining all the CP1 and marked-scalar
signed financial inputs for XXI, with BQueue actuals in the price P.E. -/
theorem assembledPlume (Mc:ℕ):
   ∃ P K x p, Spine.RibbonCourts.{u} P K x Mc ∧
    Dazzles P p ∧ ∃ C:Plume.Constellation,
      twinkling P p C.α C.δ C.bigE C.r C.L ∧
      Plume.Hill P p C:=by
 obtain ⟨P,K,x,p,R,t⟩:=royal.{u} Mc
 exact ⟨P,K,x,p,R,t, Plume.snowpack P p t R.chilled⟩


#check assembledPlume
#check royal
#check Spine.courts
#check Hem.rosebud
#check Medal.feast
#check Medal.coin_rate
#check Plume.aiming
#check Plume.positiveCt
#print axioms assembledPlume
#print axioms Plume.positiveCt
end YM.CF.Merino

