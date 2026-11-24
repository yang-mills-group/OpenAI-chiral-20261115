import GaugeFieldConstruction.PhysicalBook
noncomputable section
namespace YM.GaugeFieldConstruction.Phys
open Cauchy Row Calibration Finset Function
open Matter (Generation FlavorIndex)
open scoped BigOperators Matrix
set_option maxHeartbeats 240000
set_option maxRecDepth 4000
abbrev GoldrollFe:Book:= (1,0)
lemma goldαFe : dress (1,0)=GoldrollFe:=by
 unfold dress; rw[LinearMap.prodMap_apply]; simp only [LinearMap.id_apply, map_zero]
lemma uxrtFe(X:Shell)(h:X.2.2.2=0): (dress X).2.2.2=0:=by rw [dressX]; simp only [h,map_zero]
end YM.GaugeFieldConstruction.Phys
