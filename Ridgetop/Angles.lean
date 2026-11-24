import Ridgetop.Origin
import Risa.Warehouse
import Preen.Chey
-- pilot price exactly zero, all. 
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 5000
set_option maxHeartbeats 360000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
namespace PledgeT
open Calico
open Aria Casting Set
open scoped Pointwise
namespace MiterT
open _root_.YM.Gleam.Luster.Risa CF.BProof AnalyticBridge.VerifiedReset
open Py.Rate.LocalLimit Py Py.Dyad Papal _root_.YM.CF.Pannier.Chancel Cliplet Precision
variable (P:Spine) (s A:ℕ)(o:Bool→ Cover)(b:Bool)
lemma galop (i:ℕ): boarding P s A o false i=0:=by
 unfold boarding berlin; dsimp only
 exact Ridgetop.meal_m _ _ ((P.par.V.L.roof _).2.1 _) _ ((P.par.V.L.roof _).2.2 _) _ _ _
theorem pilot_v(Q:Pilot P s A o false):Q.price=0:=by
 have he : Tendsto (boarding P s A o false ∘ Q.station) atTop (𝓝 (0:ℝ)):= by
    simp_rw [Function.comp_def,galop]; exact tendsto_const_nhds
 exact tendsto_nhds_unique Q.market he
theorem boon_empty(d l H:ℕ)(w:Cover):boonW P d l H w=0:= pilot_v ..
#print axioms boon_empty
end MiterT
end PledgeT
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
