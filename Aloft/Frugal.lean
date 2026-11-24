import Aloft.ZL
import Aloft.Canon
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
namespace Aloft
open Py.Dyad Keeping Py.Rate.Pitching.Focus
open _root_.YM.Preen
local notation "j0"=> (3:Axis)
variable (M:Morn P.par.K)(α:ℝ)(F:ℕ)(C D:ℕ→ℕ→ℝ)(x:P.Spectrum0 3)(p:∀ s,F ≤ s→ Accordance P M F s (C s) (D s))(u:RobeRoad P F C D x)(v:Jones P M α F C D x)
local notation "ξ"=>P.otherSpectrum 3 3 x
local notation "Ω"=>P.heaven 3 ξ
local notation "Ψ"=> P.seasons 3 ξ
local notation "H"=>P.ManyF 3 ξ
local notation "ζ"=>P.wealth 3 ξ
local notation "A₀"=>paster (Ω)
local notation "U"=>P.cartage 3 ξ
abbrev amber(w d:ℕ)(o:Cover)(t:(P.calibration.ℓ:ℤ)+22 ≤ nodeC o 3):H:= A₀ (palmY P x d o t) -- d is stack, w unused
-- use smaller instance via generic negProj
abbrev adsorption {G:Hilbert}(L:Submodule ℂ G.space):G.Op:= (Submodule.orthogonal L).starProjection
local notation "L" z:max => asset P x (A₀ z)
lemma cartPaste(z:H)(r:Vantage):U r (A₀ z)=A₀ (U r z):=by
 exact turn (R:=(H)) (Ω) (P.stone_norm ..) (U r) (P.cart_empty ..) z (P.inner_pay 3 ξ r (Ω) z)
where turn {R:Hilbert}(k:R)(h:‖k‖=1)(f:R.Op)(hr:f k=k)(z:R)(hV:inner ℂ (f k) (f z)=inner ℂ k z): f (paster k z)=paster k (f z):=by rw [pasted _ h,pasted _ h,map_sub,map_smul, hr]; rw [hr] at hV; rw [hV]
-- simpler via replace h
lemma truck_view (y:Cover){f:P.Test}(p:P.birthF 3 s f) : P.viewF 3 x s (P.certify 3 s (look 3) (fun i=>y i.val) p)= P.truck 3 x (P.vtile s y) (P.viewF 3 x s p):= P.ship_ideal 3 x s (look 3) (fun i=>y i.val) p
lemma truck_here (y:Cover){f:P.Test}(p:P.birthF 3 s f): P.wealth 3 x (P.viewF 3 x s (P.certify 3 s (look 3) (fun i=>y i.val) p))=P.cartage 3 x (P.laysM (P.vtile s y)) (P.wealth 3 x (P.viewF 3 x s p)):= (congrArg (P.wealth 3 x) (truck_view P s x y p)).trans (traveller P x (P.vtile s y) (P.viewF 3 x s p))
set_option maxHeartbeats 650000 in
lemma shifted(o:Cover)(t:(P.calibration.ℓ:ℤ)+22 ≤ nodeC o 3):∃ w:Cover,∃ h:nodeC w 3=nodeC o 3,
 (∀i:Axis,i≠3→0 ≤nodeC w i ∧ nodeC w i ≤ (ruler P.par.block)) ∧
 ∃ r:Vantage,amber P x 0 s w (t.trans_eq h.symm)=U r (amber P x 0 s o t):=by -- param order check. P s x? variable order P s A etc from rig /tmp. statement d=s? amber parameters order following (x)(w d); check
 let y(i:Axis):ℤ:= -(nodeC o i/(ruler P.par.block))
 let w:= ((look 3).foldr (fun i a=>Calico.slid P.calibration i.val (y i.val) a) o)
 let Hk:=postal_account P (look 3) y o
 have h:nodeC w 3=nodeC o 3:=Hk.1; refine ⟨w,h, fun i g=> ?_, P.laysM (P.vtile s y),?_⟩ -- ∃ r combine
 · rw [show nodeC w i=_ from Hk.2 ⟨i,g⟩,mass_all]; unfold y; rw [mul_neg]
   have e:=Int.emod_lt_of_pos (nodeC o i) (ruler_gene P.par.block); have h0:=Int.emod_nonneg (nodeC o i) ((ruler_gene P.par.block).ne'); have he:=Int.emod_add_mul_ediv (nodeC o i) (ruler P.par.block)
   let r:=ruler P.par.block
   change 0 ≤ nodeC o i + -(r*(nodeC o i/r)) ∧ nodeC o i +-(r*(nodeC o i/r)) ≤r; unfold r; omega
 let Q:=P.certify 3 s (look 3) (fun i=>y i.val) (birthWP P o t)
 let ht:= P.identical_F 3 ξ s Q (birthWP P w (t.trans_eq h.symm)) (post_accel P s (look 3) y o)
 have hg: ζ (P.viewF 3 ξ s Q)= U (P.laysM (P.vtile s y)) (palmY P x s o t):=by
    exact truck_here P s ξ y _
 exact (congrArg (fun k:(P.ColorHil 3 ξ).space=> A₀ (ζ k)) ht.symm).trans ((congrArg (A₀) hg).trans (cartPaste P x _ _).symm)
-- end cheap
#print axioms shifted
end Aloft
end MiterT
end PledgeT
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
