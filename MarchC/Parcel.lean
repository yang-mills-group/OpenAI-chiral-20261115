import MarchC.Conga
import MarchC.Airport
import MarchC.Shader
import Crape.Creature
import Preen.Fitted
import SatinLocalChron
import Preen.Travel
import GlazeS.Incline
import GlazeS.Room
import SatinFacet
import Crape.Halo
import Crape.Adjust
import Crape.Supple
import Crape.TimeLine
import Nankin.Bern
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 220000
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
set_option maxRecDepth 6000
set_option maxHeartbeats 700000
open Aria Casting Set
open scoped Pointwise
namespace MiterT
namespace Mido
open Calico
variable (P:Spine)(x:P.Spectrum0 3)(J:P.Ellis 3 x)(F:ℕ)(C D:ℕ→ℕ→ℝ)(s j:ℕ)(a:Axis)
local notation "ξ"=>P.otherSpectrum 3 a x
local notation "μ" s:max p:max=>P.wealth a (P.otherSpectrum 3 a x) (P.viewF a (P.otherSpectrum 3 a x) s p)
local notation "U"=>P.cartage a (P.otherSpectrum 3 a x)
local notation "E"=>(P.seasons a (P.otherSpectrum 3 a x)).E
local notation "W" => P.ManyF a (P.otherSpectrum 3 a x)
noncomputable def beckon(b:Bool):W:=
 (((basket P.par.R.L C D F s:ℝ):ℂ) • μ s (bornP P a s (tablet P F s a b) (tablet_born P F s a b)))
noncomputable def headed(b:Bool):W:= tether P F C D j s (tablet P F j a b) a (ξ) (tablet_born P F j a b)
lemma routeM (h:F ≤ j)(q:j ≤ s)(b:Bool)(v:0 ≤ (centreA P F j a b - centreA P F s a b) a) :
 let y:=centreA P F j a b - centreA P F s a b
 headed P x F C D s j a b=U y (E (y a).toNNReal (beckon P x F C D s a b)):=by
 intro y; let r:=indi P F s j a b
 have hv:P.gridSpot s r=y:=leaseC P F s j h q _ _
 let o:= tablet P F s a b; let z:= orbitB P.par.R.L (tablet P F j a b) (s-j); have hz:metro P r o=z:=(stands P F s j h q b a).symm
 have hp₀:(P.calibration.ℓ:ℤ)+22 ≤ nodeC (tablet P F j a b) a:= tablet_born ..
 have hp:(P.calibration.ℓ:ℤ)+22 ≤ nodeC z a:=by
    unfold z; rw [dutyT _ _ P.par.R.odd_side]; simp only [Pi.smul_apply,nsmul_eq_mul]; apply hp₀.trans; apply le_mul_of_one_le_left (by omega); exact_mod_cast (show 1 ≤ P.par.R.L.val^(s-j) from Nat.one_le_of_lt (pow_pos P.par.R.L.property _))
 let p':=bornP P a s z hp
 have hl:(↑((r a).toNat):ℤ)=(r a):=Int.toNat_of_nonneg (by
    have hx:(r a:ℝ)*P.spotMesh s ≥0:= ((show 0 ≤ y a from v).trans_eq (congrFun hv a).symm).trans_eq (P.gridSpot_mul s r a)
    have hy:0 ≤ (↑(r a):ℝ):=nonneg_of_mul_nonneg_left hx (P.spotMesh_pos _)
    exact_mod_cast hy)
 let i:= ((basket P.par.R.L C D F s:ℝ):ℂ)
 have H:= travelS P a s o z r (r a).toNat hl hz ξ (tablet_born P F s a b) hp
 -- use congrArg transit instead of rw travelS
 let v1:=P.viewF a (ξ) s (bornP P a s o (tablet_born P F s a b)); let s1:= P.wealth a ξ v1
 let u1:W:=μ s p'
 have he:u1=(U y) (E (y a).toNNReal s1):= by
    exact H.trans (congrArg (fun z:Vantage=> U z (E (z a).toNNReal s1)) hv)
 exact (map_smul (P.wealth a ξ) i (P.viewF a ξ s (rooty P a s j (tablet P F j a b) hp₀))).trans ((congrArg (fun x:W=> i • x) he).trans ((map_smul (U y ∘L E (y a).toNNReal) i s1).symm))
noncomputable def askM(y:Cover):ℂ:= (basket P.par.R.L C D F s:ℂ)^2* P.singleState 3 s x ( P.chartAll 0 (wp P s (saddle P F s)) * P.chartAll y (wp P s (rider P F s)))
include J
set_option maxHeartbeats 1200000 in
lemma parcelM(y:Cover)(hy:∀i:Axis, (fitting P s (lever P F s a)).realWidth P i+(fitting P s (rider P F s)).realWidth P i < (P.gridSpot s y-P.gridSpot s 0) i): askM P x F C D s y=
 inner ℂ (beckon P x F C D s a true) (U (P.gridSpot s y-P.gridSpot s 0) (E ((P.gridSpot s y-P.gridSpot s 0) a).toNNReal (beckon P x F C D s a false))):=by
 let o:=lever P F s a
 let L:=fitting P s o; let N:= fitting P s (rider P F s); let B:= L.kiss P a; let v:=P.gridSpot s y-P.gridSpot s 0; let n:= ((basket P.par.R.L C D F s:ℝ):ℂ)
 have h := port_adv P x J (f:=y) (d:=0) s B N rfl rfl hy
 have hp:(P.calibration.ℓ:ℤ)+22 ≤ nodeC o a:= tablet_born P F s a true
 let u:=P.gridSpot s 0
 have hr:=portal_user P x J a s o (rider P F s) hp (show (P.calibration.ℓ:ℤ)+22 ≤ nodeC (rider P F s) a from tablet_born P F s a false) u (P.gridSpot s y) (hy a)
 have hx:(wp P s (saddle P F s))=B.F:=by change _ = P.reflectTest a (wp P s o); rw [wp_zap]; unfold o lever; rw [twice_zap]
 let Q:= (U v) ∘L (E (v a).toNNReal); let g:=μ s (bornP P a s o hp); let w:=rider P F s; let k:=μ s (bornP P a s w (tablet_born P F s a false)); let p(t:P.Test):=(P.singleState 3 s x) ((P.chartAll 0) t*(P.chartAll y) (wp P s w)); change n^2 * p (wp P s (saddle P F s))= inner ℂ (n • g) (Q (n • k))
 exact (congrArg (fun c:ℂ=> n^2*c) ((congrArg p hx).trans (h.trans hr))).trans (powers (X:=(W)) Q ..)
where powers{X:Hilbert}(B:X.Op)(i:ℝ)(p w:X): (i:ℂ)^2 * inner ℂ p (B w)= inner ℂ ((i:ℂ) • p) (B ((i:ℂ) • w)):=by rw [map_smul,inner_smul_left,inner_smul_right,Complex.conj_ofReal]; ring
#print axioms routeM
#print axioms parcelM
end Mido
end MiterT
end PledgeT
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
