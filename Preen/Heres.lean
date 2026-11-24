import Preen.Fitted
import Preen.Reduce
import Preen.Buckle
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
set_option maxHeartbeats 170000
open Aria Casting Set
open scoped Pointwise
namespace MiterT
open _root_.YM.Preen
variable (P:Spine)(x:P.Spectrum0 3)(s:ℕ)
local notation "ξ"=>P.otherSpectrum 3 3 x
local notation "Ω"=>P.heaven 3 ξ
local notation "ω"=>P.colorZero 3 ξ
local notation "ζ"=>P.wealth 3 ξ
local notation "ϕ"=>paster (Ω)
local notation "H"=>P.ColorHil 3 ξ
local notation "W"=>P.ManyF 3 ξ
variable(o:Cover)(h:(P.calibration.ℓ:ℤ)+22≤nodeC o (3:Axis))
local notation "E"=>P.singleState 3 s x
local notation "Y"=>palmY P x s o h
local notation "T"=>P.chartAll
lemma refresh_cost :(E (wp P s o)) = inner ℂ (Ω) (palmY P x s o h):=by
 let u:=P.viewF 3 ξ s (birthWP P o h); have hN:inner ℂ (Ω) (ζ u)=inner ℂ (ω) u:=by let v:= (decarded P (ξ) u (Ω)); exact rebar (H) (W) (ω) (Ω) u (ζ u) v -- inner reverse. use hermitian.
 exact (P.single_agrees 3 3 x _ _).symm.trans ((P.view_scalar 3 ξ s (birthWP P o h)).symm.trans hN.symm)
where rebar (X Y':Hilbert)(a:X)(b:Y')(c:X)(d:Y')(h:inner ℂ d b=inner ℂ c a) : inner ℂ b d=inner ℂ a c:=by rw [← inner_conj_symm (𝕜:=ℂ) b d, ← inner_conj_symm (𝕜:=ℂ) a c,h]
def expenseR(d f:Cover):ℂ:= E (T d (P.reflectTest 3 (wp P s o))* T f (wp P s o)) - star (E (wp P s o))*E (wp P s o)
local notation "Τ"=> P.cartage 3 ξ
local notation "Ψ"=>P.seasons 3 ξ
private lemma normV_all {X:Hilbert}{i:Axis}(S:OS.Semigroup X i)(a:ℝ≥0)(x:X):‖S.E a x‖≤‖x‖:= ((S.E a).le_opNorm x).trans (mul_le_of_le_one_left (norm_nonneg _) (S.shrinks a))
private lemma outlier {X:Hilbert}(k:X)(hk:‖k‖=1)(Yx Z:X.Op)(yh:∀y:X,‖Yx y‖≤‖y‖)(zh:∀y:X,‖Z y‖≤‖y‖)(yk:Yx k=k)(zk:Z k=k)(hy:∀ y:X,inner ℂ k (Yx y)=inner ℂ k y)(hz:∀y:X,inner ℂ k (Z y)=inner ℂ k y)(y:X): ‖inner ℂ (Yx y) (Z y)- star (inner ℂ k y)*inner ℂ k y‖≤ ‖paster k y‖^2:=by
 let L:=paster k; have he:inner ℂ (Yx (L y)) (Z (L y))=inner ℂ (Yx y) (Z y)- star (inner ℂ k y)*inner ℂ k y:=by
    have h1:Yx (L y)=L (Yx y):=by unfold L; rw [pasted _ hk, pasted _ hk,map_sub,map_smul,yk,hy]
    have h2:Z (L y)=L (Z y):=by unfold L; rw [pasted _ hk, pasted _ hk,map_sub,map_smul,zk,hz]
    rw [h1,h2,together _ hk,hy,hz]
 rw [←he,pow_two]; exact (norm_inner_le_norm _ _).trans (mul_le_mul (yh _) (zh _) (norm_nonneg _) (norm_nonneg _))
private lemma horizon_α(y:W)(r:Vantage)(t u:ℝ≥0):let U:=Ψ; let Wt:=Τ; let d:=U.E u y
 ‖inner ℂ d (U.E t (Wt r d))-star (inner ℂ (Ω) y)*inner ℂ (Ω) y‖ ≤ ‖ϕ y‖^2:=by
 intro S U d; let Q:=S.E u; let Z:=(S.E t).comp ((U r).comp Q)
 have hL(a:ℝ≥0)(z:W): inner ℂ (Ω) ((Ψ).E a z)= inner ℂ (Ω) z:= (OS.Semigroup.swing (Ψ) a (Ω) z).symm.trans (congrArg (fun c : W=> inner ℂ c z) (P.heaven_hot 3 ξ a))
 have h':∀d:W,inner ℂ (Ω) (U r d)=inner ℂ (Ω) d:=fun d=>(congrArg (fun c=>inner ℂ c (U r d)) (P.cart_empty 3 ξ r)).symm.trans (P.inner_pay 3 ξ r _ _)
 exact outlier (Ω) (P.stone_norm 3 ξ) Q Z (normV_all S u) (fun z=> (normV_all S t _).trans ((P.cart_norm 3 ξ r _).le.trans (normV_all S u z))) (P.heaven_hot 3 ξ u) (joinZ (W) (Ω) (S.E t) (U r) Q (P.heaven_hot ..) (P.cart_empty ..) (P.heaven_hot ..)) (hL _) (fun a:W=> (hL t _).trans ((h' _).trans (hL u a))) y
where joinZ (R:Hilbert)(x:R)(f g h:R.Op)(a:f x=x)(b:g x=x)(d:h x=x): f (g (h x))=x:=by rw [d,b,a]
variable {d f:Cover}
lemma expense_price(J:P.Ellis 3 x)(t:∀ i:Axis, ↑(beamU P o i)+(↑(beamU P o i):ℤ) < f i-d i): ‖expenseR P x s o d f‖ ≤ driftCost P (ξ) s o h ^ 2:=by
 let N:= fitting P s o; let r:=P.gridSpot s f-P.gridSpot s d; let τ:= (r 3-(N.realWidth P 3+N.realWidth P 3)).toNNReal
 let b:=heatU P s o; let u:= (Ψ).E b (palmY P x s o h); let a:= P.singleState 3 s x
 let i:=wp P s o
 have H': a ((P.chartAll d (P.reflectTest 3 i))*(P.chartAll f i))=inner ℂ u ((Ψ).E τ (Τ r u)):=portal_price P x s o h J t -- kiss def
 have ht:=fuseJ H' (refresh_cost P x s o h) (horizon_α P x (palmY P x s o h) r τ b)
 exact ht
where fuseJ {a b c d:ℂ}{v:ℝ}(h:a=b)(k:c=d)(t:‖b-star d*d‖≤v): ‖a-star c*c‖≤v:=by rwa [h,k]
#print axioms expense_price
end MiterT
end PledgeT
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
