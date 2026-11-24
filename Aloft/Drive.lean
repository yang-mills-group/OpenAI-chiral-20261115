import Aloft.ZL
import Aloft.SailG
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
variable (x:P.Spectrum0 3)
local notation "ξ"=>P.otherSpectrum 3 3 x
local notation "Ω"=>P.heaven 3 ξ
local notation "Ψ"=> P.seasons 3 ξ
local notation "H"=>P.ManyF 3 ξ
local notation "ζ"=>P.wealth 3 ξ
local notation "A₀"=>paster (Ω)
local notation "U"=>P.cartage 3 ξ
variable (o:Cover)
-- norm identities
lemma coaddress {R:Hilbert}(S:OS.Semigroup R (3:Axis))(U':R.Op)(t:ℝ≥0)(h:ℝ≥0)(k:R)(a:‖k‖=1)(w:∀ t,S.E t k=k)(u:U' k=k)(v:∀i:R,inner ℂ k (U' i)=inner ℂ k i)(q:∀z:R,S.E h (U' z)=U' (S.E h z))(y:R):
 inner ℂ (S.E h y) (S.E t (U' (S.E h y)))-star (inner ℂ k y)*inner ℂ k y= inner ℂ (paster k y) (S.E (h+(t+h)) (U' (paster k y))):=by
 let H':= S.E; let c:=inner ℂ k y; let z:= U' y; let f(r):=H' r z
 have h₀(t:ℝ≥0)(x:R): inner ℂ k (S.E t x)=inner ℂ k x:= (OS.Semigroup.swing S t k x).symm.trans (congrArg (fun c : R=> inner ℂ c x) (w t))
 rw [OS.Semigroup.swing,← q]
 -- E h (E t (E h..)). want paster both sides inside. use together
 have he : S.E h (S.E t (S.E h (U' y)))=S.E (h+(t+h)) z:=by unfold z; rw [S.time h _,S.time t h]; rfl
 rw [he,show S.E (h+(t+h)) (U' (paster k y))=paster k (S.E (h+(t+h)) z) from ?_, together _ a, h₀, v]
 rw [pasted _ a,pasted _ a,map_sub,map_smul,map_sub,map_smul,h₀,v,u,w]
-- shift opacity.All. use exact time budget arrival collapse total time = rGrid, avoids need heatU.Small.
variable (J:P.Ellis 3 x)(d m:ℕ)(q:Enrolled P d (stairW d) o)(g:1 ≤ m)
abbrev spotL(d m:ℕ):Vantage:= P.gridSpot (stackW d) (bootH P m d)-P.gridSpot (stackW d) 0
local notation "rP" => spotL P d m
abbrev nhot(d m:ℕ) (w:Cover):ℝ≥0:= let s:=stackW d; let b:=heatU P s w; b + (((spotL P d m) 3 -( (fitting P s w).realWidth P 3 + (fitting P s w).realWidth P 3)).toNNReal +b)
noncomputable abbrev terrain(d m:ℕ)(w:Cover) : (H).Op:= ((Ψ).E (nhot P d m w)).comp (U (spotL P d m))
include J q g
lemma portal_next(p:H)(h:p= A₀ (palmY P x (stackW d) o q.clock.1)):
 gem P d m x o=inner ℂ p (terrain P x d m o p):=by
 have hb(i:Axis): spindle P d (stairW d) i ≤ bootH P m d i:=by
    unfold bootH; split_ifs with he
    · subst i; exact le_mul_of_one_le_left (spin_k (P:=P) _).1 (by exact_mod_cast g)
    rfl
 let s:=stackW d; let η:= (rP) 3; let K:= (fitting P s o).realWidth P 3; let a:= (η-(K+K)).toNNReal; let S:= Ψ
 let z:=heatU P s o
 let t0:= U (rP)
 let R0:=palmY P x s o q.clock.1
 have u₁:=portal_price P x s o q.clock.1 J (d:=0) (f:=bootH P m d) (fun i=> (ribbon_ms P q i).trans_le (sub_le_sub_right (hb i) _))
 have u₂:= refresh_cost P x s o q.clock.1
 have uv(u:H):inner ℂ (Ω) (t0 u)=inner ℂ (Ω) u:=((congrArg (fun c=>inner ℂ c (U (rP) u)) (P.cart_empty 3 ξ (rP))).symm.trans (P.inner_pay 3 ξ (rP) _ _)) -- check
 rw [h]
 exact gunn (R:=(H)) (Ω) (S) t0 z a R0 u₁ u₂ (coaddress S t0 a z (Ω) (P.stone_norm ..) (P.heaven_hot 3 ξ) (P.cart_empty ..) uv (P.warm_drive 3 ξ (rP) z) R0)
where gunn {R:Hilbert}(k:R)(S:OS.Semigroup R (3:Axis))(U':R.Op)(b u:ℝ≥0)(y:R){x z:ℂ}(h:x=inner ℂ (S.E b y) (S.E u (U' (S.E b y))))(g:z=inner ℂ k y)(e:inner ℂ (S.E b y) (S.E u (U' (S.E b y)))-star (inner ℂ k y)*inner ℂ k y= inner ℂ (paster k y) (S.E (b+(u+b)) (U' (paster k y)))):x-star z*z=inner ℂ (paster k y) (S.E (b+(u+b)) (U' (paster k y))):=(by rwa [h,g])
#print axioms coaddress
#print axioms portal_next
end Aloft
end MiterT
end PledgeT
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
