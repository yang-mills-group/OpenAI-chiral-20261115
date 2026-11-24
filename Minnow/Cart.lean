import Minnow.Ripple
import MarchC.Shirts
import MarchC.Veneer
import MarchC.Item
import Acacia.Tan
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
open _root_.YM.Preen Cheer _root_.Acacia _root_.Yoland
variable (P:Spine)(x:P.Spectrum0 3)(J:P.Ellis 3 x)(F:ℕ)(C D:ℕ→ℕ→ℝ)(H:Rovers P F C D x)
local notation "ξ"=>P.otherSpectrum 3 3 x
local notation "S"=>P.seasons 3 ξ
local notation "K"=>P.ManyF 3 ξ
local notation "E"=>(P.seasons 3 ξ).E
local notation "U"=>P.cartage 3 ξ
local notation "Ω"=>P.heaven 3 ξ
local notation "A"=>paster (Ω)
local notation "b"=>tidal P F
local notation "m"=>poseMirror 3
variable (j:ℕ)(v:P.ManyF 3 (P.otherSpectrum 3 3 x))(g:Aloft.PeriodS P F C D x j v)
open Ballad Cordial
open Habitat.Hemlock.AuroraB Lamour.Bridge.Celeste Designs Twah Ballad Cordial Six
noncomputable def fingering(i ℓ:Lead.Clan)(t:Vantage):ℂ:= ored P x F C D t (score i+score ℓ)
noncomputable def noferal(t:Vantage)(i:Lead.Clan):K:= U (t-crest P F) (_root_.Yoland.pay (S) (score i) (t 3-b j) v)
/- the *true* point evaluation at qualified placements in ANY width chamber. Pure time derivatives score + score%
 Includes mean pasting, already zero there. -/
include H g J
lemma funding (a d:Vantage) (ha:b j< -a 3) (hd:b j< d 3)(hf:d-a∈mzone)(hj:F ≤ j)(i ℓ:Lead.Clan): inner ℂ (A (noferal P x F j v (m a) i)) (A (noferal P x F j v d ℓ)) = fingering P x F C D i ℓ (d-a):=by
 let s:=m a; let u:= b j; let t:= s 3-u; let r:= d 3-u
 have hx: -a 3 = (m a) 3:=(clock_neg _).symm
 have ht:0<t:=sub_pos.mpr (ha.trans_eq hx); have hr:0<r:=sub_pos.mpr hd
 let q:=d-a; let z:=d-s
 let vl:=noferal P x F j v s i; let vr:=noferal P x F j v d ℓ
 let F'(i:Lead.Clan)(t:ℝ):=( _root_.Yoland.pay (S) (score i) t)
 let N(i:Lead.Clan)(t:ℝ):K:=F' i t v
 let k:=crest P F
 have hE(i:Lead.Clan)(t:ℝ)(p:0<t)(y:Vantage):A (U y (N i t))=U y (N i t):= by
    let w:=N i t
    have he:A w=w:=Habitat.Hemlock.AuroraB.wall_z (S) (Ω) (P.stone_norm ..) (P.heaven_hot 3 ξ) (score i) v t p (scoring i).1
    exact (Aloft.cartPaste P x w y).symm.trans (congrArg (U y) he)
 have his:2*u < q 3:=by unfold q; change _ < d 3-a 3; change u < -a 3 at ha; change u < d 3 at hd; linarith only [ha,hd]
 have hs:U z=U q:=of_slideP x 3 _ _ (fun h p=>by change _-opposeR 3 a h=_-_; unfold opposeR mirrorΩ; rw [if_neg p])
 let D':ℝ:= q 3-(u+u)
 have he:r+t=D':=by unfold D' q r t; change _=d 3-a 3-(u+u); change -a 3=s 3 at hx; rw [←hx]; ring
 calc inner ℂ _ _ = inner ℂ vl vr:=congrArg₂ (inner ℂ) (hE i t ht (s-k)) (hE ℓ r hr (d-k))
      _=inner ℂ (N i t) (U z (N ℓ r)):= newel (X:=K) (U) (S) (fun a k z=>(DFunLike.congr_fun (P.cart_paves 3 ξ a k) z)) (fun a x y=>P.inner_pay ..) s d k _ _
      _=inner ℂ (N i t) (U q (N ℓ r)):=congrArg (inner ℂ (N i t)) (DFunLike.congr_fun hs _)
      _=inner ℂ v (U q (_root_.Yoland.pay (S) (score i+score ℓ) (r+t) v)):=calcPay (X:=K) (S) (U q) (fun t v=>(P.warm_drive 3 ξ q t v).symm) v t r ht hr (score i) (score ℓ)
      _=fingering P x F C D i ℓ q:= (congrArg (fun t:ℝ=>inner ℂ v (U q (_root_.Yoland.pay (S) (score i+score ℓ) t v))) he).trans (layered P x J F C D H q hf j hj v g his _).symm
where
 newel{X:Hilbert}(V:Vantage→X.Op)(S':OS.Semigroup X (3:Axis))(h:∀a k (i:X), V (a+k) i=V a (V k i))(p:∀a (i k:X),inner ℂ (V a i) (V a k)=inner ℂ i k)(s a k:Vantage)(i j:X):inner ℂ (V (s-k) i) (V (a-k) j)=inner ℂ i (V (a-s) j):=by rw [show a-k=s-k+(a-s) by abel,h,p]
 calcPay{X:Hilbert}(S':OS.Semigroup X (3:Axis))(V:X.Op)(h:∀k (i:X),V (S'.E k i)= S'.E k (V i))(v:X)(t r:ℝ)(ht:0<t)(hr:0<r)(i k:ℕ): inner ℂ (_root_.Yoland.pay S' i t v) (V (_root_.Yoland.pay S' k r v)) = inner ℂ v (V (_root_.Yoland.pay S' (i+k) (r+t) v)):=by rw [swing_pay S' i ht,← _root_.Yoland.turnΩ S' _ V h _ ht,← ContinuousLinearMap.comp_apply (_root_.Yoland.pay S' i t),earns_asset S' k i r t hr ht]
#print axioms funding
end Mido
end MiterT
end PledgeT
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
