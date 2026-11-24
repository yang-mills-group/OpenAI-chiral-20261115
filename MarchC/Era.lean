import MarchC.Porter
import MarchC.Parcel
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
variable (P:Spine)(x:P.Spectrum0 3)(J:P.Ellis 3 x)(F:ℕ)(C D:ℕ→ℕ→ℝ)
local notation "ξ" a:max=>P.otherSpectrum 3 a x
local notation "W" a:max=>P.ManyF a (ξ a)
local notation "U" a:max=>P.cartage a (ξ a)
local notation "E" a:max=> (P.seasons a (ξ a)).E
local notation "vM" j:max a:max b:max=> centreA P F j a b
local notation "κ" a:max=> valley P x a
noncomputable def incoming(j:ℕ)(a:Axis)(b:Bool):W a:= limUnder atTop (fun s=>headed P x F C D s j a b)
variable (H:Rovers P F C D x)
include H
lemma herald(j:ℕ)(a:Axis)(b:Bool)(h:F≤j): Tendsto (fun s=>headed P x F C D s j a b) atTop (𝓝 (incoming P x F C D j a b)):=by
 obtain ⟨y,Y⟩:=cauchySeq_tendsto_of_complete (show CauchySeq (fun s=>headed P x F C D s j a b) from H j h _ _ (tablet_paid ..) _)
 exact lm Y
where
 lm {Z:Hilbert}{f:ℕ→Z}{t:Z}(p:Tendsto f atTop (𝓝 t)): Tendsto f atTop (𝓝 (limUnder atTop f)):=by rw [p.limUnder_eq]; exact p
abbrev booth (j:ℕ)(a:Axis):ℝ:= (vM j a true) a+(vM j a false) a
abbrev yshift (j:ℕ)(a:Axis)(b:Bool):Vantage:= centreA P F j a b
local notation "cM"=>incoming P x F C D
variable (a:Axis)(j:ℕ)
variable{Y:ℕ→ Cover}{y:Vantage}
local notation "γ" s:max=>P.gridSpot s (Y s)-P.gridSpot s 0
include J
lemma limit_for (hY:Tendsto (fun s=>γ s) atTop (𝓝 y))(hp:F ≤j)(hy:∀i:Axis,0 < y i)(d:booth P F j a< y a):
 let v:=centreA P F j a true; let z:=centreA P F j a false
 Tendsto (fun s=>askM P x F C D s (Y s)) atTop (𝓝 ((κ a) (y a-booth P F j a) (y+v-z) (cM j a true) (cM j a false))):=by
 intro c z
 let p (b:Bool)(s:ℕ):=centreA P F s a b
 let f(s:ℕ):=c-p true s; let g(s:ℕ):=z-p false s
 have he(b:Bool):Tendsto (p b) atTop (𝓝 0):=tin_center P F a b
 have hf:Tendsto f atTop (𝓝 c):= show Tendsto _ atTop (𝓝 c) from sub_zero c ▸ (tendsto_const_nhds (x:=c)).sub (he true)
 have hg:Tendsto g atTop (𝓝 z):= show Tendsto _ atTop (𝓝 z) from sub_zero z ▸ (tendsto_const_nhds (x:=z)).sub (he false)
 let f'(s:ℕ):= f s a; let g'(s:ℕ):= g s a; let y'(s:ℕ):Vantage:= γ s
 have hfa:=tendsto_pi_nhds.mp hf a; have hga:=tendsto_pi_nhds.mp hg a
 have ht:Tendsto (fun s=> f' s+g' s) atTop (𝓝 (booth P F j a)):= hfa.add hga
 have hr:∀ᶠ s:ℕ in atTop,f' s+g' s < (γ s) a:=ht.eventually_lt (tendsto_pi_nhds.mp hY a) d
 let q(s:ℕ):= (y' s a)-(f' s+g' s)
 let i(s:ℕ):= y' s+ f s-g s
 have h := valley_lim P x a (u:=q) (d:=i) ((tendsto_pi_nhds.mp hY a).sub ht) ((hY.add hf).sub hg) (herald P x F C D H _ a true hp) (herald P x F C D H _ a false hp)
 apply h.congr'
 have wh:∀ i:Axis,∀ᶠ s:ℕ in atTop,(fitting P s (lever P F s a)).realWidth P i+(fitting P s (rider P F s)).realWidth P i < (γ s) i:=by
    intro i
    let w(b:Bool)(s:ℕ):ℝ:=(fitting P s (tablet P F s a b)).realWidth P i
    have hx:Tendsto (fun s=>w true s+w false s) atTop (𝓝 0):=by simpa only [add_zero] using (wharves P F a true i).add (wharves P F a false i)
    exact hx.eventually_lt (tendsto_pi_nhds.mp hY i) (hy i)
 filter_upwards [eventually_ge_atTop j, hr, hfa.eventually (le_mem_nhds (lease_pos P F j a true)), hga.eventually (le_mem_nhds (lease_pos P F j a false)), Filter.eventually_all.mpr wh] with s hs hu ha hb hw
 let v:= headed P x F C D s j a true; let w:= headed P x F C D s j a false
 let uA:=beckon P x F C D s a true; let uB:=beckon P x F C D s a false
 let R:= parcelM P x J F C D s a (Y s) hw
 change (κ a) (q s) (i s) v w = askM P x F C D s (Y s)
 exact Eq.trans ((show (κ a) (q s) (i s) v w= _ from congrArg₂ ((κ a) (q s) (i s)) (routeM P x F C D s j a hp hs true ha) (routeM P x F C D s j a hp hs false hb)).trans (valley_pre P x a ((γ s) a) (f' s) (g' s) ha hb hu uA uB (f s) (g s) (γ s)).symm) R.symm
-- choose common sequence Y. all-axis.F
omit H J
noncomputable def trued (P:Spine)(y:Vantage)(s:ℕ):Cover:=fun i=> ⌊y i / P.spotMesh s⌋
lemma truly (P:Spine)(y:Vantage): Tendsto (fun s:ℕ=>P.gridSpot s (trued P y s)-P.gridSpot s 0) atTop (𝓝 y):=by
 rw [tendsto_pi_nhds]; intro i
 let m:= P.spotMesh; let f(s:ℕ):=P.gridSpot s (trued P y s) i
 suffices h:Tendsto f atTop (𝓝 (y i)) by simpa only [f, Pi.sub_apply,P.gridSpot_mul,Pi.zero_apply,Int.cast_zero,zero_mul,sub_zero] using h
 refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (show Tendsto (fun s=>y i-m s) atTop (𝓝 (y i)) from (by simpa only [sub_zero] using (tendsto_const_nhds (x:=y i)).sub (tin_mesh P))) tendsto_const_nhds ?_ ?_
 · refine Eventually.of_forall fun s=> ?_; unfold f; rw [P.gridSpot_mul]; change _ ≤ (⌊y i/m s⌋:ℝ)*m s
   have he:= Int.lt_floor_add_one (y i/m s); have hv:= (div_lt_iff₀ (P.spotMesh_pos s)).mp he; linarith only [hv]
 exact Eventually.of_forall fun s=> (le_of_eq (P.gridSpot_mul s _ i)).trans ((le_div_iff₀ (P.spotMesh_pos s)).mp (Int.floor_le (y i/m s)))
#check le_mem_nhds
noncomputable def crownM(y:Vantage):ℂ:=limUnder atTop (fun s=>askM P x F C D s (trued P y s))
include H J
set_option maxHeartbeats 1050000 in
lemma axis_price (hp:F≤ j)(hy:∀i:Axis,0< y i)(d:booth P F j a<y a): crownM P x F C D y=(κ a) (y a-booth P F j a) (y+vM j a true-vM j a false) (cM j a true) (cM j a false):=((limhelper (show Tendsto (fun s=> askM P x F C D s (trued P y s)) atTop _ from limit_for P x J F C D H a j (truly P y) hp hy d)) )
where limhelper {f:ℕ→ℂ}{x:ℂ}(h:Tendsto f atTop (𝓝 x)):limUnder atTop f=x:=h.limUnder_eq
#print axioms axis_price
end Mido
end MiterT
end PledgeT
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
