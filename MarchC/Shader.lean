import MarchC.Admission
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
open Calico Cheer
variable (P:Spine)(x:P.Spectrum0 3)(J:P.Ellis 3 x)
local notation "ξ" a:max => P.otherSpectrum 3 a x
local notation "W" a:max=>P.ManyF a (ξ a)
local notation "U" a:max=>P.cartage a (ξ a)
local notation "E" a:max=> (P.seasons a (ξ a)).E
local notation "σ" s:max=>P.gridSpot s
local notation "μ" a:max s:max p:max=>P.wealth a (ξ a) (P.viewF a (ξ a) s p)
private lemma day_mix {H:Hilbert}{j:Axis}(S:OS.Semigroup H j)(a b:ℝ≥0)(u:ℝ)(h:(a:ℝ)+(b:ℝ)<u)(X:H.Op)(hu:∀ i (v:H),S.E i (X v)=X (S.E i v))(v w:H): inner ℂ ((S.E a) v) ((S.E ((u - ((a:ℝ)+(b:ℝ))).toNNReal)) (X ((S.E b) w))) = inner ℂ v (X ((S.E u.toNNReal) w)):=by
 have he:a+((u-((a:ℝ)+(b:ℝ))).toNNReal+b)=u.toNNReal:=by ext; rw [NNReal.coe_add,NNReal.coe_add,Real.coe_toNNReal _ (sub_pos.mpr h).le,Real.coe_toNNReal _ (add_nonneg a.prop b.prop|>.trans h.le)]; linarith only
 rw [S.swing,hu _ ((S.E b) w),hu,← ContinuousLinearMap.comp_apply (S.E (u-((a:ℝ)+(b:ℝ))).toNNReal) (S.E b),← S.time,← ContinuousLinearMap.comp_apply (S.E a),← S.time,he]
lemma shadew(a:Axis)(s:ℕ)(o:Cover)(p:(P.calibration.ℓ:ℤ)+22 ≤ nodeC o a):
 flashY x (fitting P s o) a= (E a) (whenly (timeMesh P.par) s (beamU P o a)) (μ a s (bornP P a s o p)) :=by
 let g:=P.passesLater a s (beamU P o a) (bornP P a s o p)
 have hz:= Eq.trans (P.engine_view a (ξ a) (fitting P s o)) ((P.identical_F a (ξ a) s _ g ((fitting P s o).card_price P a)).trans (P.releasedLater a (ξ a) s _ (bornP P a s o p)))
 exact (congrArg (P.wealth a _) hz).trans (P.bankHeat ..)
include J
lemma portal_user(a:Axis)(s:ℕ)(o w:Cover)(h:(P.calibration.ℓ:ℤ)+22 ≤ nodeC o a)(k:(P.calibration.ℓ:ℤ)+22 ≤ nodeC w a)(p z:Vantage)(q:(fitting P s o).realWidth P a + (fitting P s w).realWidth P a < (z-p) a):
 let y:=z-p
 P.bodyPair x ((fitting P s o).kiss P a) (fitting P s w) p z= inner ℂ (μ a s (bornP P a s o h)) ((U a) y ((E a) (y a).toNNReal (μ a s (bornP P a s w k)))):=by
 intro y; let M:=fitting P s o; let N:=fitting P s w
 let S:=P.seasons a (ξ a)
 let R:=M.kiss P a
 let g(u:ℝ)(v g:W a):=inner ℂ v (S.E ((y a-u).toNNReal) ((U a) y g))
 let b:=whenly (timeMesh P.par) s (beamU P o a); let v:=whenly (timeMesh P.par) s (beamU P w a)
 have he:(b:ℝ)+(v:ℝ)=R.realWidth P a+N.realWidth P a:=congrArg₂ (·+·) (natural_time ..).symm (natural_time ..).symm
 exact (P.bodyPair_fwd x R N a p z J q).trans ((congrArg (fun t:ℝ=>g t (glareY x R a) (flashY x N a)) he.symm).trans ((congrArg₂ (g ((b:ℝ)+(v:ℝ))) ((flashY_glare x M a).trans (shadew P x a s o h)) (shadew P x a s w k)).trans (day_mix S b v (y a) (he.trans_lt q) ((U a) y) (P.warm_drive a (ξ a) _) _ _)))
variable{f d:Cover}
lemma port_adv(s:ℕ)(L B:P.Apron)(t:L.s=s)(u:B.s=s)
 (Q:∀i,L.realWidth P i+B.realWidth P i<(((σ s) f)-((σ s) d)) i): P.singleState 3 s x ((P.chartAll d L.F)*(P.chartAll f B.F))=P.bodyPair x L B ((σ s) d) ((σ s) f):=by
 let N:=usher L B; let t':= P.gridSpot s ∘ usher d f
 have he(i:Axis):P.Turnstile i N [false,true] t':=by apply List.pairwise_pair.mpr; change P.gridSpot s d i+L.realWidth P i<P.gridSpot s f i-B.realWidth P i; have hh:=Q i; rw [Pi.sub_apply] at hh; linarith only [hh]
 have hf(D:P.Apron)(v:D.s=s):D.full P s=D.F:=by unfold Apron.full; rw [←v,Nat.sub_self]; rfl
 have ht:P.fullScroll s N (usher d f) [false,true]=(P.chartAll d L.F)*(P.chartAll f B.F):=by change P.chartAll d (L.full P s)*(P.chartAll f (B.full P s)*1)=_; rw [mul_one,hf _ t,hf _ u]
 have h':∀ i∈[false,true], (N i).s ≤ s:=by rintro (_|_) _; exact t.le; exact u.le
 exact (congrArg (P.singleState 3 s x) ht.symm).trans ((P.spot_full x N _ _ J s h' (he _) ⟨fun i=>⟨_,List.Perm.refl _,he i⟩⟩).trans (congrArg (fun z:Bool→Vantage=> P.commonWell 3 x N z [false,true]) (show (P.gridSpot s ∘ usher d f)=usher (P.gridSpot s d) (P.gridSpot s f) from (by funext i; cases i<;> rfl))))
#print axioms portal_user -- forgot include J above
#print axioms port_adv
end Mido
end MiterT
end PledgeT
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
