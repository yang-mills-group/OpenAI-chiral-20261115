import Preen.StagePiece
import Preen.Weights
import Risa.Engage
import Preen.Spurt
import Risa.SeedBox
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
open _root_.YM.Gleam.Luster.Risa CF.BProof AnalyticBridge.VerifiedReset
open Py.Rate.LocalLimit Py Py.Dyad Papal _root_.YM.CF.Pannier.Chancel Cliplet
variable (P:Spine)(s w:ℕ)(o:Bool→ Cover)(n₀:Bool)(z:ℝ)(A:ℕ)
local notation "K"=>P.calibration
local notation "V"=>P.run.meter.a s
local notation "Yx"=> hat P.par.R.L P.par.x s
local notation "θ"=>scaleY (Yx)
local notation "σ"=>sock A (Yx)
local notation "I"=>Fin (cardD P A s)
local notation "Δ" i:max=> flightY P w (i:ℕ)
local notation "η" i:max b:max=> cabinY P (o b) w (i:I).val
local notation "S₀"=>spots P s w o A
local notation "T₀"=>trialY P s w o n₀ z A
local notation "g"=>slip P s w A
local notation "Nc" i:max=> count P.run s i
private lemma late_dist (T:Finset Cover):∀ᶠ m:ℕ in atTop,Set.InjOn (wrap (More (Nc m))) T :=by
 have hp:∀ x:Cover,∀ i:Axis,∀ᶠ m:ℕ in atTop, - ((More (Nc m)).val:ℤ) <2*x i ∧2*x i ≤(More (Nc m)).val:=by
    intro x i; filter_upwards [(count_grows P.run s).eventually_ge_atTop ((x i).natAbs+1)] with m h; change _≤ (Nc m).val at h; rw [show (More (Nc m)).val=(Nc m).val*2 from rfl]; omega
 have he:= (T.eventually_all).2 (fun x _=> eventually_all.mpr (hp x))
 filter_upwards [he] with m he i t j u e; have ht(x)(p:x∈T):Lattice.lift (wrap (More (Nc m)) x)=x:=lift_eq_iff.mpr ⟨rfl,he x p⟩; rw [←ht i t,←ht j u,e]
lemma coords_e :∀ᶠ i:ℕ in atTop,∀b:Bool,Injective fun j=> anchors P s w o A (Nc i) j b:=by
 filter_upwards [late_dist P s (S₀)] with i h b j k t; have he:= h (townT P s w o A b j) (townT P s w o A b k) t; have hz:=congrFun he 3; rw [ticking P w o 3 3,ticking P w o 3 3,if_pos rfl,if_pos rfl,add_right_inj] at hz; have hp:(pollN P:ℤ)≠0:= (show 0<(pollN P:ℤ) from ruler_gene _).ne'; apply Fin.ext; replace hz:= mul_left_cancel₀ hp hz; exact Nat.add_left_cancel (Int.ofNat.inj hz)
lemma platterE(i:ℕ)(p:0<P.payday s)(h:∀ b:Bool,Injective fun j=> anchors P s w o A (Nc i) j b) :∃ F:Papal.boyQ P.run A s i z n₀ (pedestal o (Nc i)) (fun _=>1), F.S=Satin.region (S₀) (Nc i) ∧ distribute P.run P.large s i (T₀).val = Papal.Sway F :=by
 let S:= Satin.region (S₀) (Nc i)
 have hc:AtSupport false S (distribute P.run P.large s i (T₀).val):=stationed P.run P.large s _ _ ((Tapestry.locates ..).1 (zoned P s w o n₀ z A)) -- signature
 rw [lit_port P s w o n₀ z A i p] at hc
 let f:Papal.boyQ P.run A s i z n₀ (pedestal o (Nc i)) (fun _=>1):=⟨S,anchors P s w o A _,fun _ _=>1,arrive_r P s w o A _,(fun i b=>tray_tag P s w o A _ b i),h,hc⟩
 exact ⟨f,rfl,lit_port P s w o n₀ z A i p⟩
variable (p:withinT o w)
include p
lemma walls_cost(i:ℕ): ∀ j:Axis, cows j (hyphen 3 0 (Satin.region (S₀) (Nc i)) ∪ Satin.region (S₀) (Nc i)) (2*g):=by
 intro j; let n:=Nc i; have hr:=higherZ P s w o A p
 refine ⟨-(g:ℤ), fun x e=>?_⟩
 rcases Finset.mem_union.mp e with h|h; swap; · obtain ⟨t,p,rfl⟩:=Finset.mem_image.mp h; obtain ⟨a,b⟩:=hr.2 t p j; exact ⟨t j,a,(by omega),rfl⟩
 obtain ⟨y,t,rfl⟩:=Finset.mem_image.mp h; obtain ⟨u,pP,rfl⟩:=Finset.mem_image.mp t; let A':=(plane (3:Axis) 0)
 rw [Shape.anno]; refine ⟨A'.motion u j,?_,?_,rfl⟩ <;> all_goals (
   have he:=hr.2 u pP j
   unfold A'
   rw [fling_move]
   split <;> omega)
lemma locale_dist :∀ᶠ i:ℕ in atTop, Disjoint (hyphen 3 0 (Satin.region (S₀) (Nc i))) (Satin.region (S₀) (Nc i)):=by
 filter_upwards [(count_grows P.run s).eventually_ge_atTop (g+(K).ℓ)] with i h
 refine _root_.YM.CF.Pannier.Chancel.west (K) 3 0 _ ?_ -- inspect
 have hr:=higherZ P s w o A p
 intro k ht
 obtain ⟨x,b,rfl⟩:=Finset.mem_image.mp ht
 apply (band_spec ..).mpr
 let v:= x 3; let n:=Nc i
 have hu:0+(K).ℓ≤ v:=hr.1 x b -- type Tower.region
 obtain ⟨-,hh⟩:=hr.2 x b 3; change _≤ n.val at h
 change ((K).ℓ≤ ((↑(x 3):Per (More n))- ↑(0:ℤ)).val) ∧ _+ (K).ℓ ≤ n.val
 have hr:0 ≤ v:=by omega
 have hv:v.toNat<(More n).val:=by change _<n.val*2; have hp:n.val>0:=n.property; change v ≤ _ at hh; omega
 rw [Int.cast_zero,sub_zero,show (↑(x 3):Per (More n))=(v.toNat:Per (More n)) from (by rw [← Int.cast_natCast,Int.toNat_of_nonneg hr]), ZMod.val_natCast_of_lt hv]; change _ ∧ ((wrap (More n) x) 3- (0:Per (More n))).val+ _≤ _; change _ ∧ (((x 3:ℤ):Per (More n))-0).val+_≤ _
 rw [sub_zero, show (↑(x 3):Per (More n))=(v.toNat:Per (More n)) from (by rw [← Int.cast_natCast,Int.toNat_of_nonneg hr]), ZMod.val_natCast_of_lt hv]; unfold v at *; omega
#print axioms locale_dist
end MiterT
end PledgeT
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
