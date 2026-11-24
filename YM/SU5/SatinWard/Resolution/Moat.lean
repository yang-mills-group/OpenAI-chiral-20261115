import YM.SU5.SatinWard.Resolution.Equine
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 700000
set_option maxRecDepth 3200
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase
open MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound
open Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker
open scoped ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy
open Tapestry Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open CF.Velvet CF.Pannier.Chancel
open Spine Pitching.Focus QuadClock Ione Vow Swell
open _root_.Zephyr.Chern
universe uΩ


open Papal CF.Papyrus.Franc.SatinForce CF.Pannier.Chancel Checkers

open CF.Papyrus.Franc.Loaves
-- CP3 package. PUBLIC, no topology/order changes
open Moon
open Horizons FoliageP BareProgram Moonlit Moonlit.SwitchC
open _root_.YM.Regis.Head.Brecht _root_.YM.Regis.Circuit _root_.YM.Regis.Circuit.SpringDay
open SlabMark VelourBoard Papal.SkyTax Cygnet VelourWiggle
open YM.Stationary (Gaia)
open SwitchC.Garland SwitchC.Garland.Terrace SwitchC.Garland.Terrace.Juniper
open Abacus CheckerFlag SlopeCharge Maxwell
open scoped RealInnerProductSpace ContDiff
namespace Fame
variable {P:Spine}{K:P.Register}{b C:ℝ}{t σ}{W:ℕ→ HorizonLens→ HorizonLens→ℝ}{β:ℕ→ℝ}
variable (T: CouncilGrant P K b C t σ W β)(H:PublicKernel P σ W)(F D: PlaqAxes)
open BProof Pressure
open _root_.YM.Gleam.Luster.Almanac Grade
open Papal.SkyTax
namespace Regulator
local notation "Ω" s:max=> hat P.par.R.L P.par.x s
open CasaF.Signboard CF.Tap SignSlot ShapeLab Emu
open LampD Quire LitCurrent AuroraX
namespace LampRead
attribute [local irreducible] bandWidthD
open Next.Rank Next.Rank.Spindle _root_.YM.Regis.Circuit.SpringDay.Spring
local notation "Λ"=> SpinIdx × SU.Slot
local notation "Q"=> Op SU.Slot
variable (k:ℕ) (Fκ:DozeTrack k)(fκ:hungerCap k Fκ)(X:Op Λ) (B:Q)(b:Axis) (d:Gaia)
noncomputable def focalB (b:Axis)(G:Q)(d:Gaia): Op Λ →L[ℂ] ℂ:=
                let V:Op Λ →ₗ[ℂ]ℂ:=
                 { toFun A:=∑ i:principalKid,∑ j:principalKid,A (upKid i.1) (dnKid i.2)*ordinaryW b G j * kindDU d i j
                   map_add' x y:=by simp only [Matrix.add_apply,add_mul,sum_add_distrib]
                   map_smul' x y:=by simp only [Matrix.smul_apply,smul_eq_mul,RingHom.id_apply,mul_assoc,mul_sum] }; V.toContinuousLinearMap
set_option backward.isDefEq.respectTransparency true in
lemma spendF (X:Op (SpinIdx×SU.Slot)): focalB b B d X = ∑ i:principalKid,∑ j:principalKid,X (upKid i.1) (dnKid i.2)*ordinaryW b B j*kindDU d i j:=by 
 rfl
-- norm ≤∥...∥ via .opacity
lemma strideE (d:Gaia)(G:Op SU.Slot)(i:Axis): focalB b B d (CF.Tap.petal i ⊗ₖ G)=bouquet i G b B d:=by rw [spendF]; unfold bouquet; refine sum_congr rfl fun i' _=> sum_congr rfl fun j' _=>?_; rfl
variable {R r:ℝ}{X' Y':Cover}
lemma cartonLo (i:landSheet k)(j:landSheet k): focalB b B d (carton k Fκ i j)=∑ u:principalKid,∑ v:principalKid,(Fκ.2 (concern ((i,j),u))*ordinaryW b B v*kindDU d u v):=by rw [spendF]; refine sum_congr rfl fun i' _=>sum_congr rfl fun j' _=>?_ ; rw [carton,Matrix.of_apply]
lemma orbitalμ : (∑ i:PollX k,∑ j:principalKid,Fκ.2 (concern i)*ordinaryW b B j * kindDU d i.2 j) = focalB b B d (songTotal k Fκ):=by unfold songTotal; simp_rw [map_sum,cartonLo]; rw [Fintype.sum_prod_type, Fintype.sum_prod_type (α₁:=landSheet k) (α₂:=landSheet k)]
include H
lemma ginseng: ∃ C:ℝ,0≤ C∧∀ (k:ℕ) (L:DozeTrack k)(v:hungerCap k L)(x:Cover), ‖billMono L x‖≤ C*dietTotal k L:=by
 choose A q h using fun i:juniorKid×seniorKid=> ensembleOne H i.1 i.2
 let D:= ∑ i,A i; have he:0 ≤ D:=sum_nonneg fun i _=> q i
 refine ⟨1+D,by positivity,fun k L v x=>?_⟩; unfold billMono; let P:=L.2; have hx(i:PollX k): ‖marketZero i x‖ ≤ D:= (h (i.2.2,i.2.1) _).trans (single_le_sum (fun i _=> q i) (mem_univ _)); have hg:‖∑ i:PollX k,P (concern i)*marketZero i x‖ ≤ (∑ i:PollX k,‖Comb L i‖)*D:=by
    rw [sum_mul]; exact (norm_sum_le ..).trans (sum_le_sum fun i _=> (norm_mul ..).trans_le (mul_le_mul_of_nonneg_left (hx i) (norm_nonneg _)))
 let b:= dietTotal k L; have H0:‖L.1‖ ≤ b:= le_add_of_nonneg_right (sum_nonneg fun i _=> norm_nonneg _)
 refine (norm_add_le ..).trans ((add_le_add H0 (hg.trans (mul_le_mul_of_nonneg_right (feeQuota L v) he))).trans_eq (by ring))
noncomputable abbrev lessonFee(b:Axis)(B: Q):= (∑ i:principalKid, ‖ordinaryW b B i‖)
lemma pensive (E:ℝ)(p:0≤E) :∃ D:ℝ,0≤ D∧∀ {R r:ℝ}{k:ℕ}{X Y:Cover}{d:Gaia}(L:DozeTrack k),hungerCap k L → SightEra R r k X Y d → dietTotal k L≤ E → Disp r D ((R:ℂ)^6* billDuet b B k L X Y) (focalB b B d (songTotal k L)):=by
 obtain ⟨c,v,H0⟩:= packed_cross H; let K:= lessonFee b B; let D:= (E*K)*c; have hh:0≤ K:=sum_nonneg fun _ _=>norm_nonneg _; refine ⟨D,mul_nonneg (by positivity) v,?_⟩; intro R r k X Y d L p1 q g; let Hc(i:PollX k)(j:principalKid):= L.2 (concern i)*ordinaryW b B j; let W:= ∑ i:PollX k,∑ j:principalKid, ‖Hc i j‖*c; have he:W≤D:=by
    unfold W Hc; simp_rw [norm_mul,mul_assoc,←mul_sum, ←sum_mul]; change _ ≤ (E*K)*c; apply le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ((feeQuota L p1).trans g) hh) v); unfold K lessonFee; ring
 rw [←orbitalμ k L]; unfold billDuet; simp_rw [mul_sum]; refine Disp.mono (?_: Disp r W _ _) he (by linarith only [q.limit]); apply Disp.SumD; intro i t; apply Disp.SumD; intro j t; rw [mul_left_comm]; exact Disp.increase (H0 i.2 j q i.1.1 i.1.2) _
variable {s:ℕ}{X Y:Cover} (E:ℝ)(p:0≤E)(k':ℕ)(u:Chamber.Division)
local notation "Zκ"=> sweepValue u b k'
local notation "l*"=> LanternLease P.run s k' u b
local notation "ǹ"=> P.thresholdF s
local notation "x*"=> polishQ P s
local notation "ζ"=> ((1/(x*)) :ℝ)
noncomputable abbrev cutSlice(u:Chamber.Division)(k':ℕ) :Op SU.Slot:= ((bmass k':ℂ)/(2*(k':ℂ))) • commission u
omit H in
lemma shineH :sweepValue u b k' = CF.Tap.petal b ⊗ₖ cutSlice u k':= (op_kron_smul ..).symm
-- arbitrary fixed d= any for which Sight tests occur (can permit constant depending d). Real.Test with chamber.C. Include only s of Waltz.Horti.
include p E
lemma satisfiesV :∃ V:ℝ,0≤V∧ ∀ s:ℕ,∀ (R:ℝ)(X Y:Cover)(L:BeamLeaf P.run s),SightEra R (polishQ P s) (P.thresholdF s) X Y d→ LanternLease P.run s k' u b L E→ Disp (polishQ P s) V ((R:ℂ)^6*billDuet b B (P.thresholdF s) L X Y) (bouquet b (cutSlice u k') b B d):=by
 obtain ⟨Z,v,w⟩:=pensive H B b E p; let T:= focalB b B d; let D:= Z+‖T‖+ ‖bouquet b (cutSlice u k') b B d‖; refine ⟨D,by unfold D; positivity,fun s r x y L u0 u₁=>?_⟩; let d0:= P.thresholdF s; let X0:= polishQ P s; let t₀:= w L u₁.crestWind u0 u₁.scaleBill; have v': songTotal d0 L=songTotal d0 L:=rfl; let M:= bouquet b (cutSlice u k') b B d; have ht:T Zκ=M:=by rw [shineH]; exact strideE ..
 have hz: 0<X0:= by unfold X0; linarith only [u0.limit]
 refine ⟨(by unfold D; positivity),(by unfold D; linarith only [v,norm_nonneg T]),?_⟩; unfold M at ht; rw [←ht]; refine (norm_sub_le_norm_sub_add_norm_sub _ (T (songTotal d0 L)) _).trans ((add_le_add t₀.amount (?_ : ‖T (songTotal d0 L) - T Zκ‖≤ ‖T‖ * (1/X0))).trans ?_)
 · rw [←map_sub]; refine (T.le_opNorm ..).trans (mul_le_mul_of_nonneg_left u₁.value (norm_nonneg _)) -- meta rhs?
 change Z/X0 + ‖T‖ * (1/X0) ≤ D/X0; unfold D; rw [add_div,add_div,mul_one_div]; exact le_add_of_nonneg_right (by positivity)
#print axioms satisfiesV
end LampRead
end Regulator
end Fame
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
