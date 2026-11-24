import YM.SatinExist.Cameo
import YM.SatinExist.Hall
import YM.SatinExist.Fence
import SatinThinRampart
import SatinThinAngle
import YM.SatinExist.Glacis
import SatinThinSegno

set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry

open TopologicalSpace
namespace Spine
open Lamour.Bridge.Celeste
open Lamour.Bridge.Celeste.Morn
open Py.Rate.LocalLimit.Papal (Weaver household)
open TopologicalSpace Tapestry.Exhibition
variable (P:Spine)(R : P.Register)(j:Axis)
local notation "φ"=> P.groundZero j
local notation "μ"=> P.pillars j
local notation "W"=> P.calibration
local notation "Q"=> P.par.block
local notation "ℓ"=> P.calibration.ℓ
open Papal Regis.Head Gleam
/-! # Price of ensemble-of-trips. Exactly composed on printed test level before estimation. -/
open Clock Clock.Hookah Clock.Hookah.Blaze
open Preparation.Yoke Yoke.Travel Regis.Head.Garland
open QuadClock Again Pressure
variable {s t f r v i k:ℕ}
local notation "Y"=> P.run
local notation "Λ"=> P.par
local notation "L"=> P.par.R.L
local notation "H"=>P.large
/-! # Train cost comparison on elected printed heights. -/
-- support of tested pair. Need dSpacing condition eventually at roots. Using real checkpoint geometry. Only prices here. 
variable (X:Cover){C e A:ℝ}
open CF.Pannier.Chancel CF.Py.Rate.LocalLimit.Preparation.Yoke
local notation "aK"=>P.nomadic
local notation "bK"=>P.engine
set_option linter.unusedSectionVars false
variable {d x y:ℝ}{ε T₁:ℕ}(w:ℕ)
local notation "ν" v:max=> Journey.side Y i v
variable (h:Watchdesk (f:=f) P j X w)
local notation "p_"=> h.plan
local notation "£" s:max=> P.longtruck w f s
local notation "U!" s:max=> P.risingtruck w (f:=f) (v:=s) h.w0
local notation "V'" s:max=> P.clockPlate f s X
local notation "U₀" s:max=> frameOne (P.clockPlate f s X)
local notation "Ξ" s:max=> P.deskValue j X w h s
local notation "ι'" r:max v:max=> U₀ v ∪ volumeAround Λ P.width (v-r) (U₀ r)
variable {b:ℝ}{l:ℕ→ℝ}{σ:ℕ→ℕ} (p:f≤r)(u:r≤v)
variable (K': lender A C f r v l b σ P)
local notation "f!"=> ((↑(zoomM L^(r-f))):ℂ)
open Worth Pays CF.BProof
-- op estimate without small exponent opt! Use for any fixed root origin and for exp bounds later.
abbrev stemX (P:Preparation)(f:ℕ)(A:ℝ) := slotFee P f*Real.exp (8*A)
abbrev stopX (P:Preparation)(f:ℕ) := 14*meterC (hat P.R.L P.x f)
abbrev poleX (P:Spine)(f w:ℕ)(A:ℝ) := (2*truckBill P.par.block w (P.labW f) (stemX P.par f A) (stopX P.par f))^2
-- direct cam norm.
variable (N:P.NightCop)
include K' N p u
lemma cam_eight : ‖ (f! • ((b:ℂ) • (Ξ v) - Ξ r) : (P.Hil j).Op)‖ ≤ Real.sqrt (poleX P f w A+3):=by
 let z:=P.vividCard j X w h p u K'
 let X' (i:ℕ):= P.bookT (σ i) f r v (l (σ i)) X
 let Q':=gleam_path Y H P.history K'.earn
 let κ:ℕ→ℕ:=σ; have hg:Tendsto σ atTop atTop:= K'.earn.tendsto_atTop
 let W':= (U₀ v ∪ volumeAround P.par P.width (v-r) (U₀ r)); let T' := P.convoy_eight j X w h p u K'
 let a(s:ℕ):=aK s; let c(s:ℕ):= bK s
 let B:= stemX P.par f A; let d:=stopX P.par f; let x:=truckBill P.par.block w (P.labW f) B d
 have hs:0<slotFee P.par f:=by obtain ⟨k,u⟩:= K'.treasury.room.exists; exact u.2.load.health.2.2.1
 have hB:0<B:= mul_pos hs (Real.exp_pos _); have hd:0≤d:= mul_nonneg (by norm_num) (coin_pos ..).le
 have hx:0 < x:=mul_pos hB (Real.exp_pos _); let O:= poleX P f w A
 obtain ⟨J,hP,V,G⟩:= T'.bdd
 rw [← P.vivid_value j X w h p u K', Box, ← lift_box_glimmer _ _ _ _ K'.earn]
 refine onship_paid_eight Y H P.law v Q' j false (P.room j) (P.longtruck w f v) z (show Clipped _ _ _ _ from fun s=> hg.eventually (P.projection.clipped s)) (U! v) X' T' (P.bentC j X w h p u) O ?_
 constructor
 · exact pow_pos (mul_pos (by norm_num) hx) _
 have he := Filter.Eventually.and (P.touring_fee X p u) (K'.treasury.room.and (K'.pays.and ((N v).and (P.history.finance v))))
 let Wv:= plusAgain P.par.block (P.labW f); have hy:Tendsto (fun i=> (↑(side Y (a i) v).val:ℝ)) atTop atTop:= tendsto_natCast_atTop_atTop.comp (P.amount_go v)
 filter_upwards [G,hg.eventually (he.and (((P.amount_go f).eventually_ge_atTop Wv).and (hy.eventually_ge_atTop (J*(16/x)))))] with i Kx ⟨⟨t',Tm,Hk,E,fer⟩,Y₀,Y₁⟩ n hn Li Ri
 let n':= a (σ i); let k:= c (σ i); let K₀:= Hk.1; obtain ⟨b,d₀,w₀,p',η,Z⟩:= Hk.2; let S := gapMark P.run n' k b d₀ p u
 let T₁:= P.thresholdF f; let d':= rural T₁
 have ht: (RootBook P.run n' k f).p.B=T₁:=congrArg BudgetPoint.B (Papal.prices_plot Y f n' k ((p.trans u).trans fer.enters)).1
 let v':= P.rootAt f n' X; have hx:P.freightT v (σ i) (X' i)= S v':=by unfold X'; rw [Z]; exact t' b d₀
 have hz:0+(P.labW f:ℤ)≤ nodeC X j:=by simpa only [zero_add] using h.plan.seat
 let Lp:= side P.run n' f
 have hp: node v'=wrap _ (nodeC X):= node_of ..; let Sx:= (Yoke.graceful_clock Y n' k (b:=b) (z:=d₀) p u H fer T₁)
 have hr: Biscuit.Foot j (nodeC X) S (P.labW f) d' 0 (ruler P.par.block*w) (P.freightT v (σ i)) 1 (X' i) := by
   refine ⟨[v'],⟨fun x c=>?_,fun a k x c=>?_,by simp [outdoor]⟩,rfl,hx.trans ?_⟩
   · rw [List.mem_singleton.mp c, hp]; exact ⟨nodeC X j,hz,(by have hk:= h.width; omega),rfl⟩
   · rw [List.mem_singleton.mp c,hp]; rfl
   simp
 have hU(V:List (Site Lp))(hp:outdoor d' V): ‖Journey.compass Y n' k v (V.map S).prod‖ ≤ B^V.length * Real.exp (d*((More (side Y n' f)).val:ℝ)^4):=by
    apply (gap_ticket Y n' k p u V Tm.2 η (by rw [ht]; exact hp)).trans; unfold B stemX steamRent; rw [mul_pow,←Real.exp_nat_mul,mul_assoc (_^(_ : ℕ)),←Real.exp_add]; apply mul_le_mul_of_nonneg_left _ (by positivity); apply le_of_eq; congr 1; push_cast; unfold d stopX sites; push_cast; ring -- tune
 have Tv: pay (X' i) J:=Kx
 exact P.single_banner j (nodeC X) w S (X' i) fer (p.trans u) h.w0 hn Sx (aux_test (T'.whereTo i)) hr hU (fun l=>Yoke.oval _ _ _ _ _ _ fer) Tv hB hd Y₁ E Y₀ Li Ri
lemma path_paid_weight : ‖(b:ℂ) • (Ξ v) - Ξ r ‖ ≤ Real.sqrt (poleX P f w A+3)/ zoomM L^(r-f):=by
 have hs:0 < zoomM L^(r-f):=pow_pos (zoomM_p L) _
 apply (le_div_iff₀ hs).mpr; have he:= P.cam_eight j X w h p u K' N; rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hs] at he; exact (mul_comm ..).trans_le he
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
