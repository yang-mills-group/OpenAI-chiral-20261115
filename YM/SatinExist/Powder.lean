import YM.SatinExist.Lenox
import YM.SatinExist.Shield
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
abbrev stemZ (P:Spine)(A:ℝ)(f s:ℕ) := fareMin P.par.R.L (s-f) * stemX P.par f A
abbrev fenceZ (P:Spine)(A:ℝ)(f s w:ℕ) := (2*truckBill P.par.block w (P.labW f) (P.stemZ A f s) (stopX P.par f))^2
lemma natural_income {t:ℕ}(u:f ≤ t)(N:P.NightCop)
   (T:∀ᶠ i:ℕ in atTop, Credentials P.run (P.nomadic i) (P.engine i) A f t ∧ ShelterCost C P.run f (P.nomadic i) (P.engine i)):
   ‖Ξ t‖ ≤ Real.sqrt (P.fenceZ A f t w+3):=by
 let z:= P.deskCard j X w h t
 let Q':=P.history
 let B:= P.stemZ A f t; let d:=stopX P.par f; let x:= truckBill P.par.block w (P.labW f) B d
 obtain ⟨n,Yx,U⟩:= T.exists; have hp:0<stemX P.par f A:= mul_pos U.load.health.2.2.1 (Real.exp_pos _); have hB: 0<B:= mul_pos (by unfold fareMin; positivity) hp; have hd:0≤d:=mul_nonneg (by norm_num) (coin_pos ..).le; have hx:0<x:=mul_pos hB (Real.exp_pos _); let O:=P.fenceZ A f t w
 let V:= P.visitOne t (V' t)
 let hτ: InTest W true (U₀ t) false V.val:=P.basesT; obtain ⟨M,ht⟩:= valuation Y H hτ; let M₀:=M+1; have hm:pay V.val M₀:=fun _ _=>(ht ..).trans (by unfold M₀; linarith); have hMt:0<M₀:=add_pos_of_nonneg_of_pos (pay_nonneg (F:=V.val) ht) zero_lt_one
 refine onship_paid_eight Y H P.law t Q' j false (P.room j) (P.longtruck w f t) z P.projection.clipped (U! t) (fun _=> V.val) (BQueue.stay hτ hMt hm) (P.deskFrame j X w h t) O ?_
 constructor
 · exact pow_pos (mul_pos (by norm_num) hx) _
 let Wv:= plusAgain P.par.block (P.labW f); have hy:Tendsto (fun i=> (↑(side Y (aK i) t).val:ℝ)) atTop atTop:= tendsto_natCast_atTop_atTop.comp (P.amount_go t)
 filter_upwards [T,N t,P.history.finance t,(P.amount_go f).eventually_ge_atTop Wv,hy.eventually_ge_atTop (M₀*(16/x))] with i ⟨t',K₁⟩ E fer Y₀ Y₁ m q Li Ri
 let n':= aK i; let k:= bK i; let S:= Yoke.principal P.run n' k u 1; let T₁:= P.thresholdF f; let d':= rural T₁
 have ht:(RootBook Y n' k f).p.B=T₁:=congrArg BudgetPoint.B (Papal.prices_plot Y f n' k (u.trans fer.enters)).1
 let v':=P.rootAt f n' X; have hy:P.freightT t i V.val=S v':=by
    have he:=P.eerieT (i:=i) (P.high_root u X).symm fer.enters 1; rw [Complex.ofReal_one,one_smul] at he; exact he
 have hz:0+(P.labW f:ℤ)≤ nodeC X j:=by simpa only [zero_add] using h.plan.seat
 let Lp:= side Y n' f
 have hp: node v'=wrap _ (nodeC X):= node_of ..
 have hr: Biscuit.Foot j (nodeC X) S (P.labW f) d' 0 (ruler P.par.block*w) (P.freightT t i) 1 V.val := by
   refine ⟨[v'],⟨fun x c=>?_,fun a k x c=>?_,by simp [outdoor]⟩,rfl,hy.trans ?_⟩
   · rw [List.mem_singleton.mp c, hp]; exact ⟨nodeC X j,hz,(by have hk:= h.width; omega),rfl⟩
   · rw [List.mem_singleton.mp c,hp]; rfl
   simp
 have hU(V:List (Site Lp))(hp:outdoor d' V): ‖Journey.compass Y n' k t (V.map S).prod‖ ≤ B^V.length * Real.exp (d*((More (side Y n' f)).val:ℝ)^4):=by
    apply (white_ticket Y n' k t' K₁ (by rw [ht]; exact hp)).trans_eq; unfold B stemZ steamRent stemX; rw [mul_pow,mul_pow,←Real.exp_nat_mul]
    rw [show ((_ :ℝ)^V.length) * (_^V.length * Real.exp ( (V.length:ℝ)*(8*A))) * Real.exp (d*((More (side Y n' f)).val:ℝ)^4) = fareMin P.par.R.L (t-f)^V.length*((slotFee P.par f)^V.length * (Real.exp ((V.length:ℝ)*(8*A))*Real.exp (d*((More (side Y n' f)).val:ℝ)^4))) from ?_, ←Real.exp_add]
    · congr 3; push_cast; unfold d stopX sites; push_cast; ring
    ring
 exact P.single_banner j (nodeC X) w S V.val fer u h.w0 q (Yoke.truthful _ _ _ t' H fer T₁ 1) (aux_test hτ) hr hU (fun l=>Yoke.true_oval _ _ _ l 1) hm hB hd Y₁ E Y₀ Li Ri
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
