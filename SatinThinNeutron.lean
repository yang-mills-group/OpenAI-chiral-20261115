import SatinThinCarnival
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
local notation "Λ"=> P.par
local notation "L"=> P.par.R.L
local notation "H"=>P.large
local notation "N" s:max i:max => Journey.side P.run i s
/-! # Buy height and travel together. Keep both actual calibration and rank resolution schedule. -/
open CF.Pannier.Chancel CF.Py.Rate.LocalLimit.Preparation.Yoke
open Worth Pays CF.BProof
open Real (log)
open Aria Casting MacroGrid
local notation "z'" => witnessZ
open Regis.Head.Etch Push.Local AnalyticBridge.VerifiedReset
local notation "Δ" t:max x:max => P.tariffQ z' t x
variable (x : P.Spectrum0 3)
local notation "ξ"=> P.advocate 3 x 3
local notation "M"=> P.ColorHil 3 (ξ)
local notation "G"=> P.ManyF 3 (ξ)
local notation "E" r:max=> P.singleState 3 r x
local notation "Ω"=> P.colorZero 3 ξ
local notation "Γ"=>P.cartage 3 ξ
local notation "Η"=>P.seasons 3 ξ
local notation "κ"=>P.wealth 3 ξ
local notation "Πγ"=>P.enter 3 ξ
local notation "ω"=> P.heaven 3 ξ
local notation "B"=> P.basePlay x f r
local notation "K" f:max r:max=> P.megaK f r
local notation "W'" => P.tallWorth r
local notation "q!" i:max s:max=> P.runP f r i s
local notation "p!" i:max s:max=> P.meshPose r (q! i s)
local notation "O"=> P.charmF
local notation "oQ"=> opposeQ 3
local notation "oR"=> opposeR 3
open Regis.Circuit SatinJets
local notation "r!" f:max r:max=> ((P.rewardK f r):ℝ)
local notation "Cσ"=> Yoke.canonWeight
local notation "H!" i:max b:max=> P.strollQ x f r i b
local notation "Hu" i:max b:max=> P.strollV x f r i b
/-! # Purchase & projection simultaneously on exactly elected R-m&parting. 
-/
local notation "Φ"=> P.Spectrum0 3
local notation "χ"=> P.pillars 3
local notation "cwd" f:max=> slotFee P.par f

-- one frequent sequence with small aperture, for ALL widths on eventual sites. no varying volume & i.
private lemma carnation(f:ℕ→ Φ→ℝ)(h:∀ i,Continuous (f i))(v:∀ i,0≤f i)(p:∀ i,(∫ x,f i x∂χ)≤1/2) {F:Φ→ Prop} (u:∀ᵐ x∂χ,F x): ∃ x: P.Spectrum0 3, F x∧ ∃ᶠ i in atTop, f i x<1:=by
 by_contra! q
 let Wb(i:ℕ):Φ→ℝ:=fun x=> min (f i x) 1; have he(i):Continuous (Wb i):=(h i).min continuous_const
 have hs(i): 0 ≤ Wb i:= fun y=> le_min (v i y) zero_le_one
 have H' (j:Φ→ℝ)(t:Continuous j):Integrable j χ:= t.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
 have hp(i:ℕ): (∫ x, Wb i x∂χ)≤ 1/2:= (integral_mono (H' _ (he i)) (H' _ (h i)) (fun y=>min_le_left ..)).trans (p i)
 have ht: Tendsto (fun i:ℕ=>∫ x,Wb i x∂χ) atTop (𝓝 (∫ (_:Φ),(1:ℝ)∂χ)):=by
    refine tendsto_integral_of_dominated_convergence (fun (_:Φ)=> (1:ℝ)) (fun i=> (H' _ (he i)).1) (integrable_const _) (fun i=> Eventually.of_forall (fun x=> (Real.norm_of_nonneg (show 0≤ Wb i x from hs i x)).trans_le (min_le_right ..))) (u.mono ?_)
    intro z vz; refine tendsto_const_nhds.congr' ?_; filter_upwards [q z vz] with i v; exact (min_eq_right v).symm -- check push_neg
 rw [integral_const,probReal_univ,one_smul] at ht; linarith only [le_of_tendsto ht (Eventually.of_forall hp)]
def lensValue (A:ℝ):= 4* Real.exp ((16*A+1)/2)
local notation "s₀"=> lensValue
private lemma lensAm(A:ℝ) : (lensValue A)^2=16* Real.exp (16*A+1):= by
 have hp: ((16*A+1)/2)+((16*A+1)/2)=16*A+1:=by ring
 unfold lensValue; rw [mul_pow,sq (Real.exp _),← Real.exp_add,hp]; norm_num
lemma lensBasis(A:ℝ): 0< lensValue A:=by unfold lensValue; positivity
variable {A b C:ℝ}(Book:P.repeatBill (twiceT (P.baseRoot f) 3) f)(F₀:f<r)(P0:∀ v:ℕ,∀ h: r ≤ v,EarnedClockPlot P C A f r v F₀ h)(Q0:(∫ x,P.lantern x f r ∂(P.pillars 3))≤ (min7 /4)/4)(u:P.reached f r)
  (S:0< slotFee P.par f)(D:0<P.rewardK f r)
  (Z0:2*lensValue A * (P.rewardK f r * slotFee P.par f /zoomM P.par.R.L^(r-f)) ≤ b/16)
include Book F₀ P0 Q0 u S D Z0
-- elected extra has ∀ᵐ x Flag. Enough to postpone election until such an r known. Υ:=reliable threshold fixed
structure Clump (P:Spine)(A C:ℝ)(x:P.Spectrum0 3)(f r:ℕ)(b:ℝ):Prop where
 price:P.lantern x f r ≤ min7/4
 beat: ∃ᶠ v:ℕ in atTop,∃ (a:ℝ)(q:ℕ→ℝ)(t:ℕ→ℕ), lender A C f r v q a t P ∧ dist (P.invoiceV x f r v (a:ℂ)) (P.invoiceV x f r r 1) ≤ b/16
lemma phase_hit (Lk:P.Spectrum0 3→Prop)(hx:∀ᵐ x∂χ,Lk x) : ∃ x:Φ,Lk x ∧ Clump P A C x f r b :=by
 let d (v:ℕ): r≤ r+v:= Nat.le_add_right r v
 choose q a l hP b0 using fun v:ℕ=> (P0 (r+v) (d v)); let Mv(x:Φ):= P.lantern x f r; let Kp:= P.lent_anchor f; let Pv(v:ℕ)(x:Φ):= P.census f r (r+v) (d v) F₀.le (a v) x; let s:= lensValue A; let m₀:= min7 /4; let c':=(s*cwd f)^2
 have hcc:0<c':=pow_pos (mul_pos (lensBasis _) S) _; have hmn:0 < m₀:=div_pos min_positive (by norm_num); have hg:Continuous Mv:= P.lantern_cont f r; have he(v): Continuous (Pv v):=P.state_cont_cost ..; have hp: ∀ x,0≤Mv x:= fun i=>(show 0≤ P.glareF f r 1 1 0 i from norm_nonneg _).trans (P.lantern_available i f r|>.1); have hu(i x):0≤ Pv i x:=sq_nonneg _
 have hs(v:ℕ): (∫ x,Pv v x∂χ) ≤ c'/4:= le_trans (b0 v 3 _ Kp Book |>.2) ?_; swap -- tune blockproof
 · unfold c' s Yoke.owedF; rw [mul_pow,lensAm]; norm_num only [Nat.cast_ofNat]; rw [show 8*A*2+1=16*A+1 from by ring]; nlinarith only [sq_nonneg (cwd f), S, Real.exp_pos (16*A+1)]
 let g (v:ℕ)(x:Φ):= Mv x / m₀ + Pv v x / c'
 have hM(i:ℕ): (∫ x, g i x ∂χ)≤1/2:=by
   let hQ (e:Φ→ℝ)(t:Continuous e):Integrable e χ:=t.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
   unfold g; rw [integral_add (f:=fun x=> Mv x/m₀) (g:=fun x=>Pv i x/c') (hQ _ (hg.div_const _)) (hQ _ ((he i).div_const _)),integral_div,integral_div]; exact (add_le_add ((div_le_iff₀ hmn).mpr (Q0.trans_eq (show m₀/4= (1/4)*m₀ by ring))) ((div_le_iff₀ hcc).mpr ((hs i).trans_eq (show c'/4=(1/4)*c' by ring)))).trans_eq (by norm_num)
 obtain ⟨x,p,w⟩:=P.carnation g (fun i=> (hg.div_const _).add ((he i).div_const _)) (fun i x=> add_nonneg (div_nonneg (hp x) hmn.le) (div_nonneg (hu i x) hcc.le)) hM hx
 have ht(i:ℕ)(h: g i x<1): Mv x ≤ m₀ ∧ Pv i x≤ c':= by
    unfold g at h; refine ⟨(div_le_one hmn).mp ?_, (div_le_one hcc).mp ?_⟩ <;> linarith only [h, div_nonneg (hp x) hmn.le, div_nonneg (hu i x) hcc.le]
 refine ⟨x,p,ht _ w.exists.choose_spec|>.1, Filter.frequently_atTop.mpr fun n=>?_⟩
 obtain ⟨i,v,g0⟩:= frequently_atTop.mp w n; let e₂:= q; exact ⟨r+i,by omega,a i,q i,l i,hP i,(P.compare_distance x (d i) F₀.le _ s (lensBasis _) D u (ht _ g0|>.2) S).trans Z0⟩
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.phase_hit
