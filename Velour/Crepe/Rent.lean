import Velour.Crepe.Token
import SatinThinPromenade
/-! The gauge-unit pitch is proportional to (halo+resolution
fees of) f-th project. -/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6200
set_option maxHeartbeats 1200000
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
local notation "Ω"=>P.Hil j
local notation "φ"=> P.groundZero j
local notation "μ"=> P.pillars j
local notation "W"=> P.calibration
local notation "Q"=> P.par.block
local notation "ℓ"=> P.calibration.ℓ
local notation "Ξ"=> household W
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
local notation "F" s:max=>hat P.par.R.L P.par.x s
local notation "N" s:max i:max => Journey.side P.run i s
/-! # Train cost comparison on elected printed heights. -/
/-! # Fix ranks independently of layout and period. Extract for every *fixed* v from very same P (no law mutation). -/
local notation "aK"=>P.nomadic
local notation "bK"=>P.engine
variable {A C U:ℝ}

open CF.Pannier.Chancel CF.Py.Rate.LocalLimit.Preparation.Yoke Worth VelourBoard
variable {B:ℕ}{X:Cover}

open Worth Pays CF.BProof Aria Casting MacroGrid

-- pitch in f-ticks
noncomputable abbrev tentSpan (D:ℕ):=8*(P.axleQ 3 D + 
    ((univ : Finset Axis).sup frameRadius + P.sidesPerTick)+1)
noncomputable abbrev rentSpan (s:ℕ):= P.tentSpan (P.thresholdF s)
variable (d:ℕ) (l:List Axis)
local notation "Γ" s:max=> P.rootSpace d s l
local notation "Ω'" s:max=> (nodeC (Γ s) j)
lemma buys_pos (s:ℕ): 0<P.rentSpan s:=by unfold rentSpan tentSpan; omega
lemma buys_room (s:ℕ):
  nodeC (Γ s) j + ((frameRadius j:ℤ)+ℓ) + (rural (P.thresholdF s)+1:ℕ) ≤
          P.rentSpan s:=by
 have t:=P.node_ceiling j s d l
 have h:frameRadius j ≤ (univ : Finset Axis).sup frameRadius:=le_sup (mem_univ j)
 let c:=P.axleQ 3 (P.thresholdF s)
 have p: ℓ≤ c:=by change _ ≤ P.labW s+ℓ+frameRadius 3; omega
 have p':rural (P.thresholdF s)≤c:=by change _≤ (ℓ+12+rural (P.thresholdF s))+ℓ+frameRadius 3; omega
 unfold rentSpan tentSpan; change (Ω' s) ≤ (↑(2*c+1):ℤ)+_ at t
 omega 


lemma buys_roomy(s:ℕ):nodeC (Γ s) j + ((frameRadius j:ℤ)+ℓ) + (rural (P.thresholdF s)+1:ℕ) ≤
           ruler Q*(P.rentSpan s:ℤ) :=
 (P.buys_room j d l s).trans (le_mul_of_one_le_left (by positivity) (ruler_gene Q))
lemma pricedSeat (s:ℕ) : Basque s (P.rentSpan s) (Γ s) P:= by
 refine ⟨P.buys_pos s,?_,fun j=> (P.rent_honors j d s l).test,?_⟩
 · intro i; have t:=P.buys_roomy i d l s
   unfold Wall; simp only [Pi.zero_apply,mul_zero,zero_add,mul_one]
   have k:= (P.rent_honors i d s l).seat
   change (↑(ℓ+12+rural (P.thresholdF s)):ℤ) ≤ _ at k
   constructor; · omega
   change _ ≤ ruler Q * _
   omega
 intro i; have t:= P.buys_roomy i d l s; omega
lemma paysArc : Worth.Pays 0 0 6 (fun x=> (P.tentSpan (radiusB x):ℝ)):=by
 have q:∀c:ℕ, Worth.Pays 0 0 6 (fun _=>(c:ℝ)) := fun _=> Worth.Pays.merit (Pays.constant _) (by norm_num [Worth.Earlier])
 have g:=P.width_ledger 3
 
 have t(x:ℝ): (P.tentSpan (radiusB x):ℝ)= (↑(8:ℕ))*(((P.axleQ 3 (radiusB x):ℕ):ℝ)+ 
      (↑((univ : Finset Axis).sup frameRadius + P.sidesPerTick):ℝ)+(↑(1:ℕ))) :=by
    unfold tentSpan; rw [Nat.cast_mul,Nat.cast_add,Nat.cast_add]
 simp_rw [t]
 exact Pays.scale _ (plus (plus g (q _)) (q 1))

lemma rent_afford (c:ℕ): ∀ᶠ f in atTop,P.RentBox f (c*P.rentSpan f):= by
 let w:ℝ:= ((2*(P.sidesPerTick*c):ℕ):ℝ)
 have t:= times (Pays.scale 14 (show Worth.Pays r_meter 0 0 Worth.meterC from Pays.whole ..))
    (pot (Pays.scale w P.paysArc) 4)
 have h:=leap (w:=0) (p:=0) (q:=0) t (Or.inl (by norm_num [r_meter]))
 filter_upwards [(turnover P.par).eventually h] with f p
 unfold RentBox
 rw [coin_zero] at p
 unfold rentSpan; rw [show P.thresholdF f=radiusB (F f) from (P.run.meter.boot f).2.1]
 rw [show (2*VelourBoard.pitch P.calibration (c*P.tentSpan (radiusB (F f)))) =
      (2*(P.sidesPerTick*c))* P.tentSpan (radiusB (F f)) from
      (by change (2:ℕ)*(P.sidesPerTick*(c*_))=_; ac_rfl), Nat.cast_mul]
 exact p


lemma pays_feasible :
    ∀ᶠ f:ℕ in atTop,P.RentBox f (P.rentSpan f) ∧
      P.RentBox (f+1) (P.reachLeaf f (f+1) (P.rentSpan f)):= by
 filter_upwards [P.rent_afford 1,P.rent_afford (L).val] with f u t
 refine ⟨one_mul (P.rentSpan f) ▸ u,?_⟩
 rw [reachLeaf,Nat.add_sub_cancel_left,pow_one]
 refine le_trans ?_ t
 have h:meterC (F (f+1)) ≤ meterC (F f):= by
    unfold meterC BProof.coin
    simp only [mul_zero,add_zero]
    exact Real.exp_le_exp_of_le (mul_le_mul_of_nonpos_right
      (Real.log_le_log (P.f_here _) (P.base_height (Nat.le_succ _))) (by norm_num [r_meter]))
 gcongr


lemma arc_size : ∀ᶠ k in atTop, P.rentSpan (k+k)≤k:=by
 let y:= billX L
 have ye:=P.arc_price
 have h:StrictMono (fun k:ℕ=>k+k):=fun a b p=> by dsimp; omega
 have t:=leap (w:=1) (p:=0) (q:=0)
     (Pays.scale (4*y) P.paysArc) (Or.inl zero_lt_one)
 have u:= (turnover P.par |>.eventually t)
 have h0:=  mul_pos (by norm_num: (0:ℝ)<2) ye
 filter_upwards [h.tendsto_atTop.eventually u,
    tendsto_natCast_atTop_atTop.eventually_ge_atTop (P.par.x/(2*y))] with k h q
 rw [coinY (P.f_here _)] at h
 have p: (P.rentSpan (k+k):ℝ) ≤ k:=by
     unfold rentSpan; rw [show P.thresholdF (k+k)=radiusB (F (k+k)) from (P.run.meter.boot (k+k)).2.1]
     apply le_of_mul_le_mul_left _ (show 0<4*y from mul_pos (by norm_num) ye)
     change 4*y * _ ≤ P.par.x + (↑(k+k:ℕ) : ℝ)*y at h
     rw [Nat.cast_add] at h
     change _ ≤ (k:ℝ) at q
     linarith only [h,(div_le_iff₀ h0).mp q]
 exact_mod_cast p


lemma thinArc : ∀ᶠ k in atTop,
    P.rentSpan (k+k)*P.macroStep (k+k) < P.macroStep k:=by
 have e(k:ℕ): k < (L).val^k:=by
    induction k with
    |zero=>simp
    |succ n ih=>have t:= (timeMesh P.par).Llarge; rw [pow_succ]; change 1< (L).val at t; exact Nat.lt_of_le_of_lt ih (lt_mul_of_one_lt_right (pow_pos (L).property _) t)
 filter_upwards [P.arc_size] with k h
 have hp:=P.daysF (k+k) k (by omega)
 rw [show k+k-k=k from by omega] at hp
 rw [←hp]
 exact mul_lt_mul_of_pos_right (by exact_mod_cast h.trans_lt (e k)) (P.macroStep_pos (k+k))
lemma pin_lt_rent (s:ℕ):P.pinTime j d s l < P.rentSpan s * P.macroStep s:=by
 have h:=P.buys_roomy j d l s
 have u:nodeC (Γ s) j < (↑P.sidesPerTick:ℤ)*(P.rentSpan s:ℤ):=by
    rw [show (P.sidesPerTick:ℤ)=ruler Q from by unfold ruler sidesPerTick; rw [Nat.cast_mul,Nat.cast_ofNat]]
    omega
 unfold pinTime; rw [div_lt_iff₀ (show 0<(P.sidesPerTick:ℝ) from Nat.cast_pos.mpr P.sides_pos),mul_comm _ (↑P.sidesPerTick:ℝ), ←mul_assoc]
 apply mul_lt_mul_of_pos_right _ (P.macroStep_pos _)
 have he:= (Int.cast_lt (R:=ℝ)).2 u; push_cast only [Int.cast_mul,Int.cast_natCast] at he; exact he




local notation "shadow_" f:max v:max=> pivotQ (P.granule (P.megaK f v)) l
local notation "zℝ" => (P.sidesPerTick:ℝ)
private lemma shroud (v:ℕ) : |(( (shadow_ f v) j):ℝ)|≤ (P.echoFoot:ℝ):=by
 obtain h|h:= pivot_alone (P.granule (P.megaK f v)) l j <;> rw [h]; swap; · rw [Int.cast_neg, abs_neg]; exact (abs_of_nonneg (P.tiny_one_ledger v _).1).trans_le (P.tiny_one_ledger v _).2
 exact (abs_of_nonneg (P.tiny_one_ledger v _).1).trans_le (P.tiny_one_ledger v _).2

lemma reach_size (B:ℕ)(h:s≤v):
   P.reachLeaf s v B * P.macroStep v=B*P.macroStep s:=by
 unfold reachLeaf; rw [Nat.cast_mul,Nat.cast_pow,mul_comm _ (B:ℝ),mul_assoc,P.daysF v s h]
-- copied analytic estimate from SatinThinPromenade
lemma quoteBoth (y:f ≤ s)(p:Odd P.par.R.L.val):∀ᶠ v:ℕ in atTop,
   s<v ∧
    ∃X:Cover,P.clockPlate s v (P.rootSpace f s l)=
      (shadow_ f v)+P.sidesPerTick • X ∧
   P.roomy*P.macroStep v<P.meshPose v X j ∧
   P.roomy*P.macroStep v<P.reachLeaf s v (P.rentSpan s)*P.macroStep v - P.meshPose v X j := by
 let t':= P.pinTime j f s l; let c(v:ℕ):ℝ:= (P.echoFoot:ℝ)*P.macroStep v/zℝ; let d(v:ℕ):ℝ:= ((( (shadow_ f v) j):ℤ):ℝ)*P.macroStep v/zℝ
 have hc:Tendsto c atTop (𝓝 0):=by simpa only [mul_zero,zero_div,c] using ((P.macroStep_zero.const_mul (P.echoFoot:ℝ)).div_const zℝ)
 have hd:Tendsto d atTop (𝓝 0):= squeeze_zero_norm' ((Eventually.of_forall fun r=> (show ‖d r‖ ≤ c r from ?_))) hc
 have ht:Tendsto (fun r:ℕ=> t'-d r) atTop (𝓝 t'):=by simpa only [sub_zero] using tendsto_const_nhds.sub hd
 have hw:Tendsto (fun r:ℕ=> (P.roomy:ℝ)*P.macroStep r) atTop (𝓝 0):=by simpa only [mul_zero] using (P.macroStep_zero.const_mul (P.roomy:ℝ))



 have hW: 0<P.rentSpan s*P.macroStep s-t':=
    sub_pos.mpr (P.pin_lt_rent j f l s) -- parameters order? j,d,l,s.
 filter_upwards [eventually_gt_atTop s,hw.eventually_lt ht (P.pin_p j f s l),
        hw.eventually_lt (tendsto_const_nhds.sub ht) hW] with v v0 u q
   -- v d formula matches
 obtain ⟨X,V⟩:= P.charge_race f s v y v0.le l p
 refine ⟨v0,X,V,u.trans_eq (P.quote_height j l v0.le X V).symm,?_⟩
 rw [P.quote_height j l v0.le X V,
    P.reach_size (P.rentSpan s) v0.le]; exact q
 simp only [d,Real.norm_eq_abs]; rw [abs_div, abs_mul, abs_of_pos (P.macroStep_pos _), abs_of_pos (show 0< zℝ from Nat.cast_pos.mpr P.sides_pos)]; exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (P.shroud j l r) (P.macroStep_pos _|>.le)) (Nat.cast_nonneg _)
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection

