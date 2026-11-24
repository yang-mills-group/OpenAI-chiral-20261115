import SatinPP.Ratio
import SatinPP.WarpPrice
import SatinPP.Cargo

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
local notation "Ω"=>P.Hil j
local notation "φ"=> P.groundZero j
local notation "μ"=> P.pillars j
local notation "W"=> P.calibration
local notation "Q"=> P.par.block
local notation "ℓ"=> P.calibration.ℓ
local notation "Ξ"=> household W
open Papal Regis.Head Gleam
open Clock Clock.Hookah Clock.Hookah.Blaze
open Preparation.Yoke Yoke.Travel Regis.Head.Garland
open QuadClock Again Pressure
variable {s t f r v i k:ℕ}
local notation "Y"=> P.run
local notation "Λ"=> P.par
local notation "L"=> P.par.R.L
local notation "H"=>P.large
local notation "N" s:max i:max => Journey.side P.run i s
variable (X:Cover){C e A:ℝ}{d:ℕ}
open CF.Pannier.Chancel CF.Py.Rate.LocalLimit.Preparation.Yoke
local notation "aK"=> P.nomadic
local notation "bK"=> P.engine
open SlabMark.ArrayParcel


lemma conveys_freight (hp:f≤r)(hz:r≤v) (g:Ferry P.run v (P.nomadic i) (P.engine i))(σ:ℝ):
    Conveys ((P.par.R.L.val:ℤ)^(v-f)) (freightT P v i) (principal Y (aK i) (bK i) (hp.trans hz) σ):=by
 let I:=aK i; let G:= principal Y I (bK i) (hp.trans hz) σ
 let w(F A:Family W):= distribute_arith Y H v I F A 0
 refine ⟨(w 0 0).2.2.2.1,fun F A=>(w F A).2.1,?_⟩
 intro F l h j z
 let q:= graceful_prin Y I (bK i) hp hz σ H g 0
 exact ((w F 0).2.2.2.2 j _).trans ((congrArg (reflMark j (highTurn P.par f v z)) h).trans (spun_price q l j z).symm)
private lemma sideRise (p:f≤v)(i:ℕ):
    (Journey.side P.run i v).val = P.par.R.L.val^(v-f)*(Journey.side P.run i f).val:=by
 induction p with
 | refl=> simp
 | step t ih=> 
   rw [Nat.succ_sub t,pow_succ',mul_assoc, ←ih, mul_comm]
   exact (Vale.apt (P.run.ir i) P.par.block P.par.R.L _).exact_size

abbrev pageWidth (u:ℕ) := (16*P.par.block.val)*u
abbrev tierScale (f v:ℕ) := P.par.R.L.val^(v-f)
abbrev roomFee (A:ℝ):ℝ:= Real.exp (-(8*A+1002))/4
abbrev sellLeaf (f v:ℕ)(X:Cover)(A a:ℝ):Family (tent P.run P.large) :=
  ((roomFee A*a:ℝ):ℂ) • (P.visitOne v (P.clockPlate f v X)).val

/-- All shifts needed along Polity. -/
def PaidRolls (P:Spine)(v w:ℕ)(F:Family P.calibration):Prop :=
 ∀ j:Axis,∀ᶠ i:ℕ in atTop,∀ n:ℕ,∀ s:ℤ,
 0<n→ 2*(ruler P.par.block*w*n) ≤ (((Journey.side P.run (P.nomadic i) v).val:ℕ):ℤ)→
    (((Journey.side P.run (P.nomadic i) v).val:ℕ):ℤ) ≤ (4*(ruler P.par.block*w*n))→
   ‖Journey.sharp P.run P.large v (P.nomadic i) (P.engine i)
       (SlabMark.banner j w ((w:ℤ)*s) n F)‖ ≤ Real.exp (-3000*(n:ℝ))
structure Clearance (P:Spine)(f u:ℕ)(X:Cover):Prop where
 pos:0<u
 fits:∀ j:Axis, (Yoke.rural (P.thresholdF f):ℤ) < nodeC X j ∧
     nodeC X j+(Yoke.rural (P.thresholdF f):ℤ)<(P.pageWidth u:ℤ)
 space:P.repeatBill (P.pageWidth u) f

private lemma marginRoll {n:ℕ}(hn:0<n):
   3*Real.exp (-1001)^(4*n)≤Real.exp (-3000*(n:ℝ)):=by
 have ht:(1:ℝ)≤n:=by exact_mod_cast hn
 rw [←Real.exp_nat_mul]
 push_cast
 refine (mul_le_mul_of_nonneg_right (show (3:ℝ)≤ Real.exp 2 from le_trans (le_refl _) (by simpa only [show (2:ℝ)+1=3 by ring] using Real.add_one_le_exp 2)) (Real.exp_pos _).le).trans ?_
 rw [←Real.exp_add]
 exact Real.exp_monotone (by linarith only [ht])
variable {u:ℕ} {α:ℕ→ℝ}{a:ℝ}{l:ℕ→ℕ}
lemma clearance_roll (Lc:lender A C f r v α a l P)
 (O:P.NightCop)
 (w:P.CloseRates A C f r v)
 (n0:fareMin P.par.R.L (r-f)≤1)
 (hp:P.Clearance f u X):
    P.PaidRolls v (P.tierScale f v * u) (P.sellLeaf f v X A a):=by
 let τ:=Lc.treasury
 have hf:=τ.price.le
 have hr:=τ.step
 have hv:=hf.trans hr
 let B:=P.pageWidth u; have hB:0<B:=Nat.mul_pos (Nat.mul_pos (by decide) P.par.block.property) hp.pos
 let D:=plusAgain P.par.block (P.labW f)
 let q:=P.tierScale f v; have q0:0<q:=pow_pos P.par.R.L.property _
 let θ:=roomFee A*a
 let y:=P.sellLeaf f v X A a
 let Ux:=P.clockPlate f v X
 have hz:InTest W true (frameOne Ux) false y:=(show InTest W true (frameOne Ux) false (P.visitOne v Ux).val from P.basesT).smul _
 obtain ⟨U,ye⟩:= Journey.valuation Y H hz
 have u₀:0≤U:=pay_nonneg (F:=y) ye
 have ht:Tendsto (fun r=>((Journey.side P.run (aK r) v).val:ℝ)) atTop atTop:=
   tendsto_natCast_atTop_atTop.comp (P.amount_go v)
 intro j; filter_upwards [O v,P.history.finance v,ht.eventually_ge_atTop (U*(16/Real.exp (-1001))),
     (P.amount_go f).eventually_ge_atTop (B+D),τ.room,P.tail_rates Lc w n0] with i Z V he t K G n s hn lo hi
 let I:=aK i; let E:=bK i; let N₀:=side Y I f
 have hy: (RootBook Y I E f).p.B=P.thresholdF f:= (congrArg BudgetPoint.B (Papal.prices_plot P.run f I E (hv.trans V.enters)).1)
 obtain ⟨b,z,R,hG,x0⟩:= G

 have hθ: |θ| ≤ Real.exp (-(8*A+1002)) * |R*b|:=by
    unfold θ roomFee; rw [abs_mul,abs_of_nonneg (by positivity:0≤Real.exp (-(8*A+1002))/4)]
    exact (mul_le_mul_of_nonneg_left x0 (by positivity)).trans_eq (by ring)
 have hscale:(2*(B*n)≤N₀.val ∧ N₀.val≤4*(B*n)):= by
    rw [P.sideRise hv] at lo hi
    unfold ruler at lo hi; push_cast at lo hi
    have h₀:(2*((B:ℤ)*n))*(q:ℤ)≤ N₀.val*(q:ℤ):= by
       dsimp only [B,q,N₀,I,pageWidth,tierScale] at *; push_cast at *; linarith only [lo]
    have h₁:(N₀.val:ℤ)*q ≤ (4*((B:ℤ)*n))*(q:ℤ):= by
       dsimp only [B,q,N₀,I,pageWidth,tierScale] at *; push_cast at *; linarith only [hi]
    have h:0 < (q:ℤ):= by exact_mod_cast q0
    exact ⟨by exact_mod_cast le_of_mul_le_mul_right h₀ h,by exact_mod_cast le_of_mul_le_mul_right h₁ h⟩
 let Z₀:= P.freightT v i; let T:= P.rootAt f I X; let p:=principal Y I E hv θ
 let Q₀:=((L).val:ℤ)^(v-f)
 have Wy:Z₀ y=p T:= P.eerieT (P.high_root hv X|>.symm) V.enters θ
 have eB: ruler (W).B*(u:ℤ)=(B:ℤ):= by
    change ruler P.par.block*_ = _
    unfold B pageWidth ruler; push_cast; rfl
 have hx: 2*(ruler (W).B*(u:ℤ)*n) ≤ (N₀.val:ℤ):= by rw [eB]; exact_mod_cast hscale.1
 have hroom: Room j (rural (RootBook Y I E f).p.B) 0 (ruler (W).B*(u:ℤ)) (node T):=by
    rw [eB,hy]
    exact ⟨nodeC X j, (by rw [zero_add]; exact (hp.fits j).1), (hp.fits j).2, (congr_fun (node_of _ _).symm j)⟩
 obtain ⟨p₀,ph,pl,yr,hc⟩:= tally j (P.conveys_freight hf hr V θ) (by positivity:0≤(u:ℤ)) n hx (u*s) _ B T Wy hroom
 let z:=SlabMark.banner j (Q₀*u) (Q₀*(u*s)) n y
 have eq:Z₀ z=(p₀.map p).prod:=yr
 have ye':= (main_bill j (Q₀*u) (Q₀*(u*s)) n (aux_test hz) ye).2
 have yprice (x): ‖(p₀.map p).prod x‖ ≤ U^p₀.length:=by rw [←eq,pl]; exact P.plotted_cost z ye' i x
 have low:N₀.val ≤ p₀.length*B:= by rw [pl]; exact hscale.2.trans_eq (by ring)
 have up:p₀.length ≤ 2*N₀.val:=by
    rw [pl]
    have e: n ≤ B*n:=Nat.le_mul_of_pos_left _ hB
    have g:=hscale.1; omega
 have q':= compass_long Y I E hf hr p₀ (d:=B) (by rw [hy]; exact t) (by rw [hy]; exact hp.space) K.2 hG ph hθ j low up hc H V Z U u₀ yprice he
 rw [pl, ←eq] at q'
 change ‖Journey.sharp P.run P.large v I E (SlabMark.banner j (↑(q*u)) (↑(q*u)*s) n y)‖ ≤ _
 rw [show (↑(q*u):ℤ) = Q₀*u from by simp [q,tierScale,Q₀],mul_assoc]
 exact q'.trans (marginRoll hn)

end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.clearance_roll
