import YM.SatinExist.QuoteHeight
import YM.SatinExist.Timely
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
open Papal Regis.Head Gleam
open Clock Clock.Hookah Clock.Hookah.Blaze
open Preparation.Yoke Yoke.Travel Regis.Head.Garland
open QuadClock Again Pressure
open CF.Pannier.Chancel CF.Py.Rate.LocalLimit.Preparation.Yoke
open Worth Pays CF.BProof
open Real (log)
open Aria Casting MacroGrid
variable (P:Spine) (j:Axis)
/-! ## Poll the elected pilots. Along every needed orientation, x-standard and in
   exponential price. Lattice locations are `clockPlate`; no physical rescale. -/
variable {f r:ℕ}{C:ℝ}(Q':∀ᶠ s in atTop,∀ᶠ i in atTop,∀ k:ℕ,(P.run.voyage i).kick ≤ k → s ≤ P.run.uv k → ShelterCost C P.run s i k) (l:List Axis)

private lemma gcode {U:Type}[Countable U][Nonempty U] :
    ∃ M:ℕ→ U × ℕ, ∀ u:U, ∃ s t:ℕ,∀ n:ℕ,M (s*n+t)=(u,n):=by
 obtain ⟨b,h⟩:= Countable.exists_injective_nat U
 let T (i n:ℕ):ℕ:= 2^i*(2*n+1)
 have e(i n j k:ℕ)(h:T i n=T j k): i=j ∧ n=k:=by
   induction i generalizing n j k with
   | zero => cases j with
       | zero=>  simp only [T,pow_zero,one_mul] at h; omega
       | succ j=> simp only [T,pow_succ',pow_zero,one_mul,Nat.mul_assoc] at h; omega
   | succ i ih => cases j with
       | zero=> simp only [T,pow_succ',pow_zero,one_mul,Nat.mul_assoc] at h; omega
       | succ j=>
         simp only [T,pow_succ',Nat.mul_assoc] at h
         have hp:= ih n j k (show T i n=T j k from mul_left_cancel₀ (by omega: (2:ℕ)≠0) h); omega
 let F(x:U×ℕ):ℕ:= T (b x.1) x.2
 have hx:Injective F:= fun ⟨a,i⟩ ⟨c,k⟩ t=> Prod.ext (h (e (b a) i (b c) k t).1) (e (b a) i (b c) k t).2
 refine ⟨invFun F,fun i=> ⟨2^b i*2,2^b i,fun n=>?_⟩⟩
 rw [← show F (i,n)=2^b i*2*n+2^b i by unfold F T; ring]
 exact leftInverse_invFun hx _

abbrev QuickQuote (f r k:ℕ) := ForecastCard P f r j l (P.macroStep k)
lemma soon_dollars (f r:ℕ) : ∃ v:∀ k:ℕ,P.QuickQuote j l f r k,∀ᶠ k:ℕ in atTop,(v k).stage=2*k:=by
 let X(k:ℕ):=P.QuickQuote j l f r k
 have h(k:ℕ): Nonempty (X k):=P.forever_quote _ _ _ _ _ (P.macroStep_pos _)
 let v(k:ℕ):X k:=if p:∃ V:X k,V.stage=2*k then p.choose else Classical.choice (h k)
 refine ⟨v,?_⟩; filter_upwards [P.soon_quote j f r] with i t
 unfold v; rw [dif_pos (t l)]; exact (t l).choose_spec

include Q'
lemma bills_exponential (A:ℝ)(u:∀ k:ℕ,P.QuickQuote j l f r k)(hp:∀ᶠ k:ℕ in atTop,(u k).stage=2*k):
    ∀ᵐ x ∂(P.pillars 3),∀ s t:ℕ,∃ W> (0:ℝ), ∃ z≥(1:ℝ), ∀ᶠ k:ℕ in atTop,P.cardPrice j x (u k) A (s*k+t) ≤ W*z^k:=by
 obtain ⟨T,u',p'⟩:=P.tiny_purses
 obtain ⟨K,g,p⟩:=P.pilotsBudget j f l Q'
 filter_upwards [p] with x h s t
 let m:= zoomM P.par.R.L; let c:= zoomC P.par.R.L
 have hm:0< m:= zoomM_p _; have hu:1≤c:=zoomC_p _; have hc:0<c:=zero_lt_one.trans_le hu
 let n:ℝ:= 2^s; let a:= (2:ℝ)^(t+1)* (lensValue A*T)/m
 have hn:1≤n:=by unfold n; exact one_le_pow₀ (by norm_num)
 have ha:0≤a:= (div_pos (mul_pos (by positivity) (mul_pos (lensBasis _) u')) hm).le
 refine ⟨8*c*(K+a), mul_pos (mul_pos (by norm_num) hc) (add_pos_of_pos_of_nonneg g ha), c^2*(4*n), one_le_mul_of_one_le_of_one_le (one_le_pow₀ hu) (one_le_mul_of_one_le_of_one_le (by norm_num) hn),?_⟩
 let D:= (show StrictMono (fun k:ℕ=>2*k) from fun x y v=> by change 2*x<2*y; omega).tendsto_atTop
 filter_upwards [hp,D.eventually h,D.eventually p',D.eventually P.size_honors] with i y he he' R
 unfold cardPrice quotaSize lensForm
 simp only [y]; let B:=(4*n)^i
 have hN: navy (s*i+t)= n^i*(2:ℝ)^(t+1):=by unfold n navy; rw [Nat.add_assoc,pow_add,pow_mul]
 let v:= P.rootSpace f (2*i) l
 let y:= P.quoteRay j x (2*i) (2*i+1) v (P.rent_honors j f (2*i) l)
 have hw: (2:ℝ)^(2*i)≤B:= by rw [pow_mul]; exact pow_le_pow_left₀ (by positivity) (show (2:ℝ)^2 ≤ 4*n by nlinarith only [hn]) _
 let d:= navy (s*i+t)*(lensValue A*slotFee P.par (2*i))/m
 have hd:0≤d:= (div_pos (mul_pos (pow_pos (by norm_num) _) (mul_pos (lensBasis _) R.1)) hm).le
 have hz:d ≤ a*B:=by
   have hy:n^i ≤ B:= pow_le_pow_left₀ (zero_le_one.trans hn) (by linarith only [hn] : n ≤ 4*n) _
   apply le_trans _ (mul_le_mul_of_nonneg_left hy ha)
   unfold d; apply (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he'.1 (lensBasis A|>.le)) (show 0≤ navy _ from pow_nonneg (by norm_num) _)) hm.le).trans_eq
   rw [hN]; unfold a; ring
 change 2*(4*c^_)*(‖y‖+_/m^_)≤_
 rw [Nat.add_sub_cancel_left,pow_one]; change _*(‖y‖+d) ≤ _
 have heq : 4*c^(2*i+1-r) ≤ 4 * (c^2)^i*c:=by
   rw [mul_assoc]; apply mul_le_mul_of_nonneg_left _ (by norm_num); rw [←pow_mul,←pow_succ]; exact pow_le_pow_right₀ hu (Nat.sub_le ..)
 apply (mul_le_mul (mul_le_mul_of_nonneg_left heq (by norm_num : (0:ℝ) ≤ 2)) (add_le_add (he.trans (mul_le_mul_of_nonneg_left hw g.le)) hz) (add_nonneg (norm_nonneg _) hd) (by positivity)).trans_eq
 unfold B; rw [mul_pow (c^2)]; ring
omit Q'

variable {A b:ℝ}
abbrev ThermalBid (x:P.Spectrum0 3) (f r:ℕ)(v:ℕ→ℕ)(a:ℕ→ (ℕ×ℕ)→ℝ):Prop:= ∀ (j:Axis)(l:List Axis),∃ W> (0:ℝ), ∃ z≥(1:ℝ),∀ᶠ k:ℕ in atTop,∀ᶠ i:ℕ in atTop,‖(a i (f,r):ℂ) • P.beamWatch j x f (v i) l (P.macroStep k)‖≤ W*z^k
variable (G₀:P.NightCop)(Book:P.repeatBill (twiceT (P.baseRoot f) 3) f)(F₀:f<r)(P0:∀ v:ℕ,r ≤ v→∃ c a w, Workforce A C f v P c a w)(Q0:(∫ x,P.lantern x f r ∂(P.pillars 3))≤ (min7 /4)/4)(g0:P.reached f r)
  (S:0< slotFee P.par f)(D:0<P.rewardK f r)
  (Z0:2*lensValue A * (P.rewardK f r * slotFee P.par f /zoomM P.par.R.L^(r-f)) ≤ b/16)
include Q' G₀ Book F₀ P0 Q0 g0 S D Z0
lemma measured_winter (D₀:P.Spectrum0 3→Prop)(p0:∀ᵐ x∂(P.pillars 3),D₀ x)(p:Odd P.par.R.L.val) :
    ∃ x:P.Spectrum0 3,D₀ x ∧ ∃ v a, ScoutAnthem P x A C f r b v a ∧ P.ThermalBid x f r v a:=by
 choose F hF using fun (j:Axis)(l:List Axis)=>P.soon_dollars j l f r
 obtain ⟨L,t⟩:= gcode (U:=Axis × List Axis)
 let R(n:ℕ):= P.pedal_ξ (L n).1.1 (F (L n).1.1 (L n).1.2 (L n).2)
 have h:= fun (j:Axis)(l:List Axis)=>P.bills_exponential j Q' l A (F j l) (hF j l)
 obtain ⟨x,⟨d,o⟩,v,a,w⟩:= P.appearance G₀ Book F₀ P0 Q0 g0 S D Z0 R _ (p0.and (ae_all_iff.mpr fun j=> ae_all_iff.mpr fun l => h j l))
 have he(n:ℕ):∀ᶠ i:ℕ in atTop,‖(a i (f,r):ℂ) • P.beamWatch (L n).1.1 x f (v i) (L n).1.2 (P.macroStep (L n).2)‖≤ P.cardPrice (L n).1.1 x (F (L n).1.1 (L n).1.2 (L n).2) A n:=by
   filter_upwards [w.extra n,w.fast.tendsto_atTop.eventually (P.account_due _ x (F (L n).1.1 (L n).1.2 (L n).2) F₀ p n A C)] with i t u
   obtain ⟨c,l,Y⟩:=w.cruise i; exact u _ Y t
 have hz:P.ThermalBid x f r v a:=by
   intro j l; obtain ⟨s,t,e⟩:= t (j,l)
   obtain ⟨W,d,z,p,q⟩:= o j l s t; refine ⟨W,d,z,p,?_⟩
   filter_upwards [q] with k e'; have hk:= he (s*k+t); rw [e k] at hk
   exact hk.mono fun i h=> h.trans e'
 refine ⟨x,d,v,a,⟨⟨R,w⟩,?_⟩,hz⟩; intro j l e h
 obtain ⟨W,d,z,g,p⟩:=hz j l
 obtain ⟨k,u,hp⟩:= ((P.macroStep_zero.eventually (gt_mem_nhds h)).and p).exists; have hu: P.macroStep k < e:=u
 have ht:Tendsto (fun s=> (P.roomy:ℝ)*P.macroStep s) atTop (𝓝 0):=by simpa only [mul_zero] using (P.macroStep_zero.const_mul (P.roomy:ℝ))
 refine ⟨W*z^k,?_⟩; filter_upwards [w.fast.tendsto_atTop.eventually (ht.eventually (gt_mem_nhds (P.macroStep_pos k))),hp] with i p q
 have hp:(P.roomy:ℝ)*P.macroStep (v i)< P.macroStep k:= p; refine ⟨hp.trans hu, le_trans ?_ q⟩; rw [norm_smul,norm_smul]; apply mul_le_mul_of_nonneg_left _ (norm_nonneg _); apply P.beam_right_le j x _ (by rw [Apron.pivot_w,P.play_width]; exact hp.le) hu.le
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
