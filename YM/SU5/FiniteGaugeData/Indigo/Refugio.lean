import YM.SU5.FiniteGaugeData.Eight.Melt
import YM.SU5.FiniteGaugeData.Indigo.Creme
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 410000
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Eight
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Window.Brique
open Reed (Fine)
attribute [local instance] opCStarAlgebra
set_option quotPrecheck false
open Heat Quest Fock.Brique
open Nacre Heat Charm Chrono Journey
open Py Py.Rate LocalLimit Preparation Journey Fiber Vale VolumeCape FullBill
open SalonG
open Quest.Chaperone
open Steam
variable {Λ: Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(h:Real.exp 1 ≤ Λ.x)
variable {u v:ℕ→ℕ}{I:ℕ→ Family (tent Y h)→ℕ→ℂ}{E:ℕ→ Family (tent Y h)→ℂ}
variable (K:Universal Y h u v I E){P:Call Λ l}{J:Wicket Λ l}(R:Rolled Y h u v J P)
variable (A:∀ i:Axis, Repertory Y h K R i)
open Hills Tint
variable (S T:Finset Cover)(s i k:ℕ) {g α C D ε θ C₀:ℝ}
local notation "Kₜ"=> tent Y h
local notation "N"=> side Y i s
local notation "U"=> W (tent Y h)
local notation "Ω"=> (Y.voyage i).CapeT s
local notation "E₁"=> W (tent Y h)→ₗ[ℂ]ℂ
variable {a:Axis}{d w n m:ℕ}{x f:W (tent Y h)}{vD:Axis→ℕ}(L:Master Y s i)(lP:Club Y g s)
namespace Bonbon
open Steam.Indigo Window Window.Steve Next.Rank
variable (r:ℝ)
local notation "T'"=> ((Y.voyage i).X (Y.uv k)).gram s
local notation "y"=> hat Λ.R.L Λ.x s
abbrev cool_ι (Λ:Preparation)(s:ℕ):= strength Λ.K.top.clip/8 * Real.sqrt (hat Λ.R.L Λ.x s)
abbrev μX (Λ:Preparation)(s:ℕ)(r:ℝ):= r/cool_ι Λ s
local notation "t"=> μX Λ s r
local notation "F"=> Glints
local notation "M"=> More N
-- housekeeping
include Y
lemma riseY : 0< hat Λ.R.L Λ.x s:=lt_of_lt_of_le zero_lt_one (Y.oneP.trans (Vale.crown ..))
lemma boostP: 0 < cool_ι Λ s:=mul_pos (div_pos (strength_pos _) (by norm_num)) (Real.sqrt_pos.mpr (riseY Y s))
include lP
private lemma inflame(u:s≤Y.uv k) (d:ℝ)(e:0≤d) : 2* cool_ι Λ s*d ≤ d/((2*soaked (T').beta)/strength (T').funds):=by
 let W:=lP.full i k u; have hp:0<(T').beta:=(W.stamp.budget _ W.member).2.2.1; let β:= (T').beta; let D:=Real.sqrt β; let U':= cool_ι Λ s; let F':=strength Λ.K.top.clip; have he:0<F':=strength_pos _; have hD:0<D:=Real.sqrt_pos.mpr hp; let Y':=y; have hx:0<Y':= riseY Y s
 have hv:Real.sqrt (y)≤2*D:=le_of_sq_le_sq (by rw [Real.sq_sqrt hx.le,mul_pow,show D^2=(T').beta from Real.sq_sqrt hp.le]; linarith only [hp,(W.member.1 : Y'/2≤β)]) (by positivity)
 rw [show (T').funds= _ from W.clip_p, div_div_eq_mul_div]; change _≤ d*F'/(2*D⁻¹); rw [show 2*D⁻¹=2/D from (div_eq_mul_inv ..).symm, div_div_eq_mul_div]; unfold cool_ι; nlinarith only [mul_le_mul_of_nonneg_left hv (show 0 ≤ F'*d from mul_nonneg he.le e)] -- hv change budget.use variables shadow?
private lemma φGrowth (u:s≤Y.uv k)(I:Pane (N))(X:Support (More N)): (↑(glitches X (μX Λ s r) I).card:ℝ)*r≤ Window.basal (T') (soaked (T').beta) I/2:=by
 let Q:=lP.full i k u; let V:= glitches X (t) I
 let ξ:=(2*soaked (T').beta)/strength (T').funds; have hv:0≤ξ:=by unfold ξ soaked; have hp:= (Q.stamp.budget _ Q.member).2.2.1; have h:= strength_pos (T').funds; positivity
 let f(i:Face (Per (More N))):= SU.group.chord (faceValue I i); have hm(i):0≤ f i:=SU.group.chord_nonneg _; let γ(i):=f i/ξ
 have hz(i':Face (Per M))(k':i'∈ V): 2*r≤ γ i':=by
    apply (inflame Y s i k lP u _ (hm i')).trans' -- k shadow fix
    have hz:t < f i':=(mem_filter.mp (mem_filter.mp k').1).2
    let p:= (div_lt_iff₀ (boostP Y s)).1 hz; linarith -- use multiplication.
 rw [le_div_iff₀ (by norm_num : (0:ℝ)<2)]; change (V.card:ℝ)*r*2≤ ∑ i':Face (Per M), γ i'; apply le_trans _ (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ V) (fun i _ _=> div_nonneg (hm i) hv)); apply (Finset.sum_le_sum (f:=fun i=>2*r) hz).trans'; rw [sum_const,nsmul_eq_mul]; exact (show _≤_ from le_of_eq (by ring))
lemma ledger (u:s≤Y.uv k)(e:(Y.voyage i).kick≤k)(c:0≤C)(v:0≤ r): LedgerT Y s i k (fairy (μX Λ s r) (side Y i s)) 1 C (C*Real.exp (-r)) (slopeZ Λ.W g) :=by
 intro X p n Y' H k₀ z h
 let T:= (Y.voyage i).CapeT s; let Γ:= C*Real.exp (-r); have hG:0≤Γ:=mul_nonneg c (Real.exp_pos _).le; let f:= Y' ∘ drawn T; let P₀:=T'; apply Fore lP f (pow_nonneg hG _) e u -- baron
 intro x; by_cases hp:f x=0; · unfold Marks.read; change ‖inner ℂ _ (acts (f x) _)‖≤ _; rw [hp,act_zero,inner_zero_right,norm_zero]; positivity -- tune
 let β:=cool_ι Λ s; have hm:= φGrowth Y s i k lP r u x.1 X; have hξ:n ≤ (glitches X (t) x.1).card:= show _ from (k1 p n k₀ ▸ (z (drawn T x) hp)); -- ▸
 apply (Marks.read_within f x _).trans; apply (mul_le_mul (h (drawn T x)) ((lP.full i k u).budget x) (norm_nonneg _) (pow_nonneg c _)).trans; rw [mul_pow,mul_assoc]; apply mul_le_mul_of_nonneg_left _ (pow_nonneg c _); rw [←Real.exp_nat_mul,← Real.exp_add]; apply Real.exp_monotone; unfold Steam.τplus; let d:=υ Λ.K.top.clip (y) x.1; have he:0≤d:=mul_nonneg (Nat.cast_nonneg _) (frost_nn _ _ (riseY Y s).le); nlinarith only [hm,mul_le_mul_of_nonneg_right (show (n:ℝ) ≤ (glitches X (t) x.1).card from by exact_mod_cast hξ) v,he] -- hm and he defs!
 where k1(p n:ℕ)(h:p*2=1*n):n=p+p:=by omega
#print axioms ledger
end Bonbon
end YM.CF.Buffered.Afterglow.Hierarchy.Eight
