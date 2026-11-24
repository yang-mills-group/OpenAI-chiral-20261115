import ZecaBerry
import ZecaColor
import SatinThinVisit
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option synthInstance.maxSize 28000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
namespace Spine
open Aria Casting Six OS.Semigroup.Balloon


open MacroGrid SatinNucleus
variable (P:Spine)(x:P.Spectrum0 3)(j:Axis)
local notation "ξ"=> P.advocate 3 x j
variable (f r n:ℕ) (A:Coalition) (v:ℕ→ℕ)(u:StrictMono v)(a:ℕ→ℝ)
local notation "V" k:max=>v (n+k)
local notation "F" i:max=> P.basePlay x f i
-- sum with max and base n

local notation "s₀"=> parliament n A v
local notation "U"=> (F (v n)).zoom P s₀
local notation "Fh"=> fun k:ℕ=> P.basePlay x f (V k)
local notation "A'"=> fun (k:ℕ) => A.w k * (P.rewardK f r * a (n+k))
local notation "B" A:max=> P.pleading x f r n A v a u -- check order
lemma pleading_coin(p d:ℝ)(l:List Axis)(h:P.roomy * P.macroStep (v n) ≤ p)(g:P.roomy * P.macroStep (v n) ≤ d): P.ruby j ξ ((B A).pivot P l) 0 p d= ∑ i∈ A.voters, (((A.w i * (P.rewardK f r * a (n+i)) : ℝ) : ℂ)) • P.ruby j ξ ((F (V i)).pivot P l) 0 p d:= P.pivot_ruby_exact j ξ Fh A.voters (U) (s₀) _ _ _ (A') l p d ((P.base_wg x j f n A v).le.trans h) ((P.base_wg x j f n A v).le.trans g) -- check args!


section
variable {S:Type*}[NormedAddCommGroup S][NormedSpace ℂ S]{y:ℕ→S}
lemma voter_pay (d:Coalition)(z:ℕ→S){c:ℝ}(p:∀ k∈d.voters, ‖z k‖≤c):
 ‖∑ i∈d.voters, (d.w i:ℂ) • z i‖≤c:=by
 refine le_trans (norm_sum_le ..) (le_trans (sum_le_sum (g:=fun i=>d.w i*c) fun i h=>?_) ?_)
 · rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg (d.signed _ h)]
   exact mul_le_mul_of_nonneg_left (p i h) (d.signed _ h)
 rw [←sum_mul,d.pledges,one_mul]
lemma voter_budget(q:ℕ→ Coalition){c:ℝ}(p:∀ᶠ i in atTop, ‖y i‖ ≤ c):
 ∀ᶠ i in atTop, ‖∑ k∈(q i).voters, ((q i).w k:ℂ) • y (i+k)‖ ≤ c:=by
 obtain ⟨n,t⟩:=eventually_atTop.mp p
 filter_upwards [eventually_ge_atTop n] with i e
 exact voter_pay (q i) (fun k=>y (i+k)) (fun k _=> t _ (e.trans (Nat.le_add_right _ k))) -- trans'

lemma voter_tendsto (q:ℕ→ Coalition){z:S}(p:Tendsto y atTop (𝓝 z)):
 Tendsto (fun i=>∑ k∈(q i).voters, ((q i).w k:ℂ) • y (i+k)) atTop (𝓝 z):=by
 apply Metric.tendsto_nhds.mpr; intro ε h

 have m:∀ᶠ i in atTop,‖y i-z‖ ≤ ε/2:=(Metric.tendsto_nhds.mp p _ (half_pos h)).mono fun i e=> ((dist_eq_norm (y i) z).symm.trans_le e.le)
 filter_upwards [voter_budget (y:=fun i=>y i-z) q m] with i v
 rw [dist_eq_norm]
 simp_rw [smul_sub] at v
 have k : ∑ k∈(q i).voters, ((q i).w k:ℂ)=1:=by rw [← Complex.ofReal_sum,(q i).pledges, Complex.ofReal_one]
 rw [sum_sub_distrib,←sum_smul,k,one_smul] at v
 exact v.trans_lt (half_lt_self h)
end
lemma Glaze_LocalFieldBounds.voters {S:Hilbert}{d:ℕ→S.Op}{e:S.Op}
   (h:Glaze_LocalFieldBounds S atTop d e)(q:ℕ→ Coalition):
 Glaze_LocalFieldBounds S atTop (fun i=>∑ k∈(q i).voters, ((q i).w k:ℂ) • d (i+k)) e:=by
 obtain ⟨c,b,p⟩:=h.fee
 refine ⟨⟨c,b,voter_budget q p⟩, fun z=>(voter_tendsto q (h.seeks z)).congr (fun i=>?_ )⟩
 rw [_root_.sum_apply]
 simp only [_root_.smul_apply]

structure Afterimage (P:Spine)(x:P.Spectrum0 3)(Y:ℕ→P.Apron):Prop where
 dye(j:Axis)(l:List Axis):∃ D,NibLine P j (P.advocate 3 x j) D (fun i=>(Y i).pivot P l) 1

variable (y:ℕ→ℕ×ℕ→ℝ)(q:ℕ→ Coalition){C E:ℝ}
lemma sky_cinema
 (p:Skyways P f r E C (P.rewardK f r) v y)
 (k:P.NightCop): Afterimage P x (P.cinema x f r v y q u):=by
 let Y:=P.cinema x f r v y q u
 let c(i:ℕ):=P.roomy * P.macroStep (v i)
 have he:Tendsto c atTop (𝓝 0):=
    mul_zero (P.roomy:ℝ) ▸ ((P.macroStep_zero.comp u.tendsto_atTop).const_mul (P.roomy:ℝ))
 constructor
 intro j l
 obtain ⟨D,h⟩:=P.berry_bundle j x l (P.folding x p k)
 refine ⟨D,h.pay,?_,?_⟩
 · exact he.congr (fun i=>((Apron.pivot_w _ P (Y i) l).trans (P.pleading_w ..)).symm)

 intro o a₁ hp hc
 refine ((h.dye o a₁ hp hc).voters q).congr' ?_
 let z:P.Spectrum0 j:= P.advocate 3 x j
 filter_upwards [he.eventually (ge_mem_nhds hp),he.eventually (ge_mem_nhds hc)] with i d e
 rw [Pi.one_apply,one_smul,show P.cinema x f r v y q u i=P.pleading x f r i (q i) v (fun n=>y n (f,r)) u from rfl,
      P.pleading_coin _ _ _ _ _ _ _ u _ _ _ _ d e]
 exact sum_congr rfl (fun k _=>by simp only [Complex.ofReal_mul,mul_smul])
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.sky_cinema
