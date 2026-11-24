import YM.SU5.Same.TemperScout
set_option autoImplicit false
set_option maxHeartbeats 380000
noncomputable section
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000

namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection

open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase
     MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound
     Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker
     ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy
     Tapestry Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn

open CF.Velvet CF.Pannier.Chancel
open Spine Pitching.Focus
open QuadClock
open Aria Casting MacroGrid Preparation.Yoke Yoke.Travel

open SatinNucleus Six
namespace Spine
/-! # From regular ballots to the *limiting* kernel
    the regular ballot eventual statement alone would have no meaning
    independent of those instruments. This is the assertion of growth at 0.
-/
variable (P:Spine)(x:P.Spectrum0 3)(j:Axis)
variable (g r:ℕ)(v:ℕ→ℕ)(a:ℕ→(ℕ×ℕ)→ℝ)(d:StrictMono v)(q:ℕ→ Coalition)
local notation "κ" j:max=> P.advocate 3 x j
variable (V:∀ j:Axis,List Axis→ℝ→ P.ColorHil j (P.advocate 3 x j))
local notation "C₁"=> P.cinema x g r v a q d
variable (t:ℝ)(l:List Axis)
lemma beamVoteLater (i:ℕ) (u:P.roomy * P.macroStep (v i) ≤ t) : P.beamRaw j x (((C₁) i).pivot P l) t= ∑ k∈ (q i).voters, ((q i).w k:ℂ) • ((P.rewardK g r:ℂ) • ((a (i+k) (g,r):ℂ) • P.beamWatch j x g (v (i+k)) l t)):=by
 unfold cinema; rw [P.pleading_p x j _ _ _ _ _ _ _ t l u]; apply sum_congr rfl; intro k h; rw [Complex.ofReal_mul,mul_smul, Complex.ofReal_mul,mul_smul]
lemma at_vote_price {B:ℝ}(Z:Radiates P x (P.cinema x g r v a q d) V)(e:0<t)(p:∀ᶠ i:ℕ in atTop, ‖(a i (g,r):ℂ) • P.beamWatch j x g (v i) l t‖≤ B) :
  ‖V j l t‖ ≤ ‖(P.rewardK g r:ℂ)‖*B:=by
 obtain ⟨s,u⟩:=eventually_atTop.mp p
 refine le_of_tendsto (Z.cash j l t e).norm ?_
 filter_upwards [eventually_ge_atTop s,(Z.slender j).eventually (gt_mem_nhds e)] with i h w
 let A(n:ℕ):= ‖(a (i+n) (g,r):ℂ) • P.beamWatch j x g (v (i+n)) l t‖
 let Y(k:ℕ):= (P.rewardK g r:ℂ) • ((a (i+k) (g,r):ℂ) • P.beamWatch j x g (v (i+k)) l t)
 let K:= q i; let z:= ‖(P.rewardK g r:ℂ)‖
 have he:P.roomy*P.macroStep (v i)≤ t:= (P.pleading_w x j ..).ge.trans (show ((C₁) i).realWidth P j < t from w).le
 rw [P.beamVoteLater x j g r v a d q t l i he]; change ‖∑ k∈K.voters,(K.w k:ℂ) • Y k‖≤ z*B; apply (norm_sum_le ..).trans
 calc ∑ k∈K.voters, ‖(K.w k:ℂ) • Y k‖ ≤ ∑ k∈K.voters,K.w k*(z*B):= by
         apply sum_le_sum; intro k t
         unfold Y; rw [norm_smul,norm_smul,Complex.norm_real,Real.norm_of_nonneg (K.signed k t)]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (u (i+k) (by omega)) (norm_nonneg _)) (K.signed k t)
      _ = z*B:=by rw [← sum_mul,K.pledges,one_mul]

lemma rising_bill (Z:Radiates P x (P.cinema x g r v a q d) V)(e:AtGlassRate P x j g r l v a) :
   ∃ M≥(0:ℝ),∃ K≥(1:ℝ), ∀ᶠ k:ℕ in atTop, ‖V j l (P.macroStep k)‖≤ M*K^k:=by
 obtain ⟨M,u,K,h,p⟩:=e; let c:=‖(P.rewardK g r:ℂ)‖; refine ⟨c*M,mul_nonneg (norm_nonneg _) u,K,h,p.mono fun i q' =>?_⟩; rw [mul_assoc]; exact P.at_vote_price x j g r v a d q V _ l Z (P.macroStep_pos i) q'

local notation "ℓ"=> (P.par.R.L.val:ℝ)
-- any tick price. using next even after initial threshold `s` from vote estimate.
private lemma tick_purchase (s:ℕ)(e:ℝ)(u:0<e)(t:e≤P.macroStep s): ∃ k:ℕ, s ≤ k ∧ P.macroStep k ≤ e ∧ e ≤ ℓ* P.macroStep k:=by
 obtain ⟨n,h,p⟩:= ((eventually_ge_atTop s).and (P.macroStep_zero.eventually (gt_mem_nhds u))).exists
 have he: ∃ d:ℕ, P.macroStep (s+d) ≤ e:= ⟨n-s,by rw [Nat.add_sub_of_le h]; exact (show _<_ from p).le⟩
 let a:= Nat.find he
 have hp:P.macroStep (s+a) ≤ e:= Nat.find_spec he
 refine ⟨s+a,Nat.le_add_right ..,hp,?_⟩
 by_cases b:a=0
 · rw [b, add_zero]; exact t.trans (le_mul_of_one_le_left (P.macroStep_pos s|>.le) (le_of_lt (by exact_mod_cast ((timeMesh P.par).Llarge))))
 obtain ⟨y,hy⟩:=Nat.exists_eq_succ_of_ne_zero b
 have hb:y < Nat.find he:=show y<a from by rw [hy]; omega
 have ht:e< P.macroStep (s+y):=lt_of_not_ge (Nat.find_min he hb)
 rw [hy, show s+y.succ=s+y+1 by omega]; exact ht.le.trans_eq ((show ℓ*P.macroStep (s+y+1)=P.macroStep (s+y) by simpa only [Nat.add_sub_cancel_left,pow_one] using P.daysF (s+y+1) (s+y) (Nat.le_succ _)).symm)

-- on any Hilbert profiles. End uses ket priced at most t^-m for later
-- spectral argument. Defined independently of limiting V for later users.
def TemperedAtEdge(H:Hilbert)(X:ℝ→H) : Prop:= ∃ m:ℕ,∃ C≥(0:ℝ),∀ t:ℝ,0<t→t≤1→ t^m* ‖X t‖ ≤ C
-- fill to 0. doesn't commute height and t-limits.
lemma acquired_edge (H:Hilbert) (X:ℝ→H) {M K:ℝ}(p:0≤M)(u:1≤K) (h: ∀ᶠ k:ℕ in atTop, ‖X (P.macroStep k)‖≤ M*K^k)(e:AntitoneOn (fun x=> ‖X x‖) (Set.Ioi 0)) : TemperedAtEdge H X := by -- order?
 obtain ⟨s,w⟩:=eventually_atTop.mp h -- name?
 have he:1<ℓ:= by exact_mod_cast (timeMesh P.par).Llarge
 let a:=P.macroStep 0
 obtain ⟨m,u'⟩:= ((tendsto_pow_atTop_atTop_of_one_lt he).eventually_ge_atTop K).exists
 let B:= P.macroStep s; let C:= M*(ℓ*a)^m
 have hp:0≤C:=mul_nonneg p (pow_nonneg (mul_nonneg (zero_le_one.trans he.le) (P.macroStep_pos _|>.le)) _)
 refine ⟨m,max C ‖X B‖, hp.trans (le_max_left ..),fun t q r=>?_⟩
 rcases le_or_gt t B with hx|hx
 · obtain ⟨k,hk,f,ht⟩:= P.tick_purchase s t q hx
   let L':=P.macroStep k
   have hL:0<L':= P.macroStep_pos k
   have hv: (ℓ*L')^m * (ℓ^m)^k=(ℓ*a)^m:=by
      have hf: L'*ℓ^k=a:=by rw [mul_comm]; simpa only [Nat.sub_zero] using P.daysF k 0 (Nat.zero_le k)
      rw [←pow_mul, Nat.mul_comm m k,pow_mul,← mul_pow,mul_assoc,hf]
   calc t^m* ‖X t‖ ≤ (ℓ*L')^m * (M*(ℓ^m)^k):=mul_le_mul (pow_le_pow_left₀ q.le ht m) ((e hL q f).trans ((w _ hk).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (zero_le_one.trans u) (show K≤ℓ^m from u') k) p))) (norm_nonneg _) (pow_nonneg (mul_nonneg (zero_le_one.trans he.le) hL.le) _)
        _ = C := by rw [mul_left_comm, hv]
        _ ≤ _:= le_max_left ..
 exact le_trans ((mul_le_of_le_one_left (norm_nonneg (X t)) (pow_le_one₀ q.le r)).trans (e (P.macroStep_pos s) q hx.le)) (le_max_right ..)

variable {P x V}
lemma Radiates.monotone_norm {Y:ℕ→P.Apron}(Z:Radiates P x Y V){j:Axis}{l:List Axis} : AntitoneOn (fun t=> ‖V j l t‖) (Set.Ioi 0):=by
 intro t u s q h; dsimp only; rw [Z.choir j l (show 0<t from u) h]; let S:= P.physicalEnergy j (P.advocate 3 x j); exact ((S.E (s-t).toNNReal).le_opNorm (V j l t)).trans (mul_le_of_le_one_left (norm_nonneg _) (S.shrinks _)) -- order AntitoneOn

def PoweredHeat(P:Spine)(x:P.Spectrum0 3)(V:∀ j:Axis,List Axis→ℝ→ P.ColorHil j (P.advocate 3 x j)): Prop := ∀ j l, TemperedAtEdge (P.ColorHil j (P.advocate 3 x j)) (V j l)
variable (P x V)
lemma cinema_powers (e: ∀ j l,AtGlassRate P x j g r l v a) (Z:GalaxyShow P x g r (P.cinema x g r v a q d) V): PoweredHeat P x V:=by
 intro j l; obtain ⟨M,u,K,v',f⟩:=P.rising_bill x j g r v a d q V l Z.heat (e j l); exact P.acquired_edge _ _ u v' f Z.heat.monotone_norm
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms Spine.cinema_powers
