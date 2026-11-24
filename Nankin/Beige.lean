import Nankin.Cluster
import Taffeta.Stigma
import Rods.Fold
import YM.SU5.FiniteGaugeData.Tower.Baggage
import YM.SU5.FiniteGaugeData.Pannier.FeastDay
set_option autoImplicit false
set_option maxHeartbeats 550000
set_option synthInstance.maxSize 28000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower
open Function Filter Metric NormedSpace Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark
namespace Calico
open Py.Dyad Work.E08 AnalyticBridge.VerifiedReset StressFlux PlaqAxes
variable {L:Side}{F r v j:ℕ}
open VacuumSelection Py.Dyad Keeping ThinGauge
-- extraction envelope.(Finance etc external, caller chooses matrix even off-regulator from large reservoir by continuing one solution; C↓ all i). abstract subseq for every height-fixed view. D only for r; application r=v-1. 
abbrev Bills(f v r:ℕ)(L:Side)(C D:ℕ→ℝ):Prop:= (∀ i,f≤ i → i<v→Niche L (C i) 0) ∧∀ i,f ≤ i → i<r→ Niche L (C i) (D i)
lemma NiceLimit {x y:ℕ→ℝ}{a b:ℝ}(h:∀ᶠ i:ℕ in atTop, Niche L (x i) (y i))(H:Tendsto x atTop (𝓝 a))(t:Tendsto y atTop (𝓝 b)): Niche L a b:=by
 let B:= invmain * Xη L^4
 have u(i:ℕ)(p:Niche L (x i) (y i)):1 ≤ B*|x i|:=by
    have l:= mul_le_mul_of_nonneg_right p.back (abs_nonneg (x i)); rw [←abs_mul,inv_mul_cancel₀ p.non,abs_one] at l; exact l
 have hc:Tendsto (fun n=>|x n|) atTop (𝓝 |a|):= H.abs
 have hn:1 ≤ B*|a|:=le_of_tendsto_of_tendsto tendsto_const_nhds (hc.const_mul B) (h.mono u)
 have hx:a≠0:=by intro V; rw [V,abs_zero,mul_zero] at hn; norm_num at hn
 refine ⟨hx,le_of_tendsto hc (h.mono fun i p=>p.amp),le_of_tendsto (t.abs) (h.mono fun i p=>p.tax),le_of_tendsto ((H.inv₀ hx).abs) (h.mono fun i p=>p.back)⟩
lemma squeezeR {x y:ℕ→ℕ→ℝ}(T:r≤v)(P:∀ i:ℕ,Bills F v r L (x i) (y i)):
 ∃ (a:ℕ→ℕ)(C D:ℕ→ℝ), StrictMono a ∧ Bills F v r L C D ∧ (∀ k,F ≤ k → k<v → Tendsto (fun i=>x (a i) k) atTop (𝓝 (C k)))∧ (∀ k,F≤ k→k<r→ Tendsto (fun i=>y (a i) k) atTop (𝓝 (D k))):=by
 let B:=|Bmain / Xη L ^4|+1
 let fx(g:ℕ→ℕ→ℝ)(v:ℕ)(i:ℕ)(k:ℕ):ℝ:= if F ≤ k ∧k<v then g i k else 0
 let g(i:ℕ):=(fx x v i, fx y r i)
 let A:= Set.univ.pi (fun _:ℕ=>Set.Icc (-B) B)
 let U:IsCompact A:=isCompact_univ_pi (fun _=>isCompact_Icc)
 have hb:1 ≤B:= by unfold B; have u:=abs_nonneg (Bmain / Xη L ^4); linarith
 have q' (i:ℕ) : g i ∈ A ×ˢ A:=by
    constructor <;> intro k k0 <;> change (if F ≤ k ∧ k< _ then (_:ℕ→ℕ→ℝ) i k else 0)∈Set.Icc (-B) B
    · split; rename_i h
      · apply abs_le.mp; exact ((P i|>.1 k h.1 h.2).amp).trans ((le_abs_self _).trans (le_add_of_nonneg_right zero_le_one))
      exact abs_le.mp (abs_zero.trans_le (zero_le_one.trans hb))
    split; rename_i h
    · apply abs_le.mp; exact (P i|>.2 k h.1 h.2).tax.trans ((by norm_num : (1:ℝ)/8≤1).trans hb)
    exact abs_le.mp (abs_zero.trans_le (zero_le_one.trans hb))
 obtain ⟨c,t,a,h,t'⟩:= (U.prod U).tendsto_subseq (x:=g) q'; let C:=c.1; let D:=c.2
 have hp(k:ℕ)(e:F≤k)(y:k<v):Tendsto (fun i=>x (a i) k) atTop (𝓝 (C k)):=by simpa [fx,e,y,g,C,Function.comp_def] using tendsto_pi_nhds.mp ((continuous_fst (X:=ℕ→ℝ) (Y:=ℕ→ℝ)).continuousAt.tendsto.comp t') k
 have ht(k:ℕ)(e:F≤k)(u:k<r):Tendsto (fun i=>y (a i) k) atTop (𝓝 (D k)):=by simpa [fx,e,u,g,D,Function.comp_def] using tendsto_pi_nhds.mp ((continuous_snd (X:=ℕ→ℝ) (Y:=ℕ→ℝ)).continuousAt.tendsto.comp t') k
 exact ⟨a,C,D,h,⟨fun i e u=>NiceLimit (Eventually.of_forall (fun n=> P (a n)|>.1 i e u)) (hp i e u) tendsto_const_nhds,
   fun i e u=>NiceLimit (Eventually.of_forall (fun n=>P (a n)|>.2 i e u)) (hp i e (u.trans_le T)) (ht i e u)⟩,hp,ht⟩
#check Niche
#check Filter.Tendsto.abs
#check invmain
-- hGain, revenue continuity (filter eventual upwards)
lemma gains {x:ℕ→ℕ→ℝ}{C:ℕ→ℝ}(v j:ℕ)(p:∀ k,j ≤ k→ k < v → Tendsto (fun i=>x i k) atTop (𝓝 (C k))) (h:j≤v): Tendsto (fun i=> hGain (x i) v j) atTop (𝓝 (hGain C v j)):=by
 rcases h.eq_or_lt with u|e; · subst j; simpa [gain_here] using (show Tendsto (fun _:ℕ=>(1:ℝ)) atTop (𝓝 1) from tendsto_const_nhds)
 simp_rw [gain_step _ _ _ e]
 exact (p _ le_rfl e).mul (gains v (j+1) (fun k h u=>p k (by omega) u) e)
termination_by v-j
decreasing_by omega
lemma revenues(L:Side){x y:ℕ→ℕ→ℝ}{C D:ℕ→ℝ}(v j:ℕ)(p:∀ k,j ≤ k→ k<v → Tendsto (fun i=>x i k) atTop (𝓝 (C k)))(q:∀ k,j ≤ k→ k<v→Tendsto (fun i=>y i k) atTop (𝓝 (D k)))(h:j ≤v):Tendsto (fun i=>revenue L (x i) (y i) v j) atTop (𝓝 (revenue L C D v j)):=by
 by_cases t:j<v
 · have p'(k:ℕ)(l:j+1≤k):=p k (by omega)
   have hx:=gains (x:=x) v (j+1) p' t; have hy:= q j le_rfl t
   have he:=revenues L v (j+1) p' (fun i u=>q i (by omega)) t
   conv in revenue L (x _) _ v j=> rw [revenue,if_pos t]
   rw [revenue,if_pos t]; exact he.add ((hy.mul hx).div_const _)
 conv in revenue L (x _) _ v j=> rw [revenue,if_neg t]
 rw [revenue,if_neg t]; exact tendsto_const_nhds
termination_by v-j
decreasing_by omega
#print axioms squeezeR
end Calico
end YM.CF.Buffered.Afterglow.Tower
