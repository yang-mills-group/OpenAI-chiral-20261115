import GaugeFieldConstruction.Avast
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction.Wick.Yacht
open StressFHeat MeasureTheory Analysis Function Filter Metric Maxwell Finset Gap Complex Cauchy Row Phys
open scoped Topology ContDiff BigOperators
variable {α β:Type*}(D: Axis→ Module.End ℂ (J α)){L: Axis→ Module.End ℂ (J β)}(p:Bil α β)(a:J α)(b:J β)
variable (H G:HopeC E4)
def boon (n:ℕ):J α:=∑ i:Φ n, (∫ u,(dock u i:ℂ)∂H.μ) • tower D a n i
def Wane (n:ℕ)(t:ℝ):J α:=∑ i∈range (n+1),(tariff t i:ℂ) • boon D a H i
lemma B0 :boon D a H 0=a:=by simp [boon,tower,dock]
lemma stampP (n:ℕ)(t:ℝ)(Z:J α→ₗ[ℂ]ℂ): (∫ x,Z (Tapper D a n t x)∂H.μ)=Z (Wane D a H n t):=by
 have hx(i:ℕ):ContinuousOn (fun u=> (tariff t i:ℂ)*Z (gust D a i u)) H.site:=continuousOn_const.mul (outerS D a (fun _=>Z) continuousOn_id (fun _=>continuousOn_const) i) -- tune
 unfold Tapper Wane; simp_rw [map_sum,map_smul,smul_eq_mul]; rw [integral_finsetSum _ (fun i _=>span_v H _ (hx i))]; apply sum_congr rfl; intro i _; rw [integral_const_mul]; refine congrArg _ ?_; unfold boon gust; simp_rw [map_sum,map_smul,smul_eq_mul]; rw [integral_finsetSum]; · simp_rw [integral_mul_const];
 intro i v; exact (span_c H (v:=(show Continuous fun u:E4=>(dock u i:ℂ) from by unfold dock; fun_prop))).mul_const _ -- tune
lemma bankC (d:E4)(n:ℕ)(t:ℝ): (∫ u:E4×E4,port p d (Tapper D a n t u.1) (Tapper L b n t u.2) ∂(H.pairs G).μ)= port p d (Wane D a H n t) (Wane L b G n t):=by
 rw [show (H.pairs G).μ=H.μ.prod G.μ from rfl,integral_prod]; · simp_rw [stampP]; exact stampP D a H n t ((port p d).flip (Wane L b G n t))
 apply span_v (H.pairs G); apply stalag D a (u:=fun x:E4×E4=>x.1) (t:=fun _:E4×E4=>t) (f:=fun x:E4×E4=>(port p d).flip (Tapper L b n t x.2)) continuousOn_fst _ continuousOn_const n; intro v
 exact stalag L b (u:=fun x:E4×E4=>x.2) (t:=fun _:E4×E4=>t) (f:=fun _=>port p d v) continuousOn_snd (fun _=>continuousOn_const) continuousOn_const n -- tune defeq
variable (hI:Lefty p D)(g:Rorky p L)
-- early safe field support
def PathsZ (K:Set E4)(d:E4)(t:ℝ) :Prop:=∀ u∈H.site,∀ v∈ G.site,∀ r∈Set.Icc 0 t,d+r • (v-u)∈ K
lemma rebate (m:ℕ){K:Set E4}(k:IsCompact K)(v:0∉K)(hI:Lefty p D)(g:Rorky p L): ∃ C>0,∀ (t:ℝ)(d:E4),t ∈ Set.Icc 0 1→ PathsZ H G K d t → ‖ (∫ x:E4×E4, port p (d+t • (x.2-x.1)) a b ∂(H.pairs G).μ)- port p d (Wane D a H m t) (Wane L b G m t)‖ ≤ C*t^(m+1):=by
 obtain ⟨C,B,N⟩:= Fundsν.borne D p a b m hI g k G.k H.k v; refine ⟨C,B,?_⟩; intro t d s z
 let P:=H.pairs G; let F(x:E4×E4):=port p d (Tapper D a m t x.1) (Tapper L b m t x.2); let f(x:E4×E4):=port p (d+t • (x.2-x.1)) a b
 have he: Integrable f P.μ:= span_v P _ (fun ⟨a',b'⟩ l=> ((Gap.healthy (p a b) (x:=d+t • (b'-a')) (fun h=>v (h ▸ z a' l.1 b' l.2 t ⟨s.1,le_rfl⟩))).continuousAt.comp (x:=(a',b')) (f:=fun x:E4×E4=>d+t • (x.2-x.1)) (by fun_prop)).continuousWithinAt)
 rw [←bankC D p a b H G]; change ‖(∫ u,f u∂P.μ)-(∫ v,F v∂P.μ)‖≤_; rw [← integral_sub he]; · apply (norm_integral_le_of_norm_le (integrable_const (C*t^(m+1))) (P.onA.mono fun i w=> N d i.1 i.2 w.1 w.2 t s.1 s.2 (z i.1 w.1 i.2 w.2))).trans; simp
 apply span_v P; apply stalag D a (u:=fun x:E4×E4=>x.1) (t:=fun _:E4×E4=>t) (f:=fun x:E4×E4=>(port p d).flip (Tapper L b m t x.2)) continuousOn_fst _ continuousOn_const m; intro v
 exact stalag L b (u:=fun x:E4×E4=>x.2) (t:=fun _:E4×E4=>t) (f:=fun _=>port p d v) continuousOn_snd (fun _=>continuousOn_const) continuousOn_const m
end YM.GaugeFieldConstruction.Wick.Yacht
end
