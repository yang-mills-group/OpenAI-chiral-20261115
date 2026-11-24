import YM.SatinExist.Cecily
import YM.SU5.FiniteGaugeData.Poin.Regal
/-!
 # Fields in the Mink axes: account on all charts.
-/
set_option autoImplicit false
set_option maxRecDepth 2400
set_option maxHeartbeats 320000
noncomputable section
namespace YM.SatinJets
open Function Filter Metric InnerProductSpace Set Complex MeasureTheory Measure
open Analysis Boundary Spectral OS OS.Semigroup
open CF.Buffered.Afterglow.Hierarchy.Seld Poin
open scoped NNReal ENNReal Topology BigOperators InnerProductSpace ComplexOrder Classical
variable {H : Hilbert}{j:Axis} (S : OS.Semigroup H j)
local notation "Λ" => 𝓝[>] (0:ℝ)
local notation "E" => elast S
local notation "D" => Bench S
local notation "K" => Cache S
local notation "T" => M S
variable (x:H)
variable {n:ℕ} (p:E4)
def regiaN : ∀ n:ℕ,(Fin n→H.Op)→(Fin n→H.Op)→E4→(Fin n→E4)→H.space
 | 0,_,_,_,_=> x
 | m+1,A,G,p,y=> T (y 0-p) (A 0 (G 0 (regiaN m (Fin.tail A) (Fin.tail G) (y 0) (Fin.tail y))))
variable (F G:Fin n→H.Op)
abbrev regia (y:Points n):= regiaN S x n F G p y.ofLp
variable {Q:Type*}[TopologicalSpace Q]
-- uniform costs
lemma regia_co {g : Q → Fin n→E4}{h : Q → E4}(s:Continuous h)(t:∀ i,Continuous (fun x=> g x i)): Continuous (fun y=> regiaN S x n F G (h y) (g y)):=by
 induction n generalizing h with
 | zero => exact continuous_const
 | succ n ih=>
   let X(q:Q):= Fin.tail (g q); let p(q:Q):= g q 0
   have he:= ih (Fin.tail F) (Fin.tail G) (g:=X) (h:=p) (t 0) (fun i=> t i.succ)
   simp only [regiaN]

   let W(i:Q):= F 0 (G 0 (regiaN S x n (Fin.tail F) (Fin.tail G) (p i) (X i))); have hU:Continuous W:=(F 0).continuous.comp ((G 0).continuous.comp he)
   change Continuous (fun i=>T (p i-h i) (W i)); let z(i:H.space×E4):= T i.2 i.1; let U(i:Q):= (W i,p i-h i); have hv: Continuous z:= step_c S
   have hg: Continuous U:= hU.prodMk (show Continuous (fun i=> p i - h i) from (t 0).sub s); rw [show (fun i=>T (p i - h i) (W i)) = z ∘ U from rfl]; exact Continuous.comp hv hg
lemma regiaC : Continuous (regia S x p F G):= regia_co S x F G (g:= fun y:Points n=> y.ofLp) (h:=fun _=>p) continuous_const (fun _=>by exact (continuous_apply _).comp (PiLp.continuous_ofLp _ _)) -- tune
lemma regia_nrm (c:ℝ)(v:∀ i:Fin n,‖F i‖* ‖G i‖ ≤ c)(w:0 ≤ c) : ∀ p:E4,∀ z:Fin n→ E4,‖regiaN S x n F G p z‖ ≤ c^n * ‖x‖:=by
 induction n with
 | zero=> intro p y; simp only [regiaN,pow_zero,one_mul]; exact le_rfl
 | succ n ih=>
   intro p y; let t:=regiaN S x n (Fin.tail F) (Fin.tail G) (y 0) (Fin.tail y); rw [regiaN,tcost]
   refine ((F 0).le_opNorm _).trans ?_; refine (mul_le_mul_of_nonneg_left ((G 0).le_opNorm _) (norm_nonneg _)).trans ?_; change ‖F 0‖* (‖G 0‖*‖t‖) ≤ _
   rw [pow_succ,←mul_assoc,mul_comm (c^n), mul_assoc c]; exact mul_le_mul (v 0) ((ih (Fin.tail F) (Fin.tail G) (fun i=> v i.succ)) _ _) (norm_nonneg _) w
lemma regia_bdd : ∃ c≥(0:ℝ),∀ p:E4,∀ y:Points n, ‖regia S x p F G y‖ ≤ c:=by
 obtain ⟨d,t⟩:=Finite.bddAbove_range (fun i=> ‖F i‖*‖G i‖); refine ⟨(max d 0)^n * ‖x‖, by positivity, fun p y=> regia_nrm S x F G (max d 0) (fun i=> le_max_of_le_left (t (mem_range_self i))) (le_max_right ..) p _⟩
variable (f:Joint n)
lemma regiaI : Integrable (fun y:Points n=> f y • regia S x p F G y):=by
 obtain ⟨c,d,v⟩:= regia_bdd S x F G; refine (f.integrable.norm.mul_const c).mono' (f.continuous.smul (regiaC S x p F G)|>.aestronglyMeasurable) (Eventually.of_forall fun y=>?_); rw [norm_smul]; exact mul_le_mul_of_nonneg_left (v p _) (norm_nonneg _)
abbrev regia_bill(f:Joint n):= ∫ y:Points n,f y • regia S x p F G y
private def rebec : Joint n→ₗ[ℂ] H.space where
 toFun:= regia_bill S x p F G
 map_add' f g:=by change (∫ _,_)=_; simp_rw [_root_.add_apply,add_smul]; exact integral_add (regiaI ..) (regiaI ..)
 map_smul' c f:=by change (∫ _,_)= c • _; simp_rw [_root_.smul_apply,smul_eq_mul,mul_smul,integral_smul]
lemma rebec_norm (f:Joint n)(c:ℝ)(h:∀ y,‖regia S x p F G y‖≤c): ‖regia_bill S x p F G f‖ ≤ ‖SchwartzMap.toLpCLM ℂ ℂ 1 volume f‖ * c:=by
 unfold regia_bill; rw [show ‖SchwartzMap.toLpCLM ℂ ℂ 1 volume f‖=∫ y,‖f y‖ from SchwartzMap.norm_toLp_one,←integral_mul_const]
 exact norm_integral_le_of_norm_le (f.integrable.norm.mul_const _) (Eventually.of_forall fun y=> by rw [norm_smul]; exact mul_le_mul_of_nonneg_left (h _) (norm_nonneg _))
def wishL : Joint n →L[ℂ] H.space:=⟨rebec S x p F G,by
 apply continuous_of_continuousAt_zero (rebec S x p F G); obtain ⟨c,v,d⟩:=regia_bdd S x F G
 apply Metric.tendsto_nhds.mpr; intro ε he
 let f:= fun g:Joint n=>‖SchwartzMap.toLpCLM ℂ ℂ 1 volume g‖ *c; have H : Continuous f:= (SchwartzMap.toLpCLM ℂ ℂ 1 _).continuous.norm.mul continuous_const; filter_upwards [(H.tendsto 0).eventually (gt_mem_nhds (show f 0<ε from by unfold f; rw [map_zero,norm_zero,zero_mul]; exact he))] with i g
 rw [map_zero,dist_zero_right]; exact lt_of_le_of_lt (rebec_norm S x p F G i c (d p)) g⟩ -- tune
lemma wishL_eq : wishL S x p F G f= regia_bill S x p F G f:=rfl
-- order variation needed!
end YM.SatinJets
