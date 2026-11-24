import YM.SU5.FiniteGaugeData.LocalLimit.Local.Projection
import YM.Push.BETA_TRANSPORT.Noise

/-! # Conditional projection kernel on a local box used for price-compactness

The summing of shared latent tags unchanged. Factorization only after that
conditioning, and `news` does not assert continuity in fine field as actual
predictors. Compactness will use treating predictions only as parameters. -/
set_option autoImplicit false
noncomputable section
namespace YM.Push.GridApprox
open RG Lattice Wilson Filter MeasureTheory Function Finset
open scoped Topology BigOperators Classical
namespace BoxGauge
variable {G:Gauge}(r:ℕ) {v t c f:Side} (S:StepData c f) (W:StepData v t) (P:Patch)(K:KernelChoices)

local notation "Γ" => Config G c
local notation "L" => credits G r
local notation "Ω" => Space G r

/-- noise product price at just the list of predicted links. Keeps the exact
normalization of the one-link density. -/
def snow (β:ℝ) (Q x:Space G r):ℂ:= ∏ i:Tab r,(noiseLink S β (Q i) (x i):ℂ)
def news (A:paper G r)(β:ℝ) (Q:Space G r):=∫ x, snow r S β Q x * A.val x ∂credits G r

lemma snow_agrees (p:S.kernel=W.kernel)(Q x:Ω)(β:ℝ) : snow r W β Q x = snow r S β Q x:=by unfold snow noiseLink StepData.penaltyWeight StepData.penaltyZ StepData.penaltyWeight; rw [p]
lemma news_agrees (p:S.kernel=W.kernel)(A:paper G r)(β:ℝ) : news r W A β = news r S A β:= by ext Q:1; unfold news; simp_rw [snow_agrees r S W p]
lemma snow_c : Continuous fun p : (ℝ × Space G r) × Space G r=> snow r S p.1.1 p.1.2 p.2 := by unfold snow noiseLink StepData.penaltyWeight; fun_prop (disch:=intro _; exact (S.penaltyZ_pos _).ne')

section price
variable (β:ℝ)(Q:Config G c)(F:paper G r)
local notation "Qp" => tabulate r c
local notation "V" => paint r c F
private lemma localized_noise (p:2*r < c.val) :
    (∫ x:Config G c,(S.noise β Q x:ℂ)* V x∂prior G c)= news r S F β (Qp Q) := by
 let J := Set.range (base r c)
 let e:Tab r ≃ {i // i∈J}:= Equiv.ofInjective (base r c) (embed_base r p)
 let g(i:Edge (Site c)) (u:G.El):ℂ:= noiseLink S β (Q i) u
 let t(i:Edge (Site c)) (u:G.El):ℂ:= if i∈J then g i u else 1
 have hg(i): Continuous (g i):=Complex.continuous_ofReal.comp (noiseLink_cont S β _)
 have hB(y): Reads J (paint r c (G:=G) y):= fun a b p=> congrArg (Subtype.val y) (funext fun m:Tab r=> p (Set.mem_range_self _))
 have he: Envelope (paint r c F):=(paid ..).1.comp_env (tab_cont r c).measurable
 have hA i : (∫ u, g i u ∂G.probHaar)=1:=(integral_ofReal (𝕜:=ℂ) (f:=noiseLink S β (Q i))).trans (by rw [noiseLink_mass]; rfl)
 let y:=Tab r
 have hV(x: Config G c): (∏ i, g i (x i))= (S.noise β Q x:ℂ):=by unfold StepData.noise; rw [Complex.ofReal_prod]; rfl
 have hW(x:Config G c): (∏ i, t i (x i))= snow r S β (Qp Q) (Qp x):=by
    let v:= univ.image (base r c)
    have h0: (∏ i∈ v,t i (x i))=∏ i,t i (x i):= prod_subset (subset_univ _) (fun i _ p=> if_neg fun u=> (by obtain ⟨j,rfl⟩:=u; exact p (mem_image_of_mem _ (mem_univ j))))
    rw [←h0,show v=univ.image (base r c) from rfl, Finset.prod_image (fun i _ j _=> fun h=> embed_base r p h),snow]; exact prod_congr rfl fun i _=> if_pos (Set.mem_range_self _)
 have hx := pi_ignores (μ:=G.probHaar) (hF:=hB F) he hA (q':=t) (fun i=>(by by_cases p:i∈J; simp only [t,if_pos p,hA]; simp [t,p])) (fun i=>Envelope.compactC (hg i)) (fun i=>Envelope.compactC (by by_cases p:i∈J ; simp only [t,if_pos p,hg] ; simp [t,p,continuous_const])) fun i p=>funext fun u=> Eq.symm (if_pos p)
 simp_rw [hV,hW] at hx
 apply hx.trans; let A:=fun u:Space G r=> snow r S β (Qp Q) u*F.val u; have hz := projection (G:=G) r c p; have ht:=integral_map (μ:=prior G c) (f:=A) hz.aemeasurable; rw [hz.map_eq] at ht
 have hr:Continuous (snow r S β (Qp Q)):= (snow_c (G:=G) r S).comp ((continuous_const (y:=(β,(Qp Q)))).prodMk continuous_id)
 exact (ht (hr.measurable.mul ((paid r F).1.meas) |>.aestronglyMeasurable)).symm

-- comparability with whole-system back
private lemma sense : Envelope (fun u:Config G c=>(S.noise β Q u:ℂ)* (paint r c F u)) := by
  have hz:Continuous (S.noise β Q):=by unfold StepData.noise StepData.penaltyWeight; fun_prop 
  exact (Envelope.compactC (Complex.continuous_ofReal.comp hz)).mulC ((paid r F).1.comp_env (tab_cont r c).measurable)

lemma localized (x:Config G f)(p:2*r < c.val) :
 back S β (paint r c F) x= ∑ t:S.Choices,(S.likelihood x t:ℂ) * news r S F β (tabulate r c (S.prediction x t)):=by
 unfold back; simp_rw [StepData.density,Complex.ofReal_sum,Finset.sum_mul,Complex.ofReal_mul,mul_assoc]; rw [integral_finsetSum]; swap
 · intro i _; apply Integrable.const_mul; exact (sense r S β (S.prediction x i) F).integrableC _
 simp_rw [integral_const_mul,localized_noise r S β _ F p]

lemma tariff (h:S.patch.Branches S.kernel G)(p:2*r < c.val){w:ℝ} (v:∀ U:Space G r, ‖news r S F β U‖ ≤ w)(z: Config G f) :
    ‖back S β (paint r c F) z‖ ≤ w:= by
 rw [localized r S β F z p]; apply (norm_sum_le ..).trans
 calc
   _ ≤ ∑ t:S.Choices,S.likelihood z t * w:= by
       apply sum_le_sum; intro i _; rw [norm_mul,Complex.norm_real, Real.norm_of_nonneg (S.likelihood_pos _ _)]; exact mul_le_mul_of_nonneg_left (v _) (S.likelihood_pos _ _)
   _ = _:= by rw [←sum_mul,S.chosen h,one_mul]
end price
end BoxGauge
end YM.Push.GridApprox
