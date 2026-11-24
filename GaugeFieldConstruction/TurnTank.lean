import GaugeFieldConstruction.Tongs
import GaugeFieldConstruction.Spree
/-! # Projection budgets for monomials on actual covariance space. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 25000
noncomputable section
namespace YM.Gleam.Guide
open Function Lattice MeasureTheory Finset RG Wilson Tree Filter Metric Exterior Precision Next.Rank.Spindle Pressure Work.F03 Next.SectorChange Next.SectorChange.Gaussian
open Fineness Matrix Module Regis Regis.Head ProbabilityTheory
open scoped Matrix BigOperators Classical ContDiff Topology MatrixOrder ENNReal Kronecker Matrix.Norms.Frobenius
variable {c n : Side}{r:Ratio c n}{T:Forest r}{G:Gauge}{p:BudgetPoint}{q:Clip}{v t η C S w δ β κ ξ Λ:ℝ}{U:Config G n}{A:Support c}{o x z:Site n}{f m:ℕ} {X V D:Dir G n}{R:Rules G} {Z:PathData G}{b:Cell n}{H:Bed}{F:Finset T.Free}{J: ChartRatio G}
variable (B:Z.Bounds q η C S) (P:Attached H Z)(L:Floor H q n δ w)
open CF.BProof (coin coin_scale coin_mul coin_pow scaleY)
open CF.BProof.PricePort Gleam.clocks
open CF.Rue (FleetS shoreK)
open CF.Scree (pingS)
variable (s: Signed)(γ:Site n) {K:Support n}{W D':Flaws n}{E:T.Slice G}
namespace Hood
variable {f' l:ℕ}{R' D₀:ℝ}
-- rotor action module.
lemma lead_jibA (L:Tick n G): let c:= (L.leadSA q s γ).comp (stamen B P n).starProjection; ‖c‖≤ longR q:=by
 intro f; apply ContinuousLinearMap.opNorm_le_bound f (by unfold longR; have hp:= q.quadratic_pos; positivity); intro x; let X:=(stamen B P n).starProjection x; exact ((L.leadSA q s γ).le_opNorm X).trans (mul_le_mul (Tick.paysA s γ L) (pod_star ..) (norm_nonneg _) (by unfold longR; have hp:=q.quadratic_pos; positivity))
variable (T₀:List (Tick n G))
lemma θ_ballA(a:ℝ)(h:1≤a)(t:T₀.length ≤ m):
 let F(x:Altar G n):=factorV T₀ (fun i=>parcel a (i.θSlotA q s γ x))
 ContDiff ℝ 1 F ∧ ∀ x,|F x|≤(2*a)^m:=by
 have hp:0<a:=zero_lt_one.trans_le h; intro F
 constructor
 · unfold F; clear t; induction T₀ with
   | nil=> exact contDiff_const
   | cons i l ih=> exact ((parcel_diff a).comp (i.leadSA q s γ).contDiff).mul ih
 intro i; exact (factor_v _ _ (fun j _=>(parcel_cost hp _).1) (by positivity)).trans (pow_le_pow_right₀ (by linarith only [h]) t)
lemma factor_θA (X Y:Altar G n)(p:T₀.length ≤ l)(t:∀ i∈T₀, i.Compass K f)(a:ℝ)(h:1≤ a) : let Z(i:Tick n G)(x:Altar G n):=parcel a (i.θSlotA q s γ x); let k(y):=factorV T₀ (fun i=> Z i y)
   |k X-k Y| ≤ lipΔ q a l * bayColour (signX K s γ) (X-Y):=by
 intro Z k; let W:= longR q * bayColour (signX K s γ) (X-Y); have he(a):0≤ bayColour (signX K s γ) (a: Altar G n):= shade_b ..
 have hp:0≤W:=by unfold W longR; have h:=he (X-Y); have ht:=q.quadratic_pos; positivity
 have hg:∀ i∈T₀, |Z i X-Z i Y| ≤ Rpod*W:=by
    intro i v; refine (parcel_lip (zero_lt_one.trans_le h) _ _).trans (mul_le_mul_of_nonneg_left ?_ (by positivity)); rw [← Tick.lead_θA,←Tick.lead_θA,← map_sub]; exact Tick.leaderA s γ i (t i v) _
 exact (factor_var T₀ _ _ (show 1≤2*a by linarith only [h]) (by positivity) (fun i v=> (parcel_cost (zero_lt_one.trans_le h) _).1) (fun i v=> (parcel_cost (zero_lt_one.trans_le h) _).1) hg p).trans_eq (by unfold pileU W lipΔ; ring)
lemma spin_θA (k:ℝ→ℝ) : factorV T₀ (fun d=> k (d.spinner q (tiler B P (bank s γ X))))=factorV T₀ (fun d=> k (d.θSlotA q s γ (tiler B P X))):=by unfold factorV; simp_rw [Tick.bank_θA]
abbrev factor_RA (T₀: List (Tick n G))(a:Altar G n)(q:Clip)(z:Signed)(γ:Site n)(k:ℝ→ℝ):=factorV T₀ (fun d=>k (d.θSlotA q z γ a))
lemma cuts_θA (g:ℝ→ℝ)(h:Continuous g)(a:ℝ)(p:∀ x,|x|≤a → g x=x)(b:∀ x,|g x|≤|x|)(u:T₀.length ≤ f) : let f₁(x:Altar G n):=factor_RA T₀ ((stamen B P n).starProjection x) q s γ
 let μ:=stdGaussian (Altar G n)
 Integrable (fun x=> f₁ x g) μ∧ Integrable (fun x=>f₁ x id) μ ∧ |∫ x,f₁ x g ∂μ|≤ domeP (longR q) 1 f ∧ |∫ x,f₁ x id ∂μ|≤ domeP (longR q) 1 f ∧ |(∫ x,f₁ x g∂μ)-(∫ x,f₁ x id∂μ)|≤ 2*domeP (longR q) 2 f * Real.exp (-a):=by
 intro Z M; let L:= T₀.map (fun T=> (T.leadSA q s γ).comp (stamen B P n).starProjection); have he(K x) : Z x K=factorV L (fun i=>K (i x)):=by unfold Z L factorV factor_RA; simp only [factorV,List.map_map]; rfl
 let k:=longR q; have ht(i)(p:i∈L): ‖i‖≤ k:=by obtain ⟨u,p,rfl⟩:=List.mem_map.mp p; exact lead_jibA ..
 have hp:0≤k:=by unfold k longR; have h:=q.quadratic_pos; positivity
 have hv:L.length ≤ f:=by rw [show L.length=T₀.length from List.length_map _]; exact u
 obtain ⟨ha,v⟩:= shelter_v g h b k hp L ht hv; obtain ⟨hx,w⟩:= shelter_v id continuous_id (by simp) k hp L ht hv; simp_rw [he]; exact ⟨ha,hx,v,w,cuts g h a p b k hp L ht hv⟩

lemma onChartA (Light:LightM r W D' m (signX K s γ))(pW: W=misdemean t U)(h:TrustLogs (V+D) U r (grid_break r D') v)(u:0≤ v)(e:v≤R.c)(l:T₀.length ≤ l)(p:∀ i∈T₀,i.Compass K f)(k:f ≤ m) -- hazard l shadow implicit
 {a b:ℝ}(h0:1≤ a)(pK:Real.sqrt β*t+Real.sqrt β*slotError R f v ≤ a)(hB:Real.sqrt β*slotError R f v ≤ b): let y:= starOf B P r (grid_break r D') W m D β V
   |factorV T₀ (fun i=> Real.sqrt β*i.raw (pull s γ U))-factor_RA T₀ y q s γ (parcel a)| ≤ pileU (2*a) b (T₀.length):=by
 intro y; let Z(i:Tick n G):=Real.sqrt β*i.raw (pull s γ U); let Y(i:Tick n G):= i.θSlotA q s γ y; let c:= Real.sqrt β*slotError R f v
 have he:∀ i∈T₀,|Z i| ≤ Real.sqrt β*t:=fun i v=> abs_mul .. |>.le.trans (by rw [abs_of_nonneg (Real.sqrt_nonneg _)]; exact mul_le_mul_of_nonneg_left (Tick.raw_costA s γ i (p i v) pW Light) (Real.sqrt_nonneg _)) -- tune
 have hg: ∀ i∈T₀, |Z i-Y i|≤c:= fun i v=> Tick.angle_SA B P s γ i Light (p i v) h u e k
 have hc:0 ≤ c:=by unfold c slotError faceCutError; have hl:=G.colorScale_pos; have hl':=R.positive; positivity
 have hx:∀ i∈T₀,parcel a (Y i)=Y i:=fun i v=>parcel_id (zero_lt_one.trans_le h0) ((show |Y i| ≤ |Z i|+ |Z i-Y i| from (by rw [abs_sub_comm]; nth_rw 1 [show Y i= Z i + (Y i-Z i) by ring]; exact abs_add_le ..)).trans ((add_le_add (he i v) (hg i v)).trans pK))
 apply factor_var T₀ _ _ (show 1≤2*a by linarith) (hc.trans hB) (fun i v=> (he i v).trans (by unfold c at hc; linarith only [pK,h0,hc])) (fun i v=>(parcel_cost (zero_lt_one.trans_le h0) _).1) (fun i v=>?_) (le_refl _); rw [show parcel a (i.θSlotA q s γ y)=_ from hx i v]; exact (hg i v).trans hB
end Hood
end YM.Gleam.Guide
end
