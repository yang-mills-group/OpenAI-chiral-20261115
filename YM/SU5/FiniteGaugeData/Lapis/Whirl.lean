import YM.SU5.FiniteGaugeData.Lapis.Syl
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 20000
set_option linter.flexible false
set_option quotPrecheck false
noncomputable section
namespace YM.SU5.FiniteGaugeData.Lapis
open Function Finset Filter MeasureTheory Matrix Lattice Wilson RG Precision Tree Pressure Laurent Bloch
open Next.Fluctuations Next.SectorChange Next.SectorChange.Gaussian
open Drachma Affiche Galope Avenue Galope.Press Wrist Poeme Haute Punch Affiche Lantern Lantern.Cup RouteM Rally Syl
open scoped Topology InnerProductSpace Matrix MatrixOrder RealInnerProductSpace ContDiff BigOperators NNReal ENNReal Kronecker Classical
namespace Dig
section complete
variable {G:Gauge} {J:ChartRatio G} {I:Type}[Fintype I][DecidableEq I] {c:ℝ}
theorem thrill{C K A₁:ℝ}(L:Lucent J c C)(p:0≤C)  -- dimension tune even empty
 (F:LinkArray G I→ℝ)(hF: Envelope F)(g:coin (I×G.ColorIndex)→ℝ)(hg:Integrable g)(hx:(∫ x,g x)≤A₁)(hp:∀ x,0≤g x)(hK:0≤K)(budget:∀ v:LinkArray G I,F v≠0 → ∃ x: LogArray G I, release 1 x=v ∧ (∀ i,‖x i‖≤c) ∧ F v≤K*g (tape.symm x)) :
 (∫ v,F v ∂piHaar G I) ≤ ((J.scale*C)^Fintype.card I*K)*A₁ :=by
 have he(v:LinkArray G I)(hx: v∉ covered J (1:LinkArray G I)) : F v=0:=by
    by_contra hP; obtain ⟨x,r,t,b⟩:=budget _ hP; apply hx; rw [←release_image]; exact ⟨x,fun i _=> Metric.mem_ball.mpr (by rw [dist_zero_right]; exact (t i).trans_lt L.guard_l),r⟩
 let f(x:LogArray G I):= g (tape.symm x); let P:=(J.scale*C)^Fintype.card I; let v : LogArray G I→ℝ:= (mouth J).indicator (fun y=>Next.SectorChange.pay J y * F (release (1:LinkArray G I) y))
 obtain ⟨V,hi⟩:=release_integral L.chart (1:LinkArray G I) F hF.meas.stronglyMeasurable he; have hr:Integrable f:= tape_volume.symm.integrable_comp_of_integrable hg; let q : Integrable v:= V.mp (hF.integrable _)
 have hv:0≤P:= pow_nonneg (mul_nonneg L.chart.scale.le p) _
 have h0(x:LogArray G I): 0 ≤ P*K*f x:= mul_nonneg (mul_nonneg hv hK) (hp _)
 have h1: ∀ x:LogArray G I, v x≤ P*K*f x :=by
    intro x; unfold v; by_cases h: x∈ mouth J; swap; · rw [Set.indicator_of_notMem h]; exact h0 x
    rw [Set.indicator_of_mem h]; by_cases r:F (release 1 x)=0; · rw [r,mul_zero]; exact h0 x
    obtain ⟨B,hb,A₀,q⟩:= budget (release 1 x) r; have hu:B=x:= release_injOn L.chart 1 (fun i _=>Metric.mem_ball.mpr (by rw [dist_zero_right]; exact (A₀ i).trans_lt L.guard_l)) h hb; subst B
    rw [mul_assoc]; let k:=Next.SectorChange.pay J x; exact ((_root_.mul_le_mul_of_nonneg_left q (show 0≤k from prod_nonneg fun i _=> mul_nonneg L.chart.scale.le (L.chart.pos _ (h i (Set.mem_univ _))).le)).trans (_root_.mul_le_mul_of_nonneg_right (cameo L p x A₀) (mul_nonneg hK (hp _)))) -- tune
 rw [hi]; calc
    _ ≤ ∫ x,P*K*f x:= integral_mono q (hr.const_mul _) h1
    _ ≤ (P*K)*A₁:= by rw [integral_const_mul]; apply mul_le_mul_of_nonneg_left _ (mul_nonneg hv hK); exact (tape_volume.symm.integral_comp' g).le.trans hx
end complete
variable {n: Side}{G: Gauge}{Z: Finset (Site n)} {M w k:ℕ} {C κ K α L β a Δ μ g:ℝ} {p:BudgetPoint}{P:Bed}{u:Stage}{R:PathData G} {S:Arms G u} {A:Finset (Cell n)} {F:Portion n G→ℝ}{J':ChartRatio G}{ε:ℝ}
local notation "α'" => heightK p M
local notation "η" => bonusK p u β
local notation "I" => buy Z k
local notation "J" => Plush G (buy Z k)
local notation "E" => Portion n G
-- Evaluate total stencil. direct comparison adjustable by rough-tiles tax & allowance.
abbrev fine(n:Side)(ε:ℝ):ℝ:= ε* tileC n
abbrev allowance(p:BudgetPoint)(u:Stage)(A:Finset (Cell n))(β ε:ℝ) := fine n ε+ (A.card:ℝ)* (bonusK p u β/8)
-- Boat conditional for ANY qualifying marks; mark amount not raw.O. Condition p actual.Attains permits all here.
def Boat (Q:Config G n→ℝ)(W:R.Bounds u.clip u.width u.paths Δ)(B:Attached P R)(p:BudgetPoint)(F:Portion n G→ℝ)(A:Finset (Cell n))(Z:Finset (Site n))(M k w:ℕ)(κ β ε:ℝ):Prop := ∀ (V:Config G n)(g:Site n→ G.El)(X: LogField G n),
 (∀ i: Cell n,i∈A↔p.threshold < G.chord (faceValue V i))→ ‖X‖≤ heightK p M→ (∀ i∈RoomsM M Z,gauge g V i= represent X i) → Q V ≤ F ((κ*Real.sqrt β)•heatC (billsC k w Z) W B X)+allowance p u A β ε
variable (T: Attains S J' n p β α μ M k w)(hz:Z⊆ glow A M) (D:Floor P u.clip n a C)(w0:0<a)(W:R.Bounds u.clip u.width u.paths Δ)(B:Attached P R)(O:Ocean G (buy Z k))
local notation "r'"=> gross w u β α
abbrev rent(n:Side)(L:ℝ):=8*L^2*(tileC n:ℝ)
lemma recoil(x:ℝ)(hp:0≤x)(u:0≤L)(q:0≤β)(v:|κ|≤2)(t:α ≤1/2) :
  L*units n * (‖κ*Real.sqrt β‖*x) ≤ rent n L + ((1-α)*β/2)*x^2:=by
 let f:=units n; let s:=Real.sqrt β; have hs:0 ≤ s:=Real.sqrt_nonneg _; have hv:=mul_le_mul_of_nonneg_right v hs; have hxs:=Real.sq_sqrt q
 apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by rw [norm_mul,Real.norm_of_nonneg (Real.sqrt_nonneg _)]; exact (show ‖κ‖*Real.sqrt β≤ 2*s from hv) : ‖κ*Real.sqrt β‖≤2*s) hp) (mul_nonneg u (unitZ _))).trans
 calc
    _ ≤ 4*(L*f)^2+(s*x)^2/4:=by change L*f*(2*s*x) ≤_; nlinarith only [sq_nonneg (4*L*f-s*x)]
    _ ≤ _:=by unfold f s rent; rw [mul_pow, unit_sq, mul_pow, hxs]; have h1:= mul_le_mul_of_nonneg_right t (mul_nonneg q (sq_nonneg x)); nlinarith only [h1,mul_nonneg (sq_nonneg L) (show 0 ≤ (tileC n:ℝ) from Nat.cast_nonneg _)] -- tune
-- Need preserve norm^2 residual of projected row fit. Strength of WP16 offer here.
local notation "ZK"=> zodiac P G (buy Z k)
local notation "H"=> heatC (billsC k w Z) W B
local notation "M'"=> primeShare w u
include D
lemma true_offer (hm:k≤M)(U:Z⊆zones n M)(g:LogField G n):∃ y:coin J,∀ x:coin J, let V:=kickC I (x+y); let z:=H (g+kickC I x); accepts u R (billsC k w Z) (g+ kickC I x) ≥ (1-M')*dotProduct (x+y) (ZK *ᵥ (x+y))+‖z-H V‖^2:=by
 let L:= keyM G I; let V:= LinearMap.range ((H).comp L); let K:= V.starProjection; obtain ⟨y,hy⟩:=show K (H g)∈ V from V.starProjection_apply_mem _; change H (L y)=K (H g) at hy; refine ⟨y,fun x=>?_⟩; dsimp only
 have hv: H (L (x+y))=K (H (g+L x)):=by simp only [map_add, show K (H (L x))=H (L x) from Submodule.starProjection_eq_self_iff.mpr (show H (L x)∈V from ⟨x,rfl⟩),hy]; rw [_root_.add_comm (H (L x))]
 have hx:= mirror_era (w:=w) hm U W B D (x+y)
 rw [← attainedE _ W B] at hx ⊢
 let t:=H (g+ L x)
 change _ ≤ ‖t‖^2; change _+ ‖t-H (L (x+y))‖^2 ≤ _; change (1-M')*dotProduct _ (ZK *ᵥ _) ≤ ‖H (L (x+y))‖^2 at hx; rw [hv] at hx ⊢; apply (add_le_add_left hx _).trans_eq; change ‖V.starProjection t‖^2 + ‖t-V.starProjection t‖^2 = ‖t‖^2; have hz:= V.norm_sq_eq_add_norm_sq_starProjection t; rw [V.starProjection_orthogonal, ContinuousLinearMap.sub_apply,ContinuousLinearMap.id_apply] at hz; exact hz.symm
end Dig
end YM.SU5.FiniteGaugeData.Lapis
