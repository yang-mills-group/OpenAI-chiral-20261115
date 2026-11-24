import YM.SU5.Reconstruction.Vermont.Sieve
import YM.SU5.Reconstruction.Vermont.Periods
import YM.SU5.Reconstruction.Anvil.OpCoin
/-!
# Make wick correlation for separated pair of windows via script. No trailing unit.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Lens
open Function Set Filter MeasureTheory Spectral Analysis OS.Semigroup ConePrice Sail BridgeClub ContinuousLinearMap Picket
open scoped BigOperators Topology NNReal InnerProductSpace ComplexOrder
variable {H:Hilbert}{a:Axis}(S:OS.Semigroup H a) (Ω:H) {U V:Set H.Op}{u v u0 v0:ℝ≥0}
variable (d:ℝ≥0)
def score (A B:ℂ→H.Op)(z:ℂ) : ℂ:= inner ℂ Ω (A z (shifted S d z (B z Ω)))
local notation "ξ"=> score S Ω d
variable (c1:∀ t:E4,S.unit.translation t Ω=Ω)(c2:‖Ω‖=1)
namespace Meter
local notation "χ"=> S.edge
variable {A B: ℂ→H.Op}(p:WickScript S U A u u0)(q:WickScript S V B v v0)
local notation "Φ"=> score S Ω
include c1
lemma tick_lives (x:ℝ): S.edge x Ω=Ω:=by rw [← trans_time]; exact c1 _
-- independent of clock origin statement. True REAL Mink product at Wick parameter, spacetime support fixed assessed above
lemma edge_admitted (x:ℝ) (v u:ℝ≥0)(s r:ℝ) (hx:s+u+d=r) : score S Ω d A B (sideways x)=inner ℂ Ω ((stroke S A x s u) ((stroke S B x r v) Ω)):= by
 rw [score,starch, starch];
 let u₁:= A (sideways x); let v₁:=B (sideways x);
 let h₁:= χ (-(x*(s+↑u))); let h₂:=χ (x*r); let h₃:=χ (-(x*(r+↑v))); let f:= u₁ ((χ ((d:ℝ)*x)) (v₁ Ω))
 have he: h₁*h₂= χ ((d:ℝ)*x):= by unfold h₁ h₂; rw [← edge_adds,←hx,show (-(x*(s+↑u)))+x*(s+↑u+↑d)=(d:ℝ)*x from (by ring)]
 rw [shifted_side];
 change inner ℂ Ω f=inner ℂ Ω (χ (x*s) (u₁ (h₁ (h₂ (v₁ (h₃ Ω))))))
 rw [show h₃ Ω=Ω from tick_lives S Ω c1 _, show h₁ (h₂ (v₁ Ω))= _ from DFunLike.congr_fun he (v₁ Ω)]; change _=inner ℂ Ω (χ (x*s) f)
 rw [← trans_time,← adjoint_inner_left (Picket.trans S ((x*s) • basis a))];
 rw [show (trans S ((x*s) • basis _)).adjoint = trans S _ from Picket.trans_star ..]; exact congrArg (fun k=> inner ℂ k f) (c1 _).symm -- tune implicit
omit c1
include p q c2
lemma score_bound (z:ℂ) : ‖score S Ω d A B z‖≤ (u0:ℝ)*(v0:ℝ):=by
 unfold score; apply (norm_inner_le_norm ..).trans; rw [c2,one_mul]; let h:= shifted S d z; let y:= B z Ω; have ht : ‖y‖≤ v0:= ((B z).le_opNorm Ω).trans (by rw [c2,mul_one]; exact q.payee z); exact ((A z).le_opNorm (h y)).trans (mul_le_mul (p.payee z) ((h.le_opNorm _).trans ((mul_le_of_le_one_left (norm_nonneg _) (shifted_pay ..)).trans ht)) (norm_nonneg _) (by positivity))
omit c2
lemma score_cont : Continuous (score S Ω d A B):= by exact continuous_const.inner (p.with_cont _ (shifted_cont S _ _ (q.with_cont _ continuous_const)))
lemma score_glow : AnalyticOnNhd ℂ (score S Ω d A B) inside:=by
 intro z e; let p0:AnalyticAt ℂ (fun z=>(A z*(shifted S d z)*(B z))) z:= ((p.hol_paid z e).mul (shifted_hol S _ z e)).mul (q.hol_paid z e); exact (((innerSL ℂ Ω).comp (apply ℂ H.space Ω)).analyticAt _).comp p0
end Meter

variable (A B:H.Op)(C D:ℕ→ℂ→H.Op)(c:Anvil.Limited atTop (fun i=>C i 1) A)(b:Anvil.Limited atTop (fun i=> D i 1) B)
include b c
lemma spend_thin : ∀ x:H, Tendsto (fun i=> inner ℂ x (C i 1 (S.E d (B Ω)))) atTop (𝓝 (inner ℂ x (A (S.E d (B Ω))))) ∧ ∀ n,Tendsto (fun i=> inner ℂ x (C n 1 (shifted S d 1 (D i 1 Ω)))) atTop (𝓝 (inner ℂ x (C n 1 (S.E d (B Ω))))) := by
 intro x; refine ⟨c.confirms ..,fun n=>?_⟩; simp_rw [shifted_one S d,← adjoint_inner_left (C n 1),← adjoint_inner_left (S.E d)]; exact b.confirms ..
-- indep of sequence. Can choose height pairing, all cost bounds retained (don't need rearr Haar). manifest full pair recover and lower budgets.
lemma can_center : ∃ u:ℕ→ℕ,Tendsto u atTop atTop ∧ Tendsto (fun i=>score S Ω d (C i) (D (u i)) 1) atTop (𝓝 (inner ℂ Ω (A (S.E d (B Ω))))):= by
 obtain ⟨p,v⟩:= spend_thin S Ω d A B C D c b Ω
 let a(n:ℕ):= ((1:ℝ)/(n+1)); let g(n:ℕ):= inner ℂ Ω (C n 1 (S.E d (B Ω))); let f(n i:ℕ):= score S Ω d (C n) (D i) 1; choose u h e using fun n=> ((eventually_ge_atTop n).and (Metric.tendsto_nhds.mp (v n) (a n) (by unfold a; positivity))).exists
 have h0:Tendsto u atTop atTop:= tendsto_atTop_mono h tendsto_id; refine ⟨u,h0,Metric.tendsto_nhds.mpr ?_⟩
 have r:Tendsto a atTop (𝓝 0):=tendsto_one_div_add_atTop_nhds_zero_nat
 intro ε t; have p0:=half_pos t; filter_upwards [r.eventually (gt_mem_nhds p0), Metric.tendsto_nhds.mp p (ε/2) p0] with x hx k; apply (dist_triangle _ (g x) _).trans_lt; have ht: dist (score S Ω d (C x) (D (u x)) 1) (g x)< ε/2:= (e x).trans (show a x<_ from hx); linarith [(show dist (g x) _< _ from k)] -- tune
end YM.Lens
