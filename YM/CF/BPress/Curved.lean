import YM.CF.BPress.ArcCost
import Mathlib.Analysis.Asymptotics.Lemmas
/-! Four-link background cost in B-gate; also input to eq:B-Taylor. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.chord
open Filter Function Asymptotics Gauge LocalH
open scoped Topology Matrix.Norms.Frobenius InnerProductSpace ContDiff Classical
attribute [local instance] frobInner
variable {G : Gauge}
local notation "g0" => 𝓝 (0:ℝ)
local notation "gexp" => G.lieExp
local notation "idℝ" => (fun x:ℝ=>x)
variable (X Y : G.Color)
lemma smul_order (F : ℝ → ℝ) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (x:E) :
    (fun u=> F u • x)=O[g0] F:= by apply IsBigO.of_bound ‖x‖; refine Eventually.of_forall fun a=>?_ ; rw [norm_smul,mul_comm]
lemma cheap : (fun u:ℝ=> u^2) =O[g0] idℝ:= by
 apply IsBigO.of_bound 1; filter_upwards [continuous_id.continuousAt.norm (gt_mem_nhds (by simp : ‖(0:ℝ)‖ < 1))] with x h; rw [norm_pow,one_mul]; change ‖x‖<1 at h; nlinarith [norm_nonneg x]
lemma exp_price : (fun r:ℝ=>emb G (r • X)-1-r • G.colorMat X)=O[g0] fun r:ℝ=>r^2:=by
 obtain ⟨u,C,p,k,H⟩:=taylor_change _ G.exp_jet.contDiffAt G.expDiff_zero
 have he : ∀ᶠ r in g0, ‖r • X‖<u:= ((show Continuous (fun r:ℝ=> ‖r • X‖) from by fun_prop).tendsto 0).eventually (gt_mem_nhds (by simpa using p))
 refine IsBigO.of_bound (C*‖X‖^2) (he.mono fun r t=>?_ ); have e:= H _ t _ (Metric.mem_closedBall.mpr  (dist_zero_right _|>.le)) 0 (Metric.mem_closedBall_self (norm_nonneg _)); simp only [mat_one,mat_lieExp_zero,sub_zero] at e; change ‖emb G (r • X) - 1 - G.colorMat (r • X)‖≤_ at e; rw [map_smul] at e; apply e.trans_eq; rw [norm_smul,norm_pow]; ring
lemma exp_order : (fun r:ℝ=> emb G (r • X)-1)=O[g0] idℝ := by
 convert (((exp_price X).trans cheap).add (smul_order idℝ (G.colorMat X))) using 1 <;> first| rfl| (funext; simp)

def panel (r : ℝ) : G.El := gexp (r • X) * gexp (r • Y) * (gexp (r • X))⁻¹ * (gexp (r • Y))⁻¹
lemma panel_price : (fun x:ℝ=> G.mat (panel X Y x)-1-x^2 • G.colorMat (G.ad X Y))=O[g0] fun x:ℝ=>x^3:=by
 let A (u:ℝ):= gexp (u • X); let B (u:ℝ):= gexp (u • Y)
 let J:=G.ad X Y; let a(r:ℝ):=G.mat (A r)-1; let b(r:ℝ):=G.mat (B r)-1
 let x(r:ℝ):=r • G.colorMat X; let y(r:ℝ):=r • G.colorMat Y
 let j(r:ℝ):=r^2 • G.colorMat J
 have algebra (r:ℝ) : j r=x r*y r-y r*x r:=by unfold j x y J; rw [G.colorMat_ad,smul_sub]; congr 1 <;> rw [Algebra.smul_mul_assoc,Algebra.mul_smul_comm,smul_smul,sq] -- tune
 have he₁ (r:ℝ) : (G.mat (panel X Y r)-1-j r) * G.mat (B r*A r)=
         (a r*b r-x r*y r)-(b r*a r-y r*x r) - j r*(G.mat (B r*A r)-1):=by
    rw [algebra]; dsimp only [a,b]; simp only [sub_mul,mul_sub,G.mat_mul,one_mul,mul_one];
    rw [← G.mat_mul,← G.mat_mul (panel ..)]; rw [show panel X Y r * _ = A r*B r by unfold panel A B; group,G.mat_mul]; abel -- tune
 have ih {a b x y : ℝ → G.Mat} (p : (fun i=> a i-x i)=O[g0] fun i=> i^2) (q : (fun i=> b i-y i)=O[g0] fun i=>i^2) (t : x =O[g0] idℝ) (u : b=O[g0] idℝ) :
     (fun i :ℝ=> a i*b i-x i*y i)=O[g0] fun i=>i^3:= by
     simp_rw [show ∀ i, i^(3:ℕ)=(i:ℝ)^2*i from fun i=>rfl] -- maybe
     have ht: (fun i=>(a i-x i)*b i)=O[g0] fun i=>i^2*i:=p.mul u; have hk:= t.mul q
     rw [show (fun x => idℝ x * x ^ 2)=(fun x:ℝ=>x^2*x) from funext fun _=>mul_comm ..] at hk
     convert ht.add hk using 1 <;> try rfl
     funext i; rw [sub_mul,mul_sub]; abel
 have hx := smul_order (fun i:ℝ=>i^2) (G.colorMat J)
 have hy : (fun r:ℝ=> G.mat (B r*A r)-1)=O[g0] idℝ:=by
    let K : ℝ→ G.Mat:=fun r=> emb G (r • Y)*emb G (r • X)
    have hK:ContDiff ℝ ω K:=(G.exp_jet.comp (contDiff_id.smul contDiff_const)).mul (G.exp_jet.comp (contDiff_id.smul contDiff_const))
    simpa [K,A,B,emb] using (hK.differentiable (by simp : (ω:WithTop ℕ∞)≠0) 0).hasFDerivAt.isBigO_sub -- tune
 let T:= fun r:ℝ=> G.mat (panel X Y r)-1-j r
 have e : (fun i=> T i * G.mat (B i*A i))=O[g0] fun i=>i^3:=by
    have ht : (fun i=>j i * (G.mat (B i*A i)-1))=O[g0] fun i=>i^3:=hx.mul hy
    simp_rw [T,he₁]; apply IsBigO.sub _ ht; exact (ih (exp_price X) (exp_price Y) (smul_order _ _) (exp_order Y)).sub (ih (exp_price Y) (exp_price X) (smul_order _ _) (exp_order X))
 obtain ⟨C,H⟩:=e.bound; refine IsBigO.of_bound C (H.mono fun x h=>?_); rw [frob_mul_eq _ _ (G.mat_mul_star _)] at h; exact h
lemma panel_log_bound (W : Chart G) : ∃ C : ℝ, 0<C ∧ ∀ᶠ r:ℝ in g0,
    G.chord (panel X Y r)< W.δ ∧ dist (snap G (panel X Y r)) (r^2 • G.ad X Y) ≤ C* |r|^3:=by
 let A:=panel X Y; let J:= G.ad X Y; let B:=fun r:ℝ=> gexp (r^2 • J); have he:= (exp_price J).comp_tendsto (k:=fun r:ℝ=> r^2) (show Tendsto (fun r:ℝ=>r^2) g0 g0 from (by simpa using! (continuous_id.tendsto (0:ℝ)).pow 2)); -- tune
 have h2:(fun x:ℝ=> (x^2)^2)=O[g0] fun x:ℝ=> x^3:=by
   convert (isBigO_refl (fun x:ℝ=>x^2) g0).mul cheap using 1 <;> first | rfl| (funext x; ring)
 have h : (fun r:ℝ=> G.mat (A r)-G.mat (B r))=O[g0] fun r:ℝ=>r^3:=by
    convert (panel_price X Y).sub (he.trans h2) using 1 <;> try rfl
    funext x; simp [A,B,emb,J]
 obtain ⟨C,p,h⟩:=h.exists_pos; have hu (P:ℝ→G.El)(q:Continuous P)(s:P 0=1) : ∀ᶠ x:ℝ in g0, G.chord (P x)<W.δ := (G.continuous_chord.continuousAt.tendsto.comp (q.tendsto 0)).eventually (gt_mem_nhds (by rw [s,G.chord_one]; exact W.size)); refine ⟨W.C*(C/G.colorScale),mul_pos W.span (div_pos p G.colorScale_pos),?_⟩; filter_upwards [hu A (by unfold A panel; fun_prop) (by simp [A,panel]),hu B (by unfold B; fun_prop) (by simp [B]), h.bound, (show ∀ᶠ x:ℝ in g0, ‖x^2 • J‖<W.eps from (by refine ((show Continuous (fun x:ℝ=>‖x^2 • J‖) from by fun_prop).tendsto 0).eventually (gt_mem_nhds ?_); simpa using W.radius))] with x p q h l; refine ⟨p,?_⟩; refine le_trans (b:= W.C*chord (A x) (B x)) ?_ ?_
 · change dist _ (x^2 • J) ≤ _; rw [← W.unroll _ l]; exact W.fee _ _ p.le q.le
 rw [mat_eq]; exact le_trans (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right h G.colorScale_pos.le) W.span.le) (Eq.le (by rw [norm_pow]; change _= _ * ‖x‖^3; ring -- tune
     ))
end YM.CF.BPress.chord
