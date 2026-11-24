import YM.CF.Mint.Rate
set_option autoImplicit false
noncomputable section
namespace YM.CF.Mint
open Function NormedSpace Filter Finset Graph Lattice Laurent Wilson Analysis Pressure Tulip Lat Cube SU Emu Rush Scree Graph RG Scroll Peaks Drapes Cascade Vault Sods Spire Paige Nova Girt Skye Kea Ember
open scoped Topology ContDiff InnerProductSpace BigOperators Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {x y A:ℕ→ℝ}{c b w η r a e K b' v C' l s' γ μ τ H m L':ℝ}{S T:ℕ→Side}{β θ V L1 δ L:ℕ→ℝ}{J B:Side}{O:Odd J.val}{j k:ℕ}{Y:Pricing j J O (Thread j)}{P:Grasp Y B e}{hP:Pearl P}
-- nonuniform sequences. loop exponent update tracks budget. 
namespace Roe
variable {N:ℕ→Side} (D:Pic.Span hP K b' v C' l s' k) {I:∀ i,GramM (mid (N i) B)} {C Q h:ℝ}
local notation "NP"=> (fun i=> mid (N i) B)
variable (Z:WindS B N x h C r μ L' w γ c b V θ L I)
include D Z
omit D Z in
lemma rootA (t:Tendsto A atTop atTop)(p:Aqua A x)(v:∀ᶠ i in atTop,0<x i)(e:0<k) : let F(i):=(x i)^((k:ℝ)⁻¹); (∀ᶠ i in atTop,0<F i ∧ F i^k=x i)∧ Aqua A F:=by
 intro F; have hk : k≠0:=Nat.ne_zero_of_lt e; have hc : (k:ℝ)≠0:=by exact_mod_cast hk
 have he : ∀ᶠ i in atTop,0<F i∧F i^k=x i:= v.mono fun i h=>⟨Real.rpow_pos_of_pos h _,by unfold F; rw [←Real.rpow_natCast (_^(_ :ℝ)), ←Real.rpow_mul h.le, inv_mul_cancel₀ hc,Real.rpow_one]⟩
 refine ⟨he,fun n=>?_⟩; let V(i):= A i^n * F i; have hu:Tendsto (fun i=> V i^k) atTop (𝓝 0):=(p (n*k)).congr' (he.mono fun i h=> by change _*x i= V i ^ k; unfold V; rw [mul_pow,h.2,pow_mul])
 let c:ℝ:= (k:ℝ)⁻¹; have hc':0<c:=by unfold c; positivity
 have hV:Tendsto (fun i=> (V i^k) ^ c) atTop (𝓝 0):= (by simpa [Real.zero_rpow hc'.ne'] using (hu.rpow_const (p:=c) (Or.inr hc'.le))) -- tune param
 apply hV.congr'; filter_upwards [he,t.eventually_gt_atTop 0] with i ⟨e,q⟩ h; change (V i ^ k)^ c=V i; rw [←Real.rpow_natCast (V i), ← Real.rpow_mul (show 0≤ V i by unfold V; positivity),mul_inv_cancel₀ hc,Real.rpow_one]
lemma caesar:∃ T:ℕ→ℝ,Aqua (eur NP) T∧∀ᶠ i in atTop,CoolR D (N i) (T i) (I i).p.threshold:=by
 obtain ⟨u,b,t,p,Q'⟩:= manyK (B:=B)
 let S:= tame x; let E:=eur NP; let M:= fun i=>More (NP i); let y(i):=eur M i^2 * (tame x i) * b⁻¹
 have hV := Z.vol; let W:= Z.path; have hx : Aqua E y:=by
    have he:= tc W.rank; exact (((Aqua.fed (damp W.rank) ((W.age hV).powG he 2) he).pays (Gray.coef he b⁻¹) he).through he hV)
 have hz:∀ᶠ i in atTop,0<y i:= W.infl.mono fun i h=>by unfold y; have hp:=h.2.2.1; have hv:0<eur M i:=nPos (M i); positivity
 obtain ⟨e,A⟩:= rootA Z.tend hx hz t; let T :=fun i=> y i ^ ((u:ℝ)⁻¹)
 have hp:=A 10; let B1:= b'/(2 * poseX); have hC:=D.pos; have hX:0<B1:=by unfold B1; have he:=pose_p; positivity
 refine ⟨T,A,?_⟩; filter_upwards [Z.tend.eventually_ge_atTop k,e,A.shrinks.eventually (ge_mem_nhds one_pos), hp.eventually (ge_mem_nhds (lt_min D.xP one_pos)), (hp.const_mul C').eventually (ge_mem_nhds (by simpa using hX : C'*0< B1)),Z.support,W.infl] with i hi ⟨v,e⟩ t x a w u'; refine ⟨v,t,Nat.cast_le.mp hi,x,?_,fun U g=>?_⟩; -- tune shadow
 · unfold duty; rw [zero_mul,add_zero,mul_assoc]; exact a
 apply Q' _ U (I i).p.threshold (T i) ((I i).p.threshold_pos) g v t; rw [show T i^_ = _ from e,w.1]; unfold y eur M; rw [mul_comm b, inv_mul_cancel_right₀ p.ne']
end Roe
end YM.CF.Mint
