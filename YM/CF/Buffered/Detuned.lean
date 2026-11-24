import YM.CF.Buffered.Doppler
/-! Strengthen exponential escort of nonempty flags, including price W and per-unit expenses. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Alloy
open Function NormedSpace Filter Finset Graph Lattice Laurent Wilson Analysis Pressure Tulip Lat Cube SU Emu Rush Scree Graph RG Scroll Peaks Drapes Cascade Vault Sods Spire Paige Nova Girt Skye Kea Ember Phase Mint Mint.Roe
open scoped Topology ContDiff InnerProductSpace BigOperators Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {x y A:ℕ→ℝ}{c b w η r a e K b' v C' l s' γ μ τ H m L':ℝ}{S T:ℕ→Side}{β θ V L1 δ L:ℕ→ℝ}{J B:Side}{O:Odd J.val}{j k:ℕ}{Y:Pricing j J O (Thread j)}{P:Grasp Y B e}{hP:Pearl P}
variable {N:ℕ→Side} (D:Pic.Span hP K b' v C' l s' k) {I:∀ i,GramM (mid (N i) B)} {C Q h:ℝ}
local notation "NP"=> (fun i=> mid (N i) B)
variable (Z:WindS B N x h C r μ L' w γ c b V θ L I)
include D Z
lemma seals {X:ℕ→ℝ}(t:Gray (lum x) X) : Aqua (eur NP) fun i=>Real.exp (X i+flagT (NP i) (V i) (θ i) C-kinetic (More (NP i)) (I i).p L' (L i) (I i).beta w) /drip (I i) P:=by
 let β:=fun i=>(I i).beta; let Q:=More ∘ NP; let Z'(i):=gainS (Q i) (hemp x i); let Y'(i):= stoutY (Q i) (β i) (4*hemp x i) γ (tame x i) L' (L i); let G(i):= X i +flagT (NP i) (V i) (θ i) C; let F(i):= kinetic (Q i) (I i).p L' (L i) (β i) w; let Y:=Z.path; have he:= tc Y.rank; have hu:= t.add he (Y.mark Z.vol C Z.dark (Gray.thin he Z.loc.shrinks)); have ht:=Y.age Z.vol; have hv:= (Y.gate ht); have hp : Gray (lum x) (fun i=>G i + (-Real.log (Z' i))+-Real.log (horn (NP i) s')):=(hu.add he hv.neg).add he (Roe.hep D Z).neg -- tune Roe qualification
 let V'(i):= G i+-Real.log (Z' i)+-Real.log (horn (NP i) s')+Y' i; have hi:Aqua (lum x) fun i=> V' i * (vast x i)⁻¹:=((((Mint.frost Y.rank).fed hp he).panel (Y.plush ht L' γ Z.herb)).changeA (Eventually.of_forall fun i=> (add_mul (G i+-Real.log (Z' i)+-Real.log (horn (NP i) s')) (Y' i) ((vast x i)⁻¹)).symm))
 have hz : ∀ᶠ i in atTop,F i ≥ c*w/2*vast x i := Y.lo_cost (T:=fun i=> (I i).p) (Z.support.mono fun i e=>e.1) ht Z.herb L' Z.clip
 refine ((roughW Y.rank (by have he:=Y.pos; have ht:=Z.clip; positivity) hi hz).through he Z.vol).clip Z.tend ?_; filter_upwards [Roe.fog D Z,Z.path.helm,Roe.touch D Z] with i ⟨f,_⟩ ⟨v,_,_⟩ ⟨_,h⟩; have ha:0<horn (NP i) s':=by unfold horn; have he:=D.rP; have hp:=pinch_pos (NP i); positivity
 have hp:0< Z' i:=by unfold Z' Graph.gainS; positivity
 refine ⟨by positivity,?_⟩; let a:=horn (NP i) s'; have hl:0<Z' i *Real.exp (-Y' i)*a:=mul_pos (mul_pos hp (Real.exp_pos _)) ha
 change Real.exp (G i-F i)/_≤Real.exp (V' i-F i); refine (div_le_div_of_nonneg_left (Real.exp_pos _).le hl f).trans_eq ?_; change _ / (Z' i*Real.exp (-Y' i)*a)= _; unfold V' a; rw [Real.exp_sub,Real.exp_sub, Real.exp_add (y:=Y' i), Real.exp_add (x:=G i+-_),Real.exp_add (x:=G i),Real.exp_neg,Real.exp_neg,Real.exp_neg,Real.exp_log hp,Real.exp_log ha]; ring_nf; rw [inv_inv]; ring
-- uniform per-menu cost with length ≤ side^4. compare to full ticket.
variable {X:ℝ}
lemma allowance (Y Z':ℝ)(v:1 ≤ Y)(e:0<Z') : ∀ᶠ i in atTop, ∀ ℓ:ℕ, (ℓ:ℝ) ≤ (NP i).val^4 → Y^ℓ*Real.exp (flagT (NP i) (V i) (θ i) C-kinetic (More (NP i)) (I i).p L' (L i) (I i).beta w) ≤ drip (I i) P * Z'^ℓ := by
 let F:=fun i=> flagT (NP i) (V i) (θ i) C-kinetic (More (NP i)) (I i).p L' (L i) (I i).beta w
 let K:=|Real.log Y|+|Real.log Z'|; let X(i):= eur NP i^4*K; have he:= (seals D Z (X:=X) ((Z.vol.powG (Mint.tc Z.path.rank) 4).mul (Gray.coef (Mint.tc Z.path.rank) K))).shrinks
 filter_upwards [he.eventually (ge_mem_nhds one_pos),Roe.touch D Z] with i hx ⟨u,h⟩; intro ℓ hl
 let d:= drip (I i) P; let L₀:= ℓ * Real.log Z'; let A:= ℓ*Real.log Y; have hp:Tendsto x atTop atTop:=Z.path.rank
 change Y^ℓ * Real.exp (F i) ≤ d * _; rw [← Real.exp_log (x:=Y) (zero_lt_one.trans_le v),← Real.exp_log e,← Real.exp_nat_mul, ←Real.exp_nat_mul, ← Real.exp_add]; have hv: A ≤ X i + L₀ := by
    have hK:0 ≤ K:=add_nonneg (abs_nonneg _) (abs_nonneg _)
    have ht:A-L₀ ≤ X i:=by unfold A L₀; rw [←mul_sub]; refine le_trans (mul_le_mul_of_nonneg_left (show Real.log Y-Real.log Z'≤K from (by unfold K; linarith [le_abs_self (Real.log Y), neg_le_abs (Real.log Z')])) (show 0≤(ℓ:ℝ) by positivity)) (mul_le_mul_of_nonneg_right hl hK)
    linarith
 have hg: Real.exp (X i+F i) ≤ d:=by change _ / drip (I i) P ≤ 1 at hx; have hv:= (div_le_iff₀ h).1 hx; rw [one_mul, add_sub_assoc] at hv; exact hv
 refine (Real.exp_le_exp.mpr (show A+F i≤ X i+F i+L₀ by linarith)).trans ?_; rw [Real.exp_add]; exact mul_le_mul_of_nonneg_right hg (Real.exp_pos _).le
#print axioms allowance
end YM.CF.Buffered.Alloy
