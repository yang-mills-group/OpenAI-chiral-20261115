import YM.CF.Mint.Flit
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
lemma hep: Gray (lum x) fun i=>Real.log (horn (NP i) s'):=by
 let P:= eur NP; let p:=Z.vol; let x':=lum x; let v:= fun i=> Real.log (P i) -- edit
 have he:= tc Z.path.rank; let W:= fun k=> Gray.coef he k
 have hP : Gray x' v:= p.higher (Z.tend.eventually_ge_atTop 1|>.mono fun i u=>by change ‖Real.log (P i)‖ ≤P i; rw [Real.norm_of_nonneg (Real.log_nonneg u)]; exact Real.log_le_self (show 0 ≤ P i from zero_le_one.trans u)) -- tune
 have ht:= ((W (45:ℝ)).mul (Z.vol.powG he 4)).mul (Gray.add he (W (Real.log s')) ((W (2:ℝ)).mul (Gray.add he (W (Real.log Real.pi)) hP.neg)))
 apply ht.eqK; apply Eventually.of_forall; intro i; have hp:= Z.vol; have hx:=D.rP; have hg:0 <pinch (NP i):= Ember.pinch_pos _; unfold horn; change 45*P i^4*(Real.log s'+2*(Real.log Real.pi+ -(v i)))=_; dsimp only; rw [Real.log_pow,Real.log_mul hx.ne' (by positivity), Real.log_pow,pinch,Real.log_div (by positivity) (by positivity)]; unfold v P eur; push_cast; ring
-- budgets integrated all basis tests cost paid RAPID. relate to drip.
lemma touch : ∀ᶠ i in atTop,0<Graph.angle (I i) ∧0<drip (I i) P:=by filter_upwards [fog D Z,Z.path.helm] with i ⟨p,h⟩ ⟨e,v,y⟩; refine ⟨h,lt_of_lt_of_le ?_ p⟩; unfold gainS horn; have he:=D.rP; have hx:= pinch_pos (NP i); positivity
lemma ride: Aqua (eur NP) fun i=>Real.exp (flagT (NP i) (V i) (θ i) C-kinetic (More (NP i)) (I i).p L' (L i) (I i).beta w) /drip (I i) P:=by
 let β:=fun i=>(I i).beta; let Q:=More ∘ NP; let Z'(i):=gainS (Q i) (hemp x i); let Y'(i):= stoutY (Q i) (β i) (4*hemp x i) γ (tame x i) L' (L i); let G(i):= flagT (NP i) (V i) (θ i) C; let F(i):= kinetic (Q i) (I i).p L' (L i) (β i) w; let Y:=Z.path; have he:= tc Y.rank; have hu:= Y.mark Z.vol C Z.dark (Gray.thin he Z.loc.shrinks); have ht:=Y.age Z.vol; have hv:= (Y.gate ht); have hp : Gray (lum x) (fun i=>G i + (-Real.log (Z' i))+-Real.log (horn (NP i) s')):=(hu.add he hv.neg).add he (hep D Z).neg
 let V'(i):= G i+-Real.log (Z' i)+-Real.log (horn (NP i) s')+Y' i; have hi:Aqua (lum x) fun i=> V' i * (vast x i)⁻¹:=((((frost Y.rank).fed hp he).panel (Y.plush ht L' γ Z.herb)).changeA (Eventually.of_forall fun i=> (add_mul (G i+-Real.log (Z' i)+-Real.log (horn (NP i) s')) (Y' i) ((vast x i)⁻¹)).symm))
 have hz : ∀ᶠ i in atTop,F i ≥ c*w/2*vast x i := Y.lo_cost (T:=fun i=> (I i).p) (Z.support.mono fun i e=>e.1) ht Z.herb L' Z.clip
 refine ((roughW Y.rank (by have he:=Y.pos; have ht:=Z.clip; positivity) hi hz).through he Z.vol).clip Z.tend ?_; filter_upwards [fog D Z,Z.path.helm,touch D Z] with i ⟨f,u⟩ ⟨v,g,w⟩ ⟨t,h⟩; have ha:0<horn (NP i) s':=by unfold horn; have he:=D.rP; have hp:=pinch_pos (NP i); positivity
 have hp:0< Z' i:=by unfold Z' gainS; positivity; -- tune
 refine ⟨by positivity,?_⟩; let a:=horn (NP i) s'; have hl:0<Z' i *Real.exp (-Y' i)*a:=mul_pos (mul_pos hp (Real.exp_pos _)) ha
 change Real.exp (G i-F i)/_≤Real.exp (V' i-F i); refine (div_le_div_of_nonneg_left (Real.exp_pos _).le hl f).trans_eq ?_; -- tune a def
 change _ / (Z' i*Real.exp (-Y' i)*a)= _; unfold V' a; rw [Real.exp_sub,Real.exp_sub, Real.exp_add, Real.exp_add (x:=G i+-_),Real.exp_add,Real.exp_neg,Real.exp_neg,Real.exp_neg,Real.exp_log hp,Real.exp_log ha]; ring_nf; rw [inv_inv]; ring -- tune neg
end Roe
end YM.CF.Mint
