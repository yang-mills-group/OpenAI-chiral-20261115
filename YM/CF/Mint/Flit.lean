import YM.CF.Mint.Gust
set_option autoImplicit false
noncomputable section
namespace YM.CF.Mint
open Function NormedSpace Filter Finset Graph Lattice Laurent Wilson Analysis Pressure Tulip Lat Cube SU Emu Rush Scree Graph RG Scroll Peaks Drapes Cascade Vault Sods Spire Paige Nova Girt Skye Kea Ember
open scoped Topology ContDiff InnerProductSpace BigOperators Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {x y A:ℕ→ℝ}{c b w η r a e K b' v C' l s' γ μ τ H m L':ℝ}{S T:ℕ→Side}{β θ V L1 δ L:ℕ→ℝ}{J B:Side}{O:Odd J.val}{j k:ℕ}{Y:Pricing j J O (Thread j)}{P:Grasp Y B e}{hP:Pearl P}
-- nonuniform sequences. loop exponent update tracks budget. 
namespace Roe
variable (N:ℕ→Side)
local notation "midP"=> (fun i=>mid (N i) B)
structure WindS (B:Side)(N:ℕ→Side)(x:ℕ→ℝ)(h C r μ L' w γ c b:ℝ)(v η Y:ℕ→ℝ)(S:∀ i,GramM (mid (N i) B)): Prop where
 path:RangeH x (fun i=>(S i).beta) c b
 vol : Gray (lum x) (eur (fun i=>mid (N i) B))
 tend:Tendsto (eur (fun i=>mid (N i) B)) atTop atTop
 loc:Aqua (eur (fun i=>mid (N i) B)) v
 dark:Gray (lum x) η
 herb:Gray (lum x) Y
 bold:1≤ h
 wind:0<r
 size:0≤C
 clip:0<w
 row:0≤ L'
 support: ∀ᶠ i in atTop, let W:=S i; let T:= W.p
               T.threshold=tame x i ∧ Ledger h (v i) (η i) r C W ∧ W.path.Bounds W.funds μ L' (Y i)∧ w≤ W.funds.linear ∧W.funds.direct ≤γ∧ 0≤v i
variable {N} (D:Pic.Span hP K b' v C' l s' k) {I:∀ i,GramM (mid (N i) B)}
def horn(n:Side)(e:ℝ):= (e*(pinch n)^2)^(45*n.val^4)
variable {C Q h:ℝ}
lemma cupP(n:Side)(f:Kea.Slide n emptyC)(M:Jill.Male)(ht:0<s') : horn n s' ≤ iceK j f M s':=by
 unfold horn; rw [show 45*n.val^4=Fintype.card (Stag n) by unfold Stag; rw [Fintype.card_prod,site_card, slots]; omega, ←card_univ,←prod_const]; apply Finset.prod_le_prod; intro i _; positivity; intro i _; exact le_max_left _ _
include D
lemma fog (PitY:WindS B N x h C r μ L' w γ c b V θ L I) :∀ᶠ i in atTop, Graph.gainS (More (mid (N i) B)) (hemp x i)* Real.exp (-stoutY (More (mid (N i) B)) (I i).beta (4*hemp x i) γ (tame x i) L' (L i))*horn (mid (N i) B) s' ≤drip (I i) P ∧0< Graph.angle (I i):=by
 filter_upwards [PitY.path.helm,PitY.path.infl,PitY.support,PitY.tend.eventually_ge_atTop k] with i ⟨p,t,v⟩ ⟨xP,bP,T,h⟩ wK kA; obtain ⟨W,T',fℓ,g,a,hb⟩:=wK; let R:=I i; let N':= mid (N i) B; have hr:k≤N'.val:=(Nat.cast_le.mp kA); have hu:0 <gainS (More N') (hemp x i):=by unfold gainS; positivity
 have ht:= glow (bonB T' fℓ) fℓ p t (by rw [W]; exact v) a PitY.row bP.le; rw [W] at ht; have he:0<Graph.angle R:=(mul_pos hu (Real.exp_pos _)).trans_le ht; have hp:D.p=D.p:=rfl
 refine ⟨mul_le_mul ht ?_ (by unfold horn; have he:=D.rP; have hp:=Ember.pinch_pos (mid (N i) B); positivity) he.le,he⟩; exact (cupP _ (too (mid (N i) B)) (R.J.M) D.rP).trans_eq (D.fits _ hr _)
end Roe
end YM.CF.Mint
