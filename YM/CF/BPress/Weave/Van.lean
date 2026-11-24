import YM.CF.BPress.Weave.Whorl
/-! positive det, log Jacobian via logs of real eigenvalues, permit trace on coordinate rows. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Weave
open Function Filter Lattice Wilson RG Precision Grid Cube Bands Pressure Wealth Finset Branch
open scoped Topology BigOperators Classical Matrix Matrix.Norms.Frobenius InnerProductSpace
open SU Gauge
attribute [local instance] Gauge.frobInner
variable {s:Side}{B:BandWidth}(X:Bands s B)
def detM (F:BEnd X) := LinearMap.det F.toLinearMap
def traceM (F:BEnd X) := Matrix.trace (rowM X F)
def detL (F:BEnd X) := Real.log (detM X F)
def traceTab (l u:ℝ) := |Real.log l|+|Real.log u|
def jacdiff (F:Fare X)(S:Finset X.Hcols) := detL X (F S) - detL X (F ∅)
lemma trace0 (F:BEnd X) : traceM X F= LinearMap.trace ℝ _ F.toLinearMap:=by rw [LinearMap.trace_eq_matrix_trace ℝ (EuclideanSpace.basisFun (Axon X) ℝ).toBasis]; rw [traceM,basis_row]
lemma fee_trace (u v:ℝ)(t:0<v)(p:v≤ u): HasSum (fun n:ℕ=>lcoef n * (haloFee u v)^(n+1)) (Real.log u-Real.log v):=by
 let K:= haloFee u v; have he:= (tick_valid u v v t (Set.left_mem_Icc.mpr p)).1; have hu:=t.trans_le p; have hd: |K|<1:= (abs_of_nonneg he.1).trans_lt he.2; have hk: Real.log u-Real.log v= -Real.log (1-K):=by unfold K haloFee; rw [sub_sub_cancel,mul_comm u⁻¹,← div_eq_mul_inv,Real.log_div t.ne' hu.ne']; ring; -- tune
 rw [hk]; simpa only [div_eq_mul_inv,lcoef,mul_comm (_:ℝ) ((_:ℝ)⁻¹)] using Real.hasSum_pow_div_log_of_abs_lt_one hd
variable {F:Fare X}
namespace Summer
variable {X}{u l:ℝ}{r k:ℕ}(p:Summer X F u l r k)
include p
lemma root_pos (S) :0 < detM X (F S):= by obtain ⟨b,f,h⟩:= basis_harp _ (p.self S); rw [detM,h.det]; exact prod_pos fun i _=> p.pos.trans_le ((h.margin.mp (p.margin _)) i).1
lemma root_eq (S) : detL X (F S)=(Module.finrank ℝ (RaySpace X)) * Real.log u - traceM X (logp X F u S):=by
 obtain ⟨b,f,h⟩:=basis_harp _ (p.self S); let I:= sea X F u S; let L:= logp X F u S; let q(n:ℕ): BEnd X:= lcoef n • I^(n+1); let c:= Real.log u; have ht:=h.margin.mp (p.margin S); have hf(i):0<f i:= p.pos.trans_le (ht i).1; have hs:Summable q:=p.chills lcoef (fun i=>by unfold lcoef; rw [abs_of_nonneg (by positivity : 0≤((i:ℝ)+1)⁻¹)]; exact inv_le_one_of_one_le₀ (by linarith [(Nat.cast_nonneg i (α:=ℝ))])) _ _; have he : Harp b L (fun i=> c-Real.log (f i)):=by
   intro i; let l:= haloFee u (f i); let g (n:ℕ) := lcoef n*l^(n+1); have hg(n:ℕ):Flare (q n) (b i) (g n):=(((sea_harp X F u h) i).pow (n+1)).scale _; have hL:HasSum g (c-Real.log (f i)):= fee_trace u (f i) (hf i) (ht i).2; let P: BEnd X →L[ℝ] RaySpace X:= ContinuousLinearMap.apply ℝ (RaySpace X) (b i); unfold Flare; change P (∑' n,q n)=_; rw [P.map_tsum hs]; refine Eq.trans (b:=∑' n:ℕ,g n • b i) ?_ (hL.smul_const _|>.tsum_eq); exact tsum_congr fun i=> hg i
 rw [trace0,he.trace,detL,detM,h.det,Real.log_prod (fun i _=>(hf i).ne'), sum_sub_distrib,sum_const]; simp [c]
lemma price_roots (S) : |detL X (F S)| ≤ Module.finrank ℝ (RaySpace X) * traceTab l u:=by
 obtain ⟨b,f,h⟩:= basis_harp _ (p.self S); have ht(i):=(h.margin.mp (p.margin _)) i; have hf(i):0<f i:= p.pos.trans_le (ht i).1; rw [detL,detM,h.det,Real.log_prod (fun i _=>(hf i).ne')]; refine (abs_sum_le_sum_abs ..).trans ((sum_le_sum (g:=fun _=>traceTab l u) ?_).trans (Eq.le (by rw [sum_const,nsmul_eq_mul,card_univ,Fintype.card_fin]))); intro i _; unfold traceTab; apply abs_le.mpr; have h₁:= Real.log_le_log p.pos (ht i).1; have h₂:=Real.log_le_log (hf i) (ht i).2; constructor; linarith only [h₁,(neg_abs_le (Real.log l)),abs_nonneg (Real.log u)]; linarith only [h₂, le_abs_self (Real.log u), abs_nonneg (Real.log l)]
end Summer
end YM.CF.BPress.Weave
