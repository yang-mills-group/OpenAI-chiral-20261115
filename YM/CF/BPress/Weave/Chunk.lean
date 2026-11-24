import YM.CF.BPress.Weave.Turf
import YM.CF.BPress.Weave.Clerk
/-!
`eq:B-Rpoly`, powers and infinite log/geometric support-price preparation
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Weave
open Function Filter Lattice Wilson RG Precision Grid Cube Bands Pressure Wealth Finset Branch Push.AbsoluteSums
open scoped Topology BigOperators Classical Matrix Matrix.Norms.Frobenius InnerProductSpace
open SU Gauge
attribute [local instance] Gauge.frobInner
variable {s: Side}{B:BandWidth}(X : Bands s B)
variable (F:Fare X)(u:ℝ)(l:ℝ)
def sea (S:Finset X.Hcols): BEnd X:= incomeT X (F S) u
lemma sea_harp {I : Type*}[Fintype I]{S: Finset X.Hcols}{b:OrthonormalBasis I ℝ (RaySpace X)}{f:I→ℝ}(h:Harp b (F S) f): Harp b (sea X F u S) (haloFee u ∘ f):=fun i=> Flare.one.sub ((h i).scale _)
-- facts used also log
lemma sea_range (x:ℝ)(p:0<l)(v:l≤u)(e:x∈ Set.Icc l u) : haloFee u x∈Set.Icc 0 (1-l/u):= let h:=tick_valid u l x p e; ⟨h.1.1,h.2⟩
lemma sea_spec (S:Finset X.Hcols)(p:0<l)(v:l≤u)(a:IsSelfAdjoint (F S))(h:Margins (F S) l u)(n:ℕ): ‖sea X F u S ^ n‖ ≤ (1-l/u)^n:=by
 obtain ⟨I,f,t⟩:= basis_harp _ a; have he(i):= sea_range u l (f i) p v ((t.margin.mp h) i); have hz:0≤1-l/u:=sub_nonneg.mpr ((div_le_one (p.trans_le v)).mpr v); refine (show Harp I (sea X F u S ^ n) (fun i=>(haloFee u (f i))^n) from fun i => ((sea_harp X F u t) i).pow n).cap (pow_nonneg hz _) (fun i=>?_); rw [abs_of_nonneg (pow_nonneg (he i).1 _)]; exact pow_le_pow_left₀ (he i).1 (he i).2 n
lemma sea_pow (S:Finset X.Hcols)(p:0<l)(v:l≤u)(a:IsSelfAdjoint (F S))(h:Margins (F S) l u)(n:ℕ): ‖sea X F u S ^ n‖≤ Real.exp (-(l/u)*n):= (sea_spec X F u l S p v a h n).trans (geo_fee _ _ (sub_nonneg.mpr ((div_le_one (p.trans_le v)).mpr v)) le_rfl _)
lemma sea_strict (S:Finset X.Hcols)(p:0<l)(v:l≤u)(a:IsSelfAdjoint (F S))(h:Margins (F S) l u) : ‖sea X F u S‖<1:=by
 have he:= sea_spec X F u l S p v a h 1; rw [pow_one,pow_one] at he; exact he.trans_lt (sub_lt_self _ (div_pos p (p.trans_le v)))
-- chunk selection k & remainder height.
def grainFee (D r:ℕ):= (n_ang D:ℝ)* taxArea r * Real.exp 1
def grassRate (r:ℕ) := (taxArea r:ℝ)⁻¹
def cost_strand (u l:ℝ)(k:ℕ) := Real.exp (-(l/u)*k)
lemma gr_pos (r:ℕ) : 0<grassRate r:= by unfold grassRate taxArea; positivity
lemma gr_PL (r:ℝ→ℕ)(p:PL fun i=>(r i:ℝ)) : PL (fun i=> (grassRate (r i))⁻¹) :=by simp only [grassRate,inv_inv,taxArea]; push_cast; exact (((PL.const 4).mul p).add (PL.const 1)).pow _
lemma grain_PL (D:ℕ)(r:ℝ→ℕ)(p: PL fun i=>(r i:ℝ)) : PL (fun i=> grainFee D (r i)):= ((PL.const _).mul (show PL fun i=>(taxArea (r i):ℝ) from by simpa only [grassRate,inv_inv] using gr_PL r p)).mul (PL.const _)
lemma grain_nn (D r:ℕ): 0 ≤ grainFee D r:=by unfold grainFee; positivity
variable (A:Fare X)(r k:ℕ)
abbrev rise (i:ℕ): Collected X.Hcols (Axon X):= fun S=> rowM X (A S ^ i)
lemma grain (p:∀ i ≤ k,∀ S, ‖A S ^ i‖≤ 1) (h:Connect X A r)(i:ℕ)(e:i≤k) : Aura (soils X) (grassRate (k*r)) (grainFee B.D (k*r)) (rise X A i):=by
 apply Aura.weaken (charge_bay ((h.pow i).mono (Nat.mul_le_mul_right r e)) zero_le_one (p i e) (gr_pos (k*r)).le); unfold grassRate grainFee; rw [inv_mul_cancel₀,mul_one]; exact Nat.cast_ne_zero.mpr (by unfold taxArea; positivity) -- tune
lemma grain_max (p:∀ S, ‖A S ^ k‖ ≤ cost_strand u l k)(h: Connect X A r)(g:grainFee B.D (k*r)*cost_strand u l k≤ 1/2) : Aura (soils X) (grassRate (k*r)) (1/2) (rise X A k):=by
 apply Aura.weaken (charge_bay (h.pow k) (Real.exp_pos _).le p (gr_pos (k*r)).le); unfold grassRate; rw [inv_mul_cancel₀]; exact g; exact Nat.cast_ne_zero.mpr (by unfold taxArea; positivity)
lemma grain_all (p:∀ i≤k,∀ S, ‖A S ^ i‖≤1) (h:Connect X A r) (v:∀ S, ‖A S ^ k‖ ≤ cost_strand u l k)(g:grainFee B.D (k*r)*cost_strand u l k≤ 1/2)(t:0<k)(i:ℕ) : Aura (soils X) (grassRate (k*r)) (grainFee B.D (k*r)*((1:ℝ)/2)^(i/k)) (rise X A i):=by
 have he:= grain_max X u l A r k v h g; let w:= i%k; let a:=grassRate (k*r); let Z:=grainFee B.D (k*r); have H (n:ℕ): Aura (soils X) a (Z*((1:ℝ)/2)^n) (rise X A (w+k*n)):=by
   induction n with
   | zero=> simpa using grain X A r k p h w (Nat.mod_lt i t|>.le) -- tune Pos
   | succ n ih=>
     rw [pow_succ,←mul_assoc, Nat.mul_add,Nat.mul_one,←add_assoc]; apply (show _ from (by unfold rise; simp_rw [pow_add _ (w+k*n),row_P]; exact ih.walk he (gr_pos _).le)) -- tune
 specialize H (i/k); rw [show w+k*(i/k)=i from Nat.mod_add_div i k] at H -- rewrites all incl div
 exact H; -- tune better specialize
-- PL schedule
lemma buy_chunks (r:ℝ→ℕ)(l:ℝ→ℝ)(u:ℝ)(hr:PL fun i=>(r i:ℝ))(hl:PL fun i=>(l i)⁻¹)(pu:0<u)(e:∀ᶠ i in atTop, 0<l i) (D:ℕ) : ∃ k:ℝ→ℕ, PL (fun i=>(k i:ℝ)) ∧ ∀ᶠ i in atTop, 0<k i∧ grainFee D (k i*r i) * cost_strand u (l i) (k i)≤ 1/2:=by
 let X:=fun i:ℝ=> Real.log i * u * (l i)⁻¹; let k:=fun i=>⌈X i⌉₊; have he:∀ᶠ i in atTop, 0<X i:= by filter_upwards [e, Real.tendsto_log_atTop.eventually_gt_atTop 0] with i ei p; unfold X; positivity
 have hk: PL fun i=>(k i:ℝ):= (((PL.log.mul (PL.const u)).mul hl)).ceil (he.mono fun i t=> t.le); have hp: PL fun i=>grainFee D (k i*r i):= grain_PL D _ (by simp_rw [Nat.cast_mul]; apply hk.mul hr); have hh:= (hp.times npl_inv).drop; refine ⟨k,hk,?_⟩; filter_upwards [e,he, hh.eventually (ge_mem_nhds (show (0:ℝ)<1/2 by norm_num)), eventually_gt_atTop (0:ℝ)] with i ei eP h p; apply And.intro (Nat.ceil_pos.mpr eP); apply le_trans (mul_le_mul_of_nonneg_left _ (grain_nn ..)) (show grainFee D _*i⁻¹≤1/2 from h); rw [← Real.exp_log p, ← Real.exp_neg]; rw [Real.exp_log p]; unfold cost_strand; apply Real.exp_monotone; rw [neg_mul,neg_le_neg_iff]; refine le_trans ?_ (mul_le_mul_of_nonneg_left (Nat.le_ceil (X i)) (show 0≤ l i/u by positivity)); unfold X; field_simp; nlinarith
end YM.CF.BPress.Weave
