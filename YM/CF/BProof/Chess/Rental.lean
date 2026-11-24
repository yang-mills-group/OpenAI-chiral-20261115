import YM.CF.BProof.Chess.Lineup
/-! Real arithmetic to transfer, retaining exponential-price slack. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Chess
open Function Filter Metric NormedSpace Finset Lattice Cube Bide Spire Bide.Half RG Fock Lat Skye Scree
open scoped Matrix.Norms.L2Operator Matrix ComplexOrder Topology BigOperators InnerProductSpace Kronecker Classical
attribute [local instance] opCStarAlgebra
variable {N L:Side}{s t h z P w k n:ℕ}
local notation "Trup"=> Scute N L 0 w
namespace Rental
open Drum Scute Tack Drift
variable (T: Bands (More N) L s P)
abbrev VOL(N:Side):ℝ:= ((More N).val:ℝ)^4
abbrev up(n:Side)(d:ℝ):ℝ:= Real.exp (d*VOL n)
abbrev cover(N:Side)(d:ℝ):ℝ:= Real.exp (d*((More N).val:ℝ)^3)
abbrev charge(a b:ℝ):= a+|b|+2
/-- slackened constants; use P (gauge-lattice units, ≥ lane). Uniform in period -/
abbrev Ξ(P:ℕ)(a b:ℝ):ℝ:= P*charge a b+(P+1)*(a+1)+1
abbrev block(T:Bands (More N) L s P)(z:ℕ):ℕ:=z*(lane T+1)
lemma volume(N:Side) :1<VOL N:=by
 unfold VOL; have hx: 1<(More N).val:=by rw [natM]; have hp:=N.property; change 0<N.val at hp; omega
 exact one_lt_pow₀ (Nat.one_lt_cast.mpr hx) (by decide) -- indentation?
variable {a b C:ℝ}{H U:Obs N→ℝ}
attribute [local instance] opCStarAlgebra
lemma up_eq(x y:ℝ): up N x * up N y=up N (x+y):=by simp only [up,←Real.exp_add,add_mul]
lemma mono (u:a≤b): up N a ≤ up N b:= Real.exp_monotone (mul_le_mul_of_nonneg_right u (by unfold VOL; positivity))
lemma step(x:ℝ): up N x + up N x < up N (x+1):=by
 rw [←up_eq, ←mul_two]; refine mul_lt_mul_of_pos_left ?_ (Real.exp_pos _); have he:= Real.add_one_le_exp (VOL N); simp only [up,one_mul]; linarith [volume N]
lemma cover_le (p:0≤a)(v:k≤ (More N).val): cover N a^k ≤ up N a:=by
 rw [cover,up,← Real.exp_nat_mul]; refine Real.exp_monotone ((mul_le_mul_of_nonneg_right (Nat.cast_le.mpr v) (show 0 ≤ a*((More N).val:ℝ)^3 by positivity)).trans_eq ?_); unfold VOL; ring
include T
lemma bound_count {m:ℕ} (p:halfC L N (lane T*m)): 2*m≤(More N).val:=by
 have e : m ≤ lane T*m:=Nat.le_mul_of_pos_left _ (by unfold Drift.lane; positivity); have hz: lane T*m ≤ L.val*(lane T*m):=Nat.le_mul_of_pos_left _ L.property
 unfold halfC field at p; rw [natM]; omega
lemma q_count : T.q.val ≤(More N).val:= T.grid.exact_size.symm ▸ Nat.le_mul_of_pos_right _ T.grid.count.property
lemma funds : lane T ≤ P:= by
 have hx:= size T; have he:lane T ≤ L.val*lane T:=Nat.le_mul_of_pos_left _ L.property; unfold field at hx; omega
lemma pay (pT:T.q.val=2*(z*2^T.rP))(j:ℕ)(p:halfC L N (lane T*j)):j=Rental.block T z:=by
 have he:= half_m T (z*2^T.rP) pT
 have hx:halfC L N (lane T*Rental.block T z):=by unfold Rental.block; change halfC L N ((Drift.lane T+1)*(z*lane T)) at he; rwa [show (Drift.lane T+1)*(z*lane T)=lane T*(z*(Drift.lane T+1)) from by ring] at he
 have hh:=p.trans hx.symm; unfold field at hh; apply mul_left_cancel₀ (show lane T≠0 by unfold Drift.lane; positivity); apply mul_left_cancel₀ L.property.ne'; exact mul_left_cancel₀ (by decide : 2≠(0:ℕ)) hh
variable (p₁:0≤a)
include p₁
set_option linter.unusedSectionVars false in
lemma pinching : (a+1) ≤ Ξ P a b:=by
 unfold Ξ; have hx:0< charge a b:=by unfold charge; linarith [abs_nonneg b]
 have ha:0 ≤ (P:ℝ) := by positivity
 nlinarith
lemma wiggle : (lane T :ℝ)*charge a b - (Ξ P a b-1) ≤ -((a+1)*(lane T+1)):=by
 have h:(lane T:ℝ) ≤ P:=Nat.cast_le.mpr (funds T); have hx:0 ≤ charge a b:=by unfold charge; linarith [abs_nonneg b]
 unfold Ξ; nlinarith [mul_le_mul_of_nonneg_right h hx]
local instance (I : Type) [Fintype I] [DecidableEq I] : MeasurableSpace (Op I) := borel _
local instance (I : Type) [Fintype I] [DecidableEq I] : BorelSpace (Op I) := ⟨rfl⟩
-- destiny comparison. Fixed upper and fixed-period delta of real readings H,U.
structure Bond (T:Bands (More N) L s P)(a b:ℝ)(H U:Obs N→ℝ):Prop where
 actual (F:Obs N): Paid F (up N a) → U F ≤ up N (a+b)
 mercy (F:Obs N) : Envelope F → Paid F (up N a) → |H F - U F| ≤ up N (-Ξ P a b)
variable (S:Bond T a b H U)
local notation "μ_"=>up N (-Ξ P a b)
local notation "β_"=> up N (charge a b)
local notation "κ₀"=> up N (1-Ξ P a b)
omit p₁ T in
lemma enlarge {F:Obs N}(p:Paid F b)(u:b≤C) :Paid F C:=fun z=> (p z).trans u -- omit T p₁
omit T
lemma jumpOne: Paid (1:Obs N) (up N a):=fun _=> le_trans (le_of_eq norm_one) (Real.one_le_exp (mul_nonneg p₁ (by unfold VOL; positivity)))
include S T
lemma Hcost (F:Obs N)(h: Envelope F)(u:Paid F (up N a)): H F ≤ β_:=by
 have he:charge a b≥a+|b|+1:=by unfold charge; linarith
 have hz:-Ξ P a b≤a +|b| :=by have h:=pinching (b:=b) T p₁; linarith [abs_nonneg b]
 have hx:H F-U F ≤μ_:=le_trans (le_abs_self _) (S.mercy F h u); exact le_trans (b:=up N (a+|b|+1)) (by linarith only [hx, S.actual F u, mono (N:=N) (show a+b ≤ a+|b| from add_le_add_right (le_abs_self _) _), mono (N:=N) hz,step (N:=N) (a+|b|)]) (mono he) -- add_right? tune
lemma vv (u:U 1≤ μ_) : H 1 ≤ up N (1-Ξ P a b):=by
 rw [show 1-Ξ P a b=-Ξ P a b+1 from by ring]; have hz:= le_trans (le_abs_self _) (S.mercy 1 (allowI (N:=N) (S:=univ)).bounded (jumpOne p₁)); exact le_trans (by linarith) (le_of_lt (step (N:=N) (-Ξ P a b)))
omit p₁ S T
lemma root(z:ℕ): up N a ^ z = up N (z*a):=by rw [up, up,← Real.exp_nat_mul,mul_assoc] -- no x
include p₁ S T
lemma Y (D:Drum N L 0 w H)(v:0<z)(h:T.q.val=2*(z*2^T.rP))(u:U 1≤ up N (-Ξ P a b)): Costed D (lane T) (cover N a) (up N (charge a b/(2*(Rental.block T z:ℝ)))) (up N ((1-Ξ P a b)/(2*(Rental.block T z:ℝ)))) :=by
 let n:=Rental.block T z; have hx:0<(n:ℝ):=Nat.cast_pos.mpr (Nat.mul_pos v (by omega))
 have hz(j:ℕ)(p:halfC L N (lane T*j))(x:ℝ): up N (x/(2*(n:ℝ)))^(2*j)=up N x:=by
    rw [root]; push_cast; rw [show j=n from pay T h j p]; congr 1; field_simp
 refine ⟨ Real.exp_pos _, Real.exp_pos _,fun j p=> ?_,fun j p u y=> ?_⟩
 · rw [hz j p]; exact vv T p₁ S u
 rw [hz j p]; let V:=(u*u.bar)^j; apply Hcost T p₁ S V.mark V.permit.bounded; refine enlarge ?_ (cover_le p₁ (bound_count T p)); unfold V; rw [mul_comm 2 j, pow_mul'] -- tune
 exact Scute.repeat_cost _ ((sq (cover N a)) ▸ u.towerP u.bar y.2 (u.barCost y.2)) j
lemma low (D:Drum N L 0 w H)(F:T.Index→ Obs N)(g:∀ i,Allowed (T.band i) (F i))(e:w≤ s)(u:∀ i,Paid (F i) (cover N a))(h: up N (-a) ≤ U (title T F g)): up N (-Ξ P a b) ≤ U 1:=by
 obtain ⟨z,v,z'⟩:= block_half T; apply le_of_not_gt; intro t; have hz:= vv T p₁ S t.le
 let V:=Rental.block T z; have hx:0 < (V:ℝ):=Nat.cast_pos.mpr (Nat.mul_pos v (by omega)); let x:=title T F g; have hh:=decides T F g e u D (Y T p₁ S D v z' t.le) z v z'; set Q:=(lane T:ℝ); let φ:=charge a b; let t₀:=(-(a+1)); have htU:H x ≤ up N t₀:=by
    apply le_trans hh; change up N (φ/(2*(V:ℝ)))^(2*z*lane T)* up N ((1-Ξ P a b)/(2*(V:ℝ)))^(2*z)≤ _
    rw [root,root,up_eq]; push_cast; refine mono ?_; change _ ≤ -(a+1); have he: (z:ℝ)*(Q+1)=(V:ℝ):=by unfold V Rental.block; unfold Q Drift.lane; push_cast; rfl
    let b':=2*(V:ℝ); have hb:0<b':=by unfold b'; positivity
    simp_rw [←mul_div_assoc, ← add_div]; apply (div_le_iff₀ hb).2; have hp:=wiggle (b:=b) T p₁; unfold b'; rw [← he]; have hu:0≤(z:ℝ):=by positivity; -- ring linarith
    change Q*φ-_ ≤ -((a+1)*(Q+1)) at hp; rw [← show Q=2^T.rP from (by unfold Q Drift.lane; push_cast; rfl)]; nlinarith only [mul_le_mul_of_nonneg_left hp hu]
 have ⟨k,l⟩:= serial T F g e u T.q.val rfl; have hp:= S.mercy x k (enlarge l (cover_le p₁ (q_count T))); have h1: U x-H x≤ up N t₀:=by rw [abs_sub_comm] at hp; exact le_trans (le_abs_self _) (hp.trans (mono (neg_le_neg (pinching T p₁))))
 have h2: t₀+1=-a:=by unfold t₀; ring
 have h3:=step (N:=N) t₀; rw [h2] at h3; change _ ≤ U x at h; linarith only [h3,h1,h,htU]
end Rental
end YM.CF.BProof.Chess
