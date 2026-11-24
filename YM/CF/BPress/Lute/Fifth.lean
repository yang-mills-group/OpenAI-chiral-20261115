import YM.CF.BPress.Lute.Sums
import YM.CF.BPress.Magnets
/- angle calculation eq:B-radC. Radians, signed chart lifts. `legX,...` for leftover angle and B.5 pair. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Lute
open Function Finset Filter NormedSpace InnerProductSpace SU SU.Pair Spin Spin.Paint Lattice Fock Complex
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker InnerProductSpace ContDiff Classical
attribute [local instance] opCStarAlgebra
structure Counts (θ δ l k a b:ℝ): Prop where
 wing : |θ|< Real.pi
 left : |l|< Real.pi
 right : |k|< Real.pi
 mix_p : |a|<Real.pi
 mix_q : |b|<Real.pi
 dTen : χ l= χ (-4*θ)
 dF : χ k=χ (2*θ)
 mix : Real.cos δ=(1+Real.cos (3*θ))/2
 rock : χ a=χ (-θ+δ)
 wind : χ b=χ (-θ-δ)
 sumZ : -6*θ+(l+k)+(a+b)+5*l=0
local notation "π"=>Real.pi
variable {θ δ l k a b:ℝ}
lemma χ_period (t:ℝ):χ (t+2*π)=χ t:=by rw [χ_add]; simp [χ,BZ.phase]
namespace Counts
abbrev pickδ(z:ℝ):= Real.arccos ((1+Real.cos (3*z))/2)
lemma aligns(z:ℝ): Real.cos (pickδ z)=(1+Real.cos (3*z))/2:= Real.cos_arccos (by linarith [Real.neg_one_le_cos (3*z)]) (by linarith [Real.cos_le_one (3*z)])
lemma top_bound(z:ℝ) : pickδ z ≤ π/2:=by
 rw [pickδ]; exact Real.arccos_le_pi_div_two.mpr ((by linarith [Real.neg_one_le_cos (3*z)]))
private lemma high : π/5 < pickδ (4*π/5):=by
 let z:=4*π/5; let b:=π/5; let d:=pickδ z; have ht: 3*z=2*b+2*π:=by unfold z b; ring
 refine lt_of_not_ge (fun h:d≤ b=>?_); have he:= Real.cos_le_cos_of_nonneg_of_le_pi (Real.arccos_nonneg _) (show b≤π by unfold b; linarith [Real.pi_pos]) h; rw [aligns,ht, Real.cos_add_two_pi, Real.cos_two_mul] at he
 have hg :Real.cos b=(1+Real.sqrt 5)/4:= Real.cos_pi_div_five; rw [hg] at he; nlinarith [Real.sq_sqrt (show (0:ℝ)≤5 by norm_num), Real.sqrt_nonneg 5]
lemma zero_κ : Counts 0 0 0 0 0 0 := by constructor <;> norm_num [Real.pi_pos]
lemma one_κ : let θ:=2*π/5; let δ:=pickδ θ; Counts θ δ θ (2*θ) (-θ+δ) (-θ-δ):=by
 intro θ δ; have hp:0<θ:=by unfold θ; positivity
 have hc:θ=2*π/5:=rfl; have h₁:δ≤π/2:= top_bound θ; have h₂:0≤δ:= Real.arccos_nonneg _; refine ⟨?_,?_,?_,?_,?_,?_,rfl, aligns _,rfl,rfl,?_⟩; all_goals try rw [abs_lt]; constructor <;> linarith [Real.pi_pos]
 · nth_rw 1 [show θ= (-4*θ)+2*π by linarith]; exact χ_period _
 ring
lemma two_κ : let θ:=4*π/5; let δ:=pickδ θ; let l:=-4*θ+4*π; let k:=2*θ-2*π; Counts θ δ l k (-θ+δ) (-θ-δ+2*π):=by
 intro θ δ l k; have h:0<θ:=by unfold θ; positivity
 have hc: θ=4*π/5:=rfl; have hp:=Real.pi_pos; have h₁:δ≤π/2:= top_bound _; have h₂:π/5<δ:= high; unfold l k; refine ⟨?_,?_,?_,?_,?_,?_,?_,aligns _,rfl,χ_period _, by linarith⟩; all_goals try rw [abs_lt]; constructor <;> linarith
 · rw [show 4*π=2*π+2*π by ring,←add_assoc,χ_period,χ_period]
 nth_rw 2 [show 2*θ=2*θ-2*π+2*π by ring]; rw [χ_period]
lemma flip(p:Counts θ δ l k a b):Counts (-θ) (-δ) (-l) (-k) (-a) (-b):=by
 obtain ⟨p,q,h,g,u,v,t,w,i,r,j⟩:=p; refine ⟨by rwa [abs_neg], by rwa [abs_neg], by rwa [abs_neg], by rwa [abs_neg], by rwa [abs_neg], ?_,?_,?_,?_,?_,?_⟩; swap -- tune
 all_goals try linarith
 all_goals first
   | rw [mul_neg,Real.cos_neg,Real.cos_neg,w]
   | rw [mul_neg, ←χ_cc, ←χ_cc]; congr 1
   | rw [←χ_cc,i, χ_cc, show -(-θ+δ)= - -θ+ -δ by ring]
   | rw [←χ_cc,r,χ_cc, show -(-θ-δ)= - -θ- -δ by ring]
end Counts
lemma powerZ : SU.z=χ (2*π/5):=by unfold χ BZ.phase SU.z; push_cast; congr 1; ring
lemma inkχ (n:ℕ)(t:ℝ): χ t ^ n=χ (n*t) := by induction n with |zero=>simp |succ n ih=>rw [pow_succ,ih,Nat.cast_succ,add_mul,one_mul,χ_add]
-- include θ choice independent from trivial orientation etc
lemma count (i:Fin 5):∃ θ l k a b δ:ℝ,χ θ=SU.z^i.val∧Counts θ δ l k a b:=by
 fin_cases i <;> norm_num1
 · exact ⟨0,_,_,_,_,_,χ_zero, Counts.zero_κ⟩
 · exact ⟨_,_,_,_,_,_,powerZ.symm.trans (pow_one _).symm,Counts.one_κ⟩
 · refine ⟨_,_,_,_,_,_,?_ ,Counts.two_κ⟩; rw [powerZ,inkχ]; congr 1; push_cast; ring
 · refine ⟨_,_,_,_,_,_,?_, Counts.two_κ.flip⟩; rw [powerZ,inkχ, show (↑(3:ℕ):ℝ)*(2*π/5)= -(4*π/5)+2*π by push_cast; ring,χ_period]
 refine ⟨_,_,_,_,_,_,?_,Counts.one_κ.flip⟩; rw [powerZ,inkχ, show (↑(4:ℕ):ℝ)*(2*π/5)= -(2*π/5)+2*π by push_cast; ring,χ_period]
end YM.CF.BPress.Lute
