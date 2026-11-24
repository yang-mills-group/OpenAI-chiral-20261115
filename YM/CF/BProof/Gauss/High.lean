import YM.CF.BProof.Gauss.Rise

/-! Uniform budget upper on Numeric via footprints. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Gauss
open Function Filter RG Wilson Lattice Finset Work Micro MeasureTheory Mag Angular Angular.Yard Charge Charge.Form Matrix Roll Precision
open scoped Topology BigOperators Classical Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator
local notation "G"=> SU.group
variable {s:Side}(Y:Yard s)(T:PathData G)(M:ℕ)(c:Clip)(θ:ℝ)(S:Finset Y.Col)(W:Y.Branch)
variable (H:Room Y M){u p q: ℝ} (h:T.Bounds c u p q)

def fans (b:Y.Col):=∑ i:Y.Apt,‖W (b,i)‖^2
def face (l:Tile s) := ∑ b:Y.Col with Needs Y M l b,fans Y W b
def price (c:Clip)(p:ℝ) := (2*(c.direct+share))*((p+1)*4)^2
def peak (c:Clip)(p:ℝ)(d M:ℕ) := 1+price c p * gearBound d M
include H h
theorem within (l:Tile s)(u: Stove Y M l): ‖linear T M l (Y.roll W)‖^2 ≤ ((p+1)*4)^2*face Y M W l:=by
 let v:= Real.sqrt (face Y M W l); let Z: Finset Y.Col:= univ.filter (fun x=>¬Needs Y M l x); let A:=Y.roll (Y.roof Z W)
 have e: ∀ b:Y.Door, b.1∉ Z → ‖W b‖≤ v := by
    intro b hb; simp [Z] at hb; refine Real.le_sqrt_of_sq_le ((single_le_sum (f:= fun i:Y.Apt=> ‖W (b.1,i)‖^2) (fun i _=> sq_nonneg _) (mem_univ b.2)).trans (single_le_sum (f:=fans Y W) (fun i _=> sum_nonneg (fun j _=>sq_nonneg _)) (mem_filter.mpr ⟨mem_univ _,hb⟩)))
 have he(X:ℝ): X=v^2↔ X=face Y M W l:=by rw [show v^2= face Y M W l from Real.sq_sqrt (sum_nonneg (fun i _=>sum_nonneg fun j _=> sq_nonneg _))]
 rw [cave_dep Y M l H W u T (Y.roof Z W) (fun d h=>by simp [Yard.roof,Z,h]), ((he (face ..)).2 rfl),← mul_pow]; apply pow_le_pow_left₀ (norm_nonneg _); rw [mul_assoc]; exact Form.line_p M T c l h A v (fun i=>Y.roll_short W e (Real.sqrt_nonneg _) i) -- tune order

theorem pent (x:Plan Y)(ht:θ≤2)(hu:0≤θ): dotProduct x ((host Y T M c θ S) *ᵥ x) ≤ peak c p Y.short M * dotProduct x x:=by
 let B:=lowerMap Y x; let v(b:Y.Col):= fans Y B b; let W:= ∑ b:Y.Col,v b; let K:=price c p
 have hb:0≤ p:= Push.AbsoluteSums.budget_nonneg h.three; have hv(b):0≤v b:= sum_nonneg fun i _=> sq_nonneg _; have H₀:0≤K:=by unfold K price; have := c.quadratic_pos; have := share_pos; positivity
 have he(l:Tile s)(k:Stove Y M l) : 2*Q T M c θ l (Y.roll B) ≤ K*face Y M B l:= by
   have hk := within Y T M c B H h l k; unfold Q; let g:= Y.roll B; let X:= linear T M l g
   rw [show 2*(unit c θ l*‖linear T M l (Y.roll B)‖^2/2) = unit c θ l * ‖X‖^2 from by unfold X g; ring]; unfold K price; rw [mul_assoc (2*(c.direct+share))]; have hp:= (unit_p c l θ hu); have h:θ*(c.direct+share)≤2*(c.direct+share):=by gcongr; have := c.quadratic_pos; have := share_pos; positivity
   exact mul_le_mul (hp.2.trans h) hk (sq_nonneg _) (hp.1.trans (hp.2.trans h))
 let L:=good Y M S
 have hh(b:Y.Col): (L.filter (fun i=>Needs Y M i b)).card ≤ gearBound Y.short M:= le_trans (card_le_card (fun i (h:i∈L.filter _) => (engaged ..).2 ⟨(mem_filter.mp (mem_filter.mp h).1).2.1,(mem_filter.mp h).2⟩)) (gear_count Y M b)
 have hv' : (∑ i∈L, K*face Y M B i) ≤ K*gearBound Y.short M*W:=calc
   _ = K * ∑ b:Y.Col,(L.filter (fun i=>Needs Y M i b)).card*v b:=by
      rw [← mul_sum]; congr 1; unfold face; simp_rw [sum_filter]; rw [sum_comm]; apply sum_congr rfl; intro i hi; rw [← sum_filter,← nsmul_eq_mul,← Finset.sum_const]
   _ ≤ K* ∑ b:Y.Col,(gearBound Y.short M:ℝ)*v b:=by refine mul_le_mul_of_nonneg_left (sum_le_sum (fun i _=> mul_le_mul_of_nonneg_right ?_ (hv i))) H₀; exact Nat.cast_le.mpr (hh _)
   _ = _:=by rw [← mul_sum, ← mul_assoc]
 rw [paycheck,tally]; change (∑ b∈ S,v b)+_≤(1+K*gearBound Y.short M)*W; rw [work,mul_sum (s:=good Y M S),add_mul,one_mul]; refine add_le_add (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun i _ _=> hv i)) ((sum_le_sum (fun i hi=> he i ((mem_filter.mp hi).2.1))).trans hv')
theorem numbered (ht:θ≤2)(hk:1/2 ≤ θ) : Numeric (host Y T M c θ S) (Gauss.floor c Y.short) (peak c p Y.short M):= fun i=> ⟨lower_pay Y T M c θ S H hk i,pent Y T M c θ S H h i ht (by linarith)⟩
omit H h
lemma peak_hi (p:ℝ)(d:ℕ)(M:ℕ) : 1 ≤ peak c p d M:=le_add_of_nonneg_right (by have :=share_pos; have :=c.quadratic_pos; unfold price; positivity)
lemma peak_PL (p:ℝ)(d:ℕ)(M:ℝ→ℕ)(h: PL fun y=>(M y:ℝ)): PL (fun y=>peak c p d (M y)):=by
 unfold peak gearBound; push_cast; refine PL.add (PL.const _) (PL.mul (PL.const _) (PL.mul (PL.const _) (PL.pow (PL.add (PL.mul (PL.const _) (PL.add (PL.const _) (PL.mul (PL.const _) h))) (PL.const _)) 4))) -- tune
end YM.CF.BProof.Gauss
