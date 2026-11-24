import YM.SU5.FiniteGaugeData.Largo.Sonnet
set_option linter.unusedSimpArgs false
set_option autoImplicit false
set_option maxHeartbeats 320000
noncomputable section
namespace YM.CF.Window.Largo
open Function Filter Lattice Metric Complex Finset Laurent Next.Free Bloch Fir Lat MeasureTheory Fock Rush
open scoped Topology BigOperators Pointwise ENNReal Matrix Matrix.Norms.L2Operator MatrixOrder InnerProductSpace ComplexOrder Kronecker
attribute [local instance] opCStarAlgebra
variable {N:Side}{v:ℝ}{D l n:ℕ}
section schedule
variable (q p:Stereo N) (t u:Per N)(x y:SpinIdx)(M:Tulip.Male)
local notation "α"=> Chrono N
abbrev adagio (V:Momentum→Op SpinIdx)(N:Side):= twist (Chrono N) (mark N V)
variable (V:Momentum→Op SpinIdx)
private lemma mark_debut : mark N V (debut p t x) (debut q u y)= if p=q ∧ t=u then V (mel (full p t)) x y else 0:=by rw [mark,jump_apply]; simp only [Equiv.refl_apply,debut,sale_full]
private lemma chronos_mark : ((Chrono N).val * mark N V) (debut q t x) (debut p u y)= if p=q then phaseL u t /heightF N * (V (mel (full p u))) x y else 0:=by
 rw [Matrix.mul_apply,Finset.sum_eq_single (debut p u x)]; -- tune cunning dim infer
 · by_cases h:p=q <;> simp [properT,mark_debut,h,Ne.symm]
 · intro k; revert k; apply debut_cases; intro v t' a _ z; by_cases h:p=v; swap; · simp [Ne.symm h,mark_debut]
   by_cases e:u=t'; swap; · simp [Ne.symm e,mark_debut]
   subst v t'; have he: a≠x:= fun h=> z (h ▸ rfl); simp [properT, Ne.symm he,mark_debut]
 simp
lemma adagio_formula : adagio V N (debut q t x) (debut p u y)= if p=q then ∑ i:Per N,(phaseL i t/heightF N)* (V (mel (full p i)) x y)*star (phaseL i u/heightF N) else 0:=by
 rw [adagio,twist_formula,Matrix.mul_apply,mini_offer,sum_eq_single p];
 · simp_rw [Matrix.star_apply,properT,chronos_mark]; by_cases h:p=q; · subst q; simp [ite_mul,mul_ite,apply_ite star]
   simp [h]
 · intro j _ h; simp_rw [Matrix.star_apply,properT]; simp [Ne.symm h]
 simp
lemma adagio_h (p q:Mini N) (t: back p.1≠ back q.1): adagio V N p q=0:=by
 revert p q; apply debut_cases; intro i x y p; revert p; apply debut_cases; intro v t' q z; simp only [debut,back_home] at z; rw [adagio_formula]; exact if_neg (Ne.symm z)
def levit {N:Side}(t:ℤ): ℂ:= fee (periods N (full (fun _=>0) t)) -- N not in type! include
variable (a b:ℤ)
-- wrap sign to Tend at true cover. easier use mode_fee & carry
lemma mark_epoch : ∀ k:Per N, levit (N:=N) a*phaseL k a= Complex.exp (a*(Complex.I * Lat.principal k)):=by
 intro k; let z: Stereo N:=0; let f:= full (fun _:Tang=> (0:ℤ)) a; let m:=full z k; have he: wrap N f=full z (a:Per N):=by unfold f; funext i; fin_cases i <;> (first| rfl| (change Int.cast (R:=Per N) 0=0; simp))
 let T:=traced z z; have hv:traced z z=1:=by unfold z traced phaseL; simp
 change fee (periods N f) *_=_; rw [show phaseL k a= _ from ((show frequency m (wrap N f)=phaseL k a from (by rw [he]; unfold m; rw [frequencyL z z,hv,one_mul])).symm), ←freq_mode,←mode_fee (N:=N) m,mul_comm,←mode_shift,carrying];
 unfold mode; rw [foldBig]; unfold f m; simp_rw [full_before, full_last]; simp only [Int.cast_zero,mul_zero,sum_const_zero,zero_add]; unfold mel pm tmap; rw [comp_apply,full_last]; congr 1; ring_nf -- alpha pi
local notation "H"=> fun x=> -zen (mixL 4 M.val x)
abbrev reedsK (M:Tulip.Male)(N:Side):= E₁ (fun x=> -zen (mixL 4 M.val x)) N
def polae (N:Side)(a:ℤ): ℂ:= levit (N:=N) a
lemma polae_real : star (polae N a)=polae N a:= fee_real _
lemma polae_one : polae N a * polae N a=1:= fee_one _
lemma berth_u : berth (badge p) M.val N a b x y=(polae N a)*(polae N b)*adagio (fun x=> -zen (mixL 4 M.val x)) N (debut p a x) (debut p b y) := by
 rw [adagio_formula p p a b x y (H), if_pos rfl, Finset.mul_sum]; unfold berth approach; rw [Finset.mul_sum]; apply sum_congr rfl; intro i _
 simp only [aliquotMel]; unfold polae conduct; rw [Int.cast_sub,sub_mul, Complex.exp_sub,←mark_epoch,←mark_epoch, star_div₀,heightReal];
 let t:= levit (N:=N) a; let u:=levit (N:=N) b; let T:=heightF N; let P:= phaseL i (a:Per N); let Q:= phaseL i (b:Per N); let z:ℂ:= (-zen (mixL 4 M.val (floorPin (badge p) (Lat.principal i)))) x y
 change (N.val:ℂ)⁻¹*(t*P/(u*Q)*z)=t*u*(P/T*z*(star Q/T)); have hk:(u*Q)⁻¹=u*star Q:=by
    apply inv_eq_of_mul_eq_one_right; rw [show u*Q*(u*star Q)=u*u*(Q*star Q) from (by ring), phaseL_one,show u*u=1 from fee_one _,mul_one]
 rw [div_eq_mul_inv (t*P),hk,← heightSq (N:=N),mul_inv_rev]; ring -- tune ring sees T unfolding
end schedule
end YM.CF.Window.Largo
