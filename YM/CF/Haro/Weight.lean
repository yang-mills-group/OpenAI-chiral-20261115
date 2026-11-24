import YM.CF.Haro.Tacit
import YM.CF.Tap.Breeze
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Haro
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Stationary Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Fock Tulip Font Spire Nacre Ember Pec
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker MatrixOrder Classical
attribute [local instance] opCStarAlgebra
open Tap Hake Urn Yaw Levier Proa Rill
variable {n j:ℕ}
variable {a:ℝ}(W:Momentum→ Pal)(F:Cover→Pal)
abbrev ξP:= max 1 ‖(coordL (k:=SpinIdx×Slot)).symm.toContinuousLinearMap‖
lemma ζP(A:Pal)(u:∀ i j,‖A i j‖≤a):‖A‖ ≤ ξP*a:=by
 have h:0 ≤ a:=(norm_nonneg _).trans (u (Classical.arbitrary _) (Classical.arbitrary _))
 let f:=(coordL (k:=SpinIdx×Slot)); rw [←f.symm_apply_apply A]; exact (f.symm.toContinuousLinearMap.le_opNorm _).trans (mul_le_mul (le_max_right ..) ((pi_norm_le_iff_of_nonneg h).mpr fun i=>(pi_norm_le_iff_of_nonneg h).mpr (u i)) (norm_nonneg _) (zero_le_one.trans (le_max_left ..)))
open YM.Push.Loops
lemma burn (h:Reads F W)(k:1≤n)(u:RailP n F a)(s:AxisP W): ‖W 0‖≤ξP*a∧∀ i:Axis,‖deriv (fun s=> W (bout i s)) 0‖ ≤ ξP*a:=by
 have hp:0∈baseCube:=by simpa [bout_zero] using bout_h 0 0 (by norm_num)
 constructor
 · apply ζP (W 0); intro i j; rw [←h.readK 0 hp, Laurent.read]; simp only [mode_constant,one_smul]; exact (norm_tsum_le_tsum_norm ((u i j).falls.2.1)).trans (u i j).falls.2.2
 intro i; apply ζP; intro x y; let f(p):= F p x y; have ht:=u x y; obtain ⟨z,p⟩:=Tap.moments ht k i
 have hp:= s.age i; have hn:= (op_deriv.mp hp.hasDerivAt) x y; have hx:=(hn.congr_of_eventuallyEq (by filter_upwards [bout_v i] with j e; exact h.readK (bout i j) e x y)).unique p; rw [hx,norm_mul,Complex.norm_I,one_mul]; refine (norm_tsum_le_tsum_norm z.norm).trans ((z.norm.tsum_le_tsum ?_ ht.2.1).trans ht.2.2)
 · intro v; rw [norm_mul]; refine mul_le_mul_of_nonneg_right ((axis_le_size ..).trans ?_) (norm_nonneg _); unfold tweight; refine le_trans ?_ (pow_le_pow_right₀ (by simp : 1 ≤ (1:ℝ)+Laurent.size v) k); simp

lemma excise (j:ℕ)(k:1≤j)(M: Male)(W: Momentum→ Pal)(h:AxisP W): let Z:=zeus j M W; NullW (potion j M (fun p=>W p-waveB Z)) :=by
 intro Z; have he:=normalization j k M h
 have hz:potion j M (fun p=>W p-waveB Z)=potion j M W-potion j M (fun _=>waveB Z):= funext fun p=>by unfold potion; rw [mul_sub, sub_mul]; rfl
 rw [hz]; refine ⟨?_,fun i=>?_⟩; swap
 · have ht : HasDerivAt (fun x=>potion j M W (bout i x)) (petal i⊗ₖ Z) 0 :=by rw [←show zest j M W i=_ from he.2.2 i]; exact ((Psy j k M h).age i).hasDerivAt
   exact (ht.sub (boot_wave j k M Z i)).congr_deriv (by rw [sub_self])
 rw [Pi.sub_apply,he.1,(normalization j k M (symWave Z he.2.1)).1,sub_self]
lemma excels :∃ C:ℝ,0<C∧∀ (j m:ℕ)(M:Male)(W:Momentum→ Pal)(Y:Cover→Pal)(a:ℝ),1≤j→1 ≤ m→Reads Y W→RailP m Y a→AxisP W→ let Z:=zeus j M W; Mind Z∧‖Z‖ ≤ C*a∧ NullW (potion j M (fun p=>W p-waveB Z)):=by
 obtain ⟨D,h,H⟩:=Tap.zeus_cost; refine ⟨2*D*ξP,by unfold ξP; positivity,fun j m M W X a p u Y Z A=> ⟨(normalization j p M A).2.1,?_, excise j p M W A⟩⟩
 obtain ⟨t,hK⟩:=burn W X Y u Z A; exact (H j p M W A).trans ((mul_le_mul_of_nonneg_left (add_le_add t (hK 0)) h.le).trans_eq (by ring))
end YM.CF.Haro
