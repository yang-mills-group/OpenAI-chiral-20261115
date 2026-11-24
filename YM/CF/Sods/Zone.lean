import YM.CF.Sods.Toss
import YM.CF.Kea.Shift
set_option autoImplicit false
set_option maxHeartbeats 360000
noncomputable section
namespace YM.CF.Sods
open Function Filter Metric Finset Kea Lat Lattice Laurent Fir Rush Tulip Cube SU
open scoped Topology BigOperators Matrix ContDiff Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {N:Side}{k:ℝ}
lemma windy(f g:Cart N)(X:Bkg N): Lattice.gauge f (Lattice.gauge g X)= Lattice.gauge (f*g) X:=by funext i; unfold Lattice.gauge; simp [mul_assoc]
lemma windy_u(X:Bkg N):Lattice.gauge 1 X=X:=by funext i; simp [Lattice.gauge]
abbrev lawnK(U V:Bkg N)(k:ℝ):Prop:=∀ x,Cube.cmp firstF (U x) (V x) ≤ k
lemma lawnK.join {U V:Bkg N}(p:lawnK U V k)(f:Cart N):lawnK (gauge f U) (gauge f V) k:=by intro x; unfold Lattice.gauge; rw [cmp_right,cmp_left]; exact p x
lemma tax_peg(x:Candle)(a:Axis)(z:Site N)(n:ℕ):travel (Kea.tax x) z (List.replicate n (posDir a))= waveG (x a)^n :=by
 induction n generalizing z with
 | zero=>simp [travel]
 | succ n ih=> rw [List.replicate_succ,travel, ih, Step.pos_read,pow_succ']; rfl
lemma tide (d:Candle)(N:Side): layout (Kea.tax d (N:=N)) ∈ Set.univ:=trivial
lemma pacer (N:Side)(d:Candle):gauge (layout (Kea.tax d (N:=N))) (Kea.tax d)=wob N (fun a=> waveG (d a)^N.val):=by
 let V:=Kea.tax d (N:=N)
 funext i; have hp:=paleB V (le_refl (0:ℝ)) (tax_guard d N 0 le_rfl).1 i; have hv:Cube.cmp _ _ _=0:=le_antisymm (by simpa only [mul_zero] using hp) (norm_nonneg _)
 have hh:= group.mat_injective (show fund _= _ from sub_eq_zero.mp (norm_eq_zero.mp hv))
 rw [show (fun a=> waveG (d a)^N.val)=yolk V from ?_]; exact hh
 funext a; exact (tax_peg d a _ _).symm
lemma snap_p(u:TF)(k:ℕ): waveG u ^ k=waveG (snapC u k):=by
 induction k with
 | zero=>apply group.mat_injective; change (1:Op F)=Matrix.diagonal _; ext a b; by_cases h:a=b<;>simp [h,Matrix.one_apply,snapC,pw,BZ.phase]
 | succ k ih=>rw [pow_succ,ih,tax_mul]; congr 1; apply Subtype.ext; simp [snapC,add_smul]
def speedB (d:Candle)(N:Side):Prop:=∀ a i, |(d a).val i| ≤ 5 * Real.pi / N.val
lemma loft:∃ (r:ℕ)(c C:ℝ), 1 ≤ r∧ 0<c∧ 0<C∧ ∀ N:Side,∀ U:Bkg N,∀ e:ℝ,0≤e→ PlaqBound firstF U e→∀ k:ℝ,0<k→k≤1→ N.val^2 * e ≤ c*k^r→ ∃ F:Cart N,∃ d:Candle,speedB d N∧lawnK (gauge F U) (Kea.tax d) (C*k):=by
 obtain ⟨r,C,c,h1,C',c',H⟩:=accord (E:=F) (I:=Axis); refine ⟨r,c/32,400*(c/32)+C,h1,by positivity,by positivity,fun N U e h hp k u v he=>?_⟩
 let T(i:Axis):UNI F:= (yolk U i).val
 obtain ⟨V,p,V'⟩:= H k u v T (fun i=>SU.fund_det (yolk U i)) (fun i j=>le_trans (cyc_money U h hp i j) (by linarith))
 choose d hd t Q using V'; let x:E:= ⟨V,p⟩; let F0: Cart N:=fun _=> x⁻¹; let Z(a:Axis):TF:=⟨d a,hd a⟩; let P(a:Axis):= snapC (Z a) (N.val:ℝ)⁻¹; have hv:=nPos N
 have heq(i):waveG (P i)^N.val=waveG (Z i):=by rw [snap_p]; congr 1; apply Subtype.ext; change (N.val:ℝ) • (_⁻¹ • (Z i).val)=(Z i).val; simp only [smul_smul, mul_inv_cancel₀ hv.ne',one_smul]
 let K:=layout U; let D:Bkg N:=wob N (fun i=>waveG (P i)^N.val); let E₁:=layout (Kea.tax P (N:=N))
 have he':N.val^2*e ≤ c/32*k:=le_trans he (by gcongr; exact (pow_le_pow_of_le_one u.le v h1).trans_eq (pow_one _))
 have hg:lawnK (gauge F0 (wob N (yolk U))) D (C*k):=by
   rintro ⟨i,a⟩; by_cases g:drift i a; swap
   · simp only [D,wob,Lattice.gauge,F0,g,ite_false,mul_one, mul_inv_cancel] -- tune
     rw [cmp_id]; positivity
   have Hx:=Q a; rw [← twist_norm (star V),map_sub,twist_inv] at Hx
   simp only [D,wob,Lattice.gauge,F0,g,ite_true,heq]; rw [twist_formula] at Hx; exact Hx
 have hK:lawnK (gauge F0 (gauge K U)) (gauge F0 (wob N _)) ((400*(c/32))*k):=(lawnK.join (k:=400*(c/32)*k) (fun i=> le_trans (paleB U h hp i) (by nlinarith)) F0)
 have hx:lawnK (gauge F0 (gauge K U)) D ((400*(c/32)+C)*k):=fun i=> (cmp_triangle firstF _ _ _).trans ((add_le_add (hK i) (hg i)).trans_eq (by ring))
 refine ⟨E₁⁻¹ * (F0*K),P,fun i j=>?_,?_⟩
 · change |(N.val:ℝ)⁻¹* d i j|≤ _; rw [abs_mul,abs_of_pos (inv_pos_of_pos hv)]; apply le_trans (mul_le_mul_of_nonneg_left (t i j) (by positivity)); apply le_of_eq; simp [F]; ring
 have hh:= lawnK.join hx E₁⁻¹; rw [windy,windy,mul_assoc,show D=gauge E₁ _ from (pacer N P).symm,windy,inv_mul_cancel,windy_u] at hh; exact hh -- tune D
end YM.CF.Sods
