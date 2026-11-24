import YM.SU5.Selected.Dais.Zeta
import YM.SU5.Selected.Dais.Ange
import YM.SU5.FiniteGaugeData.Signal.OceanPort
/-! Exactly flat price and late penalty at t². Full rotor/gauge clause still to be imposed. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Dais.Span
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Ember Jill SU Rush Tulip Cube Fock Peaks Dial Spire Vault Scroll Paige Brace Kea Parity
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Matrix.Norms.L2Operator Kronecker ComplexOrder Classical
attribute [local instance] opCStarAlgebra
variable {N:Side}{d:Candle}{t:ℝ}{j:ℕ}
def cake(t e:ℝ):= e+t^2*(1-e)
lemma cake_pos (x:ℝ)(p:0<x)(h:0<t)(v:t≤1):0<cake t x:=by rw [cake,show x+t^2*(1-x)=t^2+(1-t^2)*x from (by ring)]; nlinarith only [sq_pos_of_pos h,mul_nonneg (show 0≤1-t^2 from by nlinarith) p.le]
lemma ace (S:Slide N d)(g:Even N.val)(j:ℕ)(M:Jill.Male) (t:ℝ):
 (grip (tickA N) (Dofu N (field S j M)) t).det=(↑((∏ i:Stag N,cake t (disk j M (angle S i)))^2):ℂ):=by
 let P:=tickA N; let K:=field S j M; let X:= ∏ i:Stag N,cake t (disk j M (angle S i)); let U: Stag N→ Op SpinIdx:= fun _ => Aop
 let f:= U*(K+t^2 • (1-K))*U+(1-U); have hp: grip P (Dofu N K) t=Dofu N f:=by unfold Parity.grip cards f; rw [show P= _ from landP N]; simp only [map_add,map_mul,map_sub,map_smul,map_one]; rfl -- tune
 have ht(i:Stag N): f i=((cake t (disk j M (angle S i)):ℝ):ℂ) • Aop+(1-Aop):=by
    change Aop*((K i)+ t^2 • (1-K i))*Aop+(1-Aop)= _; unfold cake; push_cast; congr 1
    rw [mul_add,Algebra.mul_smul_comm,_root_.mul_sub, _root_.mul_one,add_mul, Algebra.smul_mul_assoc,_root_.sub_mul,footQ S g j M i, AOne]; -- AOne namespace? module coerces mix
    simp only [show ∀ (x:ℝ)(y:Op SpinIdx),x • y=(x:ℂ) • y from fun x y=>by ext; simp [Complex.real_smul],← Complex.ofReal_pow]; module
 change (grip P _ _).det= (↑(X^2):ℂ); rw [hp]; change (twist _ (arch f)).det=_; rw [det_d,det_a]; simp_rw [ht,seatQ,← Complex.ofReal_pow]; push_cast; rw [Finset.prod_pow]; unfold X; rw [Complex.ofReal_prod]
lemma flat_prize (S:Slide N d)(g:Even N.val)(M:Jill.Male) (h:0<t)(v:t≤1) (p:∀ i:Stag N,0<disk j M (angle S i)) : let W:= tickA N; let Q:= Dofu N (field S j M);
 Real.log (grip W Q t).det.re /2 ≤ Real.log (∏ i:Stag N,disk j M (angle S i)) + ∑ i:Stag N,t^2/(disk j M (angle S i)):=by
 let f(i:Stag N):=disk j M (angle S i); let g₀(i:Stag N):=cake t (f i); intro W Q; rw [ace S g]; change Real.log ((↑((∏ i:Stag N,g₀ i)^2):ℂ).re) /2 ≤ _; have hp :=fun i=>cake_pos _ (p i) h v
 rw [Complex.ofReal_re,Real.log_pow,Real.log_prod (fun i _ => (hp i).ne'),Real.log_prod (fun i _=> (p i).ne'),←sum_add_distrib]; push_cast; rw [mul_div_cancel_left₀ _ (by norm_num : (2:ℝ)≠0)] -- multiplication order? type
 apply sum_le_sum; intro i _; rw [add_comm (Real.log _), ←sub_le_iff_le_add,← Real.log_div (hp i|>.ne') (p i|>.ne')]; apply (Real.log_le_sub_one_of_pos (div_pos (hp i) (p i))).trans; rw [sub_le_iff_le_add]; change g₀ i/f i≤ t^2/f i+1; have h':0<f i:=p i; field_simp; unfold g₀ cake; nlinarith only [mul_nonneg (sq_nonneg t) (p i).le]
abbrev candy(j:ℕ)(N:Side)(M:Jill.Male):= Real.log (∏ i:Stag N,disk j M (angle (too N) i))
lemma blank_disk {L B m:Side}{o:Odd L.val}{Y: Pricing j L o (Thread j)}{e:ℝ}(P:Grasp Y B e)(p:0<e)(k:P.roundZ≤ (CSide m B).val)(u: Pad j (CSide m B))(M:Jill.Male): Real.log (Kea.angel m P M)=candy j (CSide m B) M:= congrArg Real.log (rich k p M u emptyC (too _))
lemma delay {j:ℕ}(p:1≤j): ∃ C:ℝ,0<C∧∀ {N:Side},Pad j N → ∀ (M:Jill.Male)(t:ℝ),0<t→ t≤1 → Real.log (grip (tickA N) (spar j M (1:Bkg (More N))) t).det.re /2 ≤ candy j N M+ (N.val^4:ℝ)*C*t^2:=by
 obtain ⟨c,D,h₀,hD,h⟩:=Jill.zip p
 refine ⟨45*32/c,by positivity,fun {N} a M t p v=>?_⟩; let K:=too N; have hp: spar j M (1:Bkg (More N))= Dofu N (field K j M):=by rw [←Signal.Sparkle.LocalPlane.free1]; exact a.2 emptyC K M
 let f(x:Site N):= disk j M (pm x); have hx(x:Site N):c*‖pm x‖^2 ≤ f x:= by
    let s:=Classical.arbitrary SU.Slot; exact (h M (pm x) (by simpa only [K,too_u] using up_p K a.1 (x,s))).1
 have hP(x:Site N):0<f x:=(mul_pos h₀ (pow_pos (pt_p _) _)).trans_le (hx x); have ht := flat_prize K a.1 M p v (j:=j) (fun i=> by rw [show angle (too N) i=pm i.1 from too_u N i]; exact hP _) -- K vs too
 rw [hp]; refine ht.trans (add_le_add le_rfl ?_); change ∑ i:Stag N,_ ≤ _; simp_rw [show ∀ i:Stag N,angle K i=pm i.1 from fun i=>too_u N i]; rw [Fintype.sum_prod_type]; simp_rw [sum_const,card_univ,slots,nsmul_eq_mul,← Finset.mul_sum] -- maybe mul_sum
 let P:=(t^2*c⁻¹); have he(x:Site N): t^2 /disk j M (pm x) ≤ P*(‖pm x‖^2)⁻¹:= (div_le_div_of_nonneg_left (sq_nonneg _) (mul_pos h₀ (pow_pos (pt_p x) _)) (hx x)).trans_eq (by unfold P; field)
 let A:=(N.val:ℝ); change 45* ∑ i:Site N, (t^2/f i) ≤ (A^4)* (45*32/c)*t^2 -- tune casts
 refine (mul_le_mul_of_nonneg_left (sum_le_sum (fun i _=>he i)) (by positivity)).trans ?_; rw [←mul_sum]; exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (corner (N:=N)) (by unfold P; positivity)) (by norm_num : (0:ℝ)≤45)).trans_eq (by unfold P; ring)
end YM.CF.Dais.Span
#print axioms YM.CF.Dais.Span.delay
