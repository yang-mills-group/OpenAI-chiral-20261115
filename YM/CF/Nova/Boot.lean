import YM.CF.Nova.Gore
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Nova
open Function Filter Metric Finset NormedSpace Lattice Laurent Kea Lat Fir Tulip Rush Cube Jill Ember SU Dial Thera Fock Peaks Cascade Flare Scroll Spire Sods CF.Jet Vault Paige Brace Branch Tenant Broc Pic MeasureTheory
open scoped Topology BigOperators Matrix MatrixOrder ContDiff Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {m L B N:Side}{j n:ℕ}{o:Odd L.val}{Y:Pricing j L o (Thread j)}{e b c v K a l r t w η τ:ℝ}{P:Grasp Y B e}{H:Pearl P}(D:Span H K b v c l r n)(p:n≤ (CSide m B).val)
variable {I:Type*}[MeasurableSpace I]{A:I→Bkg (Domain m B)}{Z:I→ℝ}{u:Measure I}{F:I→wit m B}{M:Jill.Male}
include p D
abbrev qpay(Z:I→ℝ)(F:I→wit m B)(u:Measure I):ℝ:=∫ i,‖Z i • (beamM m B (F i))‖ ∂u
lemma poised(Q:Tab H A u Z F M (K*(CSide m B).val) t w η)(hp:0<t)(h:t ≤ 1)(k:(CSide m B).val^10*t≤ min v 1):
 let a:= Kea.angel m P M; let T:=duty (CSide m B).val t c w; let U:= (∫ i,Z i ∂u)*a; let L:=gleam m P M*integralF m B Z F u
 U*(η*b/poseX-T) ≤ L.re ∧ |L.im|≤ T*U ∧ qpay Z F u ≤ ((1+w)*2*c)*U :=by
 intro a T U L
 let G:=gleam m P M; let E(i:I):=beamM m B (F i); let f(i:I):= Z i • E i
 let R(i:I):=hyle m P M (Z i:ℂ) (F i) (T*a)
 have he(i):R i=(G*f i).re+T*a* Z i:=by
   unfold R hyle f; rw [Complex.real_smul]; change _=(G*((Z i:ℂ)*E i)).re+_; rw [←mul_assoc]; rfl
 have hI:Integrable f u:=Q.rich; let y(i):=G*f i; have hy:Integrable y u:= hI.const_mul _; have hz:L=∫ i,y i ∂u:=Eq.symm (integral_const_mul ..)
 constructor
 · have hr: Integrable R u:=by rw [funext he]; exact hy.re.add (Q.bright.const_mul _)
   obtain ⟨A',W⟩:= Q.orbit; let V(i:I):=∑ j:Hat,R (A' j i); have hv: Integrable V u:= by apply integrable_finsetSum; intro i _; exact ((W i).1.integrable_comp_emb (A' i).measurableEmbedding).mpr hr
   have hi : (∫ i,Z i*η*(b*a)∂u)≤∫ i,V i∂u:=integral_mono ((Q.bright.mul_const _).mul_const _) hv (fun i=> rose D p Q hp h k A' (fun i=> (W i).2) i)
   have ht : ∫ i,V i∂u=poseX*(L.re+T*U):=by
     unfold V; rw [integral_finsetSum _ (fun i _=> show Integrable (fun k=>R (A' i k)) u from ((W i).1.integrable_comp_emb (A' i).measurableEmbedding).mpr hr)]; have he(i:Hat):(∫ v,R (A' i v)∂u)=∫ i,R i∂u:= (W i).1.integral_comp (A' i).measurableEmbedding _
     simp_rw [he]; rw [sum_const,card_univ,nsmul_eq_mul]; congr 1 -- tune
     rw [show R=(fun v=>(y v).re+T*a*Z v) from funext (by intro i; exact ‹∀ i,R i=(G*f i).re+T*a* Z i› i),integral_add (show Integrable (fun k=>(y k).re) u from hy.re) (Q.bright.const_mul _),show (∫ i,(y i).re ∂u)=(∫ i,y i∂u).re from integral_re hy,show (∫ i,T * a * Z i ∂u)=T*a*∫ i,Z i ∂u from integral_const_mul (T*a) _,hz]; unfold U; ring
   rw [ht,integral_mul_const,integral_mul_const] at hi; have he:U*η*b ≤ poseX*(L.re+T*U) :=le_trans (le_of_eq (b:=(∫ i,Z i∂u)*η*(b*a)) (by unfold U; ring)) hi; rw [mul_sub,sub_le_iff_le_add, ← mul_div_assoc, div_le_iff₀ pose_p]; nlinarith [pose_p]
 refine ⟨?_,?_⟩
 · have hq(i:I):|(y i).im| ≤ Z i*(T*a):=by
      unfold y f; rcases eq_or_lt_of_le (Q.same i) with v|v; rw [←v,zero_smul,mul_zero,Complex.zero_im,abs_zero,zero_mul]
      obtain ⟨d,H⟩:= (spin D p Q hp h k i v).2; have ht:= (Complex.abs_im_le_norm _).trans H; rw [Complex.sub_im,Complex.ofReal_im,sub_zero] at ht; rw [Complex.real_smul, show G*((↑(Z i):ℂ)*E i)= (↑(Z i):ℂ)*(G*E i) by ring, Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero,abs_mul,abs_of_pos v]; exact mul_le_mul_of_nonneg_left ht v.le
   rw [hz,← (show (∫ i,(y i).im∂u)=(∫ i,y i∂u).im from integral_im hy)]; refine (norm_integral_le_integral_norm _).trans ((integral_mono (hy.im.norm) (Q.bright.mul_const _) hq).trans_eq ?_); rw [integral_mul_const]; unfold U; ring
 unfold qpay; have he(i:I): ‖f i‖≤Z i*((1+w)*(2*c*Kea.angel m P M)):=by
    rcases eq_or_lt_of_le (Q.same i) with v|v; unfold f; simp [←v]; unfold f; rw [norm_smul, Real.norm_of_nonneg v.le]; exact mul_le_mul_of_nonneg_left (Yep.lim (spin D p Q hp h k i v).1) v.le
 change (∫ i,‖f i‖∂u) ≤ _; apply le_trans (integral_mono hI.norm (Q.bright.mul_const _) he); rw [integral_mul_const]; unfold U; exact le_of_eq (by unfold a; ring)
end YM.CF.Nova
