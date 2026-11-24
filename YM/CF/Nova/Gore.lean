import YM.CF.Nova.Suns
set_option autoImplicit false
noncomputable section
namespace YM.CF.Nova
open Function Filter Metric Finset NormedSpace Lattice Laurent Kea Lat Fir Tulip Rush Cube Jill Ember SU Dial Thera Fock Peaks Cascade Flare Scroll Spire Sods CF.Jet Vault Paige Brace Branch Tenant Broc Pic MeasureTheory
open scoped Topology BigOperators Matrix MatrixOrder ContDiff Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {m L B N:Side}{j n:ℕ}{o:Odd L.val}{Y:Pricing j L o (Thread j)}{e b c v K a l r t w η τ:ℝ}{P:Grasp Y B e}{H:Pearl P}(D:Span H K b v c l r n)(p:n≤ (CSide m B).val)
variable {I:Type*}[MeasurableSpace I]{A:I→Bkg (Domain m B)}{Z:I→ℝ}{u:Measure I}{F:I→wit m B}{M:Jill.Male}
-- eta lower comparison for center partners (needn't force exact symmetry of clipped kinetic). e.g. center sym any adjoint path. 
structure Tab (H:Pearl P)(A:I→Bkg (Domain m B))(u: Measure I) (G:I→ℝ)(F:I→wit m B)(M:Jill.Male)(k z w η:ℝ): Prop where
 orbit:∃ f:Hat→I≃ᵐ I,∀ x:Hat,MeasurePreserving (f x) u u ∧ ∀ i:I,A (f x i)=welt (A i) x∧ η*G i ≤ G (f x i)
 posY:0<η
 same i: 0≤ G i
 bright:Integrable G u
 rich: Integrable (fun i=> G i • (beamM m B (F i))) u
 -- hits small fields
 inner(i) (h:0<G i) :∃ (f:Cart (Domain m B))(d:Candle), speedB d (Domain m B) ∧ lawnK (gauge f (A i)) (Kea.tax d) z
 stock(i)(h:0<G i): Stock (A i) P M (F i) k w

def integralF(m B:Side)(G:I→ℝ)(F:I→wit m B)(μ:Measure I):ℂ:=∫ i,G i • beamM m B (F i) ∂μ
abbrev poseX:= (Fintype.card Hat:ℝ)
lemma pose_p:0<poseX:=by unfold poseX; positivity
lemma spiral (d:Candle)(h:speedB d N):slowT N d:=fun i j=> (h i j).trans (div_le_div_of_nonneg_right (by linarith [Real.pi_pos]) (by positivity))
include D p
lemma spin {t:ℝ}(Q:Tab H A u Z F M (K*(CSide m B).val) t w η)(h:0<t)(l:t ≤ 1)(k:(CSide m B).val^10*t≤ min v 1)(i:I)(hk:0<Z i) : Yep (K*(CSide m B).val) (mateK (CSide m B)) (F i) ((1+w)*(2*c*Kea.angel m P M)) ∧ ∃ d:Candle, ‖gleam m P M*beamM m B (F i) - (‖AMP m P d M‖:ℂ)‖≤ duty (CSide m B).val t c w*Kea.angel m P M:=by
 obtain ⟨f,d,b,s⟩:=Q.inner i hk; have hx:=emerge D p M (A i) f d (spiral d b) s h l k (F i) (Q.stock _ hk); exact ⟨hx.2.2.2,d,hx.2.1⟩
def hyle(m:Side)(P:Grasp Y B e)(M:Jill.Male)(z:ℂ)(F:wit m B)(a:ℝ):= (gleam m P M*z*beamM m B F).re+ a*z.re
-- Hat comparison POINTWISE. extra terms w maybe gauge-var.
lemma rose (Q:Tab H A u Z F M (K*(CSide m B).val) t w η)(hp:0<t)(g:t ≤ 1)(k:(CSide m B).val^10*t≤ min v 1)(f:Hat→I≃ᵐ I)(v:∀ x:Hat, ∀ i:I,A (f x i)=welt (A i) x∧ η*Z i≤ Z (f x i))(i:I): let a:=Kea.angel m P M; let T:=duty (CSide m B).val t c w; let V(y:I):= hyle m P M (Z y:ℂ) (F y) (T*a);  Z i*η*(b*a) ≤∑ x:Hat,V (f x i):=by
 intro a T V; have ha:0<a:= angel_p H D.stmt (D.plan _ p).1 D.p D.eP _ (D.plan _ p).2; let G0:=gleam m P M; let E(y:I):= beamM m B (F y); have he(y:I): V y=Z y * ((G0*E y).re+T*a):=by unfold V hyle; rw [mul_comm (gleam ..),mul_assoc]; simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]; unfold G0 E; ring
 have hk(y:I):0≤ V y:=by
    rw [he y]; rcases lt_or_eq_of_le (Q.same y) with l|l; swap; rw [←l,zero_mul]
    obtain ⟨u,t⟩:=(spin D p Q hp g k y l).2; have ht:=(Complex.abs_re_le_norm _).trans t; rw [Complex.sub_re,Complex.ofReal_re] at ht; apply mul_nonneg l.le; change |_ - _| ≤ T*a at ht; obtain ⟨b,h⟩:=abs_le.mp ht; have he:0≤ ‖AMP m P u M‖:=norm_nonneg _; dsimp only [G0,E]; linarith
 rcases lt_or_eq_of_le (Q.same i) with h|h; swap; · rw [←h,zero_mul,zero_mul]; exact sum_nonneg fun i _=> hk _
 obtain ⟨z,d,u,b'⟩:=Q.inner i h; obtain ⟨x,x'⟩:=D.gap (CSide m B) d; let y:= f x i; have hu:η * Z i ≤ Z y:=(v x i).2; have he':= Q.posY; have hZ:0<Z y:=(mul_pos he' h).trans_le hu
 let s:=sun d x (Domain m B); have ht : ‖gleam m P M*E y - (‖AMP m P s M‖:ℂ)‖≤ T*a:=by
    have hh:=movesh t z d b' x; rw [←(v x i).1] at hh; exact (emerge D p M _ _ _ (slows _ d u _) hh hp g k (F y) (Q.stock _ hZ)).2.1 -- tune
 have hy:b*a≤‖AMP m P s M‖:=let F':=skim _ s; (D.powV _ p M s F').1.trans_eq ((D.powV _ p M s F').2.2.1 x').symm
 change ‖G0*E y- _‖≤_ at ht; have hh:= (Complex.abs_re_le_norm _).trans ht; rw [Complex.sub_re,Complex.ofReal_re] at hh
 refine le_trans (b:=V y) ?_ (single_le_sum (fun j _=> hk (f j i)) (mem_univ x)); rw [he y,mul_comm (Z i)]
 exact (mul_le_mul_of_nonneg_right hu (mul_nonneg D.pos.le ha.le)).trans (mul_le_mul_of_nonneg_left (by linarith [abs_le.mp hh]) hZ.le)
end YM.CF.Nova
