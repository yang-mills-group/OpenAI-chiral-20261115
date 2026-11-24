import YM.CF.Onyx.Pelt
set_option autoImplicit false
noncomputable section
namespace YM.CF.Onyx
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Ember Jill Flare
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
open MeasureTheory
open YM.Stationary (Gaia cartWeight)
variable {N:Side}{x:Gaia}{k:Site N}{R A e D r B:ℝ}{j:ℕ}
def duel (R:ℝ)(s:Offset N)(k:Site N):Gaia:= R • moor (glen s k)
lemma cost(h:0<R)(e:x∈ pie R k)(s:Offset N): ‖x-duel R s k‖ ≤ R*(4*pinch N):=by
 rw [duel]; nth_rw 1 [← smul_inv_smul₀ h.ne' x]; rw [←smul_sub,norm_smul,Real.norm_of_nonneg h.le]; exact mul_le_mul_of_nonneg_left (moor_s e) h.le
lemma bend(h:0<R)(e:x∈ pie R k)(s:Offset N): ‖x‖ ≤ R*(4*pinch N + 2*‖glen s k‖):=by
 refine (norm_le_norm_sub_add _ (duel R s k)).trans ?_; rw [mul_add]; refine add_le_add (cost h e _) ?_; unfold duel; rw [norm_smul,Real.norm_of_nonneg h.le]; exact mul_le_mul_of_nonneg_left (moor_z _) h.le
lemma load (s:Offset N)(M:Male)(R D:ℝ)(h:0<R)(k:Site N)(j:ℕ)(z:Cover)(F:Site N→Peb): ‖sled s (sulk s j M R D F) z R k‖ = R⁻¹ * (Real.exp (-(soft R D*disk j M (glen s k))) * ‖F k‖):=by
 unfold sled sulk; rw [norm_smul,norm_smul,norm_smul, show ‖charK s k z‖=1 from mode_real _ _ (tmap_physical _),one_mul,Real.norm_of_nonneg (by positivity),Real.norm_of_nonneg (Real.exp_pos _).le]
lemma coal(h:0<R)(w:0<A)(y:0<e)(g:0<B)(q:0<D)(f:ℝ)(p:Gaia)(m:0<‖p‖)(v:ℝ)(t:0<v)(b:A*v^2≤f)(z:‖p‖≤R*(e*v)): R⁻¹*(Real.exp (-(soft R D*f))*(B/v))≤ (B*e)*house (A/(D*e)^2) p:=by
 let F:= Real.exp (-(soft R D*f)); let G:=tog (A/(D*e)^2) p; have ht:F≤G:=Real.exp_le_exp.mpr (by
    rw [neg_mul]; apply neg_le_neg; unfold soft; refine le_trans ?_ (mul_le_mul_of_nonneg_left b (by positivity)); refine le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ m.le z _) (show 0≤ A/(D*e)^2 by positivity)) ?_; apply le_of_eq; field_simp)
 change R⁻¹*(F*(B/v))≤ B*e*(G/‖p‖)
 rw [show R⁻¹*(F*(B/v))=(B/(R*v))*F from (by field_simp),show B*e*(G/‖p‖)= (B*e/‖p‖)*G from (by ring)]
 apply mul_le_mul _ ht (Real.exp_pos _).le (by positivity); rw [div_le_div_iff₀ (mul_pos h t) m]; nlinarith only [mul_le_mul_of_nonneg_left z g.le]
lemma pulse (h:0<R)(w:0<A)(y:0<e)(g:0<B)(q:0<D)(f:ℝ)(z:0≤f)(p:Gaia)(m:0<‖p‖)(l:ℝ)(t:0<l)(c: R*l ≤1)(o:‖p‖≤ R*l*e): R⁻¹*(Real.exp (-(soft R D*f))*(B/l))≤ (B*e / Real.exp (-A*e^2))*house A p :=by
 let F:= Real.exp (-(soft R D*f)); let G:=tog A p; let K:=Real.exp (-A*e^2); have hG:0<K:=Real.exp_pos _; have hv: F≤1:=by
    unfold F; rw [Real.exp_le_one_iff,neg_nonpos]; unfold soft; positivity
 have ht: K≤G:=Real.exp_le_exp.mpr (by rw [neg_mul,neg_mul]; gcongr; exact le_trans o (mul_le_of_le_one_left y.le c))
 change R⁻¹*(F*(B/l))≤ _*(G/‖p‖)
 rw [show R⁻¹*(F*(B/l))=F*(B/(R*l)) from (by field_simp),show (B*e/K)*(G/‖p‖)= G/K*(B*e/‖p‖) from (by ring)]
 refine mul_le_mul (hv.trans ((one_le_div hG).mpr ht)) ?_ (by positivity : 0≤ B/(R*l)) ((show 0 ≤ F from (Real.exp_pos _).le).trans (hv.trans ((one_le_div hG).mpr ht))) -- tune
 rw [div_le_div_iff₀ (mul_pos h t) m]; nlinarith only [mul_le_mul_of_nonneg_left o g.le]
lemma hold_p (H:1≤j)(p:0<r)(u:0<B)(d:0<D): ∃ V: Gaia→ℝ,Integrable V∧∀ p: Gaia,p≠0→∀ {N: Side}{F:Site N→Peb}{M:Male}{s:Offset N}{R:ℝ}, Even N.val→FormU s j M r B F→0<R→R*pinch N ≤1→∀ z:Cover,‖apr (sled s (sulk s j M R D F) z R) R p‖≤ V p:=by
 obtain ⟨c,b,hc,g,X⟩:=stern H p; obtain ⟨w,e,hw,he,Z⟩:=soul j H; obtain ⟨a,l,hx,hv,V⟩:=Jill.zip H; let W:=4*b+2; let A:=a/(D*W)^2; let S:=4+2*c; have hS:0<S:=by unfold S; positivity
 have hW:0<W:=by unfold W; positivity
 have hA:0<A:=by unfold A; positivity
 let K:=e*W; let G:=B*S/Real.exp (-A*S^2); have hG:0<G:=by unfold G; positivity
 have hK:0<K:=mul_pos he hW
 let f(x:Gaia):=(K+G)* house A x; refine ⟨f,(pen hA).2.const_mul _,fun x h {N} {F} {M} {s} {R} hN l v t z=>?_⟩
 have hp:=pinch_pos N; have hx' :0< ‖x‖:=norm_pos_iff.mpr h; have hy:0< house A x:=div_pos (Real.exp_pos _) hx'
 by_cases U:∃ i:Site N,x∈ pie R i; swap; · rw [void_f (not_exists.mp U),norm_zero]; unfold f; positivity
 obtain ⟨i,U⟩:=U; rw [shout U,load s M R D v]; unfold f; rw [add_mul]; let p':=glen s i; have ht:= bend v U s
 by_cases m: r*pinch N^2 < disk j M p'
 · apply (le_add_of_nonneg_right (mul_nonneg hG.le hy.le))|>.trans' -- tune
   have hz := (X N M s i hN).2 m; change pinch N ≤ b*‖p'‖ at hz; have hg:Bound Real.pi p':=orb _ _ hN; have hi:0<‖p'‖:=by nlinarith
   rw [l.far i m]; apply le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ((Z M p' hg 1 one_pos).2) (Real.exp_pos _).le) (show 0≤R⁻¹ by positivity)); refine coal v hx hW he d (disk j M p') x hx' _ hi (V M p' hg).1 (ht.trans ?_); refine mul_le_mul_of_nonneg_left ?_ v.le; unfold W; change 4*pinch N+2*‖p'‖ ≤ (4*b+2)*‖p'‖; linarith
 apply (le_add_of_nonneg_left (mul_nonneg hK.le hy.le))|>.trans'; refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (l.near i (le_of_not_gt m)) (Real.exp_pos _).le) (show 0≤R⁻¹ by positivity)).trans (pulse v hA hS u d _ (show 0≤disk j M p' from norm_nonneg _) x hx' _ hp t ?_)
 have hj : ‖glen s i‖≤ c*pinch N:=(lt_of_not_ge (fun w=> m ((X N M s i hN).1 w))).le; refine ht.trans ?_; rw [mul_assoc R]; apply mul_le_mul_of_nonneg_left _ v.le; unfold S; linarith
end YM.CF.Onyx
