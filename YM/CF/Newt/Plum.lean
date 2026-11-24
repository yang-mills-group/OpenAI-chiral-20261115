import YM.CF.Newt.Crest
set_option autoImplicit false
noncomputable section
namespace YM.CF.Newt
open Function Filter Set Matrix Lattice Wilson RG Precision Pressure Tree Exterior MeasureTheory Metric
 AnalyticBridge.RelativeLogdet.Ink PhysicalNext.JointLoad.Heir Jet Push
open Push.Uniform (curve Slope meetVar Positions upperCol lowerCol block meet_derivative)
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {ι τ: Type} [Fintype ι] [Fintype τ] {A N C P d y s r v U B e D:ℝ} {n i j:ℕ}
variable {f f':Positions (ι⊕τ)→ℝ}{z m: Fish ι → Fish τ}{Pi₁: Fish ι → Fish τ →L[ℝ] Fish τ}{x:Fish ι}
def pace(n:ℕ) (A C:ℝ):ℝ:= 2^n * composeCost n (C*(3*A)) 1
lemma flow_cut (ha:1≤A)(hs:0<s)(h:∀ x': Fish ι, ‖x'‖<1→ Allows n z x' (A*s) ∧ Allows n m x' (A*s)∧ Slope f (meetVar (s•x') (z x'))=0)(hB:3*A*s<r)
 (hn:3*A*s≤1)(hv:Allows n (fun y=>m y-z y) x U)(hh:‖x‖<1)(hp:∀ w:Positions (ι⊕τ), ‖w‖<r→ ContDiffAt ℝ ω f w ∧ Allows n (fun y=> paintO (block f y)) w C)(hl:1 ≤ n)(hc:∀ y: Fish (ι⊕τ), ‖y‖<r→ Allows n (fun y=> Slope f' y - Slope f y) y D): -- D implicit
 let L:=paintO (block f 0)
 Allows n (fun x'=>Slope f' (meetVar (s•x') (m x'))-L (m x'-z x')) x (composeCost n D 1+pace n A C*s*U):=by
 intro L; let M(y:Fish ι):=meetVar (s•y) (m y); have hb:Allows n M x (3*A*s):=(turn_safe (h _ hh).2.1 (h _ hh).2.1 hs.le ha hh 0 (Set.left_mem_Icc.mpr zero_le_one)).germ (Eventually.of_forall fun i=>by simp [M])
 apply ((((hc _ (hb.value.trans_lt hB)).comp (hb.mono hn)).add (flow_buy ha hs h hB hn hv hh hp hl)).mono (le_of_eq (by unfold pace composeCost; ring))).germ; filter_upwards with y; unfold M; abel

def nudge (F:Positions (ι⊕τ)→ℝ) (Pi₁: Fish ι → Fish τ →L[ℝ] Fish τ)(m : Fish ι → Fish τ) (s:ℝ) (x:Fish ι): Fish τ:= m x-Pi₁ x (Slope F (meetVar (s • x) (m x)))
def pocket(n:ℕ)(A C P e:ℝ):ℝ:= 2^n*C*e+ 2^n * P*(composeCost n C 1+pace n A C*e)
structure Clinic(n:ℕ)(C P s r:ℝ)(f f':Positions (ι⊕τ)→ℝ)(Pi₁:Fish ι→ Fish τ→L[ℝ] Fish τ)(j:ℕ): Prop where
 cons:0<C
 pow:0<P
 ear {y:Positions (ι⊕τ)}: ‖y‖ < r → ContDiffAt ℝ ω f y ∧ Allows n (fun y=>paintO (block f y)) y C
 cut {y:Positions (ι⊕τ)}: ‖y‖<r→ Allows n (fun y=>Slope f' y-Slope f y) y (C*s^j)
 top {x:Fish ι}: ‖x‖<1→ Allows n Pi₁ x P
 delta {x:Fish ι}: ‖x‖<1→ Allows n (fun y=> ContinuousLinearMap.id ℝ _- (Pi₁ y).comp (paintO (block f 0))) x (C*s)
lemma newton (ha:1≤A)(hs:0<s)(ht:s≤1)(hh:∀ x': Fish ι, ‖x'‖<1→ Allows n z x' (A*s) ∧ Allows n m x' (A*s)∧ Slope f (meetVar (s•x') (z x'))=0)(hB:3*A*s<r)(hn:3*A*s≤1)(hl:1≤n)
 (h:Clinic n C P s r f f' Pi₁ j) (he:i+1≤j)(p:‖x‖<1)(hp: Allows n (fun y=>m y-z y) x (e*s^i)): Allows n (fun y=>nudge f' Pi₁ m s y-z y) x (pocket n A C P e*s^(i+1)):=by
 have hw:=flow_cut ha hs hh hB hn hp p (fun _ hy=>h.ear hy) hl (fun _ hy=> (h.cut hy).mono (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hs.le ht he) h.cons.le))
 have hr := appliance (h.delta p) hp
 apply ((subtract_p hr (appliance (h.top p) hw)).mono (le_of_eq (by dsimp only [pocket, pace,composeCost] at *; rw [pow_succ s]; ring))).germ; filter_upwards with x'; unfold nudge; simp only [_root_.sub_apply, ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply, map_sub]; abel

def streak (f:Positions (ι⊕τ)→ℝ)(P:Fish ι→Fish τ→L[ℝ] Fish τ)(s:ℝ)(m: Fish ι→Fish τ):ℕ→(Fish ι→Fish τ) | 0=> m | (i+1)=> nudge f P (streak f P s m i) s
structure Folded(m z: Fish ι→Fish τ)(n:ℕ)(t:ℝ): Prop where
 due x: ‖x‖<1 → Allows n (fun y=> m y-z y) x t
lemma purchase(n P₀:ℕ)(hl:1≤n)(hi:2≤P₀)(hC:0<C)(hp:0<P)(he:0<e)(hA:1≤A)(hb:0<r):∀ i:ℕ, i+2 ≤ P₀→∃ C' r':ℝ,0<C' ∧ 0<r' ∧
 ∀ {ι τ:Type} [Fintype ι][Fintype τ] (f f':Positions (ι⊕τ)→ℝ)(z m:Fish ι → Fish τ)(PI: Fish ι → Fish τ →L[ℝ] Fish τ) (s:ℝ),0<s→ s≤r' → Clinic n C P s r f f' PI P₀ →
 (∀ x:Fish ι, ‖x‖ < 1→ Allows n z x (A*s) ∧ Slope f (meetVar (s•x) (z x))=0)→
 Folded m z n (e*s^2) → Folded (streak f' PI s m i) z n (C'*s^(i+2)):=by
 intro i; induction i with
 | zero=> exact fun _=> ⟨e,1,he,zero_lt_one,fun _ _ _ _ _ _ _ _ _ _ _s=> _s⟩ -- tune
 | succ i ih=>
   intro hv; obtain ⟨X,Y,hX,hY,H⟩:= ih (by omega)
   let B:=X+A; have hA':1≤B:= le_trans hA (le_add_of_nonneg_left hX.le); have hB:0<B:= zero_lt_one.trans_le hA'
   let y:= min Y (min 1 ((min (r/2) 1)/(3*B))); have hy :0<y:=lt_min hY (lt_min zero_lt_one (by unfold B; have hp:0<min (r/2) 1:=lt_min (half_pos hb) zero_lt_one; positivity))
   let K:=1+|pocket n B C P X|; refine ⟨K,y,by unfold K; positivity,hy,?_⟩
   intro ι τ _ _ f f' z m Pi₁ s h0 hS ht hQ Hh
   let F:=streak f' Pi₁ s m i; have hz:s≤1:=hS.trans ((min_le_right ..).trans (min_le_left ..)); have hu:=H f f' z m Pi₁ s h0 (hS.trans (min_le_left ..)) ht hQ Hh
   have hh x (hx:‖x‖<1): Allows n z x (B*s) ∧ Allows n F x (B*s) ∧ Slope f (meetVar (s•x) (z x))=0:=by
        have he:=hQ x hx; refine ⟨he.1.mono (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hX.le) h0.le),?_,he.2⟩
        have he: X*s^(i+2)≤ X*s:= mul_le_mul_of_nonneg_left ((pow_le_pow_of_le_one h0.le hz (show 1 ≤ i+2 by omega)).trans_eq (pow_one _)) hX.le
        apply ((((hu.due _ hx).mono he).add (hQ _ hx).1).mono (Eq.ge (add_mul X A s))).germ; exact Eventually.of_forall fun y=> sub_add_cancel ..
   have hS' : 3*B*s ≤ min (r/2) 1:=(mul_comm s _).symm.trans_le ((le_div_iff₀ (show 0<3*B by positivity)).mp (hS.trans ((min_le_right ..).trans (min_le_right ..))))
   refine ⟨fun x hx=> ?_⟩
   rw [streak,show i+1+2= i+2+1 by omega]
   exact (newton hA' h0 hz hh ((hS'.trans (min_le_left ..)).trans_lt (half_lt_self hb)) (hS'.trans (min_le_right ..)) hl ht (show i+2+1 ≤ P₀ by omega) hx (hu.due _ hx)).mono (mul_le_mul_of_nonneg_right ((le_abs_self _).trans (le_add_of_nonneg_left zero_le_one)) (pow_nonneg h0.le _))
end YM.CF.Newt
