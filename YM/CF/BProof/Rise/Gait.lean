import YM.CF.BProof.Rise.Halo
import YM.CF.Jet.Quasar
/- smooth patch from norm budget. Choose K before screen for HT. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Cliff.Economy
open Function Filter Fock NormedSpace Finset Align Wick Spin Hearth
open SU Lat Dial Cube Tulip Hero Dream Lattice Jet Trek
open scoped Topology Matrix MatrixOrder InnerProductSpace Kronecker BigOperators Matrix.Norms.L2Operator Classical ContDiff
attribute [local instance] opCStarAlgebra
local notation "Gp"=> SU.group
variable (X:Chart SU.group)(x y:SU.E)(ξ:ℝ)
lemma ease_q (x y:ℝ): |ease x-ease y|≤ rateH*|x-y|:=by
 apply le_trans (b:=rateH * |Rise.clt x-Rise.clt y|) -- Trek namespace fix
 · conv_lhs=>rw [← Rise.ease_clt x,← Rise.ease_clt y] -- might rew both?
   simpa only [Real.norm_eq_abs,Real.dist_eq] using (Hero.expenses.easeW (Rise.clt x) (Rise.clt_z _) (Rise.clt y) (Rise.clt_z _))
 exact mul_le_mul_of_nonneg_left (Rise.clt_le ..) rate_p.le
def grow_ (s:ℝ): SU.group.Color := ease (s/ξ) • logG Gp x
def gait(s:ℝ):SU.E := SU.group.lieExp (grow_ x ξ s)
lemma gait_zero : gait x ξ 0=1:=by simp [gait,grow_] -- tune
variable (p:0<ξ)(h:ξ≤X.radius)(g: cd Gp x 1≤ξ) (i: X.C*ξ ≤ X.size)
include g h
lemma allotted : SU.group.chord x≤ X.radius:=by rw [← cd_one,cd_symm]; exact g.trans h
lemma grow' (t:ℝ) : ‖grow_ x ξ t‖ ≤ X.C*ξ:= by unfold grow_; rw [norm_smul,Real.norm_of_nonneg (easeZ _).1]; apply le_trans (mul_le_of_le_one_left (norm_nonneg _) (easeZ _).2); apply (X.width x (allotted X _ ξ h g)).trans; rw [←cd_one,cd_symm]; exact mul_le_mul_of_nonneg_left g (zero_le_one.trans X.C_one)
include p
lemma gait_self : gait x ξ ξ=x:=by rw [gait,grow_, div_self p.ne',ease_one,one_smul]; exact (X.exposes x (allotted X x ξ h g)).2
lemma growL (t s:ℝ) : ‖grow_ x ξ t-grow_ x ξ s‖≤ X.C * rateH*|t-s|:=by
 unfold grow_; rw [←sub_smul,norm_smul,Real.norm_eq_abs]; have he:logG Gp x=grow_ x ξ ξ:=by rw [grow_,div_self p.ne',ease_one,one_smul]
 have hp:=mul_le_mul (ease_q (t/ξ) (s/ξ)) ((congrArg norm he).trans_le (grow' X x ξ h g ξ)) (norm_nonneg _) (mul_nonneg rate_p.le (abs_nonneg _)) -- tune calc syntax
 refine hp.trans_eq ?_; rw [←sub_div,abs_div,abs_of_pos p]; field_simp -- tune
include i
lemma gait_close (t:ℝ):cd Gp (gait x ξ t) 1 ≤ X.C*(X.C*ξ):=by rw [cd_symm,cd_one]; exact (X.step _ ((grow' X x _ h g _).trans i)).trans (mul_le_mul_of_nonneg_left (grow' X x _ h g _) (zero_le_one.trans X.C_one))
abbrev lipBill(H:ℝ) := xm*H*(H*rateH)+1
lemma gait_lip (t s:ℝ) : cd Gp (gait x ξ t) (gait x ξ s) ≤ X.C*(X.C*rateH)*|t-s|:= by rw [mul_assoc]; exact (X.cost _ _ ((grow' X x _ h g _).trans i) ((grow' X x _ h g _).trans i)).trans (mul_le_mul_of_nonneg_left (growL X x ξ p h g t s) (zero_le_one.trans X.C_one)) -- rw mul_assoc picks wrong orientation tune
lemma gait_budget(S:Ballot)(t s:ℝ): let L:=lipBill X.C; ‖(SU.fund (gait x ξ t))-(SU.fund (gait x ξ s))‖≤ L*|t-s| ∧ ‖(scaledV (gait x ξ t) S).val-(scaledV (gait x ξ s) S).val‖≤L*|t-s| :=by
 intro L; have ht: xm*cd Gp (gait x ξ t) (gait x ξ s)≤L*|t-s|:=le_trans (mul_le_mul_of_nonneg_left (gait_lip X x ξ p h g i t s) xm_p.le) (by unfold L lipBill; linarith only [abs_nonneg (t-s)] ); exact ⟨(optic₁ ..).trans ht,(Xd_rate ..).trans ht⟩
omit g i p h
lemma bill_p : 1≤ lipBill X.C:=by unfold lipBill; have h1:= X.C_one; have ht:= rate_p; have hx:=xm_p; exact le_add_of_nonneg_left (by positivity)
lemma fund_s (x:SU.E) : ContDiff ℝ 1 (SU.fund ∘ (gait x ξ)):=by
 have hp:ContDiff ℝ ∞ (fun s:ℝ=> ease (s/ξ)):=by apply ContDiff.comp (g:=ease) (f:=fun s:ℝ=> s/ξ) ease_s; fun_prop -- division_zero automatic?
 have hs:ContDiff ℝ ∞ (grow_ x ξ):= hp.smul contDiff_const
 refine (Dream.smoothM _ (fun i j=>?_) ).of_le ?_ -- tune name
 exact (smoothExp i j).comp hs
 simp
lemma easyL{X:Type*}[NormedAddCommGroup X][NormedSpace ℝ X](f:ℝ→X)(v:ℝ)(u:1≤v)(h: ContDiff ℝ 1 f)(p:∀ t,‖f t‖=1)(g:∀ t s, ‖f t-f s‖≤ v*|t-s|)(x:ℝ): Allows 1 f x v:=by
 refine ⟨h.contDiffAt, fun i h=>?_⟩; interval_cases i <;> push_cast; rw [norm_iteratedFDeriv_zero,p]; exact u; rw [norm_iteratedFDeriv_one]; exact norm_fderiv_le_of_lipschitz ℝ (LipschitzWith.of_dist_le_mul (f:=f) (K:=⟨v,zero_le_one.trans u⟩) (by intro t s; change dist (f t) (f s) ≤ v*dist t s; rw [Real.dist_eq,dist_eq_norm]; exact g t s)) -- tune constructor
include p h g i
lemma plot(s:ℝ): Allows 1 (SU.fund ∘ (gait x ξ)) s (lipBill X.C):= easyL _ _ (bill_p _) (fund_s ξ x) (fun t=> CStarRing.norm_of_mem_unitary (fund_U _)) (fun t u=>(gait_budget X x ξ p h g i apex t u).1) _
lemma plotB(s:ℝ)(x':Ballot):Allows 1 (fun t=>(scaledV (gait x ξ t) x').val) s (lipBill X.C):=by
 let F(t:ℝ):= (scaledV (gait x ξ t) x').val
 apply easyL F (lipBill X.C) (bill_p _) _ (fun t=> vote_unit _) (fun s t=> (gait_budget X x ξ p h g i x' s t).2)
 have hp:= ((Jet.act_is 1).comp (f:=fun x'':ℝ=> (SU.fund (gait x ξ x''), x'.val)) ((fund_s ξ x).prodMk contDiff_const)); exact hp
end YM.CF.BProof.Cliff.Economy
