import YM.CF.Jill.Line
set_option autoImplicit false
noncomputable section
namespace YM.CF.Jill
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Ember
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker
variable {ι:Type*}
abbrev Bin:= Axis→ℝ
def Bound(k:ℝ)(u:Bin):Prop:=‖u‖≤k
lemma b_abs(u:Bin)(i:Axis):|u i|≤‖u‖:=by exact norm_le_pi_norm u i
lemma height(u:Bin): ‖tmap u‖= ‖u‖:= le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg u)).mpr fun i=> (Complex.norm_real _).le.trans (norm_le_pi_norm ..)) ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i=> (Complex.norm_real _).symm.le.trans (norm_le_pi_norm (tmap u) i))
lemma abut(u:Bin):‖u‖^2 ≤ lengthSq (tmap u):=by
 obtain ⟨i,hi,H⟩:= exists_max_image univ (fun i=> |u i|) univ_nonempty
 have ht: ‖u‖≤|u i|:= (pi_norm_le_iff_of_nonneg (abs_nonneg (u i))).mpr (fun j=> H _ (mem_univ (α:=Axis) j))
 refine (pow_le_pow_left₀ (norm_nonneg _) ht 2).trans ?_; rw [show |u i|= ‖tmap u i‖ from (Complex.norm_real _).symm]; exact single_le_sum (f:=fun i=>‖tmap u i‖^2) (fun i _=>sq_nonneg _) (mem_univ _)
lemma b_base {u:Bin}(p:Bound Real.pi u): tmap u∈baseCube:= ⟨tmap_physical _,fun i=> by change |((↑(u i)):ℂ).re|≤_; rw [Complex.ofReal_re]; exact (b_abs u i).trans p⟩
lemma go_b{t:Tax ι}(x:ι→Bin)(e:∀ i,t.r i=‖x i‖)(h:∀ i,Bound Real.pi (x i)): Move t fun i _=> tmap (x i):= Move.left (fun i=> b_base (h i)) one_pos fun i=> by rw [height,e i,one_mul]
abbrev Male:= {i:Side// Odd i.val}
lemma court(k:ℕ)(l:1≤k){t:Tax ι}(M:ι→Male)(x:ι→Bin)(e:∀ i,t.r i=‖x i‖)(h:∀ i,Bound Real.pi (x i)):∃ c:ℝ,0<c∧∀ i,c*(t.r i)^2 ≤ ‖shell k (M i).val (tmap (x i))‖:=by
 obtain ⟨a,C,ha,hc,H⟩:=massPay k l (fun i=> (M i).val) (fun i=>(M i).property); have ht:=meter.low_pos; refine ⟨(1/2*meter.low^2)/C,by positivity,fun i=>?_⟩
 let K:=(M i).val; let p:= tmap (x i); have hp:p∈realCube zone:= base_subset_realCube zone_pos (b_base (h i)); have hm:= mass_ne k K (M i).property hp
 rw [shell,norm_div,le_div_iff₀ (norm_pos_iff.mpr hm)]
 refine (mul_le_mul_of_nonneg_left (show ‖mass k K p‖≤C by simpa using (H i).bound p (mem_cube_real (base_subset_realCube ha (b_base (h i))) ha)) (by positivity : 0 ≤ 1/2*meter.low^2/C*(t.r i)^2)).trans ?_
 rw [show (1/2*meter.low^2/C)*(t.r i)^2*C= (1/2)*(meter.low^2*(t.r i)^2) from (by field_simp),e i]
 exact (mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_left (abut _) (by positivity : (0:ℝ)≤meter.low^2)).trans (divisor_real_bounds K hp).1) (by norm_num : (0:ℝ)≤1/2)).trans ((D_lower K hp.1).trans (Complex.re_le_norm _)) -- tune
-- shell positive real
lemma express(j:ℕ)(u:Bin)(U:Side)(g:tmap u∈ realCube zone)(p: Odd U.val):shell j U (tmap u)= (‖shell j U (tmap u)‖:ℂ):=by
 let x:=tmap u; by_cases h:x=0
 · change shell _ _ x=_; rw [show tmap u=x from rfl,h]; simp
 let T:= mixL j U x
 rw [shell_inv _ _ g h, prodM_self _ (phys_mix j U p _ g.1)]
 let r:= ∑ i:Axis,(T i).re^2; have hr:0≤r:=sum_nonneg fun i _=>sq_nonneg _
 change ((1:ℂ)+(r:ℂ))⁻¹= _; rw [show (1:ℂ)+(r:ℂ)=((1+r:ℝ):ℂ) from (Complex.ofReal_add ..).symm,← Complex.ofReal_inv,Complex.norm_real,Real.norm_of_nonneg (by positivity)]
-- shift log analytic small relative value
private lemma portal{t:Tax ι}{F:ι→ℂ→ℂ}{d:ℤ}(H:Act t d F)(c:ℝ)(p:0<c)(u:∀ i,c*(t.r i)^d≤ ‖F i 0‖): Act t 0 fun i z=> Complex.log (F i z/F i 0):=by
 have e(i):F i 0≠0:=norm_pos_iff.mp (lt_of_lt_of_le (mul_pos p (zpow_pos (t.pos i) _)) (u i))
 let V i z:= F i z/F i 0; have ht:Act t 0 V:=by simpa only [V,div_eq_mul_inv,add_neg_cancel,div_eq_mul_inv] using H.mul (H.core.inv ⟨c,p,u⟩)
 have hx(i) : V i 0=1:=div_self (e i)
 let Ω:= closedBall (1:ℂ) (1/2); have hv:Ω ⊆ Complex.slitPlane:=by
   intro x a; apply Or.inl; have he:= Complex.abs_re_le_norm (x-1); rw [Complex.sub_re] at he; have h:(‖x-1‖≤1/2):=by simpa only [Ω,mem_closedBall,dist_eq_norm] using a
   norm_num only [Complex.one_re] at he; linarith [abs_le.mp he]
 obtain ⟨a,T,ha,hT,P⟩:= ht.dam; obtain ⟨l,y,hl,w,W⟩:= ht
 obtain ⟨B,b⟩:= (isCompact_closedBall (1:ℂ) (1/2:ℝ)).bddAbove_image (((show ContinuousOn Complex.log Ω from fun i p=>(Complex.differentiableAt_log (hv p)).continuousAt.continuousWithinAt)).norm)
 refine ⟨min (min a l) (1/(2*T)),max B 1,lt_min (lt_min ha hl) (by positivity),lt_max_of_lt_right one_pos,fun i z h=>?_⟩; obtain ⟨h,k⟩:= lt_min_iff.mp h; obtain ⟨t',m⟩:= lt_min_iff.mp h
 have he:V i z∈Ω:=by have he:=P i z (mem_ball_zero_iff.mpr t'); rw [hx i,zpow_zero,mul_one] at he; unfold Ω; rw [mem_closedBall,dist_eq_norm]; apply he.trans; have hh:=(_root_.lt_div_iff₀ (show 0 < 2*T by positivity)).mp k; linarith
 refine ⟨(Complex.differentiableAt_log (hv he)).comp z (W i z m).1,?_⟩
 rw [zpow_zero,mul_one]; exact (b ⟨_, he,rfl⟩).trans (le_max_left ..)
lemma out_b' {t:Tax ι}(j)(k:1≤j)(M:ι→Male)(x:ι→Bin)(e:∀ i,t.r i=‖x i‖)(h:∀ i,Bound Real.pi (x i))(a:Axis): Act t 0 fun i z=>Complex.log (shell j (M i).val (tmap (x i)+spark a (raf t i z))/shell j (M i).val (tmap (x i))):=by
 let F(i:ι)(z:ℂ):=tmap (x i)+spark a (raf t i z); have ht:Move t F:= Move.add (go_b x e h) (sparkBud t (raft ..) a) (by intro; simp [raf,spark])
 obtain ⟨r,H,R⟩:= court j k M x e h; let T i z:=shell j (M i).val (F i z)
 have hp i: F i 0=tmap (x i):=by simp [F,raf,spark]
 change Act t 0 fun i z=>Complex.log (T i z/shell j (M i).val (tmap (x i)))
 have he:(fun i=>T i 0)=(fun i=>shell j (M i).val (tmap (x i))):=funext fun i=>by simp [T,hp]
 have hk:= portal (t:=t) (F:=T) (ht.glass (fun i=>(M i).val) (fun i=>(M i).property) j k) r H (fun i=> by unfold T; rw [hp,zpow_ofNat]; exact R i); convert hk using 1; ext1 i; ext1 z; rw [show T i 0= _ from congr_fun he i]
end YM.CF.Jill
