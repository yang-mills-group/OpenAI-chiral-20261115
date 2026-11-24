import YM.SU5.Selected.Rail.Faune
/-! # Power residual projection. Genuine rate in all four coordinates.
-/
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Crest.Rail
open Function Filter Metric NormedSpace Lattice Laurent Bloch Next.Free MeasureTheory
open Ember Jill Fir Shore Real Airy Fock Topology
open scoped Topology BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace ComplexOrder
local notation "I"=>Complex.I
local notation "φ" => 2*π
local instance : Fact (0<φ):= ⟨piRank⟩
attribute [local instance] opCStarAlgebra
open Finset Lat
variable {n k t:ℕ}{q:Type*}[Fintype q][DecidableEq q]
lemma treaty {r:ℝ}(p:0≤r)(v:r≤1)(K L:ℕ)(u:0<K) : (1-r)^(K*L) * r^L ≤ ((K:ℝ)⁻¹)^L:=by
 let y:=1-r; have h:0 ≤ y:=sub_nonneg.mpr v; have hx:y≤1:=sub_le_self _ p; let a:=∑ i∈range K, y^i; have hg:(K:ℝ)*y^K≤ a:=by 
    let S:=Finset.range K
    rw [show (↑K:ℝ)*y^K= ∑ i∈ S,y^K from (by simp [S,nsmul_eq_mul])]; exact sum_le_sum (fun i h'=>pow_le_pow_of_le_one h hx (mem_range.mp h').le) -- tune
 have he:a*r≤1:=by unfold a; rw [show r=1-y from (by unfold y; ring),geom_sum_mul_neg]; exact sub_le_self _ (pow_nonneg h K)
 rw [pow_mul,←mul_pow]; apply pow_le_pow_left₀ (mul_nonneg (pow_nonneg h K) p); 
 rw [← one_div]; apply (le_div_iff₀ (show (0:ℝ)<K by exact_mod_cast u)).mpr; nlinarith only [mul_le_mul_of_nonneg_right hg p,he]
lemma welt(k:ℕ)(w:Coast)(Z:q→basisRule):ShiftY k Z w=(lacuna w)^k • ShiftY 0 Z w:=by ext; simp [ShiftY,hull,tilt]
lemma fish_guard(N:Side)(x:Site N) : Bound Real.pi (pm x):=stemG.mp (stem_one _)
lemma gratitude {x:Bin}(p:x∈stemGuard)(t:x≠0)(M:Maj) : disk 4 M x≤1:=by
 -- invoice. rewrite as `(1+s)^(-1)`. 
 let F:=tmap x; let Z:=mixL 4 M.val F; let a:=∑ i:Axis,(Z i).re^2; have hp:F∈realCube zone:=base_subset_realCube zone_pos (b_base (stemG.mp p)); have hF:F≠0:=gentil p t; have ha:0≤a:=sum_nonneg fun i _=>sq_nonneg _
 unfold disk; rw [shell_inv 4 M.val hp hF, prodM_self _ (phys_mix 4 M.val M.property _ hp.1)]; change ‖((1:ℂ)+(a:ℂ))⁻¹‖ ≤ 1; rw [←Complex.ofReal_one,←Complex.ofReal_add,norm_inv,Complex.norm_of_nonneg (by positivity)]; exact inv_le_one_of_one_le₀ (by linarith)
lemma shallow_cost {x:Bin}(p:x∈stemGuard)(t:x≠0)(Z:q→basisRule)(C:ℝ)(h:‖ShiftY 0 Z (harbor x)‖≤ C) (l:ℕ)(M:Maj) :
  ‖Deep M (l+2) Z x‖ ≤ vlow⁻¹ * ‖x‖^l * C:=by
 unfold Deep; rw [welt, lacuna_h,show _^_= fleece (l+2) x from (rfl: fade (x 3)^(l+2)=_), Matrix.mul_smul, ← Matrix.smul_mul]; exact (Matrix.l2_opNorm_mul ..).trans (mul_le_mul (arc_plain l _ (disk_wagon p M t)) h (norm_nonneg _) ((norm_nonneg _).trans (arc_plain l _ (disk_wagon p M t)))) -- mul_le_mul expects 0≤‖Y‖ and 0≤b where b what? tune
lemma afloat {x:Bin}(p:x∈stemGuard)(t:x≠0)(Z:q→basisRule)(C:ℝ)(h:‖ShiftY 0 Z (harbor x)‖≤ C) (l K:ℕ)(e:0<K)(M:Maj):
    let a:=disk 4 M x; let V:=(1-a:ℝ)^(K*l); ‖ (↑V:ℂ) • Deep M (2*l+2) Z x‖ ≤ vlow⁻¹*(vlow⁻¹)^l*C * ((K:ℝ)⁻¹)^l:=by
 intro a V; let f:=vlow; have h₀ : 0<f:= vpay; have hf:0≤ V:= pow_nonneg (sub_nonneg.mpr (gratitude p t M)) _; have hp : 0 ≤ C:= (norm_nonneg _).trans h
 have he: ‖x‖^ (2*l:ℕ) ≤ (f⁻¹)^l*a^l:=by rw [pow_mul,← mul_pow]; apply pow_le_pow_left₀ (sq_nonneg ‖x‖); rw [le_inv_mul_iff₀ h₀]; exact disk_price p M -- fails if l=0 use instead
 rw [norm_smul,Complex.norm_of_nonneg hf]; apply (mul_le_mul_of_nonneg_left (shallow_cost p t Z C h _ M) hf).trans; let F:= f⁻¹*f⁻¹^l * C; have hF:0≤F:=by unfold F; positivity
 have hg: V*a^l ≤ ((K:ℝ)⁻¹)^l:=treaty (show 0 ≤ a from norm_nonneg _) (gratitude p t M) _ _ e; refine le_trans ?_ (mul_le_mul_of_nonneg_left hg hF); change V*(f⁻¹*‖x‖^(2*l)* C) ≤ f⁻¹*f⁻¹^l*C * (V*a^l); nlinarith only [mul_le_mul_of_nonneg_left he (show 0 ≤ V*f⁻¹*C by positivity)]
-- recurrence R
variable (Z:q→ basisRule){N:Side} (M:Maj)(u:Site N)
local notation "P0" N:max=> freeze (fun _:Site N=> Aop)
def betaA (M:Maj)(x:Bin): Op SpinIdx:= bar 4 M.val (tmap x)
abbrev wageErr (N:Side)(M:Maj):Op (SpinN N):= tip N M * (1-P0 N)
def spirale (N:Side)(M:Maj)(y:ℕ)(i:Site N):ℂ:= ↑( (1-disk 4 M (pm i))^y)
lemma vessel : wageErr N M= freeze (fun i:Site N=> betaA M (pm i) * (1-Aop)):=by
 rw [wageErr,show 1-P0 N=freeze (fun _:Site N=>(1-Aop)) from (freeze_one (N:=N) (n:=SpinIdx)) ▸ (freeze_sub (fun _=>(1:Op SpinIdx)) (fun _=> Aop)).symm]; rw [tip,freeze_mul]; rfl
lemma camper {x:Bin}(p:x∈stemGuard)(t:x≠0):betaA M x* (1-Aop)* Deep M k Z x=(↑(1-disk 4 M x):ℂ) • Deep M k Z x:=by
 let f:=Deep M k Z x; let V:= ShiftY k Z (harbor x); have hv:Aop*f=V:=conceal ..; have he: betaA M x* V=(disk 4 M x:ℂ) • f:=by
    change _ = _ • (wagon M x * V); rw [← Matrix.smul_mul,wage p M t,Matrix.mul_assoc,show Aop*V=V from stitch_y ..]; rfl
 change _*_ * f= _; rw [Matrix.mul_assoc, Matrix.sub_mul,Matrix.one_mul, hv,Matrix.mul_sub, show betaA M x * f=f from projection M k Z x p t, he,Complex.ofReal_sub, sub_smul,Complex.ofReal_one,one_smul]
lemma spanned(y:ℕ) : wageErr N M ^ y * chamberU Z N u M k= presentP N u (fun i=> spirale N M y i • Deep M k Z (pm i)):=by
 induction y with
 | zero=> simp_rw [pow_zero,Matrix.one_mul,spirale,pow_zero,Complex.ofReal_one,one_smul]; rfl
 | succ y ih=>rw [pow_succ',Matrix.mul_assoc,ih,vessel,presence]; congr 1; funext i; rw [Matrix.mul_smul,camper Z M (stem_one _) (pm_nonzero _), smul_smul,spirale,spirale,pow_succ,Complex.ofReal_mul]
-- choose Cboot
lemma climate (f:Coast→ WRect SpinIdx q)(h:Continuous f):∃ C,0<C∧∀ x,‖f x‖≤ C:=let F:C(Coast,WRect SpinIdx q):=⟨f,h⟩; ⟨‖F‖+1,by positivity,fun x=>(F.norm_coe_le_norm x).trans (le_add_of_nonneg_right zero_le_one)⟩
lemma breeds (p:3≤k)(W:FaceL)(n t:ℕ): ∃ C:ℝ,0<C∧∀ (N:Side)(M:Maj)(u:Site N),‖clerks W N u n t‖≤C∧ ‖exactU Z N u k‖≤C∧ ‖chamberU Z N u M k‖≤ C:=by
 obtain ⟨A,v,z⟩:=climate _ (spouse_c (n:=n) W t); obtain ⟨B,u,h⟩:=climate _ (shift_c k Z); obtain ⟨E,w,e⟩:=climate _ (shift_c 0 Z); let F:=vlow⁻¹*π^(k-2)*E; have hF:0<F:=by unfold F; have hz:=vpay; positivity
 let C:= A+B+F; refine ⟨C,by unfold C; positivity, fun N M q'=> ⟨?_,?_,?_⟩⟩; · exact (show ‖clerks W N q' n t‖≤A from pay N q' v.le (fun i=> z _)).trans (by unfold C; linarith)
 · exact (show ‖exactU Z N q' k‖≤B from pay N q' u.le (fun i=> h _)).trans (by unfold C; linarith)
 unfold chamberU; apply le_trans _ (by unfold C; linarith : F ≤ C); refine pay N q' hF.le (fun i=>?_); change ‖Deep M k Z _‖≤ F; have hp:= shallow_cost (stem_one i) (pm_nonzero i) Z E (e _) (k-2) M; rw [show k-2+2=k by omega] at hp; apply hp.trans; unfold F; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (stemG.mp (stem_one i)) _) (inv_pos.mpr vpay).le) w.le
lemma trains (l:ℕ): ∃ C',0<C'∧ ∀ (N:Side)(u:Site N)(M:Maj) (K:ℕ),0<K→ ‖wageErr N M ^ (K*l) * chamberU Z N u M (2*l+2)‖≤ C' *((K:ℝ)⁻¹)^l:=by
 obtain ⟨C,p,h⟩:=climate _ (shift_c 0 Z); let A:=vlow⁻¹ * vlow⁻¹^l*C; have ht:= vpay; refine ⟨A,by unfold A; positivity, fun N u M K k=>?_⟩; rw [spanned]; apply pay N u (by unfold A; positivity); intro x; exact afloat (stem_one x) (pm_nonzero x) Z _ (h _) _ K k M
end YM.CF.Crest.Rail
open YM.CF.Crest.Rail
#print axioms treaty
#print axioms trains
#print axioms breeds
#print axioms spanned
