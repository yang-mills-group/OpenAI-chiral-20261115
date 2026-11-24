import YM.SU5.Hiro.Chop
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.Regis.Head.Brecht
open Function Filter Metric Lattice Laurent Next.Free Bloch Finset Exterior Precision RG Work.F03 Gleam MeasureTheory NormedSpace ProbabilityTheory Wilson Matrix
open Circuit
open scoped Matrix Topology BigOperators NNReal ENNReal InnerProductSpace Classical Matrix.Norms.Frobenius
variable {q: Clip}{n: Side}{M: Bed}{G:Gauge}{Z:PathData G}{η C v σ θ w a k t u:ℝ}
variable (B: Z.Bounds q θ w a)(P:Attached M Z)(L:Floor M q n η C)(H:M.covered σ C)(e:0<σ)
local notation "r"=> stamen B P n
variable (F D: PlaqAxes)(x y:Cover)(p:0<k)
local notation "κ"=> rimble n M ((wrap n x),plaquette F) ((wrap n y),plaquette D)
local notation "μX"=>(wrap n x,plaquette F)
local notation "μY"=>(wrap n y,plaquette D)
def elbow (X:Body 2 n)(u:ℝ)(y:r): G.Color:= WithLp.toLp 2 (fun i=> inner ℝ (plar B P X u i) y)
local notation "I"=> G.ColorIndex
local notation "T"=> (Fintype.card I:ℝ)
local notation "φ"=> plar B P μX u
local notation "χ"=> plar B P μY u
local notation "ᵮ"=> elbow B P μX u
local notation "ᵯ"=> elbow B P μY u
local notation "Δ"=> plateView F D x y G p
local notation "μ"=>stdGaussian (r)
lemma bare_elbow {X:Site n}{a:PlaqAxes}(D:r): elbow B P (X,plaquette a) u D = u • Etch.river q (X,a) D.val:= by ext i; change inner ℝ (u • trill B P i _) _=u*_; rw [real_inner_smul_left (trill B P i (X,plaquette a)) D u,joy,inspire]; rfl
lemma elbow_sum {A:Body 2 n}(D:r): coalK (plar B P A u) D=‖elbow B P A u D‖^2:=by rw [EuclideanSpace.real_norm_sq_eq]; rfl
lemma limb_light (b:r): (Δ).sketch q u 0 b.val= inner ℝ (drinkT k (ᵮ b)) (drinkT k (ᵯ b)):=by rw [bare_elbow,bare_elbow]; unfold Etch.sketch; change inner ℝ (drinkT k (u • Etch.river q (slotFace (colorOf F x) 0) b.val)) (drinkT k (u • Etch.river q (slotFace (colorOf D y) 0) b.val))=_; rw [colorful,colorful] -- tune order
lemma limb_budget : Integrable (fun y=> inner ℝ (ᵮ y) (ᵯ y)) μ:=by
 have he : (fun y=>inner ℝ (ᵮ y) (ᵯ y))=(fun y=> ∑ i:I, inner ℝ (φ i) y*inner ℝ (χ i) y):=by funext y; rw [PiLp.inner_apply]; apply sum_congr rfl; intro i _; rw [real_inner_comm, RCLike.inner_apply]; rfl
 rw [he]; apply integrable_finsetSum; intro i _; have ht(v:r):MemLp (fun Z:r=> inner ℝ v Z) 2 μ:=by simpa using coats v 1
 exact (ht _).integrable_mul (ht _)
include L H e
lemma limb_fact(z:Even n.val): (↑(∫ x, inner ℝ (ᵮ x) (ᵯ x) ∂ μ):ℂ)= Fintype.card I* (u:ℂ)^2 *κ:= by
 have h0(y): inner ℝ (ᵮ y) (ᵯ y)= ∑ i:I, inner ℝ (φ i) y*inner ℝ (χ i) y:=by rw [PiLp.inner_apply]; apply sum_congr rfl; intro i _; rw [real_inner_comm,RCLike.inner_apply]; rfl
 have hx(i:I): (↑(inner ℝ (φ i) (χ i)):ℂ)= (u:ℂ)^2*κ:=by
    have he:= chimes B P L H e i i ((wrap n x),plaquette F) ((wrap n y),plaquette D) z; simp_rw [←joy,appraisal] at he; unfold plar; rw [real_inner_smul_left (trill B P i μX) (u • trill B P i μY) u, real_inner_smul_right (trill B P i μX) (trill B P i μY) u]; push_cast; rw [he,sch,if_pos rfl]; push_cast; ring
 simp_rw [h0]; rw [integral_finsetSum]; swap; · intro i _; have ht(v:r):MemLp (fun Z:r=> inner ℝ v Z) 2 μ:=(by simpa using coats v 1); exact (ht _).integrable_mul (ht _)
 simp_rw [appraisal]; push_cast; simp_rw [hx]; simp; ring -- tune procedure
omit L H e
private lemma several {a b k:ℝ}(p:0<k)(u:0≤a)(h:0≤b) (finα:ℝ)(e:|finα|≤a*b): let f:=barQ k a; let g:=barQ k b; |f*g*finα-finα|≤ 2*(2+a^4+b^4)/k:=by
 intro f g; obtain ⟨hx,y⟩:= volumeT p a; obtain ⟨hv,z⟩:=volumeT p b; rw [show f*g*finα-finα=(f*g-1)*finα from (by ring),abs_mul]; have he : f*g ≤ 1:= mul_le_one₀ y hv z; have hp:1-f*g≤ (a^2+b^2)/k:=by
    have hf:1-f≤a^2/k:=thirst p a; have ht:1-g≤b^2/k:=thirst p b; have hu:(1-f)+ f*(1-g)=1-f*g:=by ring
    rw [←hu,add_div]; exact add_le_add hf (le_trans (mul_le_of_le_one_left (sub_nonneg.mpr z) y) ht)
 rw [abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr he)]; refine (mul_le_mul hp e (abs_nonneg _) (by positivity)).trans ?_; rw [div_mul_eq_mul_div]; apply div_le_div_of_nonneg_right _ p.le; by_cases hh:a≤b
 · apply le_trans (show (a^2+b^2)*(a*b)≤(b^2+b^2)*(b*b) by gcongr); nlinarith only [sq_nonneg (a^2)]
 apply le_trans (show (a^2+b^2)*(a*b)≤(a^2+a^2)*(a*a) from (by have hv:= le_of_not_ge hh; gcongr)); nlinarith only [sq_nonneg (b^2)]
local notation "Λ"=>2*(Real.sqrt q.direct)⁻¹
variable (z:Even n.val)(ψ:|u|≤2)
def pepperK (q:Clip)(G:Gauge):ℝ:= let Ιt:= G.ColorIndex; let b:= balboa (2*(Real.sqrt q.direct)⁻¹) Ιt; 2*(4+(Fintype.card Ιt:ℝ)^3*(b+b))
include L H e z p ψ
lemma straw_bill : ‖((Δ).muρ q B P u n:ℂ) - Fintype.card I * (u:ℂ)^2 * κ‖ ≤ pepperK q G / k := by
 let t: r→ℝ:= fun y=> talents φ 4 y; let s: r→ℝ:= fun y=> talents χ 4 y;
 let T'(y:r):= (Δ).sketch q u 0 y.val; let Z'(y:r):= inner ℝ (ᵮ y) (ᵯ y); have he' : Integrable T' μ:= Regis.bree _ _ (((Δ).sketch_smooth q u 0).continuous.comp continuous_subtype_val |>.measurable) (fun _=> (Δ).bound _)
 let a(y):= t y+s y; let K:= (2:ℝ)/k; let b:ℝ:= balboa Λ I
 have hx:Integrable t μ:= (partT _ _).integrable (by norm_num); have hz:Integrable s μ:= (partT _ _).integrable (by norm_num); let x0: r→ℝ:= fun i=> K * (4+T^3*a i); have hu:Integrable a μ:= hx.add hz; have hp:0≤K:=by unfold K; positivity
 rw [← limb_fact B P L H e F D x y z,Etch.muρ, clouds,← Complex.ofReal_sub,Complex.norm_real, ← integral_sub he' (limb_budget B P F D x y)];
 refine (norm_integral_le_of_norm_le (g:=x0) (((integrable_const (4:ℝ)).fun_add (hu.const_mul _)).const_mul K) (ae_of_all _ fun i=>?_)).trans ?_
 · change ‖T' i- Z' i‖≤x0 i; unfold T'; rw [limb_light,drinkT,drinkT,real_inner_smul_left,real_inner_smul_right,←mul_assoc,Real.norm_eq_abs]; -- T' syntax
   let U:=‖ᵮ i‖; let V:=‖ᵯ i‖; refine (several p (norm_nonneg _) (norm_nonneg _) (Z' i) (abs_real_inner_le_norm ..)).trans (le_trans (a:= 2*(2+U^4+V^4)/k) (Eq.le (show _=K*(2+U^4+V^4) from (by unfold K; ring))) (mul_le_mul_of_nonneg_left ?_ hp))
   have he' : U^8 ≤ T^3*t i:=le_trans (Eq.le (by ring : U^8= (U^2)^4)) (by unfold U; rw [←elbow_sum]; exact tributeV ..); have hs: V^8 ≤ T^3*s i:=le_trans (Eq.le (by ring : V^8= (V^2)^4)) (by unfold V; rw [←elbow_sum]; exact tributeV ..)
   unfold a; nlinarith only [he',hs,sq_nonneg (U^4-1/2),sq_nonneg (V^4-1/2)]
 have he: (∫ x,a x∂μ) ≤ b+b:=by unfold a; rw [integral_add hx hz]; exact add_le_add (tin_four _ (by positivity : 0≤Λ) (fun i=>mintBudget _ _ _ i ψ)) (tin_four _ (by positivity : 0≤Λ) (fun i=>mintBudget _ _ _ i ψ))
 unfold x0; rw [integral_const_mul, integral_add (integrable_const _) (hu.const_mul _),integral_const,probReal_univ,one_smul,integral_const_mul]; exact (mul_le_mul_of_nonneg_left (add_le_add_right (mul_le_mul_of_nonneg_left he (by positivity : 0≤T^3)) 4) hp).trans_eq (by unfold pepperK K b; ring)
-- pepperK forward declare
end YM.Regis.Head.Brecht
#print axioms YM.Regis.Head.Brecht.straw_bill
