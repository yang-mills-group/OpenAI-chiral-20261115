import YM.SU5.Circuit.Quartet
import YM.SU5.Regis.Masonry
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.Regis.Head.Brecht
open Function Filter Metric Lattice Laurent Next.Free Bloch Finset Exterior Precision RG Work.F03 Gleam MeasureTheory NormedSpace ProbabilityTheory Wilson Matrix
open Circuit
open scoped Matrix Topology BigOperators NNReal ENNReal InnerProductSpace ContDiff Classical Matrix.Norms.Frobenius
variable {q: Clip}{n: Side}{M: Bed}{G:Gauge}{Z:PathData G}{η C v σ θ w a k t u:ℝ}
variable (B: Z.Bounds q θ w a)(P:Attached M Z)(L:Floor M q n η C)(H:M.covered σ C)(e:0<σ)
local notation "r"=> stamen B P n
abbrev colorOf (a:Lattice.PlaqAxes)(x:Cover): RG.Slot:=Etch.entrust x ⟨[],a⟩
lemma colorful (a:Lattice.PlaqAxes)(x:Cover): slotFace (colorOf a x) (0:Site n)=(wrap n x,a):=by rw [colorOf,Etch.toPoint]; simp [slotFace, RG.Slot.offset,Lattice.stop]

private lemma distOne (h:0<k)(x y:ℝ)(p:0≤x)(t:x≤y): |viewμ k (y^2)-viewμ k (x^2)| ≤ (1+k) * (y-x) :=by -- remove G
 let D:=1+x^2/k; let S:=1+y^2/k; have hv:1≤ D:= le_add_of_nonneg_right (by positivity); have ht:0<S:=by unfold S; positivity
 have hp:0<D:=by linarith
 have hc:y+x≤ (1+k)* S:= by unfold S; field_simp; nlinarith only [t,sq_nonneg (y-1),sq_nonneg (y-k),h, mul_le_mul_of_nonneg_left t h.le, mul_nonneg h.le (sq_nonneg y)] -- tune ∼2 \sqrt k
 have ha:0≤ y-x:=sub_nonneg.mpr t
 have he:viewμ k (y^2)-viewμ k (x^2)=(y-x)*((y+x)/S)/D:=by unfold viewμ; change y^2/S-x^2/D=_; field_simp; unfold D S; ring
 rw [he,abs_of_nonneg (by have hp':0≤y:=p.trans t; positivity : 0≤(y-x)*((y+x)/S)/D),mul_comm (1+k)]; exact (div_le_self (by have hp':0≤y:=p.trans t; positivity) hv).trans (mul_le_mul_of_nonneg_left ((div_le_iff₀ ht).mpr hc) ha)
def blazing (G:Gauge)(c:Lattice.PlaqAxes)(x:Cover)(k:ℝ)(h:0<k): Etch G Unit where
 slot _:= colorOf c x
 f y:= viewμ k (‖y ()‖^2)
 arc:= k
 bound i:= (abs_of_nonneg (clipμ h _ (sq_nonneg _)).1).trans_le (clipμ h _ (sq_nonneg _)).2.1
 diff:= by
    let F: (Unit→ G.Color)→ℝ:=fun y=> ‖y ()‖^2; have he:ContDiff ℝ 1 F:= (contDiff_norm_sq ℝ).comp (contDiff_apply ℝ G.Color ()) -- tune
    apply he.div (contDiff_const.add (he.div_const k)); intro y; change 1+ ‖y ()‖^2/k≠0; positivity
 favor:=⟨1+k,by positivity⟩
 steady:= LipschitzWith.of_dist_le_mul fun i j=>by
    let y:= ‖i ()‖; let z:= ‖j ()‖; let Vx (x:ℝ):= viewμ k (x^2); change dist (Vx y) (Vx z) ≤ (1+k)*_; have he(c:Unit): dist (i c) (j c)≤ dist i j:=by rw [dist_eq_norm,dist_eq_norm]; apply norm_le_pi_norm (i-j) c
    rcases le_total z y with p|p
    · have hp': y-z≤dist (i ()) (j ()):=by rw [dist_eq_norm]; exact norm_sub_norm_le ..
      exact (distOne h z y (norm_nonneg (j ())) p).trans (mul_le_mul_of_nonneg_left (hp'.trans (he ())) (by positivity))
    rw [dist_comm]; refine le_trans (distOne h y z (norm_nonneg _) p) (mul_le_mul_of_nonneg_left ?_ (by positivity)); exact (by rw [dist_comm i]; refine (norm_sub_norm_le (j ()) (i ())).trans ?_; rw [← dist_eq_norm,dist_comm (j ()),dist_comm j]; exact he ()) -- tune
 move z y:= by rw [G.norm_adjoint]
-- Gaussian budget on physical curvature of slot
abbrev plar (W:Body 2 n)(u:ℝ)(i:G.ColorIndex): r:= u • trill B P i W
lemma fire (F:Lattice.PlaqAxes)(x:Cover)(h:0<k)(u:ℝ)(y:r): (blazing G F x k h).sketch q u (0: Site n) y.val= viewμ k (coalK (plar B P (wrap n x,plaquette F) u) y):=by
 unfold Etch.sketch blazing; dsimp only; apply congrArg (viewμ k); rw [EuclideanSpace.real_norm_sq_eq]; unfold coalK talents; rw [colorful]; apply sum_congr rfl; intro i _; rw [plar, real_inner_smul_left (trill B P i (wrap n x,plaquette F)) y u,joy,inspire]; rfl
lemma trillLimit (X:Body 2 n)(i:G.ColorIndex): ‖trill B P i X‖ ≤ (Real.sqrt q.direct)⁻¹:=by
 let D:=(Real.sqrt q.direct)⁻¹; have he:0 ≤ D:=by unfold D; positivity
 let V:=trill B P i X; change ‖V‖ ≤ D; by_cases e:V=0; · rw [e,norm_zero]; exact he
 have hx:=norm_pos_iff.mpr e; have hp:‖V‖^2=(beamZ B P X V) i:=by rw [←joy,show trill B P i X=V from rfl,real_inner_self_eq_norm_sq]
 apply le_of_mul_le_mul_right  (show ‖V‖*‖V‖ ≤ D*‖V‖ from ?_) hx; rw [← sq, hp]; change D*(V.val (orbe X,false,i)) ≤ _; apply mul_le_mul_of_nonneg_left (?_) he
 let d:=(orbe X,false,i); apply le_trans (le_abs_self _); rw [←sq_le_sq₀ (abs_nonneg _) (norm_nonneg _), sq_abs]; change V.val d ^2 ≤ ‖V.val‖^2; rw [EuclideanSpace.real_norm_sq_eq]; exact single_le_sum (f:=fun i=>V.val i^2) (fun i _=>sq_nonneg _) (mem_univ _)
lemma mintBudget (X:Body 2 n)(i:G.ColorIndex)(e:|u|≤2): ‖plar B P X u i‖≤ 2*(Real.sqrt q.direct)⁻¹:=by rw [plar,norm_smul,Real.norm_eq_abs]; exact mul_le_mul e (trillLimit ..) (norm_nonneg _) (by norm_num)
section
variable (F D: PlaqAxes)(x y:Cover)(p:0<k)
local notation "μ"=>stdGaussian (r)
local notation "A"=> ((wrap n x,plaquette F):Body 2 n)
local notation "E"=> ((wrap n y,plaquette D):Body 2 n)
local notation "κ"=>rimble n M A E
local notation "Ĝ"=>G.ColorIndex
local notation "U"=>2*(Real.sqrt q.direct)⁻¹
variable (z:Even n.val)
def glamourK(q:Clip)(G:Gauge):ℝ:= let I:=G.ColorIndex; let A':=2*(Real.sqrt q.direct)⁻¹; (Fintype.card I:ℝ)*A'^2
def glitterK(q:Clip)(G:Gauge):ℝ:= let I:=G.ColorIndex; let A':=2*(Real.sqrt q.direct)⁻¹; 1 + (Fintype.card I:ℝ)^3*balboa A' I
def sprayμ(q:Clip)(G:Gauge):ℝ:= sizingμ G.ColorIndex (2*(Real.sqrt q.direct)⁻¹)
def tollK(q:Clip)(G:Gauge):ℝ:= sprayμ q G+2* glamourK q G*glitterK q G
include e L H z
local notation "ɐ"=> blazing G F x k p
local notation "ɒ"=> blazing G D y k p
local notation "ζ" i:max=> (Etch.muρ i q B P u n)
variable (hu: |u| ≤ 2)
lemma tradition : let V:=plar B P A u; let v:=plar B P E u; ↑(∫ i,coalK V i * coalK v i∂ μ)=(↑(∫ i,coalK V i∂ μ):ℂ)*↑(∫ i,coalK v i∂ μ)+2*Fintype.card Ĝ*(u:ℂ)^4*κ^2:=by -- syntax parse u signature (implicit variable section)
 intro V w; rw [workDuet]; push_cast; congr 1; have ht(i j:Ĝ): (↑(inner ℝ (V i) (w j)):ℂ)= (u:ℂ)^2 *(sch (G:=G) i j)*κ:=by
    have he:= chimes B P L H e i j A E z; simp_rw [←joy,appraisal] at he; unfold V w plar; rw [real_inner_smul_left (trill B P i A) (u•trill B P j E) u, real_inner_smul_right (trill B P i A) (trill B P j E) u]; push_cast; rw [he]; ring
 simp_rw [ht]; have hw(i:Ĝ): (∑ j:Ĝ, ((u:ℂ)^2 * (sch (G:=G) i j)*κ)^2)= (u:ℂ)^4*κ^2:=by simp [sch, apply_ite (fun x:ℝ=>(x:ℂ)),mul_ite,ite_mul,ite_pow]; ring
 simp_rw [hw]; simp; ring
omit L H e z
include hu p
lemma affluent : let X:= (∫ i, coalK (plar B P A u) i ∂ μ); 0 ≤ ζ ɐ ∧ ζ ɐ ≤ X ∧ X ≤ glamourK q G ∧ X-ζ ɐ ≤ glitterK q G/k:=by simp_rw [Etch.muρ,clouds,fire]; exact clipD (B:=2*(Real.sqrt q.direct)⁻¹) _ (by positivity) (fun i=>mintBudget _ _ _ i hu) p -- issue `B:=` conflict? 
include L H e z
lemma regard : ‖(↑(ζ (ɐ.radial ɒ) - ζ ɐ * ζ ɒ):ℂ) - 2*Fintype.card Ĝ*(u:ℂ)^4*κ^2‖ ≤ tollK q G/k:=by
 obtain ⟨hx,hy,hs,Hx⟩:= affluent (n:=n) B P F x p hu; obtain ⟨hv,hw,ht,Ht⟩:=affluent (n:=n) B P D y p hu
 let Y:= plar B P A u; let R:= plar B P E u; let I:=∫ x, coalK Y x∂ μ; let R':=∫ x,coalK R x∂ μ; let C':= ζ (ɐ.radial ɒ); let S:= ∫ i,coalK Y i*coalK R i∂ μ
 have hp:C'≤ S ∧ S-C'≤ sprayμ q G/k:=by simp_rw [C',Etch.muρ, clouds,Etch.radial_s, fire]; exact clipE (B:=2*(Real.sqrt q.direct)⁻¹) Y R (by positivity) (fun i=>mintBudget _ _ _ i hu) p (fun i=>mintBudget _ _ _ i hu)
 have he: |I*R'-ζ ɐ * ζ ɒ| ≤ 2*glamourK q G*glitterK q G/k:=by
    rw [abs_of_nonneg (sub_nonneg.mpr (mul_le_mul hy hw hv (hx.trans hy)))]; let xx:=glitterK q G/k; have hn:0≤xx:=(sub_nonneg.mpr hy).trans Hx
    calc _ ≤ xx * glamourK q G + xx * glamourK q G:=by
               have hr:(I-ζ ɐ)*R'≤xx* glamourK q G:= mul_le_mul Hx ht (hv.trans hw) hn
               have hg:(R'-ζ ɒ)*ζ ɐ ≤ xx* glamourK q G:= mul_le_mul Ht (hy.trans hs) hx hn; -- spacing
               linarith only [hr,hg] -- tune replace
         _ = _:= by unfold xx; ring
 let F':=C'-S; let B':=I*R'-ζ ɐ*ζ ɒ; have hz:(2*Fintype.card Ĝ*(u:ℂ)^4*κ^2:ℂ)=S-(I:ℂ)*R':= by have hp: (S:ℂ)=_:= tradition (u:=u) B P L H e F D x y z; rw [hp]; ring
 rw [hz]; push_cast; change ‖((C':ℂ)-_)-_‖≤_; rw [show _-_=(↑(F'+B'):ℂ) from ?_, Complex.norm_real, Real.norm_eq_abs]; swap; · unfold F' B'; push_cast; ring
 have hv: |F'| ≤ _ := (abs_sub_comm C' S).trans_le ((abs_of_nonneg (sub_nonneg.mpr hp.1)).trans_le hp.2)
 exact (abs_add_le ..).trans ((add_le_add hv he).trans_eq (by unfold tollK; ring)) -- name
end
end YM.Regis.Head.Brecht
#print axioms YM.Regis.Head.Brecht.regard
