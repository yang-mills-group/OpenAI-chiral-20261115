import SatinThinSeason
import YM.SU5.Circuit.Zinnias
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
-- one clover comparison at an arbitrary (shifted) site
open Etch Garland
variable (o b:Site n)(F Q:PlaqAxes)(i:G.ColorIndex)(hk:0<k)
abbrev componentI(z: Tray→ r) : r:= (4:ℝ)⁻¹ • ((z (false,false) + z (false,true))+(z (true,false)+z (true,true)))
abbrev curlsW(i:PlaqAxes)(v:Tray) (b:Site n) : Body 2 n :=( (slotFace (atTray v.1 v.2 i) b).1, plaquette i)
abbrev sparkZ(u:ℝ):= componentI B P fun v=> plar B P (curlsW F v o) u i
lemma currency_bound (h:|u|≤ 2): ‖sparkZ B P o F i u‖ ≤ 2*(Real.sqrt q.direct)⁻¹:=by
 let W(v:Tray):=plar B P (curlsW F v o) u i; have hx(v): ‖W v‖≤_:= mintBudget B P (curlsW F v o) i h
 unfold sparkZ componentI; rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0:ℝ)≤4⁻¹)]; apply (mul_le_mul_of_nonneg_left ((norm_add_le ..).trans (add_le_add ((norm_add_le ..).trans (add_le_add (hx (false,false)) (hx (false,true)))) ((norm_add_le ..).trans (add_le_add (hx (true,false)) (hx (true,true)))))) (by norm_num:(0:ℝ)≤4⁻¹)).trans_eq; ring
lemma tray_form (v:Tray)(x:r): (u:ℝ) • river q (slotFace (atTray v.1 v.2 F) o) x.val= u • beamZ B P (curlsW F v o) x:=by unfold curlsW; rw [inspire]; cases v; rfl
lemma spar_form (x:r): (spigot (fun v:Tray=> u • river q (slotFace (atTray v.1 v.2 F) o) x.val)) i=inner ℝ (sparkZ B P o F i u) x:=by
 unfold sparkZ componentI; have he(i j:r)(c:ℝ) : inner ℝ (c•i) j=c*inner ℝ i j:= real_inner_smul_left i j c; simp_rw [he,inner_add_left,plar,he,joy]; rw [show (fun v:Tray=> u • _) = (fun v:Tray=> u • beamZ B P (curlsW F v o) x) from funext (fun i=> tray_form B P o F i x)]; unfold spigot; rfl -- tune
lemma mellow_form(x:r): (mellow G F k hk).sketch q u o x.val= viewμ k (coalK (fun i=>sparkZ B P o F i u) x):=by
 unfold mellow sketch; dsimp only; apply congrArg (viewμ k); rw [EuclideanSpace.real_norm_sq_eq]; simp_rw [spar_form ..]; rfl
lemma chalk_form {I:Type*}[Fintype I] (A:Etch G I)(x:r): A.chalk q u 1 o x.val=A.sketch q u o x.val:=by -- I tune
 obtain ⟨V,h⟩:= x.property; rw [← h,A.chalk_now ..]; unfold Etch.sketch; simp_rw [river_now ..]; apply congrArg A.f; funext j; apply congrArg (u • ·); have ht:= slot_deriv (A.slot j) 0 (bank 1 o V); simp_rw [bank_at, Slot.atSite,expandAt_pull,affine,Signed.act_zero,zero_add,pull_id] at ht; exact ht.unique (slot_deriv ..)
-- Gaussian mean & pair estimates. `rimble` averaged fixed stencil. polynomial Wick & clips.
private abbrev μ := stdGaussian (r)
abbrev coilAt (u:ℝ)(x:r):= coalK (fun i=>sparkZ B P o F i u) x
abbrev cljAt (x:r):= viewμ k (coilAt B P o F u x)
local notation "μτ"=>stdGaussian r
noncomputable abbrev cloudV (v:r→ℝ):= ∫ x,v x ∂ stdGaussian r
include hk in
lemma phaseNorm (h:|u|≤2): let X:= cloudV B P (coilAt B P o F u); let x:= cloudV B P (cljAt (u:=u) (k:=k) B P o F); 0≤x ∧ x≤ X ∧ X ≤ glamourK q G ∧ X-x≤ glitterK q G/k:= by
 exact clipD (B:=2*(Real.sqrt q.direct)⁻¹) _ (by positivity) (fun i=>currency_bound B P o F i h) hk
abbrev singleBeam (x y: Site n)(M:Bed)(i j:PlaqAxes)(v:Tray)(w:Tray):= rimble n M (curlsW i v x) (curlsW j w y)
noncomputable def pairR (x y: Site n)(M:Bed)(i j:PlaqAxes):ℂ:=(4:ℂ)⁻¹* ((4:ℂ)⁻¹*∑ v:Tray,∑ w:Tray, singleBeam x y M i j v w)
lemma meanTray(x:Tray→ r): componentI B P x=(4:ℝ)⁻¹ • ∑ i:Tray,x i:= by unfold componentI; rw [Fintype.sum_prod_type]; simp [add_comm _ (x (false,true)),add_comm _ (x (true,true))]; abel -- tune
include H e L in
lemma spark_inner(j:G.ColorIndex)(h:Even n.val): (↑(inner ℝ (sparkZ B P o F i u) (sparkZ B P b Q j u)):ℂ)= (u:ℂ)^2*(sch (G:=G) i j)*pairR o b M F Q:=by -- adapt Lieble
 have he(v w:Tray): ( (↑(inner ℝ (plar B P (curlsW F v o) u i) (plar B P (curlsW Q w b) u j)):ℂ))=(u:ℂ)^2*(sch (G:=G) i j)*singleBeam o b M F Q v w:=by
    have he:= chimes B P L H e i j (curlsW F v o) (curlsW Q w b) h; simp_rw [←joy,appraisal] at he; unfold plar; rw [real_inner_smul_left (trill B P i (curlsW F v o)) (u•trill B P j (curlsW Q w b)) u, real_inner_smul_right (trill B P i (curlsW F v o)) (trill B P j (curlsW Q w b)) u]; push_cast; rw [he]; unfold singleBeam; ring
 unfold sparkZ; have h(x y:r)(c:ℝ) : inner ℝ (c•x) y=c*inner ℝ x y ∧ inner ℝ x (c•y)=c*inner ℝ x y:=⟨real_inner_smul_left x y c, real_inner_smul_right x y c⟩; rw [meanTray,meanTray,(h _ _ _).1,(h _ _ _).2]; simp_rw [sum_inner,inner_sum]; push_cast; simp_rw [he,← mul_sum]; unfold pairR; ring
include L H e in
lemma rawVision (h:Even n.val): let C:= coilAt B P o F u; let D:= coilAt B P b Q u; ↑(cloudV B P (fun x=> C x * D x))=(cloudV B P C:ℂ)*(cloudV B P D:ℂ)+(u:ℂ)^4*duoPower G (pairR o b M F Q):=by
 intro X Y; let I:=G.ColorIndex; let S:ℂ:=pairR o b M F Q; change (↑(∫ x, coalK _ x * coalK _ x∂μτ):ℂ)= _; rw [workDuet]; push_cast; simp_rw [spark_inner B P L H e o b F Q _ _ h]; have hx(i:G.ColorIndex): (∑ j:G.ColorIndex, ((u:ℂ)^2 * (sch (G:=G) i j)*S)^2)= (u:ℂ)^4*S^2:=by simp [sch, apply_ite (fun x:ℝ=>(x:ℂ)),mul_ite,ite_mul,ite_pow]; ring
 unfold S at hx; simp_rw [hx]; unfold duoPower; rw [sum_const,card_univ,nsmul_eq_mul]; congr 1; ring
include L H e hk in
lemma twoVision (h:Even n.val)(p:|u|≤2) : let f:= cljAt B P o F (k:=k) (u:=u); let g:= cljAt B P b Q (k:=k) (u:=u); let A:= cloudV B P f; let D:= cloudV B P g;
 ‖(↑(cloudV B P (f*g)-A*D):ℂ) - (u:ℂ)^4*duoPower G (pairR o b M F Q)‖ ≤ tollK q G/k:=by
 intro ξ τ B' E'; let I:= cloudV B P (coilAt B P o F u); let I':= cloudV B P (coilAt B P b Q u); obtain ⟨hx,hy,hs,Hx⟩:= phaseNorm B P o F hk p; obtain ⟨hu,hv,hw,Hv⟩:= phaseNorm B P b Q hk p
 let S':= cloudV B P (coilAt B P o F u*coilAt B P b Q u); let C':= cloudV B P (ξ*τ); have hp:C' ≤ S' ∧ S'-C'≤ sprayμ q G/k:= clipE (B:=2*(Real.sqrt q.direct)⁻¹) _ _ (by positivity) (fun i=>currency_bound B P o F i p) hk (fun i=>currency_bound B P b Q i p)
 have he: |I*I'-B'* E'| ≤ 2*glamourK q G*glitterK q G/k:=by
    rw [abs_of_nonneg (sub_nonneg.mpr (mul_le_mul hy hv hu (hx.trans hy)))]; let xx:=glitterK q G/k; have hn:0≤xx:=(sub_nonneg.mpr hy).trans Hx; calc
     _ ≤ xx * glamourK q G + xx * glamourK q G:=by
               have hr:(I-B')*I'≤xx* glamourK q G:= mul_le_mul Hx hw (hu.trans hv) hn
               have hg:(I'-E')*B' ≤ xx* glamourK q G:= mul_le_mul Hv (hy.trans hs) hx hn
               linarith only [hr,hg]
     _ = _:=by unfold xx; ring
 let F':=C'-S'; let U:=I*I'- B'* E'; have hz:(u:ℂ)^4*duoPower G (pairR o b M F Q)=(S':ℂ)-(I:ℂ)*I':= by have hp: (S':ℂ)=_:= rawVision (u:=u) B P L H e o b F Q h; rw [hp]; ring
 rw [hz]; push_cast; change ‖((C':ℂ)-_)-_‖≤_; rw [show _-_=(↑(F'+U):ℂ) from ?_, Complex.norm_real, Real.norm_eq_abs]; swap; · unfold F' U; push_cast; ring
 have hv: |F'| ≤ _ := (abs_sub_comm C' S').trans_le ((abs_of_nonneg (sub_nonneg.mpr hp.1)).trans_le hp.2)
 exact (abs_add_le ..).trans ((add_le_add hv he).trans_eq (by unfold tollK; ring))
end YM.Regis.Head.Brecht
#print axioms YM.Regis.Head.Brecht.twoVision
