import SatinThinPanoramic
import Anomaly.Ward.Voice
/-!
Replica packed probes over curvature$$U_k, allowing price transfer of
*mesoscopically* supported tolls in the Ward analysis.

Critical: cannot use just same-plaquette correlations to get pseudoscalar
rank. Use price claims on ANY polynomial payload here *quadratic*, including
product of 2 complex probes allowing reflection sign orientation. Here helper
budget. Locations held in gauge coordinates. This is variant of XX via
project's Head.Curators, Panorama.
-/
set_option autoImplicit false
set_option maxHeartbeats 720000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.Regis.Head.GeometryP
open Function Lattice MeasureTheory Finset RG Wilson Tree Filter Metric Exterior Precision Next.Rank.Spindle Pressure Work.F03 Next.SectorChange Next.SectorChange.Gaussian
open Gleam Matrix ProbabilityTheory
open scoped Matrix BigOperators Classical ContDiff Topology MatrixOrder ENNReal Kronecker Matrix.Norms.Frobenius NNReal InnerProductSpace
variable {c n : Side}{r:Ratio c n}{G:Gauge}{p:BudgetPoint}{q:Clip}{v t η C S w δ β κ ξ Λ:ℝ}{U:Config G n}{A:Support c}{o x z:Site n}{f m:ℕ} {R:Rules G} {Z:PathData G}{b:Cell n}{H:Bed}
variable (B:Z.Bounds q η C S) (P:Attached H Z)(L_:Floor H q n δ w)
open CF.Swell.Sonar Garland Etch Next.Free
variable {I J:Type*} [Fintype I][Fintype J] {Q:ℝ}
-- shift. uses ANY odd/even gauge moves including into clover geometry. from mark around U.
lemma heading (X:Cell n)(s:Signed)(a:Site n)(U:Dir G n) :
 faceCurl X (bank s a U) = turned s X.2 • faceCurl (Face.send s a X) U:=by
 let e:= Face.send s 0 X; let x:= s; let W:= arbor a U
 have he: Work.F03.faceCurl X (bank s a U)= turned x X.2 • Work.F03.faceCurl e W:=by
    ext i; change (d 1 _ *ᵥ (parts _ _ (Bid.pulled W x) i)) _= turned _ _ *(d 1 _*ᵥ(parts _ _ W i)) _; rw [pigment]; exact rotations_d ..
 refine he.trans (congrArg (fun i=> turned x X.2 • i) ((face_drift a U e.2 e.1).trans ?_)); unfold e Face.send Face.lower atFace affine; dsimp only; simp only [add_zero]; -- tune pos
 apply congrArg (fun i=>Work.F03.faceCurl (i,X.2.rotate x) U); abel

-- tag.Length arbitrary.Rand derivative sum by Cauchy. Weighted sum with shape from ONE reference. No worst-case orientation ledger (but can afford Finset Signed).
def neck : ContDiffBump (0:ℝ):=⟨1,2,zero_lt_one,one_lt_two⟩
def stopper(x:ℝ):ℝ := neck x*x
-- adapt Rub
lemma strollL : ∃ C:ℝ≥0,LipschitzWith C stopper:=by
 refine ContDiff.lipschitzWith_of_hasCompactSupport (n:=1) (𝕂:=ℝ) ?_ ?_ ?_
 · exact HasCompactSupport.mul_right neck.hasCompactSupport
 · exact neck.contDiff.mul contDiff_id
 norm_num
abbrev tariffLip:ℝ≥0:=Classical.choose strollL
abbrev snub (D x:ℝ):=D*stopper (x / D)
lemma snub_budget {D:ℝ}(p:0<D)(x:ℝ) : |snub D x|≤2*D ∧ |snub D x|≤|x| ∧ (|x|≤D→ snub D x=x):=by -- D binder
 let z:=x/D; have h: snub D x=neck z*x:=by unfold snub stopper; change _*(neck z*z)=_; unfold z; field_simp
 have he: dist z (0:ℝ)=|x|/D:=by unfold z; rw [dist_zero_right,Real.norm_eq_abs,abs_div,abs_of_pos p];
 have h₁:|snub D x|≤|x|:=by rw [h,abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) ((abs_of_nonneg neck.nonneg).trans_le neck.le_one)
 refine ⟨?_,h₁,fun a=>?_⟩
 · by_cases e:|x| ≤2*D; exact h₁.trans e
   rw [h,neck.zero_of_le_dist (he ▸ ((le_div_iff₀ p).mpr (le_of_not_ge e) : (2:ℝ)≤ |x|/D)),zero_mul,abs_zero]; positivity
 rw [h,neck.one_of_mem_closedBall (Metric.mem_closedBall.mpr (he.trans_le ((div_le_one p).mpr a))),one_mul]

lemma cutter (D:ℝ)(p:0<D)(x y:ℝ): |snub D x-snub D y| ≤ (tariffLip:ℝ)*|x-y|:=by unfold snub; rw [←mul_sub,abs_mul,abs_of_nonneg p.le]; refine (mul_le_mul_of_nonneg_left (strollL.choose_spec.dist_le_mul (x/D) (y/D)) p.le).trans_eq ?_; rw [Real.dist_eq,←sub_div,abs_div,abs_of_nonneg p.le]; field_simp -- tune defeq
variable {X: Type}[NormedAddCommGroup X] [NormedSpace ℝ X] (W:tableQ G n X)(s:Signed)(a:Site n)(q:Clip)(ε D:ℝ)
-- pointing at poses relative to root.And.Sqrt Pact λ. preserves $abs and grade. choose γ_t times.H'$ at this pose.
abbrev chills (x: TrackKey G n) : TrackKey G n:= (Face.send s a x.1, x.2)
def giveAt (y:Altar G n)(k:TrackKey G n):ℝ:= let b:= Face.send s a k.1; turned s k.1.2 * ε * (river q b y) k.2
def crystalT (y:Altar G n):X:= tariff W (fun k=>giveAt s a q ε y k)
def coverT (y:Altar G n):X:= tariff W (fun k=>snub D (giveAt s a q ε y k))
lemma offerCont(x:TrackKey G n):ContDiff ℝ 1 (fun y:Altar G n=>giveAt s a q ε y x):=by
 let S:(Altar G n)→L[ℝ]ℝ:= EuclideanSpace.proj x.2 ∘L ((river (G:=G) q (Face.send s a x.1)).toContinuousLinearMap); exact contDiff_const.mul (ContinuousLinearMap.contDiff (f:=S)) -- maybe S not f
lemma cutCont : ContDiff ℝ 1 (snub D):=by unfold snub stopper; have he:ContDiff ℝ 1 neck:=neck.contDiff; fun_prop
lemma smoothEarn : ContDiff ℝ 1 (coverT W s a q ε D):=by
 apply ContDiff.sum; intro i _; exact ContDiff.smul (contDiff_prod (fun j _=> (cutCont D).comp (offerCont s a q ε (i j)))) contDiff_const
lemma projected_cursor (q:Clip)(P:Attached H Z)(B: Z.Bounds q η C S)(s:Signed)(a:Site n)(r:Dir G n)(u:ℝ)(x:TrackKey G n): giveAt s a q u (tiler B P r) x=receipt (u • bank s a r) x:=by
 let i:= Face.send s a x.1; have h(b:Face (Per n))(r:Dir G n) :faceCurl b (u • r)=u • faceCurl b r:=by
    ext j; unfold faceCurl dColor; change ((d 1 n)*ᵥ(u • parts G 1 r j)) _ = u * _; rw [Matrix.mulVec_smul]; rfl
 unfold receipt; rw [h, heading]; simp only [giveAt]; rw [river_now q B P]; simp only [PiLp.smul_apply,smul_eq_mul]; ring
private lemma pointed(s t:Signed)(a b:Site n)(v:Dir G n): bank t b (bank s a v)=bank (s*t) (affine s a b) v:=by
 apply Sep; intro i; rw [bank_at,bank_at, bank_at, pull_pull]
where Sep {w v:Dir G n}(p:∀ t:ℝ,represent (t • w)=represent (t•v)): w=v:=by
       -- generic chart. adapt StageQ. \n
       funext i; rcases i with ⟨i,a⟩; obtain ⟨j,rfl⟩:=axisEquiv.surjective a; let e:Edge (Site n):=(i,j); let x:=collect G w e; let y:=collect G v e
       change x=y; let f:= G.plog∘ G.mat; have hv(x:G.Color) : ∀ᶠ a :ℝ in 𝓝 0, f (G.lieExp (a • x))=a • x:= (show Tendsto (fun t:ℝ=>t • x) (𝓝 0) (𝓝 0) from by simpa using! (show Continuous (fun t:ℝ=>t • x) from by fun_prop).tendsto 0).eventually G.plog_left
       obtain ⟨a,ht,h0,hx⟩:= ((hv x|>.filter_mono (nhdsWithin_le_nhds (s:={(0:ℝ)}ᶜ))).and ((hv y|>.filter_mono (nhdsWithin_le_nhds (s:={(0:ℝ)}ᶜ))).and self_mem_nhdsWithin)).exists
       apply smul_right_injective _ (show a≠0 from hx); change a • x = a • y; rw [←ht,←h0]; refine congrArg f ?_; have he:G.lieExp (a • x)*1=G.lieExp (a • y)*1:=congrFun (p a) e; rwa [mul_one,mul_one] at he
lemma carries (q:Clip)(P:Attached H Z)(B: Z.Bounds q η C S)(s t:Signed)(b a:Site n)(U:Dir G n): coverT W (s*t) (affine s a b) q ε D (tiler B P U)=coverT W t b q ε D (tiler B P (bank s a U)):=by
 unfold coverT; simp_rw [projected_cursor q P B,pointed]
lemma potQ (p:0<D)(y:Altar G n): ‖coverT W s a q ε D y‖ ≤ (2*D)^2*costs W:=by refine (norm_sum_le ..).trans (?_); unfold costs; rw [mul_sum]; refine sum_le_sum fun i _=>?_ ; rw [norm_smul, Real.norm_eq_abs, abs_prod]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); apply (Finset.prod_le_prod (fun _ _=>abs_nonneg _) (fun j _=>(snub_budget p _).1)).trans_eq; rw [prod_const,card_univ,Fintype.card_fin]; -- tune
end YM.Regis.Head.GeometryP
