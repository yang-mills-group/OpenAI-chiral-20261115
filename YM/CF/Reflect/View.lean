import YM.CF.Reflect.Radial

/-! RP for even and odd sides; CAR algebra, insertions at bra. -/
set_option maxHeartbeats 400000
set_option autoImplicit false
set_option maxRecDepth 8000
noncomputable section
namespace YM.CF.RP
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology BoundedContinuousFunction ComplexOrder
open Function Fock Filter NormedSpace SU Lat Lattice Branch Cube Tenant Phase Mir Mir.Trip MeasureTheory Finset Reflect
attribute [local instance] opCStarAlgebra
variable {m B : Side} {c : Phase.Part m B} {A D d e β : ℝ} {W : Scroll m B c}

structure OfferedF (m B : Side) (i : Axis) (f : Test m B) (b : Bool) : Prop where
  cont : Continuous f
  sector (x) : Sector (colony m B i) b (f x)
  localU x y : NorthOf m B i x y → f x=f y

def fiscal (m B : Side) (i : Axis) (f : Test m B) (b : Bool) (x : Pack m B) := chord b • (theta (finger m B i) (f (Pbar m B i x)) * f x)

def staple (m B : Side) (i : Axis) (x : Pack m B) (e β : ℝ) := {y:Pack m B | tiedK m B i x y y∈ TallyR m B e β}
variable (H : ScaleK A D W) (g : Budget B e d) (l : Foot m B) (t : ℝ) (k : 0≤t) (a : ℝ) (β) (i : Axis) (x : Pack m B) (f : Test m B) (b : Bool) (h : OfferedF m B i f b)

lemma staple_meas (e : ℝ) : MeasurableSet (staple m B i x e β) := (show Continuous fun u:Pack m B=>tiedK m B i x u u from (zoneA i x).comp (continuous_id.prodMk continuous_id)).measurable (tally_meas ..)
include H g k h
lemma in_spot [Nonempty (staple m B i x e β)] : let T := staple m B i x e β; ∃ R : CSeat T (Xmind m B), R∈Cloud (finger m B i) (colony m B i) T ∧ ∀ y z : T,
    R (y,z) (upperP (CSide m B)) (upperP (CSide m B))= amplitude W (axisCut m B i l) β t a (fiscal m B i f b) (tiedK m B i x y.val z.val) := by
  intro T; let N := CSide m B; let M := Xmind m B; let r := tiedK m B i x; let U := finger m B i
  let s (x:T×T) := r x.1.val x.2.val; let f₁ := fun j:T=>s (j,j)
  have hF y z : s (y,z)∈ TallyR m B e β := (apt ..).mpr ⟨y.property,z.property⟩
  have hf v : f₁ v∈payer m B e := tallyP (hF v v)
  have hc : Continuous f₁ := (zoneA i x).comp (continuous_subtype_val.prodMk continuous_subtype_val)
  let c₀ (j:T) := Real.sqrt (net m B β (f₁ j)); let d₀ (j:T) := Complex.exp (-(a:ℂ)*inPort W i (f₁ j)); let D₀ : T → FC M := fun j=> ((c₀ j : ℂ)*d₀ j) • f (f₁ j)
  have hb : Continuous c₀ := ((net_cont m B β).comp hc).sqrt
  have ht : Continuous d₀ := Complex.continuous_exp.comp (continuous_const.mul ((innateC H g i).comp_continuous hc hf))
  have H₀ : Continuous D₀ := by unfold D₀; exact ((Complex.continuous_ofReal.comp hb).mul ht).smul (h.cont.comp hc)
  obtain ⟨v,hV⟩ : ∃ v, ∀ t, ‖D₀ t‖ ≤ v := by
    obtain ⟨o,w,hW⟩ := port_lim H g i
    obtain ⟨p,v,V⟩ := circular (f:=fun i:ℂ=>Complex.exp (-(a:ℂ)*i)) (by fun_prop) (isCompact_closedBall (0:ℂ) o)
    obtain ⟨u,pu,hu⟩ := roofC h.cont
    obtain ⟨L,K,hL⟩ := roofC ((net_cont m B β).sqrt)
    refine ⟨L*p*u,fun j=>?_⟩
    unfold D₀; rw [norm_smul, norm_mul]
    exact mul_le_mul (mul_le_mul (by rw [Complex.norm_real]; exact hL _) (V _ (Metric.mem_closedBall.mpr (by rw [dist_zero_right]; exact hW _ (hf j)))) (norm_nonneg _) K) (hu _) (norm_nonneg _) (by positivity)
  let B₀ : CBox T M := BoundedContinuousFunction.ofNormedAddCommGroup D₀ H₀ v hV
  have he (y : T) : Sector (colony m B i) b (B₀ y) := (h.sector _).scale _
  let d := axisCut m B i l
  obtain ⟨Y,hy,vv⟩ := accomplish i x (fun x:T=>x.val) continuous_subtype_val l t k
  obtain ⟨P',Q,kV⟩ := anterior i x (fun x:T=>x.val) g.1 continuous_subtype_val (fun y z=> tallyP (hF y z))
  let K := tile U b B₀
  have hz : K*Y*P'∈ Cloud U (colony m B i) T := rain_mul (rain_mul ((Faced.square b B₀ he).run) hy (movedCol ..)) Q (movedCol ..)
  refine ⟨_,hz,?_⟩; intro y z
  rw [← bra_fix ((K*Y*P') (y,z))]; change inner ℂ _ (acts (K (y,z)*Y (y,z)*P' (y,z)) _)=_
  let G := s (y,z); let p := f₁ y; let q := f₁ z
  -- shadow G name
  have h₁ : f p=f G := h.localU _ _ (strum i x y.val y.val z.val)
  have h₂ : f q=f (Pbar m B i G) := by unfold G s r; rw [sew]; exact h.localU _ _ (strum i x z.val z.val y.val)
  have h₃ : c₀ z*c₀ y=net m B β G := by
    have he : 0≤net m B β p := net_pos ..; have hl : 0≤net m B β q := net_pos ..; have hp : 0 ≤ net m B β G := net_pos ..
    unfold c₀; change Real.sqrt _*Real.sqrt _=_; rw [←sq_eq_sq₀ (show 0≤ Real.sqrt (net m B β q) * Real.sqrt (net m B β p) from mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hp,mul_pow,Real.sq_sqrt he,Real.sq_sqrt hl]; rw [mul_comm]; exact (decks i x y.val z.val β).symm
  have h₄ : star (d₀ z)*d₀ y=Complex.exp (-(a:ℂ)*cabin W G) := by
    have hk : cabin W G=inPort W i p+star (inPort W i q) := ports i x y.val z.val H g (hF y z) -- tune G passed shadow
    unfold d₀; change star _ * _=_; rw [hk, show ∀ z, star (Complex.exp z)=Complex.exp (star z) from fun z=>Complex.exp_conj z|>.symm, ←Complex.exp_add]; congr 1
    change star (-(a:ℂ)*inPort W i q)+ -(a:ℂ)*inPort W i p= _; rw [star_mul', star_neg]; simp; ring
  let E : ℂ := (net m B β G:ℂ)*Complex.exp (-(a:ℂ)*cabin W G)
  have Hk : K (y,z)= E • fiscal m B i f b G := by
    unfold K; rw [brick]; change chord b • (theta U (((c₀ z:ℂ)*d₀ z) • f q)*(((c₀ y:ℂ)*d₀ y) • f p))=_
    rw [theta_smul, Algebra.mul_smul_comm, Algebra.smul_mul_assoc, h₁,h₂,fiscal,star_mul']
    simp only [smul_smul, Complex.star_def, Complex.conj_ofReal];
    apply congrArg (fun k:ℂ=> k • (theta U (f (Pbar m B i G))*f G)); unfold E; rw [← h₄,←h₃]; push_cast; change _=_; simp only [Complex.star_def]; ring
  rw [act_mul (_ * _), kV, vv, Hk, Algebra.smul_mul_assoc,act_smul, inner_smul_right]; rfl

lemma meas_pos0 : (∫ u, ratioR W e β t a (axisCut m B i l) (fiscal m B i f b) (quill m B i (x,u)) ∂((wheel m B).prod (wheel m B)))≥0 := by
  let T := staple m B i x e β; let X := (wheel m B); let P := amplitude W (axisCut m B i l) β t a (fiscal m B i f b)
  let F := fun p:Pack m B × Pack m B=> P (quill m B i (x,p))
  let J := T×ˢT
  -- indicator exact
  have hm : MeasurableSet T := staple_meas β i x e -- tune
  have he u : ratioR W e β t a (axisCut m B i l) (fiscal m B i f b) (quill m B i (x,u))= J.indicator F u := by
    unfold ratioR; have ht : quill m B i (x,u)∈ TallyR m B e β ↔ u∈J := apt ..
    by_cases h : u∈J
    · rw [Set.indicator_of_mem h,Set.indicator_of_mem (ht.mpr h)]
    rw [Set.indicator_of_notMem h,Set.indicator_of_notMem (fun p=> h (ht.mp p))]
  simp_rw [he]; change 0≤∫ u,J.indicator F u ∂(X.prod X)
  rw [integral_indicator (hm.prod hm),show (X.prod X).restrict J = (X.restrict T).prod (X.restrict T) from (Measure.prod_restrict ..).symm] -- tune
  cases isEmpty_or_nonempty ↥T
  · rw [show T=∅ from Set.isEmpty_coe_sort.mp (by infer_instance)]; simp
  -- transfer to subspace measures
  let Y := X.comap ((↑) : T →Pack m B)
  let A' : T × T → Pack m B × Pack m B := Prod.map ((↑):T→Pack m B) ((↑):T→Pack m B)
  have H' : MeasurePreserving ((↑) : T→ Pack m B) Y (X.restrict T) := ⟨measurable_subtype_coe, map_comap_subtype_coe hm X⟩
  rw [← (H'.prod H').integral_comp (f:=A') ((MeasurableEmbedding.subtype_coe hm).prodMap (MeasurableEmbedding.subtype_coe hm)) F]
  obtain ⟨Q,p,v⟩ := in_spot β H g l t k a i x f b h
  have hg (u : T × T) : F (A' u)=Q u (upperP (CSide m B)) (upperP (CSide m B)) := (v u.1 u.2).symm
  simp_rw [hg]; exact cloud_pos _ _ (slide_plus i) (movedCol ..) Y p -- tune
lemma usable : Integrable (ratioR W e β t a (axisCut m B i l) (fiscal m B i f b)) (wheel m B) := by
  apply sojourn H g; unfold fiscal
  exact (continuous_const (y:=chord b)).smul (((theta_cont (finger m B i)).comp (h.cont.comp ((slideM m i).convey B))).mul h.cont)
-- consumes one axis seam cut. No normalization needed until later proof of strictness.
theorem crossing_nonnegative : 0 ≤ rawE W e β t a (axisCut m B i l) (fiscal m B i f b) := by rw [rawE,heard m B i _ (usable β H g l t k a i f b h)]; exact integral_nonneg fun x=> meas_pos0 β H g l t k a i x f b h
end YM.CF.RP
