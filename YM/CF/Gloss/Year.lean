import YM.CF.Gloss.Scene
set_option autoImplicit false
set_option synthInstance.maxSize 18000
noncomputable section
namespace YM.CF.RP.Str
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology BoundedContinuousFunction ComplexOrder
open Function Fock Filter NormedSpace SU Lat Lattice Branch Cube Tenant Phase Mir Mir.Trip MeasureTheory Sample Finset Reflect Gloss
attribute [local instance] opCStarAlgebra
variable {m B : Side} {c : Phase.Part m B} {A D d e β : ℝ} {W : Scroll m B c}
noncomputable def amplitudeF {c : Phase.Part m B} (W : Scroll m B c) (l : Foot m B) (β t a : ℝ) (f : Test m B) (x : Pack m B) :=
    ((net m B β x):ℂ)*Complex.exp (-(a:ℂ)*cabinQ W x)*inner ℂ (linearB (CSide m B)) (acts (f x*quant (n:=Xmind m B) (grow (wiel m B l x.1) t)) (pairWave (n:=Xmind m B) (pair m B x.1 x.2)))
def ratioRF {c : Phase.Part m B} (W : Scroll m B c) (e β τ k : ℝ) (l : Foot m B) (f : Test m B) := (TallyR m B e β).indicator (amplitudeF W l β τ k f)
def rawEF {c : Phase.Part m B} (W : Scroll m B c) (e β τ k : ℝ) (l : Foot m B) (f : Test m B) := ∫ x,ratioRF W e β τ k l f x ∂wheel m B
section rays
variable (g : ScaleK A D W) (k : Budget B e d)
include g k
lemma bill_lim (S : costG m B) {x:Pack m B}(f:x∈payer m B e): ‖billP W S x‖≤ rip m*W.mint S.2:=by
 unfold billP workQ; rw [norm_smul, pay_t,Real.norm_of_nonneg (by unfold rip; positivity)]; apply mul_le_mul_of_nonneg_left ((gainS g k _).norm _ (voxel B _ _ _ f)); unfold rip; positivity
lemma port_limF (i) : ∃ c≥(0:ℝ), ∀ x∈payer m B e, ‖passQ W i x‖≤c := by
  let f (S:costG m B) := ‖bonus (target S) i‖*(rip m*W.mint S.2)
  have he S : 0≤f S := mul_nonneg (norm_nonneg _) (mul_nonneg (by unfold rip; positivity) (gainS g k _).pos)
  refine ⟨∑ S,f S,sum_nonneg (fun S _=>he S),fun x h=>?_⟩; unfold passQ; apply (norm_sum_le ..).trans; exact sum_le_sum fun S _=> by rw [norm_smul]; exact mul_le_mul_of_nonneg_left (bill_lim g k S h) (norm_nonneg _)
lemma cabin_limF : ∃ c≥(0:ℝ), ∀ x∈payer m B e, ‖cabinQ W x‖≤c := by
  obtain ⟨v,p,L⟩ := port_limF g k 0; exact ⟨v+v,by positivity,fun x h=>by rw [vx 0]; apply (norm_add_le ..).trans; rw [norm_star]; exact add_le_add (L x h) (L _ (dominated _ _ h))⟩
lemma amplitude_sizeF {f : Test m B} (h : Continuous f) (β t a : ℝ) (l:Foot m B) :
    ∃ c:ℝ,0≤c∧ ContinuousOn (amplitudeF W l β t a f) (payer m B e) ∧ ∀ x∈payer m B e, ‖amplitudeF W l β t a f x‖≤c := by
  let p := payer m B e; let N := CSide m B; let M := Xmind m B; let s:= linearB N
  let F := fun x:Pack m B => f x*quant (n:=M) (grow (wiel m B l x.1) t)
  let P := fun x: Pack m B=>pairWave (n:=M) (pair m B x.1 x.2)
  let X := cabinQ W; let L x : ℂ := ↑(net m B β x)
  let E (Y : ℂ) := Complex.exp (-(a:ℂ)*Y)
  have he : Continuous L := Complex.continuous_ofReal.comp (net_cont m B β)
  have hf : Continuous F := h.mul (actualC ..)
  have hp : ContinuousOn P p := (pairWave_cont (n:=M)).comp_continuousOn (pair_cont k.1)
  have ht : ContinuousOn X p := continuousOn_finsetSum _ fun i _=> brave g k i
  have hx : Continuous E := Complex.continuous_exp.comp (continuous_const.mul continuous_id)
  obtain ⟨v,pV,hV⟩ := cabin_limF g k
  obtain ⟨c,pA,hA⟩ := roofC hf; obtain ⟨m₁,p₁,h₁⟩ := roofC he
  obtain ⟨w,p₂,h₂⟩ := circular hx (isCompact_closedBall 0 v)
  obtain ⟨v₁,p₃,h₃⟩ := circular (pairWave_cont (n:=M)) (isCompact_closedBall (0:Op M) 1)
  refine ⟨(m₁*w)*(‖s‖ * (c*v₁)),by positivity, ?_,?_⟩
  · change ContinuousOn (fun x=>L x*E (X x)*inner ℂ s (acts (F x) (P x))) _
    exact (he.continuousOn.mul (hx.comp_continuousOn ht)).mul (continuousOn_const.inner ((acts_cont.comp hf).continuousOn.clm_apply hp))
  intro x l; let Y := pair m B x.1 x.2; have hz : ‖Y‖=1 := CStarRing.norm_of_mem_unitary (kappa (0:Phase.Part m B) k.1 l.1 l.2).1
  have hL : ‖P x‖≤v₁ := h₃ Y (by simpa using hz.le)
  have hy : ‖acts (F x) (P x)‖ ≤ c*v₁ := (ContinuousLinearMap.le_opNorm ..).trans (mul_le_mul (show ‖acts (F x)‖≤c by rw [acts, Matrix.l2_opNorm_toEuclideanCLM]; exact hA _) hL (norm_nonneg _) pA)
  change ‖L x*E (X x)*inner ℂ s (acts (F x) (P x))‖≤ _; rw [norm_mul,norm_mul];
  exact mul_le_mul (mul_le_mul (h₁ _) (h₂ (X x) (by simpa using hV _ l)) (norm_nonneg _) p₁) ((norm_inner_le_norm ..).trans (mul_le_mul_of_nonneg_left hy (norm_nonneg _))) (norm_nonneg _) (mul_nonneg p₁ p₂)
lemma sojournF {f: Test m B} (h : Continuous f) (β t a : ℝ) (l:Foot m B) : Integrable (ratioRF W e β t a l f) (wheel m B) := by
  obtain ⟨K,m',H,G⟩ := amplitude_sizeF g k h β t a l
  exact gift_integrate _ (fun i g=> tallyP g) (tally_meas ..) m' H G
end rays
variable (H : ScaleK A D W) (g : Budget B e d) (l : Foot m B) (t : ℝ) (k : 0≤t) (a : ℝ) (β) (i : Axis) (x : Pack m B) (f : Test m B) (b : Bool) (h : OfferedF m B i f b)
include H g k h
lemma in_spotF [Nonempty (staple m B i x e β)] : let T := staple m B i x e β; ∃ R : CSeat T (Xmind m B), R∈Cloud (finger m B i) (colony m B i) T ∧ ∀ y z : T,
    R (y,z) (upperP (CSide m B)) (upperP (CSide m B))= amplitudeF W (axisCut m B i l) β t a (fiscal m B i f b) (tiedK m B i x y.val z.val) := by
  intro T; let N := CSide m B; let M := Xmind m B; let r := tiedK m B i x; let U := finger m B i
  let s (x:T×T) := r x.1.val x.2.val; let f₁ := fun j:T=>s (j,j)
  have hF y z : s (y,z)∈ TallyR m B e β := (apt ..).mpr ⟨y.property,z.property⟩
  have hf v : f₁ v∈payer m B e := tallyP (hF v v)
  have hc : Continuous f₁ := (zoneA i x).comp (continuous_subtype_val.prodMk continuous_subtype_val)
  let c₀ (j:T) := Real.sqrt (net m B β (f₁ j)); let d₀ (j:T) := Complex.exp (-(a:ℂ)*passQ W i (f₁ j)); let D₀ : T → FC M := fun j=> ((c₀ j : ℂ)*d₀ j) • f (f₁ j)
  have hb : Continuous c₀ := ((net_cont m B β).comp hc).sqrt
  have ht : Continuous d₀ := Complex.continuous_exp.comp (continuous_const.mul ((pᵣ H g i).comp_continuous hc hf))
  have H₀ : Continuous D₀ := by unfold D₀; exact ((Complex.continuous_ofReal.comp hb).mul ht).smul (h.cont.comp hc)
  obtain ⟨v,hV⟩ : ∃ v, ∀ t, ‖D₀ t‖ ≤ v := by
    obtain ⟨o,w,hW⟩ := port_limF H g i
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
  have h₄ : star (d₀ z)*d₀ y=Complex.exp (-(a:ℂ)*cabinQ W G) := by
    have hk : cabinQ W G=passQ W i p+star (passQ W i q) := pairt H g i x y.val z.val _ (hF y z) -- tune G passed shadow
    unfold d₀; change star _ * _=_; rw [hk, show ∀ z, star (Complex.exp z)=Complex.exp (star z) from fun z=>Complex.exp_conj z|>.symm, ←Complex.exp_add]; congr 1
    change star (-(a:ℂ)*passQ W i q)+ -(a:ℂ)*passQ W i p= _; rw [star_mul', star_neg]; simp; ring
  let E : ℂ := (net m B β G:ℂ)*Complex.exp (-(a:ℂ)*cabinQ W G)
  have Hk : K (y,z)= E • fiscal m B i f b G := by
    unfold K; rw [brick]; change chord b • (theta U (((c₀ z:ℂ)*d₀ z) • f q)*(((c₀ y:ℂ)*d₀ y) • f p))=_
    rw [theta_smul, Algebra.mul_smul_comm, Algebra.smul_mul_assoc, h₁,h₂,fiscal,star_mul']
    simp only [smul_smul, Complex.star_def, Complex.conj_ofReal];
    apply congrArg (fun k:ℂ=> k • (theta U (f (Pbar m B i G))*f G)); unfold E; rw [← h₄,←h₃]; push_cast; change _=_; simp only [Complex.star_def]; ring
  rw [act_mul (_ * _), kV, vv, Hk, Algebra.smul_mul_assoc,act_smul, inner_smul_right]; rfl

lemma meas_pos0F : (∫ u, ratioRF W e β t a (axisCut m B i l) (fiscal m B i f b) (quill m B i (x,u)) ∂((wheel m B).prod (wheel m B)))≥0 := by
  let T := staple m B i x e β; let X := (wheel m B); let P := amplitudeF W (axisCut m B i l) β t a (fiscal m B i f b)
  let F := fun p:Pack m B × Pack m B=> P (quill m B i (x,p))
  let J := T×ˢT
  -- indicator exact
  have hm : MeasurableSet T := staple_meas β i x e -- tune
  have he u : ratioRF W e β t a (axisCut m B i l) (fiscal m B i f b) (quill m B i (x,u))= J.indicator F u := by
    unfold ratioRF; have ht : quill m B i (x,u)∈ TallyR m B e β ↔ u∈J := apt ..
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
  obtain ⟨Q,p,v⟩ := in_spotF β H g l t k a i x f b h
  have hg (u : T × T) : F (A' u)=Q u (upperP (CSide m B)) (upperP (CSide m B)) := (v u.1 u.2).symm
  simp_rw [hg]; exact cloud_pos _ _ (slide_plus i) (movedCol ..) Y p -- tune
lemma usableF : Integrable (ratioRF W e β t a (axisCut m B i l) (fiscal m B i f b)) (wheel m B) := by
  apply sojournF H g; unfold fiscal
  exact (continuous_const (y:=chord b)).smul (((theta_cont (finger m B i)).comp (h.cont.comp ((slideM m i).convey B))).mul h.cont)
-- consumes one axis seam cut. No normalization needed until later proof of strictness.
theorem crossing_nonnegativeF : 0 ≤ rawEF W e β t a (axisCut m B i l) (fiscal m B i f b) := by rw [rawEF,heard m B i _ (usableF β H g l t k a i f b h)]; exact integral_nonneg fun x=> meas_pos0F β H g l t k a i x f b h

omit H g k h
lemma from_toF (p q:Foot m B) (t a:ℝ) (x : Pack m B) (f f' : Test m B) (h : twist (quantU (fringe p q)) (f x)=f' x) : ratioRF W e β t a p f x=ratioRF W e β t a q f' x := by
  unfold ratioRF; by_cases k:x∈TallyR m B e β <;> try simp [k]
  unfold amplitudeF
  let U := fringe p q; let A := wiel m B p x.1; let P := quantU U; let C := pair m B x.1 x.2
  have he : twist U A=wiel m B q x.1 := swingFringe p q _
  apply congrArg; change _=inner ℂ _ (acts (f' x*quant _) (pairWave C)); rw [←h,←he,←quant_flow];
  have hy : acts P.val (pairWave C)=pairWave C := (pair_cov U.val C).trans (congrArg (pairWave (n:=Xmind m B)) (grade_fringe p q _))
  change inner ℂ _ (acts (f x*_ ) (pairWave C))=inner ℂ _ (acts (twist P _*twist P _) (pairWave C)); rw [←map_mul]; nth_rw 2 [←hy]; exact (bra U (fixedSign p q) _ _).symm
lemma bill_rotF (v : Foot m B) (i : Trip m) (x : Pack m B) (b : ∀ j,i.glare j=false) (f f' : Test m B) (h : f' (onPack B i x)= twist (quantU (siteM (fperm m B i))) (f x)) (t a:ℝ) :
    ratioRF W e β t a (far B i v) f' (onPack B i x)=ratioRF W e β t a v f x := by
  unfold ratioRF; by_cases k:x∈TallyR m B e β
  · rw [Set.indicator_of_mem k, Set.indicator_of_mem ((turn_ineq i x).mp k)]; unfold amplitudeF; rw [newbill,←Gloss.ζ_b, Gloss.pure, show ∀ z:ℂ, Spire.payZ (phat i) z=z from fun z=> by unfold Spire.payZ; rw [Gloss.η_x i b]; rfl, Gloss.ζ_b]
    let q := onPack B i x; let U := siteM (fperm m B i); let P := quantU U; let S := pair m B x.1 x.2
    have hu : wiel m B (far B i v) q.1= twist U (wiel m B v x.1) := (careH i b _ v).symm
    have hh : pair m B q.1 q.2=congrC U S := by
      have he s t : bow m B (through B i x.1) (i.riseF s) t=congrC U (bow m B x.1 s t) := by rw [bow,played, ←siteField]; rfl
      exact he (slot m x.2) (stick 0)
    rw [hu,h, ←quant_flow,hh]; apply congrArg
    change inner ℂ _ (acts (twist P _*twist P _) (pairWave _))=_; rw [←map_mul]
    unfold congrC; rw [←pair_cov]; exact bra U (fixedPerm _) _ _
  rw [Set.indicator_of_notMem k, Set.indicator_of_notMem (fun l=>k ((turn_ineq i x).mpr l))]
include H g
lemma displacementF (v : Site (More m)) (l : Foot m B) (i : Axis) (t a : ℝ) (k : 0≤t) (f b) (h : OfferedF m B i f b) :
    0 ≤ rawEF W e β t a l (squareR m B v l i f b) := by
  let I := northTrip m v; let T := far B I l; let y := axisCut m B i T; let p := siteM (fperm m B I); let q := fringe T y
  let F := squareR m B v l i f b; let G := fiscal m B i f b
  let J := fun x => twist (star (quantU q)) (G x)
  have he x : ratioRF W e β t a l F x=ratioRF W e β t a y G (onPack B I x) := by
    let z := onPack B I x
    have hp (U : UNI (Finset (Model (CSide m B)))) (A : FC (Model (CSide m B))) : twist U (twist (star U) A)=A := by simpa only [star_star] using twist_inv (star U) A
    apply Eq.trans _ (from_toF β T y t a z J G (hp ..))
    apply (bill_rotF β l I x (fun _=>rfl) F J _ t a).symm
    let v := quantU p; let w := quantU q
    have ht : quantU (q*p) = w*v := Subtype.ext (quant_mul _ _)
    change twist (star w) _=twist v (twist (star (quantU (q*p))) _); rw [ht,star_mul,Fock.twin,hp]
  unfold rawEF; change 0≤ ∫ x,ratioRF W e β t a l F x ∂_; simp_rw [he]; rw [use_trip I (ratioRF W e β t a y G)]; exact crossing_nonnegativeF β H g T t k a i f b h
end YM.CF.RP.Str
