import YM.SU5.Circuit.Muse
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
noncomputable section
namespace YM.Regis.Circuit
open Function Filter Metric Lattice Laurent Next.Free Bloch Finset CF CF.Lat CF.Jill CF.Ember CF.Flare CF.Onyx CF.Fir
open Precision Exterior Matrix RG Work.F06 MeasureTheory
open YM.Stationary (Gaia cartWeight)
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Classical
variable {x:Gaia}(P Q:Lattice.PlaqAxes)
local notation "A" => P.val.1
local notation "B" => P.val.2
local notation "Cμ" => Q.val.1
local notation "D" => Q.val.2 -- exclude C
-- adapt d_plaquettes to wedge
lemma boreal (p:Gaia) (k:Axis): BoreV p 1 (plaquette P) (coord k)= (if k=B then arrow p A else 0) - if k=A then arrow p B else 0:=by
 let F:= plaquette P; have he:A < B:=P.property; have h:F.val={A,B}:=rfl
 unfold BoreV wedge; simp only [Matrix.sum_apply,Matrix.smul_apply]; rw [←sum_subset (subset_univ ({A,B}:Finset Axis)),sum_insert (by simp [he.ne]),sum_singleton]; swap
 · intro i _ hi; unfold Exterior.left; rw [Matrix.of_apply,dif_neg (show i∉F.val from hi)]; simp
 have hA:A∈F.val:=mem_insert_self ..; have hB:B∈F.val:=mem_insert_of_mem (mem_singleton_self _); have ha:Exterior.remove A F hA=coord B:=by ext i; simp [Exterior.remove,coord,h]; rintro rfl; exact he.ne'
 have hb: Exterior.remove B F hB=coord A:=by ext i; by_cases x:i=B<;>simp [x,coord,h,Exterior.remove,he.ne']
 have h0 : parity F.val A ℂ=1 := by simp [parity,pre,h,Finset.filter_insert,Finset.filter_singleton,he.not_gt]; -- tune
 have h1 : parity F.val B ℂ= -1 := by simp [parity,pre,h,Finset.filter_insert,Finset.filter_singleton,he]
 change _ * Exterior.left ℂ 1 A F (coord k) + _ * Exterior.left ℂ 1 B F (coord k) = _; unfold Exterior.left; rw [of_apply,of_apply,dif_pos hA,dif_pos hB,ha,hb,h0,h1]; simp only [coord_iff,mul_ite,mul_one,mul_neg, mul_zero]; unfold arrow; simp only [eq_comm]; -- align maybe reverses both due ordering
 split_ifs <;> abel_nf <;> try rfl

lemma arrow_neg (p:Gaia)(a: Axis): star (arrow p a)= -arrow p a:=by simp [arrow,mul_comm]
def solo (k l:Axis)(x:ℂ):= if k=l then x else 0
lemma boreScore (p:Gaia): (BoreV p 1*(BoreV p 1)ᴴ) (plaquette P) (plaquette Q)= -(solo D B (arrow p A*arrow p Cμ)-solo Cμ B (arrow p A*arrow p D))+(solo D A (arrow p B*arrow p Cμ)-solo Cμ A (arrow p B*arrow p D)):=by -- negative applied
 rw [Matrix.mul_apply, ← Equiv.sum_comp axisEquiv]; simp_rw [Matrix.conjTranspose_apply,coord_map,boreal]; simp only [solo,star_sub, apply_ite (star : ℂ→ℂ),arrow_neg,star_zero,sub_mul,mul_sub, ite_mul, zero_mul,Finset.sum_sub_distrib]; simp [eq_comm]; split_ifs <;> abel
lemma elegant (v:ℝ)(x p:Gaia): inspiration (plaquette P) (plaquette Q) v x p = solo Cμ B (music A D v x p) - solo D B (music A Cμ v x p) - (solo Cμ A (music B D v x p)-solo D A (music B Cμ v x p)):=by
 unfold inspiration Boreas; rw [Matrix.smul_apply,boreScore]; unfold solo music nerve purr pet; push_cast; rw [_root_.zpow_neg,zpow_ofNat]; unfold arrow; -- push cast unfolded?
 split_ifs <;> ring
lemma Solo_works (k l:Axis)(x:ℂ) : (if k=l then (1:ℂ) else 0)*x= solo k l x:= by cases eq_or_ne k l<;> simp [*,solo]
lemma inConcerto (d:ℝ)(x:Gaia)(h:0<d): hotK (plaquette P) (plaquette Q) (d^2)⁻¹ x = solo Cμ B (kinder A D d x)- solo D B (kinder A Cμ d x) - (solo Cμ A (kinder B D d x)-solo D A (kinder B Cμ d x)):=by
 let y:=(d^2)⁻¹; have hp:0<y:=by unfold y; positivity
 unfold hotK; simp_rw [elegant P Q]; simp_rw [← Solo_works]; unfold kinder; 
 have hf(c:ℂ)(a b:Axis):= (toneBudget hp a b x).const_mul c
 rw [integral_sub (Integrable.sub' (hf _ _ _) (hf _ _ _)) (Integrable.sub' (hf _ _ _) (hf _ _ _)), integral_sub (hf _ _ _) (hf _ _ _), integral_sub (hf _ _ _) (hf _ _ _)]; simp_rw [integral_const_mul]; ring
lemma warmer (p:x≠0): Tendsto (fun d:ℝ=> hotK (plaquette P) (plaquette Q) (d^2)⁻¹ x) atTop (𝓝 ((Maxwell.bareCurl A B Cμ D x:ℝ):ℂ)):=by
 let I (a b:Axis):= ((Maxwell.grad a (Maxwell.grad b Maxwell.Green) x: ℝ):ℂ)
 have he(k l a b:Axis): Tendsto (fun d=> solo k l (kinder a b d x)) atTop (𝓝 (solo k l (I a b))):=by simp_rw [←Solo_works]; exact (kiss a b p).const_mul _
 have h:= ((he Cμ B A D).sub (he D B A Cμ)).sub ((he Cμ A B D).sub (he D A B Cμ)); unfold Maxwell.bareCurl; rw [Pi.sub_apply,Maxwell.Bare.opp_grad p,Maxwell.Bare.opp_grad p]; convert h.congr' ((eventually_gt_atTop 0).mono fun i q=> (inConcerto P Q i x q).symm) using 3; unfold solo I; push_cast; split_ifs <;> rfl
abbrev specter (x:Gaia):ℂ:= Maxwell.bareCurl A B Cμ D x
/-- HARD (unsmeared) curvature covariance at any fixed noncoincident ray. -/
theorem mercury {S:ℕ→ Side}{M:ℕ→Bed}{R:ℕ→ℝ}{z:ℕ→Cover}{η σ V:ℝ}{q:Clip}(U:Yard S R)(v: Tendsto (fun i=>riseX (R i) (z i)) atTop (𝓝 x))(w:x≠0)(G:∀ i,(M i).covered σ V)(W:∀ i, Floor (M i) q (S i) η V)(u:0<σ)(a:0<V): Tendsto (fun i=> magnify (M i) (R i) (plaquette P) (plaquette Q) (z i) (S i)) atTop (𝓝 (specter P Q x)):=by
 obtain ⟨B₅,b,Y⟩:= unpublished S R z U v w u a η q (plaquette P) (plaquette Q)
 let F(i):=specter P Q i; let H(i):=hotK (plaquette P) (plaquette Q) (i^2)⁻¹ x; let T(i):=magnify (M i) (R i) (plaquette P) (plaquette Q) (z i) (S i)
 have hx:Tendsto H atTop (𝓝 (F x)):=warmer P Q w
 refine Metric.tendsto_nhds.mpr fun e he=> ?_; have ht:Tendsto (fun x:ℝ=> B₅/x^2) atTop (𝓝 0):=by have hg:= (tendsto_inv_atTop_zero (𝕜:=ℝ)).comp (tendsto_pow_atTop (by decide : (2:ℕ)≠0)); simpa only [Function.comp_def,mul_zero,←div_eq_mul_inv] using hg.const_mul B₅
 obtain ⟨d,⟨hd,hy⟩,d'⟩:= (((Metric.tendsto_nhds.mp hx (e/3) (by linarith)).and (ht.eventually (gt_mem_nhds (show 0<e/3 by positivity)))).and (eventually_gt_atTop 0)).exists; let L(i):= chant (M i) (R i) d (plaquette P) (plaquette Q) (z i) (S i)
 filter_upwards [Y,Metric.tendsto_nhds.mp (show Tendsto L atTop (𝓝 (H d)) from daylightK U W G u a v d' (plaquette P) (plaquette Q)) (e/3) (by linarith)] with i hi hv; specialize hi d d' (M i) (G i) (W i); rw [← dist_eq_norm] at hi; change dist (T i) (F x)<_; change dist (T i) (L i)≤_ at hi; change _<_ at hy; have h':B₅/d^2< e/3:= hy; linarith only [hi,h',hd,hv,dist_triangle (T i) (L i) (F x),dist_triangle (L i) (H d) (F x)]
end YM.Regis.Circuit
#print axioms YM.Regis.Circuit.mercury
