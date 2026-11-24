import YM.SU5.FiniteGaugeData.Cirrus.Maison
import YM.SU5.FiniteGaugeData.Poin.Sonic
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin.Maison
open Complex Filter Function Set MeasureTheory MeasureTheory.Measure Boundary OS OS.Semigroup Mink.Lorentz
open scoped Topology NNReal InnerProductSpace
variable {H:Hilbert}(S: OS.Semigroup H timeAxis)
variable {E:Type*}[NormedAddCommGroup E][NormedSpace ℂ E][CompleteSpace E](F: H.space→L[ℂ]E)(x:H)
local notation "c"=> basis timeAxis
local notation "J"=>M S
section
lemma edgeRules (t:ℝ)(k:∀ᶠ r:ℝ in 𝓝 t,F (S.edge r x)=0) : ∀ r:ℝ, F (S.edge r x)=0:=by
 let m(z:ℂ):= z.re.toNNReal; let g(z:ℂ):= F (S.edge (-z.im) (S.E (m z) x))
 have v: Continuous g:= F.continuous.comp (S.cont_edge (fun z=>S.E (m z) x) (fun z=>-z.im) ((S.continuousE x).comp (show Continuous m from by unfold m;fun_prop)) continuous_im.neg)
 have h:DifferentiableOn ℂ g inside:=by
    let A:= F.comp (ContinuousLinearMap.apply ℂ H.space x); apply ((A.differentiable.comp_differentiableOn S.localHeat.differentiableOn)).congr
    intro z hz; have hu: 0 < m z:=Real.toNNReal_pos.mpr hz; apply congrArg F; rw [← S.roots_heat hu]; apply Eq.trans (DFunLike.congr_fun (S.along (dur.mpr hu) (-z.im)) x); congr 1; simp only [ContinuousLinearMap.id_apply]; apply congrArg S.F; apply Complex.ext <;> simp [sideways,duration,m, Real.coe_toNNReal _ (show 0< z.re from hz).le]
 have he(r:ℝ):g ⟨0,-r⟩=F (S.edge r x):=by simp [g,m,S.eZero]
 have ht: ∀ᶠ r:ℝ in 𝓝 (-t), g ⟨0,r⟩=0:=by
    have V:Tendsto (fun r:ℝ=>-r) (𝓝 (-t)) (𝓝 t):= by simpa using ((continuous_neg (G:=ℝ)).tendsto (-t));
    filter_upwards [V.eventually k] with r hr; rw [← neg_neg r,he]; exact hr
 intro r; rw [← he]; exact crease g (-t) v h ht (show (0:ℝ)≤0 from le_rfl)
open Mink Mink.Poincare
variable (X:Boundary.Action H)(hx:∀ p:E4,X.orbit.translation p=M S p)
include hx
lemma raised (L:Mink.Lorentz)(t:ℝ) : M S (t • L.act (c))= X.V (motion L) * S.edge t * X.V (motion L)⁻¹ :=by
 let A:= motion L; rw [← timeslot,← hx,← hx]; change X.V _= X.V A * X.V _ * X.V _; rw [show ∀ p q,X.V p* X.V q= X.V (p*q) from fun p q=>(X.mult p q).symm];
 rw [show ∀ p q,X.V p* X.V q= X.V (p*q) from fun p q=>(X.mult p q).symm]
 apply congrArg X.V; apply mul_right_cancel (b:=A)
 rw [mul_assoc,mul_assoc,inv_mul_cancel,mul_one]
 apply by_placement; intro x; unfold A; simp [map_smul]
omit hx in
lemma alongSplit (p:E4) : ∃ (a b:ℝ) (L:Mink.Lorentz), p=a • basis timeAxis + b • L.act (basis timeAxis):=by
 let T:=‖spatial p‖; rcases eq_or_lt_of_le (show 0≤T from norm_nonneg _) with t|h
 · refine ⟨time p,0,1, ext_by ?_ ?_⟩; simp [show spatial p=0 from norm_eq_zero.mp t.symm]; simp
 let E':Ray:=⟨T⁻¹ • spatial p,by rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr h)]; exact inv_mul_cancel₀ h.ne'⟩
 let s:= Real.sinh 1; have hs:0<s:=Real.sinh_pos_iff.mpr zero_lt_one; let b:= T/s; refine ⟨time p-b*Real.cosh 1,b,E'.boost 1, ext_by ?_ ?_⟩
 · have hv:b*s=T:=div_mul_cancel₀ _ hs.ne'; rw [Ray.boost_at]; simp [Ray.newSpace,Ray.along,←mul_smul,show b*Real.sinh 1=T from hv]; change spatial p=T • (T⁻¹ • spatial p); rw [smul_smul,mul_inv_cancel₀ h.ne',one_smul]
 rw [Ray.boost_at]; simp [Ray.newClock,Ray.along]
lemma still (u:E4)(p: ∀ᶠ q in 𝓝 u,F (M S q x)=0) : ∀ q:E4,F (M S q x)=0:=by
 let P(z:E4):Prop:=∀ᶠ i in 𝓝 z,F (M S i x)=0; have he(E:Mink.Lorentz)(s:ℝ)(z:E4)(h:P z): P (z+s • E.act (c)):=by
    obtain ⟨U,v,V,w⟩:= (mem_nhds_iff.mp h)
    let i(r:ℝ):= r • E.act (c); let g:= motion E; let f(y:E4):=y-i s
    have hy(z:E4)(t:z∈ U)(r:ℝ) : F (M S (z+i r) x)=0:=by
       let G:= ((F.comp (M S z)).comp (X.V g)); let y:= X.V g⁻¹ x; have hs (r:ℝ) : F (M S (z+i r) x)= G (S.edge r y) :=by rw [← tgo,raised S X hx E]; rfl
       rw [hs]; apply edgeRules S G y 0 _ r; let T (r:ℝ):=z+i r; have ht: Continuous T:=by unfold T i;fun_prop;
       filter_upwards [ (ht.tendsto 0).eventually (show ∀ᶠ u in 𝓝 (T 0),u∈ U from V.mem_nhds (show T 0∈U from by simpa [T,i] using t))] with r hr; rw [← hs r]; exact v hr
    have H:f (z+s • E.act (c))∈ U:=by unfold f i; rw [add_sub_cancel_right]; exact w;
    refine ((show Continuous f from continuous_id.sub continuous_const).continuousAt.tendsto.eventually (show ∀ᶠ u in 𝓝 (f (z+s • E.act (c))), u∈ U from V.mem_nhds H)).mono (fun t r=>?_); exact (show f t+i s=t from sub_add_cancel ..) ▸ hy (f t) r s
 intro q; obtain ⟨a,b,E,r⟩:= alongSplit (q-u); have k:u+a • basis timeAxis+b • E.act (c) = q:= by rw [add_assoc,← r,add_comm,_root_.sub_add_cancel];
 have e: P (u+a • basis timeAxis):=by simpa using he (1:Mink.Lorentz) a _ p;
 have hv:∀ᶠ y in 𝓝 q, F (M S y x)=0:=k ▸ he E b _ e; exact hv.self_of_nhds
#print axioms still
end
end YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin.Maison
