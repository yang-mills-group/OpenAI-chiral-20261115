import YM.SU5.Reconstruction.Vermont.Playlist
import YM.SU5.Reconstruction.Vermont.Seam
/-!
# Merge across horizontal intervals with vertical wick doors.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Lens
open Function Set Filter MeasureTheory Spectral Analysis OS.Semigroup ConePrice Sail ContinuousLinearMap
open scoped BigOperators Topology NNReal InnerProductSpace ComplexOrder
variable {H:Hilbert}{a:Axis}{S:OS.Semigroup H a}{L:H.Op}{r:ℝ}
local notation "Δ" z:max=> LorTime S (-(z:ℂ).im) L
variable {X Y:ℂ→H.Op}{A B:H.Op}{v w c d:ℝ≥0}(x: Port S L r X A v c)(y:Port S L r Y B w d)
noncomputable def alloy (X Y:ℂ→H.Op)(A B:H.Op)(v:ℝ≥0)(z:ℂ): H.Op:= if z.re ≤ (v:ℝ) then X z* B else A * Y (z-(v:ℝ))
local notation "𝔍" => alloy X Y A B v
local notation "𝒬" => bore r ((v+w:ℝ≥0):ℝ)
local notation "𝔳"=> (((v:ℝ):ℂ))
local notation "ϕ"=>fun (z:ℂ)=> z - ((v:ℝ):ℂ)
@[simp ↓] private lemma shift_im (z:ℂ): (z - ((v:ℝ):ℂ)).im=z.im:= by simp
@[simp ↓] private lemma shift_re (z:ℂ): (z - ((v:ℝ):ℂ)).re=z.re - (v:ℝ) :=by simp
lemma ahead {z:ℂ}(p:z.re≤(v:ℝ)) : alloy X Y A B v z=X z*B:= if_pos p
include x y
lemma aft {z:ℂ}(p: (v:ℝ)≤ z.re) (e:|z.im|≤r) : 𝔍 z=A*Y (z - ((v:ℝ):ℂ)):= by
 unfold alloy; split; rename_i h; swap; rfl
 have t:= h.antisymm p; rw [x.right z t e, y.left (z-𝔳) (by simp [t]) (by simpa using e), shift_im, mul_assoc]
omit x y
private lemma rear {z:ℂ}(p:z∈ bore r ((v+w:ℝ≥0):ℝ)) (k: (v:ℝ)≤ z.re) : z-𝔳∈ bore r (w:ℝ) := by
  have h:z.re≤ (v:ℝ)+(w:ℝ):= p.1.2; exact ⟨⟨by simpa using sub_nonneg.mpr k,by rw [shift_re]; linarith⟩,by rw [shift_im]; exact p.2⟩
private lemma road {z:ℂ}(p:z∈ veil 0 ((v+w:ℝ≥0):ℝ) r) (k: (v:ℝ)< z.re) : z-𝔳∈ veil 0 (w:ℝ) r:= by
 have h:z.re< (v:ℝ)+(w:ℝ):= p.2.1; refine ⟨by simpa using sub_pos.mpr k,by rw [shift_re]; linarith,?_⟩; change |(z-𝔳).im|<_; rw [shift_im]; exact p.2.2
include x y
private lemma funds (p q:H) : ContinuousOn (fun z=>inner ℂ p (𝔍 z q)) (𝒬):= by
 let A₀: Set ℂ:= {z|z.re≤(v:ℝ)}; let B₀:Set ℂ:= {z| (v:ℝ)≤ z.re}; let F(z:ℂ):= inner ℂ p (𝔍 z q)
 have h:ContinuousOn F (𝒬∩A₀):= ((x.guard p (B q)).mono (fun z t=>⟨⟨t.1.1.1,t.2⟩,t.1.2⟩)).congr fun z t=> by unfold F; rw [ahead (z:=z) t.2]; rfl
 have g:ContinuousOn F (𝒬∩B₀):= by
   refine ((y.guard (A.adjoint p) q).comp (f:=ϕ) (((continuous_id (X:=ℂ)).sub continuous_const).continuousOn) (fun z t=> rear t.1 t.2)).congr ?_
   intro z t; unfold F; rw [aft x y t.2 t.1.2]; exact (adjoint_inner_left A _ _).symm
 exact (h.union_of_isClosed g ((bore_c ..).inter (isClosed_le Complex.continuous_re continuous_const)) ((bore_c ..).inter (isClosed_le continuous_const Complex.continuous_re))).mono (fun z u=> by rcases le_total z.re (v:ℝ) with a|b; exact Or.inl ⟨u,a⟩; exact Or.inr ⟨u,b⟩) -- tune `∩` mem defs local

lemma welding : Port S L r (alloy X Y A B v) (A*B) (v+w) (c*d):=by
 refine ⟨(norm_mul_le ..).trans (mul_le_mul x.order y.order (norm_nonneg _) ((norm_nonneg _).trans x.order)),funds x y, ?_,?_,?_,?_⟩
 · intro z p; rcases le_total z.re (v:ℝ) with t|h
   · rw [ahead t]; exact (norm_mul_le ..).trans ((mul_le_mul (x.toll z ⟨⟨p.1.1,t⟩,p.2⟩) y.order (norm_nonneg _) ((norm_nonneg _).trans (x.toll z ⟨⟨p.1.1,t⟩,p.2⟩))).trans_eq (by push_cast; ring))
   rw [aft x y h p.2]; exact (norm_mul_le ..).trans ((mul_le_mul x.order (y.toll _ (rear p h)) (norm_nonneg _) ((norm_nonneg _).trans x.order)).trans_eq (by push_cast; ring))
 · intro p q; let U:= veil 0 ((v+w:ℝ≥0):ℝ) r; let f(z:ℂ):=inner ℂ p (𝔍 z q); have h:IsOpen U:= veil_open _ _ _; apply DifferentiableOn.analyticOnNhd ?_ h; refine seam_cement (t:=(v:ℝ)) ?_ ((funds x y p q).mono (bore_v _ _)) h
   intro z e a₀; rcases lt_or_gt_of_ne a₀ with t|u
   · apply (x.analytic p (B q) z ⟨e.1,t,e.2.2⟩).differentiableAt.congr_of_eventuallyEq
     filter_upwards [(isOpen_lt Complex.continuous_re continuous_const).mem_nhds t] with z q'; change inner ℂ p (𝔍 z q)=_; rw [ahead (show z.re< _ from q').le]; rfl
   apply ((y.analytic (A.adjoint p) q _ (road e u)).differentiableAt.comp (f:=ϕ) z (differentiableAt_id.sub (differentiableAt_const _))).congr_of_eventuallyEq
   filter_upwards [h.mem_nhds e,(isOpen_lt continuous_const Complex.continuous_re).mem_nhds u] with z e' k
   change inner ℂ p (𝔍 z q)=_; rw [aft x y (show (v:ℝ)<z.re from k).le ((bore_v _ _ e').2)]; exact (adjoint_inner_left A _ _).symm
 · intro z p q; rw [ahead (p ▸ (v:ℝ≥0).property),x.left z p q,mul_assoc]
 intro z p q; have hp:z.re= (v:ℝ)+(w:ℝ):= p; rw [aft x y (hp.symm ▸ le_add_of_nonneg_right (w:ℝ≥0).property) q,y.right (z-𝔳) (by rw [shift_re,hp]; ring) (by simpa using q), shift_im, mul_assoc]

omit y in
lemma Port.creates (y:Port S L r Y B v d) : Port S L r (fun z=>X z + Y z) (A+B) v (c+d):= by
 refine ⟨(norm_add_le ..).trans (add_le_add x.order y.order),fun p q=>?_,?_,fun p q=>?_,fun z e f=> by rw [x.left _ e f,y.left _ e f,mul_add],fun z e f=> by rw [x.right _ e f,y.right _ e f,add_mul]⟩
 · simp only [add_apply,inner_add_right]; exact (x.guard p q).add (y.guard p q)
 · exact fun z h=> (norm_add_le ..).trans ((add_le_add (x.toll z h) (y.toll z h)).trans_eq (add_mul ..).symm)
 simp only [add_apply,inner_add_right]; exact (x.analytic p q).add (y.analytic p q)
-- omit variable shadower
omit y in
lemma Port.raise (t:ℂ): Port S L r (fun z=> t • X z) (t • A) v (‖t‖₊*c):=by
 refine ⟨?_,fun p q=>?_,fun z h=>?_,fun p q=>?_,fun z e f=> by rw [x.left _ e f,Algebra.mul_smul_comm],fun z e f=> by rw [x.right _ e f,Algebra.smul_mul_assoc]⟩
 · rw [norm_smul]; exact mul_le_mul_of_nonneg_left x.order (norm_nonneg _)
 · simp only [smul_apply,inner_smul_right]; exact continuousOn_const.mul (x.guard p q)
 · rw [norm_smul]; exact (mul_le_mul_of_nonneg_left (x.toll z h) (norm_nonneg t)).trans_eq (mul_assoc ..).symm
 simp only [smul_apply,inner_smul_right]; exact analyticOnNhd_const.mul (x.analytic p q)
omit x y
lemma Port.tend {X:ℂ→H.Op} (p:Port S L r X A v c)(u:c ≤ d) : Port S L r X A v d:= ⟨p.order.trans u,p.guard,fun z k=>(p.toll z k).trans (mul_le_mul_of_nonneg_right (show (c:ℝ)≤ (d:ℝ) from u) (norm_nonneg _)),p.analytic,p.left,p.right⟩
lemma Script.port {M:Set H.Op} (v1:∀ A∈ M,∀ t:ℝ, |t|≤r → Commute A (LorTime S t L))(u : Script S M A w d) : ∃ X, Port S L r X A w d := by
 induction u with
 | weather c => exact ⟨_,storm_port ..⟩
 | now A t p e=> exact ⟨_,instant _ _ _ t e (v1 A p)⟩
 | link _ _ ih h=> exact ⟨_,welding ih.choose_spec h.choose_spec⟩
 | plus _ _ ih h=> exact ⟨_,Port.creates ih.choose_spec h.choose_spec⟩
 | scale _ t ih=> exact ⟨_, Port.raise ih.choose_spec t⟩
 | charge _ t ih=> exact ⟨_,Port.tend ih.choose_spec t⟩
end YM.Lens
