import YM.CF.Mesa.Portico
import YM.Gauge.Nearest
/-! Uniform filling: finite net of Lipschitz templates. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Mesa
open Function Set Filter Metric Matrix
open scoped Topology NNReal BigOperators InnerProductSpace Matrix.Norms.Frobenius
variable {G:Gauge}{d:ℕ}{E Y:Type*}[MetricSpace E][MetricSpace Y]
lemma quota_net {s:Set E}{t:Set Y} {I:Type*}(f:I→E→Y) {K:ℝ≥0}{r:ℝ}(hr:0<r)(h:IsCompact s)(w:IsCompact t)(g:∀ i,LipschitzOnWith K (f i) s)(v:∀ i,MapsTo (f i) s t):
    ∃ A:Finset I,∀ i,∃ j∈A,∀ x∈s, dist (f i x) (f j x)<r:=by
  classical
  let a:= r/(8*(K+1:ℝ)); have hp:0<a:=by unfold a; positivity
  obtain ⟨X,ht,hX,hk⟩:= finite_cover_balls_of_compact h hp
  obtain ⟨W,-,hW,hJ⟩:= finite_cover_balls_of_compact w (show 0<r/4 by positivity)
  choose b H hb using fun (i:I)(x:X)=> mem_iUnion₂.mp (hJ (v i (ht x.property)))
  let L (i:I)(x:X): W:= ⟨b i x,H i x⟩
  letI:= hX.fintype; letI:=hW.fintype
  choose u hu using fun y:range L=> y.property
  refine ⟨Finset.univ.image u,fun i=> ?_⟩
  let j:=u ⟨_,mem_range_self i⟩
  refine ⟨j,Finset.mem_image_of_mem u (Finset.mem_univ _),fun x hx=>?_⟩
  obtain ⟨y,hy,hyx⟩:= mem_iUnion₂.mp (hk hx)
  have ha:=g i|>.dist_le_mul _ hx y (ht hy); have hB:=g j|>.dist_le_mul _ hx y (ht hy)
  let z:X:=⟨y,hy⟩
  have he:b i z=b j z:= (congr_arg (fun w:X→W=>(w z).val) (hu ⟨_,mem_range_self i⟩)).symm
  have hc:=hb i z; have hD:=hb j z
  change dist (f i y) (b i z)<r/4 at hc; change dist (f j y) (b j z)<r/4 at hD
  rw [he] at hc; change dist x y < a at hyx
  have hs:a*(8*(K+1:ℝ))=r:=by unfold a; field_simp [K.coe_nonneg]
  have hQ: (K:ℝ)*dist x y ≤(K:ℝ)*a := mul_le_mul_of_nonneg_left hyx.le K.coe_nonneg
  have hP:=dist_triangle4_right (f i x) (f j x) (f i y) (f j y) -- check
  have hg:=dist_triangle_right (f i y) (f j y) (b j z)
  nlinarith

section
variable {E':Type*}[MetricSpace E']
lemma bolt (u v z:G.El): dist (G.mat (u*z)) (G.mat (v*z))= dist (G.mat u) (G.mat v) := by rw [dist_eq_norm,G.mat_mul,G.mat_mul,← sub_mul,Gauge.frob_mul_eq _ _ (G.mat_mul_star _),dist_eq_norm]
lemma bolt' (u v z:G.El): dist (G.mat (z*u)) (G.mat (z*v))= dist (G.mat u) (G.mat v) := by rw [dist_eq_norm,G.mat_mul,G.mat_mul,← mul_sub,Gauge.mul_frob_eq _ _ (G.mat_star_mul _),dist_eq_norm]
lemma bolt_inv (u v:G.El): dist (G.mat u⁻¹) (G.mat v⁻¹)= dist (G.mat u) (G.mat v):=by rw [← bolt u⁻¹ v⁻¹ u,← bolt' _ _ v]; simp [dist_comm]
lemma bolt_lip {A B:E'→G.El}{s:Set E'}{K L:ℝ≥0}(h:LipschitzOnWith K (G.mat ∘ A) s)(g:LipschitzOnWith L (G.mat ∘ B) s): LipschitzOnWith (K+L) (G.mat ∘ (A*B)) s := LipschitzOnWith.of_dist_le_mul (fun x hx y hy=>by
  simp only [Function.comp_apply, Pi.mul_apply]
  apply (dist_triangle _ (G.mat (A y*B x)) _).trans; rw [bolt,bolt',NNReal.coe_add,add_mul]; exact add_le_add (h.dist_le_mul _ hx _ hy) (g.dist_le_mul _ hx _ hy))
lemma bolt_back {A:E'→G.El}{s:Set E'}{K:ℝ≥0}(h:LipschitzOnWith K (G.mat ∘ A) s): LipschitzOnWith K (G.mat ∘ A⁻¹) s:= LipschitzOnWith.of_dist_le_mul (fun x hx y hy=>by simp only [Function.comp_apply,Pi.inv_apply, bolt_inv]; exact h.dist_le_mul _ hx _ hy)
lemma near_stone (G:Gauge)(d:ℕ)(K:ℝ≥0): ∃ r:ℝ, ∃ J,0<r∧∀ A:Board d→G.El,LipschitzOnWith K (G.mat ∘ A) (Peri _) →(∀ x∈Peri (Board d), ‖G.mat (A x)-1‖<r)→ ∃ U:Board d→G.El,LipschitzOnWith J (G.mat ∘ U) (terrace _) ∧ EqOn U A (Peri _):=by
  obtain ⟨L,t,hT,hl⟩:= (G.focus_diff.of_le (by exact le_top : (1:WithTop ℕ∞) ≤ (⊤:WithTop ℕ∞))).exists_lipschitzOnWith
  obtain ⟨r,hp,H⟩:=Metric.mem_nhds_iff.mp (inter_mem hT G.nearest_is_focus)
  let R:ℝ≥0:=⟨r,hp.le⟩
  refine ⟨r,L*(0+(2*K+R)),hp,fun A h hv=>?_⟩
  let S:=G.mat ∘ A; let f (x:Board d):= S x-1
  have hf : LipschitzOnWith K f (Peri _):=LipschitzOnWith.of_dist_le_mul (fun x hx y hy => by simp only [f,dist_sub_right]; exact h.dist_le_mul _ hx _ hy)
  have hg:=bristles (C:=R) (fun i hi=> (hv i hi).le) hf
  let B:=fun x=>1+brisk f x
  have ha (x) (hx:x∈terrace d): B x∈ ball 1 r:=by
    by_cases e:x=0
    · simp [B,brisk,e,hp]
    simp only [mem_ball,dist_eq_norm,B,brisk,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_norm]
    exact lt_of_le_of_lt ((mul_le_mul_of_nonneg_right (show ‖x‖≤1 by simpa using hx) (norm_nonneg _)).trans_eq (one_mul _)) (hv _ (pathX e))
  refine ⟨G.focus ∘ B,hl.comp (show LipschitzOnWith _ B _ from ((LipschitzWith.const _).add hg).lipschitzOnWith) (fun x hx=> (H (ha x hx)).1),fun x hx=>?_⟩
  have he : B x=G.mat (A x):=by simp [B,brisk,rocket,f,S, show ‖x‖=1 by simpa [Peri,mem_sphere] using hx]
  exact Eq.symm ((H (ha _ (peri_le hx))).2 (A x) (fun y=>by rw [he,sub_self,norm_zero]; positivity))
end
private lemma gm_fill (hd:d≤3)(f: Board d→SU.E)(h:Story (Peri (Board d)) (SU.group.mat ∘ f)):∃ F:Board d→SU.E,Story (terrace d) (SU.group.mat ∘ F) ∧ EqOn F f (Peri _) :=by
  obtain ⟨g,⟨K,hK⟩,he,hp⟩:= bowl hd 4 (SU.fund ∘ f) h (fun i _=>⟨SU.fund_U _,SU.fund_det _⟩); classical
  let F (x:Board d):SU.E:= if h:x∈terrace d then ⟨⟨g x,(hp x h).1⟩,(hp x h).2⟩ else 1
  have H (x) (hx:x∈terrace d) : SU.group.mat (F x)=g x:=by unfold F; rw [dif_pos hx]; rfl
  refine ⟨F,⟨K,LipschitzOnWith.of_dist_le_mul fun x hx y hy=>?_⟩,fun x hx=> SU.group.mat_injective ((H x (peri_le hx)).trans (he hx))⟩
  dsimp only [Function.comp_apply]; rw [H x hx,H y hy]; exact hK.dist_le_mul _ hx _ hy
lemma moment (hd:d≤3)(K:ℝ≥0): ∃ J,∀ A:Board d→SU.E, LipschitzOnWith K (SU.group.mat ∘ A) (Peri _)→∃ B:Board d→SU.E,LipschitzOnWith J (SU.group.mat ∘ B) (terrace d)∧EqOn B A (Peri _):=by
  let s:=Peri (Board d); let f:=SU.group.mat; classical
  let I:Type:= {A: Board d→SU.E // LipschitzOnWith K (f ∘ A) s}
  obtain ⟨r,J,hp,H⟩:=near_stone SU.group d (K+K)
  obtain ⟨X,hX⟩:=quota_net (fun i:I=> f ∘ i.val) hp (isCompact_sphere (0:Board d) 1) (isCompact_range SU.group.continuous_mat) (fun i=>i.property) (fun i k hk=> mem_range_self _)
  have Y (i:I):= gm_fill hd i.val ⟨K,i.property⟩; choose F h p using Y; unfold Story at h; choose k hF using h
  let T:= X.sup k
  refine ⟨J+T,fun A hA=>?_⟩
  obtain ⟨i,hi,hh⟩:= hX ⟨A,hA⟩
  obtain ⟨W,hW,hE⟩:= H (A*i.val⁻¹) (bolt_lip hA (bolt_back i.property)) (fun x hx=>by
    rw [Pi.mul_apply, Pi.inv_apply, ← SU.group.mat_one, ← mul_inv_cancel (i.val x), ← dist_eq_norm,bolt]
    exact hh _ hx)
  refine ⟨W * F i,LipschitzOnWith.weaken (bolt_lip hW (hF i)) (add_le_add_right (Finset.le_sup (f:=k) hi) _),fun x hx=>?_⟩
  simp [hE hx,p i hx]
end YM.CF.Mesa
