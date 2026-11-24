import YM.CF.Summit.Wharf
set_option autoImplicit false
noncomputable section
namespace YM.CF.Summit
open Function Filter Set Matrix MeasureTheory FreeResolvent TestD AnalyticBridge.RelativeLogdet Differential
open Next.SectorChange.Schur (principal)
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {ι κ X E τ : Type}[Fintype ι][Fintype κ][DecidableEq ι][NormedAddCommGroup E][NormedSpace ℝ E]
 {W:Mark τ X}{D:Cost X}{v:τ→E}{p:ι→ X}{q:κ→ X}{x:E}{A:E→Square ι}{H: E×ℝ→ Matrix ι κ ℝ}{α σ r C d u Y N:ℝ}{n:ℕ}
lemma span_gap (p:Gap (A x) r)(h:0 ≤ r)(w:ℝ): Gap (spanX (A x) w) (min r 1/2):=by -- min r 1/2 def ((min _)/2)
 let t:=min r 1; have he:0≤t:=le_min h zero_le_one; refine ⟨fun v =>?_⟩
 unfold spanX; rw [add_mulVec,smul_mulVec,smul_mulVec,one_mulVec,dotProduct_add,dotProduct_smul,dotProduct_smul,smul_eq_mul,smul_eq_mul]; let k:=v ⬝ᵥ v; have hk:0≤k:= normSum_nn v
 calc
    _ ≤ (1-w)^2 * (t*k)+ w^2*(t*k) := by nlinarith only [mul_nonneg (mul_nonneg he hk) (sq_nonneg (w-1/2))]
    _ ≤ _ := by
        exact add_le_add (mul_le_mul_of_nonneg_left ((p.mono (min_le_left r 1)).lower v) (sq_nonneg _)) (mul_le_mul_of_nonneg_left (mul_le_of_le_one_left hk (min_le_right r 1)) (sq_nonneg _))
lemma one_r : Bundle v W D p p (fun _ : E=> (1:Square ι)) x n σ 1:=by
 refine ⟨contDiffAt_const,fun l h=>?_⟩; by_cases h:l=[]; · subst l; rw [zeroth]; exact Mark.Bill.origin W .one
 rw [jet_const v l h]; exact .zero zero_le_one
lemma span_pay (k:Bundle v W D p p A x n σ C)(h:0≤C){w:ℝ}(p':w∈ Isle): Bundle v W D p p (fun y=>spanX (A y) w) x n σ (C+1):=by
 refine ((k.scale ((1-w)^2)).one_add ((one_r (x:=x) (v:=v) (p:=p)).scale (w^2))).mono le_rfl ?_
 rw [abs_of_nonneg (sq_nonneg _), abs_of_nonneg (sq_nonneg _),mul_one]; apply add_le_add
 · refine mul_le_of_le_one_left h (pow_le_one₀ (sub_nonneg.mpr p'.2) (by have := p'.1; linarith))
 exact pow_le_one₀ p'.1 p'.2
section window
variable {I:ι→ Set ι}{hI:∀ i, i∈ I i}
lemma pie_s (H: E × ℝ → Square ι)(k:Ink.Arc H n x)(hI:∀ i,i∈ I i)(h:∀ t∈Isle, Gap (H (x,t)) r)(p:0<r): Ink.Arc (fun z=> pie I (H z) 0) n x:=by
 intro t ht; apply rectangle_smooth; intro i j
 by_cases hi:i∈I j; swap
 · simp_rw [pie_miss _ _ _ _ _ hi]; exact contDiffAt_const
 simp_rw [pie_read _ _ _ _ _ hi (hI _),resolve,zero_smul,add_zero]
 exact typed (reflected ((selectL (Subtype.val : I j→ι)).contDiff.contDiffAt.comp _ (k t ht)) (((h _ ht).submatrix _ Subtype.val_injective).unit_det p)) (⟨i,hi⟩) (⟨j,hI _⟩)
lemma pole_paid (k:Bundle v W D p p A x n σ C)(p':Gap (A x) r)(p1:0<r)(p2:0 ≤ C)(p3:Price σ (C+1) (min r 1/2) d u Y 1 n)(h: D.Volume p d Y)(ht:W.Move D d u)(hI:∀ i,i∈ I i)(hy:(study I hI).Near D p N):
 let K(y:E)(w:ℝ):=spanX (A y) w
 let R:= meter n n (C+1) u (rise Y (min r 1/2)); let e:=Real.exp (-(n+1:ℕ)*d*N)
 ∀ w∈Isle, Bundle v W D p p (fun y=>(K y w)⁻¹) x n d R ∧ Bundle v W D p p (fun y=>pie I (K y w) 0 - (K y w)⁻¹) x n d (e* tagPrice u n R (tagPrice u n (C+1) (Y*R))):=by
 intro K R e w p0; let B:=fun y=>K y w; have hv := span_pay k p2 p0
 have hk: Knew W D p v x n σ (C+1) (min r 1/2) 1 B:=⟨hv.smooth,span_gap p' p1.le w,recovered hv, by rw [mul_one]; exact fun l _ z=>hv.bound l z⟩
 have hB:= hk.volume_price p3 (u:=0) le_rfl ht h
 have he:= hk.discrepancy p3 (u:=0) le_rfl ht h hy
 have hp : drain 0=1:= by simp [drain]
 have hh: action B 0=fun y => (K y w)⁻¹:= funext fun y=>by simp only [action, resolve, zero_smul,add_zero]; rfl
 rw [hp,hh,mul_one] at hB; dsimp only at he; rw [hp,hh,mul_one] at he
 have hs:d ≤ 4*(n+1:ℕ)*d:=by rw [mul_assoc]; apply le_trans ?_ (le_mul_of_one_le_left (by have:=p3.pos; positivity) (by norm_num)); exact le_mul_of_one_le_left p3.pos.le (by simp)
 refine ⟨hB.mono hs le_rfl,?_⟩
 rw [show (fun y : E=> pie I (K y w) 0-(K y w)⁻¹)=glimpse (study I hI) B 0 - fun y=>(K y w)⁻¹ from funext fun y=> congrArg (·-(K y w)⁻¹) (pie_inspects _ _ _ hI)]
 exact he.mono le_rfl (le_of_eq (by unfold R e tagPrice; ring))
end window
end YM.CF.Summit
