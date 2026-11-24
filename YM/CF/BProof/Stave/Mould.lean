import YM.CF.BProof.Stave.Iso
import YM.CF.Mesa.Value
import YM.CF.BProof.Extension.SU
/-! On dim ≤3 (all the needed frames adjacent to bad-only faces), extend AMBIENT reps
within ε of St classes. This simplifies Lemma FD away from the good subcomplex, sufficing
for every Guard requirement. Plaquette bounds use that closeness separately. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Mesh.Stave
open Function Filter Topology Set NormedSpace Metric Extension
open scoped Matrix Matrix.Norms.Frobenius Topology BigOperators NNReal ComplexConjugate Classical
variable {I J K:Type*}[Fintype I][Fintype J][Fintype K]

-- frustum: formula via product with ℝ and Extension.normalizeLip!
private lemma frustum {X:Type*}[NormedAddCommGroup X][NormedSpace ℝ X](d:ℝ)(h:0<d):
    ∃ F:X→X,LipschitzWith 2 F ∧ (∀ x,‖F x‖≤d) ∧ ∀ x,‖x‖≤d→ F x=x:=by
 let A(x:X):= (x,d); let Y(x:X): X:= d • (‖A x‖⁻¹ • A x).1
 have hm(x:X):‖A x‖=max ‖x‖ d:=by simp [Prod.norm_def,A,Real.norm_of_nonneg h.le]
 have hz(x:X): d ≤ ‖A x‖:=by rw [hm]; exact le_max_right ..
 have hw(x:X): ‖‖A x‖⁻¹ • A x‖=1:=by rw [norm_smul,Real.norm_of_nonneg (by positivity),inv_mul_cancel₀ (h.trans_le (hz x)).ne']
 have hl:Lip univ 1 A:= fun x hx y hy=> by simp [A,← dist_eq_norm]
 refine ⟨Y,LipschitzWith.of_dist_le_mul (fun x y=>?_ ),fun x=> ?_,fun x hx=>?_⟩
 · unfold Y; rw [dist_eq_norm,←smul_sub,norm_smul,Real.norm_of_nonneg h.le]; push_cast; apply le_trans (mul_le_mul_of_nonneg_left (le_trans (norm_fst_le ..) (normalizeLip hl h (fun x _=>hz x) x (mem_univ _) y (mem_univ _))) h.le) (le_of_eq (by field_simp))
 · unfold Y; rw [norm_smul,Real.norm_of_nonneg h.le]; exact mul_le_of_le_one_right h.le ((norm_fst_le ..).trans_eq (hw x))
 unfold Y; rw [hm,max_eq_right hx]; simp [A,h.ne']

variable {X:Type*}[PseudoMetricSpace X]{s:Set X}
abbrev Tame (s:Set X){E:Type*}[PseudoMetricSpace E](f:X→E):=∃ K, LipschitzOnWith K f s
lemma Tame.li {E:Type*}[PseudoMetricSpace E]{f:X→ E} (h:Tame s f): LipschitzOnWith h.choose f s:=h.choose_spec
lemma monk {E:Type*}[SeminormedAddCommGroup E]{f:X→ E}{u:ℝ}(h:0≤u)(g:Lip s u f): Tame s f:=⟨⟨u,h⟩,(lip_iff ..).mp g⟩
lemma Tame.vein {E:Type*}[SeminormedAddCommGroup E]{f:X→ E}(h:Tame s f): Lip s h.choose f:=(lip_iff ..).mpr h.li
lemma Tame.subset {E:Type*}[PseudoMetricSpace E]{f:X→ E}{t:Set X}(h:Tame s f)(u:t ⊆ s): Tame t f:=⟨_,h.li.mono u⟩
lemma Tame.copy {E:Type*}[PseudoMetricSpace E]{f g:X→ E}(h:Tame s f)(e:EqOn f g s): Tame s g:=by
 refine ⟨h.choose,LipschitzOnWith.of_dist_le_mul (fun x hx y hy=>?_)⟩; rw [← e hx, ← e hy]; exact h.li.dist_le_mul x hx y hy
lemma Tame.boundary {E:Type*}[PseudoMetricSpace E]{Y:Type*}[PseudoMetricSpace Y]{t:Set E}{F:E→Y}{f:X→ E}(h:Tame s f)(g:Tame t F)(e:MapsTo f s t): Tame s (F ∘ f):=⟨_,g.li.comp h.li e⟩

lemma weak_fill {Y:Type*}[NormedAddCommGroup Y][NormedSpace ℝ Y][FiniteDimensional ℝ Y]{s:Set X}{A:Y}{d:ℝ}{B:X→Y}(h:0<d)(g:Tame s B)(e:∀ x∈s,‖B x-A‖≤ d): ∃ F:X→ Y,Tame univ F∧EqOn B F s∧∀ x,‖F x-A‖≤d:=by
 obtain ⟨F,hF,w⟩:=g.li.extend_finite_dimension; obtain ⟨q,hq,hQ,Q⟩:= frustum (X:=Y) d h
 exact ⟨fun x=> q (F x-A)+A,⟨_,((hq.comp (hF.sub (LipschitzWith.const A))).add (LipschitzWith.const A)).lipschitzOnWith⟩,fun x hx=> by dsimp only; rw [← w hx,Q _ (e x hx),sub_add_cancel],fun x=> by dsimp only; rw [add_sub_cancel_right]; exact hQ _⟩
lemma Tame.rollZ {f:X→plate I}{g:X→ SU.E}{d:ℝ}(hf:Tame s f)(hg:Tame s (SU.fund ∘ g)) (h:0≤d)(p:∀ x∈s,‖f x‖≤ d):Tame s (fun x=> roll (f x) (g x)):=by
 refine monk (show 0≤ (hf.choose:ℝ)+d*(hg.choose:ℝ) by positivity) (fun x hx y hy=>?_)
 rw [← dist_eq_norm]; apply (dist_triangle _ (roll (f y) (g x)) _).trans; rw [roll_dist,dist_eq_norm (roll (f y) (g x)),roll,roll,← Matrix.mul_sub,add_mul,mul_assoc]; apply add_le_add (hf.li.dist_le_mul x hx y hy)
 exact (Matrix.frobenius_norm_mul ..).trans (mul_le_mul (p y hy) (hg.vein x hx y hy) (norm_nonneg _) h)
lemma foyer (A:plate I){f:X→plate I}(hf:Tame s f):Tame s (fun x=> Aᴴ*f x):= by
 refine monk (show 0≤ ‖A‖*(hf.choose:ℝ) by positivity) (fun x hx y hy=>?_)
 rw [← Matrix.mul_sub,mul_assoc,← size_HH A] -- size_HH will rewrite A?
 exact (Matrix.frobenius_norm_mul ..).trans (mul_le_mul_of_nonneg_left (hf.vein x hx y hy) (norm_nonneg _))

def podium(A:plate I)(B:plate I):SU.E:= Mesa.nick SU.group (Aᴴ*B)
lemma proj_price{d:ℝ}{A B:plate I}(p:A∈ King I) (g:Like d A B):∃ u, dist (roll A u) B≤ d∧ dist (Aᴴ*B) (SU.fund u) ≤ 3*d:=by
 obtain ⟨u,h⟩:=g; refine ⟨u,h,?_⟩; rw [dist_comm,dist_eq_norm] at h; rw [dist_eq_norm, show SU.fund u=Aᴴ*roll A u from by rw [roll, ← Matrix.mul_assoc, show Aᴴ*A=1 from p,Matrix.one_mul],← Matrix.mul_sub]; exact (Matrix.frobenius_norm_mul ..).trans (mul_le_mul ((size_HH ..).trans_le (king_le p)) h (norm_nonneg _) (by norm_num))
lemma podium_meets{d:ℝ}{A B:plate I}(p:A∈ King I)(g:Like d A B): dist (roll A (podium A B)) B≤ 7*d:=by
 obtain ⟨u,h,q⟩:= proj_price p g; let P:=podium A B
 have hv:= (SU.group.nearest_exists (Aᴴ*B)).choose_spec u
 change ‖Aᴴ*B-SU.fund P‖ ≤ ‖Aᴴ*B-SU.fund u‖ at hv
 simp_rw [←dist_eq_norm] at hv
 apply (dist_triangle _ (roll A u) _).trans
 change dist (A*SU.fund P) _+_≤_; rw [roll,dist_eq_norm, ← Matrix.mul_sub,size_mul (show Aᴴ*A=1 from p),← dist_eq_norm]
 have hp:=dist_triangle_left (SU.fund P) (SU.fund u) (Aᴴ*B) -- check
 unfold roll at h
 linarith
lemma lift_price{u:ℝ} {s:Set X} {A:plate I} {f:X→plate I}(hf:Tame s f)(p:A∈ King I)(e:∀ x∈s,Like u A (f x)) {L:ℝ≥0}{r:ℝ}(h:3*u<r)(g:LipschitzOnWith L (SU.group.mat ∘ Mesa.nick SU.group) (⋃ v,ball (SU.group.mat v) r)): Tame s (fun x=> SU.fund (podium A (f x))):= by
 have H:MapsTo (fun x=> Aᴴ*f x) s (⋃ v:SU.E,ball (SU.fund v) r):=by
    intro x hx; obtain ⟨u,_,q⟩:= proj_price p (e x hx); exact mem_iUnion.mpr ⟨u,q.trans_lt h⟩
 exact ⟨_,(show LipschitzOnWith L (fun B:plate (Fin 5)=> SU.fund (Mesa.nick SU.group B)) _ from g).comp (foyer A hf).li H⟩ -- tune defeq elaborator
end YM.CF.BProof.Mesh.Stave
