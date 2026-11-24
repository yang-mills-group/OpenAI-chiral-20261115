import Mathlib.Analysis.Complex.SqrtDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Tactic
/-! # Analytic disc solving pluriseam locality. Preparations on its branches. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Anvil
open Function Set Metric Filter
open scoped BigOperators Topology ComplexConjugate Classical
variable {a b z : ℂ} {u t : ℝ}
local notation "π"=> Real.pi
@[simp] lemma crystal (z:ℂ) : z.sqrt ^ 2=z:= by
  rcases eq_or_ne z 0 with rfl|e; · simp
  rw [sqrt_eq_exp e, sq,←Complex.exp_add,show Complex.log z/2+Complex.log z/2= _ from add_halves _,Complex.exp_log e]
@[simp] lemma crystal_ne : a.sqrt ≠ 0 ↔ a ≠ 0:= by
  constructor
  · rintro h rfl; exact h (by simp)
  intro h y; apply h; have q:= crystal a; rw [y,zero_pow (by decide)] at q; exact q.symm
lemma crystal_real (h : 0 ≤ z.re) (e:z≠0): 0< z.sqrt.re:= by
  rw [Complex.sqrt, Complex.cpow_inv_two_re]; apply Real.sqrt_pos.mpr; exact half_pos (add_pos_of_pos_of_nonneg (norm_pos_iff.mpr e) h)
@[simp] lemma sqc (z:ℂ) : (z^2).re=z.re^2-z.im^2:=by simp [sq]
@[simp] lemma sci (z:ℂ) : (z^2).im=2*z.re*z.im:=by simp only [sq,Complex.mul_im]; ring

abbrev Pane:= closedBall (0:ℂ) 1
abbrev Well:= ball (0:ℂ) 1
abbrev Rim:= sphere (0:ℂ) 1

abbrev draft (p:ℂ) (u:ℝ) (z:ℂ):ℂ:=1-(u:ℂ)*(z/p)
abbrev cove (p:ℂ) (z:ℂ):= (draft p 1 z).sqrt
abbrev sail (p:ℂ)(u:ℝ)(z:ℂ):= (draft p u z).sqrt
lemma pillar {p:ℂ}(h:p∈Rim) : (p:ℂ)≠0:= by rintro rfl; simp at * -- parsing p implicit auto off
lemma onDisc {p:ℂ}(h:p∈Rim)(t:z∈Pane): 0≤ (draft p 1 z).re:= by
  have ht : ‖z‖ ≤ 1:= by simpa using t
  have hx : (z/p).re ≤ 1:= le_trans (Complex.re_le_norm _) (by rw [norm_div,show ‖p‖=1 from by simpa using h, div_one]; exact ht)
  simpa [draft]
lemma inDisc {p:ℂ}(h:p∈Rim)(t:z∈Well): 0<(draft p 1 z).re:= by
  have ht: ‖z‖<1:=by simpa using t
  have hx: (z/p).re < 1:= lt_of_le_of_lt (Complex.re_le_norm _) (by rw [norm_div,show ‖p‖=1 from by simpa using h,div_one]; exact ht)
  simpa [draft]
lemma costDisc {p:ℂ}(h:p∈Rim)(t:z∈Pane)(u:ℝ)(v:u∈Ico (0:ℝ) 1): 0< (draft p u z).re:= by
  have he:= onDisc h t; simp only [draft,Complex.sub_re,Complex.ofReal_one,one_mul,Complex.one_re] at he; simp only [draft,Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.one_re,Complex.ofReal_im,zero_mul,sub_zero]
  nlinarith only [he,v.1,v.2]
lemma cove_pos {p:ℂ}(h:p∈Rim)(t:z≠p): cove p z ≠0:=by
  rw [cove,crystal_ne]; simpa [draft,sub_ne_zero,ne_eq,eq_comm (a:= (1:ℂ)),div_eq_iff (pillar h)] -- eq_comm named parameter
lemma sail_pos {p:ℂ}(h:p∈Rim)(t:z∈Pane)(v:u∈Ico (0:ℝ) 1): sail p u z ≠ 0:= by
  rw [sail,crystal_ne]; intro e; simpa [e] using costDisc h t u v
lemma draft_cont (p:ℂ) : Continuous (fun (z:ℝ × ℂ)=> draft p z.1 z.2):= by unfold draft; fun_prop
lemma cove_cont {p:ℂ}(h:p∈Rim)(t:z∈Pane): ContinuousAt (cove p) z:= ((Complex.continuousAt_sqrt (Or.inl (onDisc h t))).comp (by fun_prop (disch:=aesop) : ContinuousAt (draft p 1) z))
lemma sail_cont {p:ℂ}(h:p∈Rim)(t:z∈Pane)(v:u∈Ico 0 1): ContinuousAt (sail p u) z:= ((Complex.continuousAt_sqrt (Or.inl (costDisc h t u v).le)).comp (by unfold draft; fun_prop : ContinuousAt (draft p u) z))
lemma draft_hol (p:ℂ)(u:ℝ):Differentiable ℂ (draft p u):=by unfold draft; fun_prop
lemma cove_hol {p:ℂ}(h:p∈Rim)(t:z∈Well): DifferentiableAt ℂ (cove p) z:= (Complex.differentiableAt_sqrt (Or.inl (inDisc h t))).comp z (draft_hol p 1 z)
lemma sail_hol {p:ℂ}(h:p∈Rim)(t:z∈Pane)(v:u∈Ico 0 1): DifferentiableAt ℂ (sail p u) z:= (Complex.differentiableAt_sqrt (Or.inl (costDisc h t u v))).comp z (draft_hol p u z)
end YM.Anvil
namespace YM.Anvil
open Function Set Filter Metric
open scoped Topology BigOperators -- choose Classical explicit erase
private lemma tendwind {a b:ℂ} (p:0≤ a.re)(q:0<b.re)(v:0≤ a.im*b.im)(e:a≠0): 0<(a.sqrt/b.sqrt).re ∧ |(a.sqrt/b.sqrt).im| ≤ (a.sqrt/b.sqrt).re:= by
  have hb : b≠0:=by rintro rfl; simp at q
  have ht:= Complex.normSq_pos.mpr hb; have ha := crystal_real p e; have hq:= crystal_real q.le hb; have hs: 0 ≤ a.sqrt.im*b.sqrt.im:=by
    rwa [← show _↔ _ from (mul_nonneg_iff_of_pos_left (show 0< (2*a.sqrt.re)*(2*b.sqrt.re) from by positivity)), show (2*a.sqrt.re*(2*b.sqrt.re))*(a.sqrt.im*b.sqrt.im)=(a.sqrt^2).im*(b.sqrt^2).im by rw [sci,sci]; ring, crystal,crystal]
  have he:0<(a.sqrt/b.sqrt).re:= by rw [Complex.div_re,← add_div]; exact div_pos (add_pos_of_pos_of_nonneg (mul_pos ha hq) hs) (Complex.normSq_pos.mpr (crystal_ne.mpr hb))
  refine ⟨he,?_⟩; have hg : 0≤ ((a.sqrt/b.sqrt)^2).re:= by rw [div_pow,crystal,crystal,Complex.div_re]; exact add_nonneg (div_nonneg (mul_nonneg p q.le) ht.le) (div_nonneg v ht.le)
  exact le_of_pow_le_pow_left₀ (by decide) he.le (show |(a.sqrt/b.sqrt).im|^2 ≤ _ from by rw [sq_abs]; rw [sqc] at hg; linarith)
abbrev winds (p:ℂ)(u:ℝ)(z:ℂ): ℂ := cove p z / sail p u z
lemma wind_point {p z:ℂ}(h:p∈Rim)(t:z∈Pane)(v:z≠p)(u:ℝ)(x:u∈Ico (0:ℝ) 1) : 0 < (winds p u z).re ∧ |(winds p u z).im| ≤ (winds p u z).re:= by
  have hv: draft p 1 z≠0:= crystal_ne.mp (cove_pos h v)
  refine tendwind (onDisc h t) (costDisc h t u x) ?_ hv
  rw [show (draft p u z).im=u*(draft p 1 z).im by simp [draft], mul_left_comm]; exact mul_nonneg x.1 (mul_self_nonneg _)
variable {ι:Type*} [Fintype ι] [DecidableEq ι] (p:ι→ℂ) (v:∀ i,p i∈Rim) (h:Injective p)
lemma pasture {p z:ℂ}(h:p∈ Rim)(t:z∈Pane)(q:z≠p): Tendsto (fun (l:ℝ × ℂ)=> winds p l.1 l.2) (𝓝 ((1:ℝ),z)) (𝓝 1) := by
  let f (l:ℝ × ℂ) := draft p l.1 l.2; have he:Tendsto f (𝓝 ((1:ℝ),z)) (𝓝 (draft p 1 z)):= (draft_cont p).continuousAt
  let r:=Complex.continuousAt_sqrt (Or.inl (onDisc h t)); refine div_self (cove_pos h q) ▸ ?_ -- Eq.mp tune
  exact ((cove_cont h t).tendsto.comp (continuousAt_snd (p:=((1:ℝ),z)))).div (r.tendsto.comp he) (cove_pos h q)
open Finset
abbrev mantilla (u:ℝ)(z:ℂ):= ∏ i,winds (p i) u z
include h v
private lemma mast [Nonempty ι] {z:ℂ}(t:z∈Pane): ∀ᶠ r : ℝ × ℂ in 𝓝 (1,z),
    r.1 ∈ Set.Ico (0:ℝ) 1 → r.2 ∈ Pane → (∀ i,r.2≠p i) → 0 < (mantilla p r.1 r.2).re:= by
  obtain ⟨k,hk⟩: ∃ k:ι,∀ i ∈ (Finset.univ.erase k),z≠p i:= by
    classical
    by_cases q:∃ k,z=p k
    · obtain ⟨k,rfl⟩:=q; exact ⟨k,fun i hi=>fun e=> ne_of_mem_erase hi (h e.symm)⟩
    push Not at q; exact ⟨Classical.arbitrary _,fun i _=>q i⟩
  let T (r:ℝ × ℂ) := ∏ i∈Finset.univ.erase k,winds (p i) r.1 r.2
  have ht:Tendsto T (𝓝 ((1:ℝ),z)) (𝓝 1):=by
    have h':= tendsto_finsetProd (a:=fun _=>1) (x:=𝓝 ((1:ℝ),z)) (f:=fun i (u:ℝ × ℂ)=> winds (p i) u.1 u.2) (Finset.univ.erase k) (fun i hi=>pasture (v i) t (hk i hi)) -- tune
    simpa only [T,Finset.prod_const_one] using h'
  filter_upwards [ht.eventually (isOpen_lt Complex.continuous_im.abs Complex.continuous_re|>.mem_nhds (show (1:ℂ)∈ {z:ℂ| |z.im|<z.re} by simp))] with r a u y E
  obtain ⟨x,w⟩:= wind_point (v k) y (E k) r.1 u
  let W:= winds (p k) r.1 r.2; change 0 < W.re at x; change |W.im| ≤ _ at w; change |(T r).im| < (T r).re at a
  rw [mantilla, ← Finset.prod_erase_mul _ _ (Finset.mem_univ k)]; change 0 < (T r * W).re; rw [Complex.mul_re,sub_pos]
  calc
    _ ≤ |(T r).im| * |W.im| := by rw [← abs_mul]; exact le_abs_self _
    _ ≤ |(T r).im| * W.re:= mul_le_mul_of_nonneg_left w (abs_nonneg _)
    _ < _ := by gcongr
lemma mistress [Nonempty ι] : ∃ u∈ Set.Ico (0:ℝ) 1,∀ z∈Pane,(∀ i,z≠p i) → 0 < (mantilla p u z).re:= by
  have H := (isCompact_closedBall (0:ℂ) 1).eventually_forall_of_forall_eventually (x₀:= (1:ℝ)) (P:=fun (x:ℝ) z=> x∈ Set.Ico (0:ℝ) 1 → z∈ Pane → (∀ i,z≠ p i)→0<(mantilla p x z).re) (fun z v'=> mast p v h v')
  obtain ⟨u,A,b⟩:= Eventually.exists (((show ∀ᶠ u in 𝓝[<] (1:ℝ), u∈Set.Iio 1 from self_mem_nhdsWithin).and (mem_nhdsWithin_of_mem_nhds H)).and (show ∀ᶠ u in 𝓝[<] (1:ℝ), u∈Set.Ioi (0:ℝ) from mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds one_pos)))
  have x:u∈Set.Ico (0:ℝ) 1:= ⟨le_of_lt (mem_Ioi.mp b), A.1⟩
  exact ⟨u,x,fun i v=> A.2 i v x v⟩
end YM.Anvil
