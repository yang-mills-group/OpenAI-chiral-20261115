import Velour.Crepe.Prate
/-! Calculus of bounded strong star. -/
set_option autoImplicit false
set_option maxRecDepth 2000
noncomputable section
namespace YM.Velour.Gleams
open Function TopologicalSpace Filter Set Metric
open scoped Topology InnerProductSpace BigOperators NNReal ComplexConjugate

variable {H:Hilbert} {f g:ℕ→H.Op}{x y:H.Op}

lemma norm_paid (h:Gleams H f x) {B:ℝ} (w:∀ᶠ i in atTop, ‖f i‖ ≤ B): ‖x‖ ≤B:=by
 obtain ⟨i,q⟩:= w.exists
 refine ContinuousLinearMap.opNorm_le_bound _ ((norm_nonneg _).trans q)
       fun v=>le_of_tendsto (h.gaze v).norm (w.mono fun i k=>?_ )
 exact (f i|>.le_opNorm v).trans (mul_le_mul_of_nonneg_right k (norm_nonneg _))
lemma unique (h:Gleams H f x)(k:Gleams H f y):x=y:=
 ContinuousLinearMap.ext fun v=>tendsto_nhds_unique (h.gaze v) (k.gaze v)
lemma agree (h:Gleams H f x)(e:f=ᶠ[atTop] g): Gleams H g x:=by
 obtain ⟨B,p⟩:= h.bought
 refine ⟨⟨B,(p.and e).mono ?_⟩,
    fun v=>(h.gaze v).congr' (e.mono fun i z=>by rw [z]),
    fun v=>(h.turn v).congr' (e.mono fun i z=>by rw [z])⟩
 intro i y; exact y.2 ▸ y.1


lemma tightly (t:Tendsto f atTop (𝓝 x)): Gleams H f x:=by
 refine ⟨⟨‖x‖+1, t.norm.eventually_le_const (lt_add_one _)⟩,?_,?_⟩
 · exact fun y=>((ContinuousLinearMap.apply ℂ H y).continuous.tendsto _).comp t
 exact fun y=>((ContinuousLinearMap.apply ℂ H y).continuous.tendsto _).comp t.star
lemma const (x:H.Op): Gleams H (fun _=>x) x:= tightly tendsto_const_nhds

lemma swap (h:Gleams H f x): Gleams H (fun i=>star (f i)) (star x):=by
 refine ⟨by simpa only [norm_star] using h.bought, h.turn, ?_⟩
 simp only [star_star]; exact h.gaze
lemma both {v:ℕ→H}{w:H}(h:Gleams H f x)(p:Tendsto v atTop (𝓝 w)):
   Tendsto (fun i=>f i (v i)) atTop (𝓝 (x w)):=by
 obtain ⟨B,b⟩:=h.bought
 have g: Tendsto (fun i=>f i (v i-w)) atTop (𝓝 0):=by
    apply squeeze_zero_norm' (b.mono fun i t=>(f i|>.le_opNorm _).trans (mul_le_mul_of_nonneg_right t (norm_nonneg _)))
    simpa using ((p.sub (tendsto_const_nhds (x:=w))).norm).const_mul B
 simpa using g.add (h.gaze w)


lemma mul(h:Gleams H f x)(k:Gleams H g y): Gleams H (fun i=> f i * g i) (x*y):=by
 obtain ⟨B,p⟩:=h.bought; obtain ⟨C,q⟩:=k.bought
 have e:(0:ℝ)≤B:= (norm_nonneg _).trans p.exists.choose_spec
 refine ⟨⟨B*C,(p.and q).mono fun i b=>le_trans (norm_mul_le ..)
      (mul_le_mul b.1 b.2 (norm_nonneg _) e)⟩,
      fun v=> h.both (k.gaze v), fun v=>?_⟩
 simp only [star_mul]; exact k.swap.both (h.turn v)
lemma add(h:Gleams H f x)(k:Gleams H g y): Gleams H (fun i=>f i + g i) (x+y):=by
 obtain ⟨B,p⟩:=h.bought; obtain ⟨C,q⟩:=k.bought
 refine ⟨⟨B+C,(p.and q).mono fun i b=>le_trans (norm_add_le ..)
      (add_le_add b.1 b.2)⟩,
      fun v=> (h.gaze v).add (k.gaze v), fun v=>?_⟩
 simp only [star_add]; exact (h.turn v).add (k.turn v)


lemma smul {a:ℕ→ℂ}{b:ℂ}(h:Gleams H f x)(k:Tendsto a atTop (𝓝 b)):
    Gleams H (fun i=> a i • f i) (b • x):=by
 obtain ⟨B,p⟩:=h.bought
 let C:=‖b‖+1; have q:∀ᶠ i in atTop, ‖a i‖ ≤ C:=k.norm.eventually_le_const (lt_add_one _); have e:= (norm_nonneg _).trans q.exists.choose_spec
 refine ⟨⟨C*B,(q.and p).mono fun i s=>(norm_smul _ _).trans_le (mul_le_mul s.1 s.2 (norm_nonneg _) e)⟩,
    fun v=>k.smul (h.gaze v),fun v=>?_⟩
 simp only [star_smul]; exact k.star.smul (h.turn v)

variable {j:Axis}
lemma warm (S:OS.Semigroup H j){a:ℕ→ℝ≥0}{b:ℝ≥0}(p:Tendsto a atTop (𝓝 b)):
    Gleams H (fun i=>S.E (a i)) (S.E b):=by
 have e(t:ℝ≥0):star (S.E t)=S.E t:=S.sym _
 refine ⟨⟨1,Eventually.of_forall fun i=>S.shrinks _⟩,
       fun v=>((S.continuousE v).tendsto b).comp p,fun v=>?_⟩
 simp only [e]
 exact ((S.continuousE v).tendsto b).comp p

lemma pad (h:Gleams H f x)(S:OS.Semigroup H j){a b:ℕ→ℝ}{r t:ℝ}
     (p:Tendsto a atTop (𝓝 r))(q:Tendsto b atTop (𝓝 t)):
     Gleams H (fun i=>S.pad (a i) (b i) (f i)) (S.pad r t x):=
 ((warm S ((continuous_real_toNNReal.tendsto r).comp p)).mul h).mul (warm S ((continuous_real_toNNReal.tendsto t).comp q))

lemma wrap (h:Gleams H f x)(S:OS.Semigroup H j)(a b:ℝ):
   Gleams H (fun i=> S.pad a b (f i)) (S.pad a b x):=
 h.pad S tendsto_const_nhds tendsto_const_nhds
end YM.Velour.Gleams


