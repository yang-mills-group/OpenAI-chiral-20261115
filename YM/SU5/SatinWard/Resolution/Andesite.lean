import YM.SU5.Registration.Ink.Potential
import YM.SU5.SatinWard.Resolution.LimeWave
set_option maxHeartbeats 280000
set_option quotPrecheck false
noncomputable section
namespace YM.SatinWFixed.Andesite
open Function Filter MeasureTheory Set Complex Submodule SatinRegistration LimeWave
open Boundary Probe Mink OS OS.Semigroup SatinEdge.RealSheet Analysis
open CF.Buffered.Afterglow.Hierarchy.Seld
open scoped Topology BigOperators NNReal ENNReal InnerProductSpace ComplexOrder ContDiff Classical
variable {H:Hilbert}{ι:Type*}[Fintype ι](S:OS.Semigroup H timeAxis)(L:ι→ℝ→ℝ→ H.Op)(A:ι→ℕ→ℝ→ℝ→ H.Op) {ℓ:ℕ→ℝ} {z:ℕ}
local notation "Mark"=> (ι→ℂ)
variable (W:∀ i:ι,LimeWave.Post S ℓ (L i) (A i) z)
variable (Ω:H) (T:‖Ω‖=1) (δ:∀ e:E4, S.unit.translation e Ω=Ω) (h:∀ t, S.E t Ω=Ω)
def herald (i:ι) (r:ℂ): Mark:= Pi.single i r
@[simp] lemma herald_apply (i:ι)(r:ℂ) : herald i r i=r:= Pi.single_eq_same ..
@[simp] lemma herald_no {i j:ι}(h:j ≠ i)(r:ℂ) : herald i r j=0:= Pi.single_eq_of_ne h _
theorem herald_full (v:Mark): ∑ i:ι, herald i (v i)=v:=by ext1 i; simp_rw [Finset.sum_apply]; exact (Finset.sum_eq_single_of_mem i (Finset.mem_univ _) (fun a _ p=> herald_no (Ne.symm p) ..)).trans (herald_apply ..) -- ext maybe ℂ components
local notation "zE"=> (0:ℝ≥0)
-- Clip at zero when creating dictionary
def paint (p:ℝ≥0) (v:Mark): H.Op:= if 0<p then (∑ i, v i • (L i p p)) else 0
lemma at_herald (i:ι)(p:ℝ≥0)(u:0<p) (r:ℂ): paint L p (herald i r)= r • L i p p:=by
 unfold paint; rw [if_pos u, Finset.sum_eq_single i,herald_apply]; · intro j _ e; rw [herald_no e,zero_smul]
 intro e; exact (e (Finset.mem_univ _)).elim
lemma paint_add (p:ℝ≥0)(v w:Mark) : paint L p (v+w)= paint L p v+paint L p w:=by unfold paint; split <;> simp [*,add_smul,Finset.sum_add_distrib]
lemma paint_scale (p:ℝ≥0)(v:Mark)(t:ℂ) : paint L p (t • v)= t • paint L p v:=by unfold paint; split <;> simp [*,Finset.smul_sum,smul_smul] 
-- fork of Closet.lean estimates restricted to marks
private lemma pad_income {H':Hilbert}{B:ℝ≥0→ H'.Op} {m n:ℕ}{c:ℝ}(u:m≤n)(t:PadBound B m c) : PadBound B n c:=fun p q h=>(mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one (show (0:ℝ)≤(p:ℝ) from q.le) (show (p:ℝ)≤(1:ℝ) from h) u) (norm_nonneg _)).trans (t p q h)
include W
lemma canvas (v:Mark) : PadPaid (fun p=> paint L p v):=by
 choose k C hC hc using (fun i=> (W i).payQ); let d:= Finset.univ.sup k; have hd(i:ι):PadBound (fun p:ℝ≥0=>L i p p) d (C i) := pad_income (Finset.le_sup (s:=Finset.univ) (f:=k) (b:=i) (Finset.mem_univ _)) (hc i) -- implicit H
 have h(i:ι) :0≤‖v i‖*C i:=mul_nonneg (norm_nonneg _) (hC i); refine ⟨d,∑ i,‖v i‖*C i,Finset.sum_nonneg (fun i _=>h i),fun p u v' =>?_⟩
 dsimp only [paint]; rw [if_pos u]; apply (mul_le_mul_of_nonneg_left (norm_sum_le ..) (by positivity :0 ≤ (p:ℝ)^d)).trans; rw [Finset.mul_sum]; apply Finset.sum_le_sum; intro i _; rw [norm_smul,mul_left_comm]; exact mul_le_mul_of_nonneg_left (hd i p u v') (norm_nonneg _)
lemma as_paint (v:Mark) : SatinRegistration.Sound S (fun p=>paint L p v):=by
 intro p x t; dsimp only [paint]; rw [if_pos x, if_pos (show 0 < p+t from add_pos_of_pos_of_nonneg x (by positivity)), Finset.mul_sum, Finset.sum_mul]; apply Finset.sum_congr rfl; intro i _; have y: L i (p+t:ℝ≥0) (p+t:ℝ≥0)=_:= (W i).soundQ _ x t; rw [y, Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
-- Which Eu multipliers at asymmetric lags? later.
noncomputable def expedition : Carton S Mark where
 bar t:= { toFun v:= paint L t v, map_add':= paint_add L t, map_smul' x a:=paint_scale L t a x }
 coherent := as_paint S L A W
 price := canvas S L A W
 omega := Ω
 hot:= h
 size:= T
 stay:=δ
local notation "B"=> expedition S L A W Ω T δ h
#print axioms expedition
omit W
/- Real chars for axis3 reflections. -/
variable (ε:ι→ℝ)(u:∀ i, ε i*ε i=(1:ℝ))
local notation "θ"=> (fun i=>(↑(ε i):ℂ))
noncomputable def asJ : JMap Mark where
 toFun v i:= θ i * star (v i)
 map_add' x y:= by ext1 i; simp [mul_add]
 map_smul' c x:= by ext1 i; simp; ring
include W
lemma at_lights(p:ℝ≥0)(g:0<p)(v:Mark): (B).bar p v= ∑ i:ι, v i • (L i p p):= (if_pos g: paint L p v=_)
lemma at_emerald(i:ι)(p:ℝ≥0)(r:ℂ)(g:0<p): (B).bar p (herald i r)= r • L i p p:=at_herald L i p g r -- cannot infer
include u
omit W
lemma signP : Involutive (asJ ε):=by intro x; funext i; change θ i * star (θ i * star (x i))=_; rw [star_mul, star_star, star_def, conj_ofReal, mul_left_comm, show x i * _ =x i from ?_]; rw [←ofReal_mul, u, ofReal_one,mul_one] -- mul_left_comm rewrites? star mul star second.
include W
lemma planner (s:∀ (i:ι)(t:ℝ),0<t→star (L i t t)= θ i • L i t t): Remembers (B) (asJ ε):=by
 refine ⟨signP ε u,fun p v=> ?_⟩; by_cases g: zE<p; swap; · change paint L p _= (paint L p v).adjoint; unfold paint; rw [if_neg g,if_neg g,map_zero]
 rw [at_lights S L A W Ω T δ h _ g, at_lights S L A W Ω T δ h _ g, ← ContinuousLinearMap.star_eq_adjoint, star_sum]; apply Finset.sum_congr rfl; intro i _; rw [star_smul, s i p g, smul_smul,mul_comm (star _)]; rfl
#print axioms planner
omit u
end YM.SatinWFixed.Andesite
