import YM.SU5.Reconstruction.Trap.Catch
import YM.SU5.Reconstruction.Cone.Pressure
/-!
# Picket spectrum and k-axis passages
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Picket
open Function Set Filter MeasureTheory Spectral Analysis Metric InnerProductSpace
open scoped Topology NNReal ENNReal ComplexOrder InnerProductSpace
open YM.Multiplier Chirp CrossedFrame OS Semigroup Boundary Probe
-- one Semigroup branch REALIZATION requires e≥abs here; reverse chart j-title for other
variable {H D:Hilbert} (a b : Axis) (e s t :ℝ)
noncomputable def ticket (r:E4):= max 0 (r a+e*r b)
@[fun_prop] lemma ticket_cont : Continuous (ticket a b e):= by unfold ticket; fun_prop
-- rays
noncomputable def cross (h:b≠a): Cross a:=⟨basis b,by change basis b a=0; simp [h.symm]⟩
noncomputable def head:E4:= basis a+ e • basis b
lemma innerB (x:E4) : inner ℝ x (basis a) = x a:=by rw [real_inner_comm, basis_inner]
lemma dot (x : E4)(s:ℝ) : inner ℝ x (s • head a b e)=s*(x a+e*x b):= by unfold head; rw [real_inner_smul_right,inner_add_right,real_inner_smul_right,innerB,innerB]
variable {a} (S:OS.Semigroup H a)
local notation "P" => S.ℚmeasure
-- use spectral support. tag price
abbrev Paces : Prop:= ∀ x:H,∀ y∈ (S.ℚmeasure.diagonal x).support, |y b| ≤ y a
def trans (S: OS.Semigroup H a) (x:E4):H.Op:= S.unit.translation x
-- spectral identity for register any plane label E4
lemma story (x:E4): Registers S.ℚmeasure (fun p=> plane p x) (trans S x):=⟨⟨by unfold plane; fun_prop,1,zero_le_one,fun y=> (plane_norm y _).le⟩,fun z=> (S.joint z x).symm⟩
lemma mobile (x:E4): Pays (trans S x):= by
 have ht: ∀ a:E4,(star (trans S a))=trans S (-a):= by
   intro a; apply Registers.single ((story S a).adjoint); convert story S (-a) using 1; funext x; simp [plane,← Complex.exp_conj]
 constructor
 · rw [ht]; exact (S.unit.sends ..).trans (neg_add_cancel x ▸ S.unit.origin) -- tune
 rw [ht]; exact (S.unit.sends ..).trans (add_neg_cancel x ▸ S.unit.origin)
lemma trans_space {h:b≠a}: trans S (s • basis b)= S.U (s • cross (a:=a) b h):= ConePrice.translation S (s • cross a b h) -- tune a implicit?
lemma trans_time : trans S (s • basis a)=S.edge s:=by
 let hp:SEP a (s • basis a)=0:= Subtype.ext (by change _-_=(0:E4); simp)
 simp only [trans, Semigroup.unit, hp,S.uZero]; simp
-- ray light + ± spectral mode
variable (q:Paces b S)
local notation "L" => ticket a b e
include q
lemma well (x:H):∀ᵐ y ∂ S.ℚmeasure.diagonal x, |y b|≤ y a:= Eventually.mono Measure.support_mem_ae (fun _ v=> q x _ v)
lemma rays (x:H)(c:e=1∨e=-1) : L =ᵐ[S.ℚmeasure.diagonal x] fun y=> y a+e*y b:= by
 filter_upwards [well b S q x] with y v; obtain ⟨h,m⟩:= abs_le.mp v; apply max_eq_right; rcases c with c|c<;> rw [c]<;> linarith
lemma shift (c:e=1∨e=-1) : concern S.ℚmeasure L t= trans S (t • head a b e):= by
 apply (current _ L (ticket_cont a b e|>.measurable) t).single; refine (story S _).agrees ((current P L (ticket_cont a b e|>.measurable) t).price) ?_ -- tune
 intro y; filter_upwards [rays b e S q y c] with w hw
 unfold plane sound; change Complex.exp _= Complex.exp ((t:ℂ)*(L w:ℂ)*_)
 rw [dot, (show ticket a b e w=_ from hw)]; push_cast; rfl
-- allocate Eu measures with light coordinates
omit q
lemma positive (p:E4):0 ≤ ticket a b e p:= le_max_left ..
-- for both real prices representation and complex contour estimates
noncomputable def column (S:OS.Semigroup H a) (b:Axis)(e:ℝ)(z:ℂ) : H.Op:= order S.ℚmeasure (slopeRay 1 (ticket a b e) z)
lemma columns {z:ℂ}(p:0≤ z.re): Registers S.ℚmeasure (slopeRay 1 L z) (column S b e z) := by
 apply order_reads; refine ⟨by unfold slopeRay; fun_prop,1,zero_le_one,fun x=>?_⟩
 simp [slopeRay,Complex.norm_exp,Complex.mul_re]; have h:=positive b e x (a:=a); positivity -- tune
lemma columns_hol :AnalyticOnNhd ℂ (column S b e) {x:ℂ| 0<x.re}:= (show {x:ℂ|0<x.re}=sailsOn 1 from by ext;simp [sailsOn]) ▸ bill P (ticket a b e) (ticket_cont ..|>.measurable) (positive b e) 1 -- tune
@[simp] lemma column_zero : column S b e 0=1:= by apply Registers.single (columns b e S (z:=0) (by simp)); rw [show slopeRay 1 L 0= 1 from funext fun x=> by unfold slopeRay; simp]; exact Registers.one P
lemma column_misc (t:ℂ)(d:ℂ) : column S b e (t*d)=order P (slopeRay t L d):= by rw [column]; congr 1; funext x; unfold slopeRay; ring_nf
-- uses exponent with -( (t:ℝ)+ ...)
noncomputable def stroke (e:ℝ) (x y:ℂ):=(x-(e:ℂ)*Complex.I*y)/2
lemma contour_re (x y:ℝ) : (stroke e x y).re=x/2:=by simp [stroke,Complex.mul_re]
include q
set_option maxHeartbeats 320000 in
lemma eu_exp (t:ℝ≥0) (h : b≠ a) (c:e=1∨e=-1) : S.U (s • cross (a:=a) b h)*S.E t= column S b e (stroke e (t:ℝ) s)*column S b (-e) (stroke (-e) (t:ℝ) s) := by
 let x:ℂ:= stroke e (t:ℝ) s; let y:ℂ:= stroke (-e) (t:ℝ) s
 let f:= slopeRay 1 L x; let g:= slopeRay 1 (ticket a b (-e)) y
 have v(c:ℝ): 0≤(stroke c (t:ℝ) s).re:= by rw [contour_re]; positivity
 have k := (columns b e S (v e)).times (columns b (-e) S (v (-e)))
 refine Registers.single ⟨k.price,?_⟩ k
 intro w; refine Eq.trans (ConePrice.damped S w t (s • cross (a:=a) b h)) ?_
 apply integral_congr_ae; filter_upwards [rays b e S q w c, rays b (-e) S q w (by rcases c with c|c<;>rw [c]<;>simp)] with p e' u
 change plane p (s • basis b) * Complex.exp ((p a:ℂ)* ((t:ℝ)*Complex.I)*Complex.I) = slopeRay 1 (ticket a b e) x p * slopeRay 1 (ticket a b (-e)) y p
 simp only [plane, real_inner_smul_right, innerB,slopeRay]; unfold x y stroke; rw [(show ticket a b e p=_ from e'),(show ticket a b (-e) p=_ from u), ← Complex.exp_add,← Complex.exp_add]; push_cast; congr 1; rcases c with c|c <;> rw [c] <;> push_cast <;> ring_nf <;> simp <;> ring
omit q
lemma column_dawn {ι:Type*}(l: Filter ι)[l.IsCountablyGenerated](X:ι→ℂ)(p:∀ᶠ i in l, 0 ≤ (X i).re){z:ℂ}(q:0≤z.re)(v:Tendsto X l (𝓝 z))(x:H) : Tendsto (fun i=> column S b e (X i) x) l (𝓝 (column S b e z x)) := by
 -- clamp off. registers convergence no continuity op
 classical
 let X'(i:ι) := if 0 ≤ (X i).re then X i else z
 have ht(i): 0 ≤ (X' i).re:=by unfold X';split_ifs with h <;> assumption
 have hp:X =ᶠ[l] X':= p.mono fun i u=> Eq.symm (if_pos u)
 apply Tendsto.congr' (f₁:=fun i=> column S b e (X' i) x) (hp.mono (fun i h=> congrArg (fun z=> column S b e z x) h.symm))
 refine Registers.tends l _ _ (columns b e S q) (fun i=> columns b e S (ht i)) x 1 (Eventually.of_forall (fun i=> Eventually.of_forall (fun r=>?_))) (Eventually.of_forall (fun x=> (?_:Tendsto (fun i=> slopeRay 1 L (X' i) x) l (𝓝 (slopeRay 1 L z x)))))
 · simp [slopeRay,Complex.norm_exp,Complex.mul_re]; have h:=positive b e r (a:=a); have hv:=ht i; positivity
 exact ((rayValue L 1 x|>.continuousAt).tendsto.comp (v.congr' hp))
lemma column_size (z:ℂ)(g:0≤z.re): ‖column S b e z‖ ≤ 1:= by apply (columns b e S g).fare zero_le_one; intro v; simp [slopeRay,Complex.norm_exp,Complex.mul_re]; have hv:=positive b e v (a:=a); positivity
end YM.Picket
