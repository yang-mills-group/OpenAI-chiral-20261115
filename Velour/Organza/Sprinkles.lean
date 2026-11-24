import Velour.Crepe.Glow
import Velour.Organza.Takings
import Velour.Organza.Surges
/-! Stable on width limits at **fixed** positive budgets. Extend to jointly
varying word products preserving strong* graph convergence (before heat removal). -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxRecDepth 1100
noncomputable section
namespace YM.OS.Semigroup
open Function Set Filter Complex Analysis MeasureTheory
open scoped NNReal ENNReal Topology BigOperators ContDiff InnerProductSpace ComplexOrder
variable {H : Hilbert} {a : Axis} (S:Semigroup H a)

open Velour
open Boundary Probe
local notation "α" => S.dangle
local notation "U" => S.unit.translation
local notation "R" => S.gauze
local notation "D" => S.muslin
local notation "B" => S.weight

variable {w:ℕ→H.Op}{x:H.Op}


private lemma content (g:Gleams H w x) (f:Test4)(v:H) :
 Tendsto (fun i=> S.rasp (w i) f v) atTop (𝓝 (S.rasp x f v)):= by
 obtain ⟨k,p⟩:= g.bought
 simp_rw [rasp_apply]
 refine tendsto_integral_filter_of_dominated_convergence (fun b=>‖f b‖* (k*‖v‖))
   (Eventually.of_forall fun i=> (S.unsoiled (w i) f v).1)
   (p.mono fun i q=>ae_of_all _ fun b=>?_ )
   (f.integrable.norm.mul_const _)
   (ae_of_all _ fun b=> ?_)
 · rw [norm_smul]
   exact mul_le_mul_of_nonneg_left ((S.dangle_bill ..).trans
    (mul_le_mul_of_nonneg_right q (norm_nonneg _))) (norm_nonneg _)
 exact tendsto_const_nhds.smul (((U b).continuous.tendsto _).comp (g.gaze (U (-b) v)))


lemma gleams_rasp (g:Gleams H w x)(f:Test4):
 Gleams H (fun i=> S.rasp (w i) f) (S.rasp x f):=by
 obtain ⟨k,p⟩:=g.bought
 refine ⟨⟨L₁ f*k,p.mono fun i q=>(S.rasp_bill ..).trans
     (mul_le_mul_of_nonneg_left q (L₁_nonneg _))⟩,
   S.content g f, fun v=> ?_⟩
 simp_rw [S.rasp_star]
 exact S.content g.swap (bar f) v

lemma gleams_rise (g:Gleams H w x)(f:Test4)(n:ℕ) :
  Gleams H (fun i=> S.rise (w i) n f) (S.rise x n f):=by
 induction n generalizing f with
 | zero=>exact S.gleams_rasp g f
 | succ n ih=>
   simp_rw [S.rise_step]
   exact (ih f).add ((ih _).mul (Gleams.const _))

#print axioms gleams_rise


lemma tender_zero (n:ℕ) : tender a n 0=0:=by
 induction n with
 | zero=>exact zero_L₁
 | succ n ih=>simp only [tender, map_zero, ih, add_zero]

lemma gleams_rising (g:Gleams H w x){f:Test4}{q:ℕ→Test4}(p:Tendsto q atTop (𝓝 f))(n:ℕ):
 Gleams H (fun i=>S.rise (w i) n (q i)) (S.rise x n f):=by
 let r:=fun i=>q i - f
 have h:Tendsto r atTop (𝓝 0):=by simpa only [sub_self] using p.sub (tendsto_const_nhds (x:=f))
 have h₁:Tendsto (fun i=>S.rise (w i) n (r i)) atTop (𝓝 0):=by
     obtain ⟨k,e⟩:=g.bought
     refine squeeze_zero_norm' (e.mono fun i j=>(S.rise_bill ..).trans
       (mul_le_mul_of_nonneg_left j (tender_nonneg n (r i)))) ?_
     have t:Tendsto (fun i=>tender a n (r i)) atTop (𝓝 (tender a n 0)):=
       ((tender_cont n).tendsto 0).comp h
     rw [tender_zero] at t; simpa using t.mul (tendsto_const_nhds (x:=k))
 have p:= (Gleams.tightly h₁).add (S.gleams_rise g f n)
 simp only [r,map_sub, sub_add_cancel,zero_add] at p
 exact p


lemma surges_width (g:Gleams H w x){f:Test4}{q:ℕ→Test4}(p:Tendsto q atTop (𝓝 f)):
 S.Surges atTop (fun i=> S.labelled (w i) (q i)) (S.labelled x f):=by
 intro v y h n
 have t:= (S.gleams_rising g p n).both (h n)
 have hi (T:H.Op)(b:Test4)(u:D):(B n (S.labelled T b u)).val=S.rise T n b (B n u).val:= by
    simpa only [zero_add] using S.labelled_refines T b n u
 simp_rw [hi]; exact t
end YM.OS.Semigroup
namespace YM.Velour
open Filter
open scoped Topology
lemma Gleams.glints {H:Hilbert}{w : ℕ→H.Op}{x:H.Op}
   (g:Gleams H w x){j:ℕ→ℕ}(e:Tendsto j atTop atTop):
 Gleams H (w ∘ j) x:= ⟨by obtain ⟨k,u⟩:=g.bought; exact ⟨k,e.eventually u⟩,
      fun v=>(g.gaze v).comp e,fun v=>(g.turn v).comp e⟩
#print axioms YM.OS.Semigroup.surges_width

