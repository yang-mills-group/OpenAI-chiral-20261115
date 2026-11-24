import Merino.Cuff.Stroke
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Merino.Cuff
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre Vow
open RG Mew Rive Nor Hake MeasureTheory Bake Rue Salt
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Swell

variable {n:Side}
local notation "I"=> Single n

open Push.Uniform Planned.JetPort Peaks
open scoped ContDiff
open AnalyticBridge.Merino
variable {d r C : ℝ}
local notation "A"=>Openc (More n) d
local notation "M"=> (↥(Openc (More n) d))

variable {F: Openc (More n) d → Op (Single n)} {T:Sa n} {W:Toll (Single n)}


abbrev planS {n:Side}(d:ℝ)(T:Sa n)(W:Toll (Single n))(F:Openc (More n) d→Op (Single n)):=
   Suite (badge (Openc (More n) d)) (bail n d) (bail n d) T W F

/-- piece's own chart probe. Keep them separate through Ward. -/
def floret (F:M→Op I)(U:Pane n):ℝ := (equalizer (fun z=>(F z).trace) (profile U)).re

abbrev glint (F:M→Op I):=floret F ∘ dyeB n

lemma positive_led (q:planS d T W F):0≤ledgerV W:=
 sum_nonneg (fun _ _=>sum_nonneg (fun _ _=> q.toTicket.nonn _ _))

variable (h:Room d r C)(q:planS d T W F)

lemma glint_eq:glint F= fun x=>∑ i:I, flash (fun z:M=>F z i i) x:=by
 ext x
 change (equalizer (fun z=>(F z).trace) (gleam n x)).re=_
 unfold flash equalizer
 split
 · simp [*, Matrix.trace,Complex.re_sum]
 simp [*]

lemma open_frame {U:Pane n}(hx:profile U∈A)(g:Seat n→SU.E):
   profile (gauge g U)∈A:=by
  rw [profile_g]
  exact (rayG n d g ⟨_,hx⟩).property

include q

lemma floret_frame (U:Pane n)(g:Seat n→SU.E):
   floret F (gauge g U)= floret F U:=by
  by_cases hx:profile U∈A


  · rw [floret,floret,equalizer,dif_pos (open_frame hx g),equalizer,dif_pos hx]
    let x:M:=⟨_,hx⟩
    have he:F (rayG n d g x)= twist (tradew n g) (F x):= q.frame.frame g x
    let z:M:=⟨_,open_frame hx g⟩
    have hz:z=rayG n d g x:=Subtype.ext (profile_g _ U)
    change (F z).trace.re=_
    rw [hz,he,trace_twist]
  have hy:profile (gauge g U)∉A:=by
     intro ht; apply hx; have hm:= open_frame ht g⁻¹
     have hf:gauge g⁻¹ (gauge g U)=U:=by
        funext e; simp [Lattice.gauge,mul_assoc]
     rwa [hf] at hm
  rw [floret,floret,equalizer,dif_neg hy,equalizer,dif_neg hx]

include h
lemma glint_cost:Afford (glint F) r (ledgerV W*C):=by
  intro x u
  rw [glint_eq]
  let X(i:I): M→ ℂ:=fun z=>F z i i
  have e(i):Jet.Allows 3 (flash (X i)) x (W i i*C):=
    h.pay (X i) (W i i) (q.fuel i i) (q.toTicket.cont.matrix_elem i i) (q.expo i i).bounded u
  refine (Jet.allows_sum (s:=univ) (fun i _=>e i)).mono ?_
  rw [←sum_mul]
  exact mul_le_mul_of_nonneg_right (sum_le_sum fun i _=>single_le_sum (fun j _=>q.toTicket.nonn i j) (mem_univ i)) h.price.le


lemma glint_zero: Jet.Allows 3 (glint F) 0 (ledgerV W*C):=
 glint_cost h q (by rw [norm_zero];exact h.haveR.le)
lemma glint_smooth: ContDiffAt ℝ 2 (glint F) 0:=(glint_zero h q).smooth.of_le (by norm_num)
lemma glint_decent: Decent (floret F):= ⟨fun g U=>floret_frame q U g,glint_smooth h q⟩

lemma glint_first: fderiv ℝ (glint F) 0=0:=flat_critical Thera.yet_one (glint_decent h q)

abbrev silk (F:M→Op I):= round (glint F)
abbrev frond {n:Side}(s:Site n→Hue):= gradient (G:=group) s
lemma silk_exact (s:Seat n→Hue)(v:Bows n):
   silk F (frond s) v=0:=by
 rw [silk,roundV]
 rw [show iteratedFDeriv ℝ 2 (glint F) 0 ![frond s,v]=0 from hessian_gradient Thera.yet_one (glint_decent h q) s v,zero_div]
lemma silk_line (v w:Bows n)(l:Agrees T v w):
    silk F v v=silk F w w:=by
 have hx(x:Bows n): ∀ᶠ t:ℝ in 𝓝 0, gleam n (bolt x t)∈A:=by
    have hv:Continuous fun t=>‖bolt x t‖:=(bolt x).continuous.norm
    have he: ‖bolt x 0‖<r:=by rw [map_zero,norm_zero]; exact h.haveR
    filter_upwards [(hv.tendsto 0).eventually (gt_mem_nhds he)] with t hy
    exact h.get _ (le_of_lt hy)
 apply round_diag (glint_smooth h q)
 filter_upwards [hx v,hx w] with t hv hw


 change (equalizer (fun z=>(F z).trace) (gleam n (bolt v t))).re=
   (equalizer (fun z=>(F z).trace) (gleam n (bolt w t))).re
 rw [equalizer,dif_pos hv,equalizer,dif_pos hw]
 let x:M:= ⟨_,hv⟩
 let y:M:= ⟨_,hw⟩
 have g:fare T x.val y.val=0:=by
    apply fare_vanish; intro i hi ht
    change group.lieExp (t • v i)*_ = group.lieExp (t • w i)*_
    rw [l i hi ht]
 change (F x).trace.re= (F y).trace.re
 have he:F x=F y:=by
    ext i j
    have hp:= (q.expo i j).variation x y
    change ‖_‖ ≤ W i j*(Tulip.fare T x.val y.val/|d|) at hp
    rw [g,zero_div,mul_zero] at hp; exact sub_eq_zero.mp (norm_le_zero_iff.mp hp)
 rw [he]

lemma silk_kills (x y:Bows n)(g:Agrees T x 0):
   silk F x y=0:=by
 have e:= silk_line h q x _ g
 have a:= silk_line h q (x+y) y (fun i v w=> by rw [Pi.add_apply,g i v w,Pi.zero_apply,zero_add])
 have b:silk F y x=silk F x y:=round_symm (glint_smooth h q) _ _
 rw [map_zero] at e
 simp only [map_add,LinearMap.add_apply,b,e] at a
 linarith only [a]
end YM.CF.Merino.Cuff
