import Merino.Cabinet
import YM.CF.Chaff.Pulse
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Merino
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre Vow
open RG Mew Rive Nor Hake MeasureTheory Bake Rue Salt
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Swell

variable {n:Side}
local notation "I"=> Single n

variable {o:Seat n} {p:BudgetPoint} {d a b:ℝ} {K:Scree.Loom n} {X:SOp n}{k:ℕ}

/-- These qualifications are simple consequences of the working Roof receipt at
high height. Assume them generically for the pricing mechanisms. -/
structure Skylit (p:BudgetPoint)(d:ℝ)(K:Scree.Loom n):Prop where
  pos:0<d
  box:∃ e δ:ℝ, ∃ r:ℕ, Roof n e δ r K ∧ p.threshold ≤ e ∧ δ ≤ d ∧ p.B/10+r ≤ p.B

abbrev pass (p:BudgetPoint)(o:Seat n):Set (Pane n) :=
  {x|pingS p.threshold (purse p.B o) x}
local notation "Z" => (↥(Openc (More n) d))
abbrev ask (K:Scree.Loom n)(_p:BudgetPoint)(_o:Seat n)(X:SOp n)
    (V:Pane n)(τ:Ids n): Op I:=X (profile (K (V,τ)))
def fixedTags(n:Side):Ids n:=Classical.arbitrary _
/-- Always uses actual reader input as first Pane; can be zero at boundaries. -/
def masked (K:Scree.Loom n)(p:BudgetPoint)(o:Seat n)(X:SOp n):
    Pane n → Op I :=
  (pass p o).indicator fun V=>ask K p o X V (fixedTags n)
variable (r:Skylit p d K)
local notation "S"=>purse (p.B/10) o

namespace Skylit
include r
lemma enter (V:Orbit n):profile (K V) ∈ Openc (More n) d:=by
 obtain ⟨e,δ,l,R,_,v,_⟩:=r.box
 exact ⟨K V,(R.paid V).shrink v,by simpa using r.pos⟩

def slot (V:Orbit n):Z:=⟨_,r.enter V⟩

lemma lit {V:Pane n}(v: V∈pass p o)(τ:Ids n):
    Agrees S (K (V,τ)) V:=by
 obtain ⟨e,δ,l,R,t,_,h⟩:=r.box
 have a:pingS e (purse p.B o) V:=fun i u=>(v i u).trans_le t
 intro i vi wi
 apply R.lamp
 apply Disjoint.mono_right ?_ ((show Disjoint (purse p.B o) _ from ping_le a).symm)
 intro x g
 obtain ⟨z,y,u⟩:=halo_spec.mp g
 obtain ⟨j,f,m⟩:=halo_spec.mp (show z∈S from insert_subset vi (singleton_subset_iff.mpr wi) y)
 exact halo_spec.mpr ⟨j,f,(separation_triangle _ z _).trans (by omega)⟩
lemma slot_gauge (V:Pane n)(τ:Ids n)(g:Seat n→E):
    r.slot (gauge g V,threadG g τ)=rayG n d g (r.slot (V,τ)):=by
 obtain ⟨_,_,_,R,_⟩:=r.box
 apply Subtype.ext
 change profile _ =_
 rw [R.rev,profile_g]
 rfl
end Skylit

lemma mask_meas [MeasurableSpace (Op I)][BorelSpace (Op I)] (r:Skylit p d K)
    (h:Soak o X a b d) : Measurable (masked K p o X):=by
 obtain ⟨_,_,_,R,_⟩:=r.box
 let G:Set (Pane n):={U| profile U ∈ Openc (More n) d}
 let f (x:Pane n) : ↥G:= ⟨K (x,fixedTags n),r.enter _⟩
 have hv:Measurable f:=(R.bill.comp (measurable_id.prodMk measurable_const)).subtype_mk
 let H(v:↥G):Z:=⟨profile v.val,v.property⟩
 have hH: Continuous H:=(Dial.profile_c.comp continuous_subtype_val).subtype_mk _
 exact (((soak_cont h).comp hH).measurable.comp hv).indicator ping_o.measurableSet

variable (ha:0≤a)(h:Trunk o X (p.B/10) a b d)
    {U V U' V':Pane n}
local notation "askX"=>ask K p o X
local notation "M"=>masked K p o X
lemma fare_local {T:Sa n}(h:Agrees T U V) (g:Agrees T U' V'):
    fare T (profile U) (profile U') = fare T (profile V) (profile V'):=by
 unfold fare
 refine sum_congr rfl fun i hi=>?_
 obtain ⟨_,l,u⟩:=mem_filter.mp hi
 have e:profile U i=profile V i:=by unfold profile; rw [h i l u]
 have f:profile U' i=profile V' i:=by unfold profile; rw [g i l u]
 rw [e,f]

include ha h r
lemma ask_cong (pV: V∈pass p o)(pU:U∈pass p o)
    (g:Agrees S V U)(τ t:Ids n):
    askX V τ=askX U t:=by
 let x:=r.slot (V,τ); let y:=r.slot (U,t)
 refine trunk_local h ha x y ?_
 change fare S (profile _) (profile _)=0
 rw [fare_local (r.lit pV τ) (r.lit pU t),fare_vanish g]

lemma mask_eq (v: V∈pass p o)(τ:Ids n):
   M V=askX V τ:=by
 rw [masked,Set.indicator_of_mem v]
 exact ask_cong r ha h v v (fun _ _ _=>rfl) _ _

/-- Evaluation with a whole qualified Pane with agreeing local links
after passing. -/
lemma mask_extension (v:V∈pass p o)(z:profile U ∈ Openc (More n) d)
    (l:Agrees S V U) :
    M V=X (profile U):=by
 rw [masked,Set.indicator_of_mem v]
 let x:=r.slot (V,fixedTags n)
 refine trunk_local h ha x (⟨_,z⟩:Z) ?_
 apply fare_vanish
 intro i pv pw; exact ((r.lit v _ i pv pw).trans (l i pv pw))

lemma mask_lip (v:V∈pass p o)(u:U∈pass p o)(i j:I):
   ‖M V i j-M U i j‖ ≤ b*(fare S (profile V) (profile U) / |d|):=by
 let τ:=fixedTags n
 rw [masked,Set.indicator_of_mem v,Set.indicator_of_mem u,←fare_local (r.lit v τ) (r.lit u τ)]
 exact trunk_lip h ha (r.slot _) (r.slot _) _ _
lemma mask_gauge (V:Pane n)(g:Seat n→E):
  M (gauge g V)=twist (tradew n g) (M V):=by
 have he:gauge g V ∈ pass p o ↔ V∈pass p o:= pingB V g
 by_cases v:V∈pass p o
 · let t:=fixedTags n
   rw [mask_eq r ha h (he.mpr v) (threadG g t),mask_eq r ha h v t]
   change X (r.slot _).val=_
   rw [r.slot_gauge,soak_frame h.pay]
   rfl
 rw [masked,Set.indicator_of_notMem (mt he.mp v), Set.indicator_of_notMem v,map_zero]

abbrev casing (p:BudgetPoint)(o:Seat n):Sa n:=purse (p.B+12) o
omit ha h r in
lemma inside : purse (p.B/10) o ⊆ casing p o:=Corona.halo_mono (by omega) le_rfl
omit ha h r in
lemma inspection : inspected (purse p.B o) ⊆ casing p o:=by
 refine Subset.trans (Yaw.touchK _) ?_
 intro i v
 obtain ⟨j,r,l⟩:=halo_spec.mp v
 obtain ⟨t,u,d⟩:=halo_spec.mp r
 exact halo_spec.mpr ⟨t,u,(separation_triangle _ j _).trans (Nat.add_le_add d l)⟩
lemma mask_local: LocalOn (casing p o) M:=by
 intro U V u
 have hi:Agrees (inspected (purse p.B o)) U V:=agrees_mono u inspection
 have hv:U∈pass p o↔V∈pass p o:=Chaff.fenceW _ hi _
 by_cases l:U∈pass p o
 · rw [masked,Set.indicator_of_mem l,Set.indicator_of_mem (hv.mp l)]
   exact ask_cong r ha h l (hv.mp l) (agrees_mono u inside) _ _
 rw [masked,Set.indicator_of_notMem l,Set.indicator_of_notMem (mt hv.mpr l)]

lemma mask_short (V:Pane n) (i j:I) (l:M V i j ≠ 0):
    node i.1.1∈S ∧ node j.1.1∈S:=by
 by_cases t:V∈pass p o
 · rw [masked,Set.indicator_of_mem t] at l
   exact trunk_lives h (r.slot _) _ _ l
 rw [masked,Set.indicator_of_notMem t] at l
 exact (l rfl).elim

lemma mask_sum (V:Pane n):
    (∑ i:I,∑ j:I,‖M V i j‖) ≤ b:=by
 by_cases t:V∈pass p o
 · rw [masked,Set.indicator_of_mem t]
   exact soak_sum h.pay (r.slot _) ha
 rw [masked,Set.indicator_of_notMem t]
 suffices 0≤b by simpa
 exact (norm_nonneg _).trans (norm_U h.pay ha (r.slot (V,fixedTags n)))
lemma mask_trace (V:Pane n):‖(M V).trace‖ ≤ b:=by
 refine (norm_sum_le univ (fun i:I=>M V i i)).trans (le_trans ?_ (mask_sum r ha h V))
 exact sum_le_sum fun i _=> single_le_sum (f:=fun j=>‖M V i j‖) (fun _ _=>norm_nonneg _) (mem_univ i)

lemma mask_env [MeasurableSpace (Op I)][BorelSpace (Op I)] :Envelope M:=by
 refine ⟨mask_meas r h.pay,b, fun V=>?_⟩
 have hx:=norm_U h.pay ha (r.slot (V,fixedTags n))
 unfold masked
 by_cases u:V∈pass p o
 · rw [Set.indicator_of_mem u]
   exact hx
 rw [Set.indicator_of_notMem u,norm_zero]
 exact (norm_nonneg _).trans hx
end YM.CF.Merino

