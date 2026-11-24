import ZecaCuts
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 320000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
variable (P: Spine) (j:Axis) (x:P.Spectrum0 j)
open Aria Set TopologicalSpace Metric

open Hierarchy.Seld Hierarchy.Seld.Zeca
local notation "G" => P.ManyF j x
local notation "Ω"=> P.heaven j x
local notation "S"=>P.seasons j x
local notation "E"=> (P.seasons j x).E

variable {I:Type} (D:I→Zeca.Moment (P.ManyF j x)) (Z:ℕ→I→P.Apron)
  (p:I→Vantage)(u:ℕ→I→Vantage)
  (b:∀i,P.Bought j x (D i) (fun k=>Z k i))
  (v:∀i, Tendsto (fun k=>u k i) atTop (𝓝 (p i)))
  {y z:I→ℝ}(L:List I)
local notation "t" => fun i=> p i j
variable (d:Drape (fun i=>p i j) y z L)

def stripY (Z:I→P.Apron)(u:I→Vantage)(y z:I→ℝ)(i:I):=
 P.ruby j x (Z i) (u i) (u i j - y i) (z i-u i j)
abbrev spY (j:Axis)(p:I→Vantage) := fun i=>poseSp j (p i)
abbrev atY (y z:I→ℝ):=
 padOp S D (spY j p)
     (frontP (fun i=>p i j) y) (rearP (fun i=>p i j) z)

include b v d in
lemma strip_go (i:I)(r:i∈L):
   Glaze_LocalFieldBounds G atTop
    (fun k=>P.stripY j x (Z k) (u k) y z i)
    (atY P j x D p y z i):=by
 obtain ⟨F,w,h⟩:=b i
 have e : Tendsto (fun k=> u k i j) atTop (𝓝 (p i j)) :=
   ((continuous_apply j).tendsto _).comp (v i)
 obtain ⟨a,r⟩:= d.inner i r
 let l:=p i j - y i
 let g:=z i - p i j

 have pl:0<l:=sub_pos.mpr a
 have pg:0<g:=sub_pos.mpr r
 have t₀:=w.read pl pg (e.sub_const (y i)) (e.const_sub (z i)) (v i)
 have c:=h.translation _ _ (Real.toNNReal_pos.mpr pl) (Real.toNNReal_pos.mpr pg)
 rw [Real.coe_toNNReal l pl.le,Real.coe_toNNReal g pg.le] at c
 change Glaze_LocalFieldBounds G atTop _ (optx S ((D i).cost S l.toNNReal g.toNNReal) (poseSp j (p i)).val)
 rw [←c, ←P.dazzle_m]
 exact t₀.congr' (Eventually.of_forall fun _=>one_smul ..)

include b v d

lemma strip_ok:
  ∀ᶠ k in atTop,∀ i∈L,y i < P.porchY j (Z k) (u k) i ∧ P.resignY j (Z k) (u k) i < z i:=by
 classical
 refine ((eventually_all_finset L.toFinset).mpr ?_).mono (fun k h i g=>h i (List.mem_toFinset.mpr g))
 intro i g
 have e : Tendsto (fun k=> u k i j) atTop (𝓝 (p i j)) :=
   ((continuous_apply j).tendsto _).comp (v i)
 obtain ⟨F,w,-⟩:=b i
 obtain ⟨a,r⟩:= d.inner i (List.mem_toFinset.mp g)
 apply Eventually.and ((e.sub w.thin).eventually (lt_mem_nhds ?_))
            ((e.add w.thin).eventually (gt_mem_nhds ?_))
 · rwa [sub_zero]
 rw [add_zero]; exact r

lemma strip_turn:
 ∀ᶠ k in atTop, P.Turnstile j (Z k) L (u k):=by
 filter_upwards [P.strip_ok j x D Z p u b v L d] with k r
 exact d.order.imp_of_mem (fun e h m=> (r _ e).2.trans (m.trans_lt (r _ h).1))

lemma strip_prod: Glaze_LocalFieldBounds G atTop
 (fun k=> (L.map (P.stripY j x (Z k) (u k) y z)).prod)
 (L.map (atY P j x D p y z)).prod:=by
 induction L with
 | nil=>exact Glaze_LocalFieldBounds.const _
 | cons i L ih=>
   simpa only [List.map_cons,List.prod_cons] using!
    (P.strip_go j x D Z p u b v (i::L) d i List.mem_cons_self).mul (ih d.tail)

lemma strip_exact:
 ∀ᶠ k in atTop,
  inner ℂ Ω ((L.map (P.stripY j x (Z k) (u k) y z)).prod Ω)
   = P.memorial j x (Z k) L (u k):=by
 filter_upwards [P.strip_ok j x D Z p u b v L d] with k r
 unfold memorial
 rw [←curtain_payment S Ω _ _ _ y z (P.heaven_hot j x) L r d.seam]
 have e:P.stripY j x (Z k) (u k) y z=behind S
   (P.commuteTight j x (Z k) (u k)) (P.porchY j (Z k) (u k))
    (P.resignY j (Z k) (u k)) y z:=by
   funext i
   unfold stripY ruby Aria.behind commuteTight porchY resignY Apron.time_panel Apron.time_edge
   rw [sub_right_comm (u k i j) (y i),sub_sub (z i), mul_assoc]
   rfl
 rw [e]

omit d
lemma memorial_quote
 (o:L.Pairwise (fun i h=>p i j < p h j)):
 (∀ᶠ k:ℕ in atTop,P.Turnstile j (Z k) L (u k)) ∧
 Tendsto (fun k=>P.memorial j x (Z k) L (u k)) atTop
    (𝓝 (quoteL S Ω D (spY j p) (fun i=>p i j) L)):=by
 obtain ⟨y,z,d⟩:=drape_get _ _ o
 refine ⟨P.strip_turn j x D Z p u b v L d,?_⟩
 rw [quoteCuts S _ _ _ (P.prepaid j x) d]
 exact (tendsto_const_nhds.inner
   ((P.strip_prod j x D Z p u b v L d).app tendsto_const_nhds)).congr'
       (P.strip_exact j x D Z p u b v L d)

omit b v
lemma quoteWell (x:P.Spectrum0 3)(V:P.Ellis 3 x)
 (D:I→Zeca.Moment (P.ManyF j (P.advocate 3 x j)))
 (Z:ℕ→I→P.Apron)(p:I→Vantage)(u:ℕ→I→Vantage)
 (L L':List I)(e:L'.Perm L)
 (b:∀i,P.Bought j (P.advocate 3 x j) (D i) (fun k=>Z k i))
 (v:∀i,Tendsto (fun k=>u k i) atTop (𝓝 (p i)))
 (o:L.Pairwise (fun i h=>p i j < p h j)):
 Tendsto (fun k=>P.commonWell 3 x (Z k) (u k) L') atTop
     (𝓝 (quoteL (P.seasons j (P.advocate 3 x j)) (P.heaven j (P.advocate 3 x j))
       D (spY j p) (fun i=>p i j) L)):=by
 obtain ⟨c,r⟩:=P.memorial_quote j _ D Z p u b v L o
 refine r.congr' (c.mono fun k h=>?_)
 exact (P.common_cult 3 x (Z k) (u k) L' V e h).symm
#print axioms quoteWell

end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
