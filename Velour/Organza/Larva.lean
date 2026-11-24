import Velour.Organza.Welcoming
/-! 
# Unpadding and all word estimates

Widths go to zero first; now work with the true closed slabs insulated by
fixed dials. **Unpad** the smeared words, including allowing test variation.
Any axis. Graph convergence on the one domain and energy bounds at every step.
-/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxRecDepth 1100
noncomputable section
namespace YM.OS.Semigroup
open Function Set Filter Complex Analysis MeasureTheory
open scoped NNReal ENNReal Topology BigOperators ContDiff InnerProductSpace ComplexOrder
variable {H : Hilbert} {a : Axis} (S:Semigroup H a)

open Boundary Probe
local notation "R" => S.gauze
local notation "D" => S.muslin
local notation "B" => S.weight

local notation "E" => S.E
local notation "G" => S.heatL


lemma heatL_add (t u:ℝ≥0): G (t+u)=G t*G u:= by
 ext1 v
 apply Subtype.ext
 change _=E t (E u v.val)
 rw [heatL_coe,S.time];rfl

lemma heat_left_label (e:ℝ≥0)(X:H.Op)(f:Test4):
 S.labelled (E e*X) f = G e * S.labelled X f:= by
 ext1
 apply Subtype.ext
 rw [labelled_coe,S.rasp_more_left _ _ (fun b=>S.unit_heat b e)];rfl

lemma heat_right_label (e:ℝ≥0)(X:H.Op)(f:Test4):
 S.labelled (X * E e) f = S.labelled X f * G e:= by
 ext1
 apply Subtype.ext
 rw [labelled_coe,S.rasp_more_right _ _ (fun b=>S.unit_heat b e)];rfl

/-- Independently priced caps. Symmetric Q on equal positive arguments. -/
def insulate (Q:ℝ≥0→H.Op)(l r:ℝ≥0):H.Op:=
 let d:= min l r
 E (l-d) * Q d * E (r-d)
lemma insulate_same (Q:ℝ≥0→H.Op)(t:ℝ≥0): S.insulate Q t t=Q t:=by
 unfold insulate; dsimp only; rw [min_self, tsub_self,S.eZero,show ContinuousLinearMap.id ℂ H.space=(1:H.Op) from rfl,one_mul, mul_one]


variable {S}
variable {ι:Type}{p: Filter ι}{F:ι→Test4} {f:Test4}
variable {Q:ℝ≥0→H.Op}
variable {T:S.Detector}

lemma Touchable.surges (h:S.Touchable T)(e:Tendsto F p (𝓝 f)):
 S.Surges p (fun i=>T (F i)) (T f):=by
 intro v w k n
 obtain ⟨m,b⟩:=h; obtain ⟨X,q⟩:=b n
 have r:Continuous (fun z:H.Op × H.space=> z.1 z.2):=by fun_prop
 have t:= (r.tendsto _).comp (((X.continuous.tendsto _).comp e).prodMk_nhds (k (m+n)))
 unfold Refines at q
 simp_rw [q]; exact t

namespace Instates

lemma either_pad (h:S.Instates Q T){l r:ℝ≥0}(u:0<l)(v:0<r)(f:Test4):
 S.labelled (S.insulate Q l r) f= G l * T f * G r:=by
 let d:=min l r
 change S.labelled (E (l-d) * Q d * E (r-d)) f=_
 rw [heat_right_label,heat_left_label, h.guard f d (lt_min u v),
    ←mul_assoc, ← mul_assoc, ←heatL_add, tsub_add_cancel_of_le (show d≤l from min_le_left ..),mul_assoc,
    ←heatL_add, add_tsub_cancel_of_le (show d≤r from min_le_right ..)]


lemma surge_warming (h:S.Instates Q T)(e:Tendsto F p (𝓝 f)){A B':ι→ℝ≥0}
  (t:Tendsto A p (𝓝 0)) (u:Tendsto B' p (𝓝 0)):
 S.Surges p (fun i=> G (A i) * T (F i)*G (B' i)) (T f):=by
  have y:=((S.surges_warm t).mul (h.touch.surges e)).mul (S.surges_warm u)
  rwa [one_mul, mul_one] at y

lemma yield (h:S.Instates Q T)(e:Tendsto F p (𝓝 f)){A B':ι→ℝ≥0}
  (t:Tendsto A p (𝓝[>] 0)) (u:Tendsto B' p (𝓝[>] 0)):
 S.Surges p (fun i=> S.labelled (S.insulate Q (A i) (B' i)) (F i)) (T f):=by
  apply (h.surge_warming e (t.mono_right nhdsWithin_le_nhds) (u.mono_right nhdsWithin_le_nhds)).consent
  filter_upwards [t.eventually self_mem_nhdsWithin,u.eventually self_mem_nhdsWithin] with i pt pu
  exact (h.either_pad pt pu _).symm

/-- Symmetric dials. -/
lemma harvest (h:S.Instates Q T)(f:Test4):
 S.Surges (𝓝[>] (0:ℝ≥0)) (fun t=>S.labelled (Q t) f) (T f):=by
  have p:=h.yield (tendsto_const_nhds (x:=f)) tendsto_id tendsto_id
  simpa only [id_eq, S.insulate_same] using p


/-- Symmetric dials on vector, suppress graph costs. -/
lemma meet (h:S.Instates Q T)(f:Test4)(w:D):
 Tendsto (fun t=> S.rasp (Q t) f w.val) (𝓝[>] (0:ℝ≥0)) (𝓝 (T f w).val):=
 ((h.harvest f).at_one w).plain

variable {V:S.Detector}{J:ℝ≥0→H.Op}
lemma common (h:S.Instates Q T)(k:S.Instates J V)
   (g:Q =ᶠ[𝓝[>] (0:ℝ≥0)] J): T=V:=by
 ext1 b; ext1 v; apply Subtype.ext
 exact tendsto_nhds_unique ((h.meet b v).congr' (g.mono fun t e=>by rw [e]))
   (k.meet ..)

lemma mirror (h:S.Instates Q T)(k:S.Instates J V)
   (g:(fun t=> star (Q t)) =ᶠ[𝓝[>] (0:ℝ≥0)] J)(f:Test4):
 S.Faces (T f) (V (bar f)):=by
 intro x y
 have p:=
   ((h.meet f x).inner (𝕜:=ℂ) (tendsto_const_nhds (x:=y.val)))
 have q:= ((tendsto_const_nhds (x:=x.val)).inner (𝕜:=ℂ)
         (k.meet (bar f) y))
 apply tendsto_nhds_unique p
 exact q.congr' (g.mono fun t e=>by
    rw [←e]; exact (S.labelled_faces (Q t) f x y).symm)


lemma move (h:S.Instates Q T)(u:E4)(f:Test4):
 T (ahead u f)=S.liftL u * T f * S.liftL (-u):=by
 ext1 x; apply Subtype.ext
 have p:=((S.unit.translation u).continuous.tendsto _).comp (h.meet f (S.liftL (-u) x))
 exact tendsto_nhds_unique (h.meet (ahead u f) x)
    (p.congr fun t=> by exact (congrArg (fun m:H.Op=> m x.val)
      (S.rasp_ahead (Q t) f u)).symm)
lemma translates (h:S.Instates Q T)(u:E4)(f:Test4):
 T (ahead u f) * S.liftL u = S.liftL u * T f:=by
 rw [h.move, mul_assoc, ←liftL_add,neg_add_cancel,liftL_zero,mul_one]
end Instates

/-- Single word harvest with no pads in final answer. Can also be used on
starred prices. Costs at each step are obtained via either_pad and the explicit
`Refines.bill` estimate (no heating cost in any energy graph). -/


lemma yield_word {κ:Type} (L:List κ)
   (q:κ→ℝ≥0→H.Op)(a':κ→S.Detector) (t:κ→Test4)(v:κ→ι→Test4)
   (l r:κ→ι→ℝ≥0) (h:∀k∈L, S.Instates (q k) (a' k))
   (g:∀k∈L, Tendsto (v k) p (𝓝 (t k)))
   (e:∀k∈L, Tendsto (l k) p (𝓝[>] 0)) (z:∀k∈L, Tendsto (r k) p (𝓝[>] 0)):
 S.Surges p (fun i=>
    (L.map fun k=> S.labelled (S.insulate (q k) (l k i) (r k i)) (v k i)).prod)
    (L.map fun k=> a' k (t k)).prod:=
   Surges.per_word (F:=fun k i=>S.labelled (S.insulate (q k) (l k i) (r k i)) (v k i))
     _ (fun k b=>(h k b).yield (g k b) (e k b) (z k b))

#print axioms yield_word
#print axioms Instates.translates
#print axioms Instates.mirror

