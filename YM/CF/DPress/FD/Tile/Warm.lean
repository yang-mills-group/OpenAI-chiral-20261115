import YM.CF.DPress.FD.Tile.Weld
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.DPress.FD
open Function Set Metric Filter SU MeasureTheory Ramp Row Frame
open scoped Topology BigOperators NNReal ENNReal Matrix.Norms.Frobenius Classical
attribute [local instance] Gauge.frobInner
variable {I K:Type*}[Fintype I][Fintype K]{m:ℕ}
namespace Warm
variable (S:Finset I)(r:ℕ)(p:0<m)(F:Ramp I m→ArrayF K) {a:ℝ} 
abbrev Shape (D:Set (Ramp I m))(F:Ramp I m→ArrayF K):Prop:= Set.MapsTo F D (Frame K)
structure Seam (D:Set (Ramp I m))(F G:Ramp I m→ ArrayF K)(a:ℝ):Prop where
 legal : Shape D F
 pay : ∀ x∈ D,Frame.Fits 0 (F x) (G x)
 e : Speed D G a
abbrev level (x:Ramp I m):=(supportT x).card
variable {S}
lemma touch (i:Finset I){x:Ramp I m}(p:x∈ facet i)(h:i ⊂ S): x∈ boundary S:= ⟨p.1,lt_of_le_of_lt p.2 h⟩
lemma shapeP (C:Set (Ramp I m))(h:Shape C F) (G:Ramp I m→ArrayF K)(p:∀ x∈ C,Frame.Fits 0 (F x) (G x)):Shape C G:=by
 intro i g; obtain ⟨j,u⟩:= p i g; exact (dist_le_zero.mp u) ▸ stays (h g) j
namespace Seam
variable {D:Set (Ramp I m)}{F G H:Ramp I m→ ArrayF K}
lemma shape(t:Seam D F G a):Shape D G:= shapeP F _ t.legal _ t.pay
lemma more {E:Set (Ramp I m)} (t:Seam D F G a)(h:E⊆D)(b:ℝ)(p:a≤b):Seam E F G b:= ⟨fun _ v=> t.legal (h v),fun _ v=> t.pay _ (h v),enlarge t.e h p⟩
lemma congr (t:Seam D F G a)(h:EqOn G H D): Seam D F H a:=by refine ⟨t.legal,fun x v=> h v ▸ (t.pay x v), fun x v y p=>?_⟩; rw [←h v,←h p]; exact t.e x v y p
-- coherent lifts over next cell using SU extension. boundary transition from the two.Seam.Room ∀. Fits eq.
lemma lift {b:ℝ}(t:Seam D F G a)(h:Seam D F H b):∃ f:Ramp I m→E, Speed D f (a+b)∧EqOn (fun x=> sail (G x) (f x)) H D:=by
 have hX(i)(w:i∈D):Frame.Fits 0 (G i) (H i):=by simpa only [add_zero] using Frame.triangle (transpose (t.pay i w)) (h.pay i w)
 choose f v using hX; let l(i):= if p:i∈D then f i p else 1; have hl(i)(u:i∈D):sail (G i) (l i)=H i:=by unfold l; rw [dif_pos u]; exact dist_le_zero.mp (v i u)
 refine ⟨l,fun i u j w=>?_ ,fun i u=>hl i u⟩; rw [←sail_R (t.shape u)]; refine (dist_triangle _ (sail (G j) (l j)) _).trans ?_; rw [hl i u, dist_comm (sail (G j) _), sail_L, hl j w]; -- order tune. telescope
 have hp:= add_le_add (h.e i u j w) (t.e i u j w); exact hp.trans_eq (by rw [add_mul,add_comm])
end Seam
end Warm
end YM.CF.DPress.FD
