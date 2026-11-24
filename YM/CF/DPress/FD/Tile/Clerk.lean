import YM.CF.DPress.FD.Tile.Cone
import YM.CF.BPress.Selector
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.DPress.FD
open Function Set Metric Filter SU MeasureTheory Ramp Row Frame
open scoped Topology BigOperators NNReal ENNReal Matrix.Norms.Frobenius Classical
attribute [local instance] Gauge.frobInner
variable {I K:Type*}[Fintype I][Fintype K]{m:ℕ}
namespace Frame
abbrev veil(K:Type*):=↥(Frame K)
lemma defaultP(K:Type*)[Nonempty K]: (fun _:K=>1)∈ Frame K:=⟨fun i=>plant 1,Classical.arbitrary K,1,rfl⟩
-- inheritance.Reserve
lemma reflex(a: ArrayF K):Fits 0 a a:=⟨1,by rw [sail_id,dist_self]⟩
lemma skip {A B:ArrayF K}{D:Finset K}(p: Fits 0 A B) (u:Warm.Skip A D): Warm.Skip B D:=by
 obtain ⟨i,h⟩:=p; rw [← dist_le_zero.mp h]; intro k t; rw [sail,u k t,zero_mul]
end Frame
namespace Warm
abbrev Paint(I K:Type*)(m:ℕ):= Ramp I m→ ArrayF K
abbrev Clear(D:Set (Ramp I m))(P:Ramp I m→ArrayF K)(Y:Finset K):Prop:=∀ i∈ D,Skip (P i) Y
abbrev Tends(U:Finset I)(F:Ramp I m→ArrayF K)(u:ℝ):Prop:= ∃ G, Seam (facet U) F G u
-- extension from proper faces.
lemma issue(a:ℝ)(h:0 ≤ a):∃ b:ℝ,a≤ b∧∀ {I K:Type*}[Fintype I][Fintype K] (m:ℕ),0 < m → ∀ (S:Finset I),S.Nonempty→S.card≤5→∀ (U:Ramp I m→ArrayF K), (∀ i⊂S,Tends i U a) →∀ (k:K)(T:Finset K), k ∉ T → (∀ i∈ boundary S, U i k=0) → Clear (boundary S) U T→ ∃ F:Ramp I m→ArrayF K, EqOn F U (boundary S) ∧ Clear (facet S) F T∧ Tends S F b:=by
 obtain ⟨b,hb,t⟩:= boundary_ride a h; let c:=4*Row.rad+4*b; refine ⟨c+a,le_add_of_nonneg_left (by unfold c; have h:= Row.alive; positivity),?_⟩; intro I K i k m p S H he F h s T ts u C; obtain ⟨G,g⟩:= t S he m p F h
 have hg(i)(p:i∈ boundary S):G i s=0:= Frame.skip (g.pay i p) (show Skip (F i) {s} from (fun j t=> (Finset.mem_singleton.mp t).symm ▸ u i p)) s (Finset.mem_singleton_self _)
 let G':= cones H s G; let Z(x):= if x∈boundary S then F x else G' x; have hx:MapsTo G' (facet S) (Frame K) := fun i v=> coat H p s G g.shape hg v; have z:0≤a:= ‹_›; have hz(i):i∈ boundary S →Z i= F i:= fun v=> if_pos v
 refine ⟨Z,fun i v=>hz i v,?_,G',⟨fun i v=>?_,fun i v=>?_,enlarge (widen_cost H p s G g.shape g.e hb) (Set.Subset.refl _) (le_add_of_nonneg_right z)⟩⟩
 · intro i v; unfold Z; split; next m=> exact C i m
   exact hem H p s G (fun i t=> Frame.skip (g.pay i t) (C i t)) ts v
 · unfold Z; split; next h=> exact g.legal h
   exact hx v
 unfold Z; split; next h=> unfold G'; rw [entry H p s G h (hg i h)]; exact g.pay i h
 next p=> exact Frame.reflex _
-- Borel law of F as a function of boundary data; away from valid arbitrary Frame.Tuple.S. pick candidates always in veil; may require restriction projection guarantee `reads only input on boundary` even where no valid. Achieve by explicit masked inputs to selector. Need Window.SecondCount.K.Path.Instances. 
local notation "Wf"=> (Paint I K m)
abbrev Pair(K:Type*)(I:Type*)(m:ℕ):= (Ramp I m→Frame.veil K) × (Ramp I m→Frame.veil K)
abbrev faceF (v:Ramp I m→Frame.veil K):Paint I K m:=fun i=> (v i).val
variable {S:Finset I}
scoped instance : MeasurableSpace Key := borel _ -- check conflicts.Instead scoped? 
end Warm
end YM.CF.DPress.FD
