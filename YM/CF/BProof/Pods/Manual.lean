import YM.CF.BProof.Payment.Sphere
import YM.CF.BProof.Pods.Cup

/- Gig assignments: one adjoining N Mark label per column, and Framed Sum forbids every
Glyph variation in D. Counting retained. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BProof.Pods.Manual
open Function Filter MeasureTheory Relation Finset RG Law
open Lattice Prox Grid Angular Angular.Yard Release Payment Mapping
open scoped Topology BigOperators Classical ENNReal
variable {s m N:Side}(Y:Yard s)
abbrev Key:= Y.Col→Fin 5
abbrev Marked(p:Y.Glyph): Prop:=∀ i,Y.D i→p i=0
def marks(p:Key Y):Y.Glyph:= fun i b=> if Y.D i then 0 else p (location Y i b.1,b.2)
abbrev nIndex (i:Y.Index) := if Y.D i then i+1 else i
abbrev nSide (i:Y.Index) : Bool := if Y.D i then false else true
lemma wall (i:Y.Index):¬ Y.D (nIndex Y i):=by
 unfold nIndex; split; next h=>exact fun p=> Y.next i |>.1 p h
 next h=> exact h -- tune
lemma slide (i:Y.Index): location Y (nIndex Y i) (nSide Y i)=i:=by unfold nSide location nIndex; split <;> rename_i h <;> simp [h]
lemma round (b:Bool)(i:Y.Index)(h:¬Y.D i): nIndex Y (location Y i b)=i∧ nSide Y (location Y i b)=b:=by cases b<;>simp [nIndex,nSide,location,(Y.prev i).2 h,h] -- tune prev
lemma marks_m (p:Key Y): Marked Y (marks Y p):=fun i t=>funext fun _=> if_pos t
def gets(p:Y.Glyph):Key Y:= fun y=> p (nIndex Y y.1) (nSide Y y.1, y.2)
lemma gets_m(p:Key Y): gets Y (marks Y p)=p:=by
 ext i; unfold gets marks; rw [if_neg (wall Y i.1), slide]; -- tune reduce Prod
lemma ruling(p:Y.Glyph)(k:Marked Y p): marks Y (gets Y p)=p:=by
 funext i ⟨a,b⟩; unfold marks; split; · rename_i h; rw [k _ h]; rfl
 rename_i h; unfold gets; dsimp only; rw [(round Y a _ h).1,(round Y a _ h).2]
abbrev Cart:= Y.Col→ Bool
def cart : Cart Y ≃ Finset Y.Col:=
 ⟨fun f=> Finset.univ.filter fun i=> f i,fun p i=>decide (i∈ p),fun p=> by ext i; simp,fun i=>by ext a; simp⟩ -- tune Bool
abbrev Marbles:= Key Y × Cart Y
abbrev lots (b:Marbles Y) : Finset Y.Col:= cart Y b.2
abbrev code(b:Marbles Y):Y.Glyph:=marks Y b.1
section
variable (Y:Yard (Cube.More N))(y:ℝ)
abbrev Disney:= Marbles Y × Dish Y
abbrev box (x:Disney Y) : Sphere Y:= wrap Y (code Y x.1) (lots Y x.1) x.2
def name : Measure (Disney Y):= (Measure.count.prod Measure.count).prod (chase Y y)
lemma name_fin(p:xi y≤1): IsFiniteMeasure (name Y y):=by haveI:= chase_p Y y p; unfold name; infer_instance
@[fun_prop] lemma box_m : Measurable (box Y):= measurable_from_prod_countable_right (fun i=> wrap_m Y (code Y i) (lots Y i)) -- tune
variable (F:Sphere Y→ℂ)(p:xi y≤1)(f:Envelope F)(h:∀ x:Sphere Y,¬ Marked Y x.1.mood → F x=0)
include p f h
lemma power : (∫ x,F x ∂globe Y y)=∫ x,F (box Y x) ∂name Y y :=by
 haveI:=chase_p Y y p; haveI q(j:Y.Glyph)(s:Finset Y.Col):=globe_p Y y j s p; rw [category Y y p F f]; let G(p:Y.Glyph)(S:Finset Y.Col):= (∫ x,F x ∂globeP Y y p S)
 have hp:(∑ p:Y.Glyph,∑ Z:Finset Y.Col,G p Z)=∑ p:Key Y, ∑ q:Cart Y,G (marks Y p) (cart Y q):=by
    conv_rhs=>congr; rfl; intro p; rw [Equiv.sum_comp (cart Y)] -- tune
    symm; rw [←Finset.sum_subset (s₂:=Finset.univ) (s₁:=Finset.univ.filter (Marked Y)) (filter_subset ..)] -- tune target order
    swap; · intro p' t hp; apply sum_eq_zero; intro Z _; have he:¬Marked Y p':= fun l=>hp (mem_filter.mpr ⟨t,l⟩); unfold G; rw [←Law.apply_pres (sampled Y y p' Z) f.meas]; simp only [show ∀ x:Dish Y,F (wrap Y p' Z x)=0 from fun _=>h (wrap Y p' Z _) he,integral_zero];
    apply sum_nbij' (marks Y) (gets Y); intro x p; exact mem_filter.mpr ⟨mem_univ _,marks_m Y x⟩; intro i _; exact mem_univ _; intro i _; exact gets_m Y i; intro i p; exact ruling Y i (mem_filter.mp p).2; exact fun _ _=> rfl
 change (∑ p:Y.Glyph, ∑ x:Finset Y.Col,G p x)=_; rw [hp,name,integral_prod]; swap; · exact Law.pay (Law.pull f (box_m Y))
 rw [integral_prod (f:=fun u:Marbles Y=> ∫ x,F (box Y (u,x)) ∂chase Y y), count_asks]; swap; · exact Law.pay (Law.fund _ (Law.pull (f:=F) f (box_m Y)))
 apply sum_congr rfl; intro i h; rw [count_asks]; apply sum_congr rfl; intro j _; exact (Law.apply_pres (sampled Y y _ _) f.meas).symm
end
end YM.CF.BProof.Pods.Manual
