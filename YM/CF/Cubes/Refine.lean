import YM.CF.Cubes.Transport
import YM.CF.Lattice.Joint
import YM.Lattice.Subdivision

/-! Refinement. Admissibility requires local elementary plaquettes only. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Cube
open YM.Lattice Lat SU
open scoped Matrix.Norms.L2Operator MatrixOrder Topology
attribute [local instance] opCStarAlgebra
variable {N : Side}
-- doubled so the fermion plane is through a gauge slice.
abbrev More (N : Side) := N*2
def assembly (N : Side) : Ratio N (More N) := ⟨2,rfl⟩
def node (x : Site N) : Site (More N) := (assembly N).root x + 1
lemma after (x : Site N) (i : Axis) : node (x+step i)=node x+step i+step i := by
  have he : (assembly N).root (step i)=step i+step i := by
    rw [Ratio.root_embed, ← wrap_step N, Ratio.embed_wrap,map_nsmul,wrap_step]; change 2 • _=_; rw [two_smul]
  unfold node; rw [map_add,he]; abel

variable {K : Type*} [Group K]
def links (U : RLink (More N) K) : RLink N K := fun ⟨x,i⟩ => U (node x,i) * U (node x+step i,i)
lemma links_cont [TopologicalSpace K] [IsTopologicalGroup K] : Continuous (links (N:=N) (K:=K)) :=
  continuous_pi (fun ⟨_,_⟩ => (continuous_apply _).mul (continuous_apply _))
lemma deep (U : RLink (More N) K) (x : Site N) (w : Walk) :
    travel (links U) x w=travel U (node x) (w.flatMap fun i => [i,i]) := by
  have hn (x : Site N) (p : Step) : node (x+p.vec)=node x+p.vec+p.vec := by
    rcases p with ⟨i,h|h⟩; exact after x _
    have H := after (x+ (-step i)) i; rw [add_assoc,neg_add_cancel,add_zero] at H
    change node (x+ -step i)=node x + -step i + -step i; rw [H]; abel
  have hp (x : Site N) (p : Step) : p.read (links U) x=travel U (node x) [p,p] := by
    rcases p with ⟨i,h|h⟩
    · change U _*U _=_; simp only [travel,mul_one]; rfl
    change (U _ * U _)⁻¹=_; simp only [travel,Step.read,mul_one,Bool.true_eq,ite_true]
    change (U (node (x-step i),i)*U (node (x-step i)+step i,i))⁻¹=
      (U (node x-step i,i))⁻¹*(U (node x+ -step i-step i,i))⁻¹
    have he := after (x-step i) i; rw [sub_add_cancel] at he
    rw [he,mul_inv_rev,add_sub_cancel_right, show node (x-step i)+step i+step i+ -step i-step i=node (x-step i) by abel]
  induction w generalizing x with
  | nil => simp [travel]
  | cons i w ih =>
    rw [travel,List.flatMap_cons,travel_append,hp,ih,hn]; rfl
lemma links_g (U : RLink (More N) K) (p : Site (More N) → K) : links (gauge p U)=gauge (p ∘ node) (links U) := by
  funext ⟨x,i⟩; unfold links Lattice.gauge; simp [after,mul_assoc]
lemma absorb {I : Type*} [Fintype I] [DecidableEq I] (R : K →* UNI I) (U : RLink (More N) K) {e : ℝ}
    (he : 0≤e) (h : PlaqBound R U e) : PlaqBound R (links U) (256*e) := by
  intro x i j H; rw [deep]
  let w := (square i j).flatMap fun d=> [d,d]
  have heq : stop (0:Cover) w=stop (0:Cover) [] := by simp [w,square,stop]; abel
  have hx := near_hop he h (node x) w [] heq
  change ‖(R (travel U (node x) w)).val-1‖ ≤ _
  unfold cmp at hx
  rw [travel,map_one,show (1:UNI I).val=1 from rfl, show w.length=8 from rfl] at hx
  norm_num at hx ⊢; exact hx

def firstF : E →* UNI F where
  toFun g := ⟨fund g,fund_U g⟩
  map_one' := Subtype.ext fund_one
  map_mul' g h := Subtype.ext (fund_mul g h)
-- impose in both defining and matter reps. Still local elementary cap.
def Guard (U : Bkg N) (e : ℝ) := PlaqBound firstF U e ∧ PlaqBound matter U e
lemma Guard.shrink {U : Bkg N} {e f : ℝ} (h : Guard U e) (g : e ≤ f) : Guard U f :=
  ⟨fun i j k he => (h.1 i j k he).trans g, fun i j k he => (h.2 i j k he).trans g⟩
lemma Guard.children {U : Bkg (More N)} {e : ℝ} (h : Guard U e) (g : 0≤e) : Guard (links U) (256*e) := ⟨absorb _ _ g h.1,absorb _ _ g h.2⟩
lemma Guard.cov {U : Bkg N} {e : ℝ} (h : Guard U e) (t : Site N → E) : Guard (gauge t U) e := ⟨plaq_gauge _ t U h.1,plaq_gauge _ t U h.2⟩
lemma turn_sub (g : E) (x y : Vect) : turn g (x-y)=turn g x-turn g y := map_sub ..
lemma turn_seq (g h : E) (x) : turn (g*h) x=turn g (turn h x) := act_mul ..
lemma turn_inv_g (g : E) (x) : turn g⁻¹ (turn g x)=x := by rw [←turn_seq,inv_mul_cancel,turn,fund_one,act_one]
lemma Guard.descend {U : Bkg (More N)} {v : Site (More N) → Vect} {e : ℝ} (g : Slow U v e) : Slow (links U) (v ∘ node) (2*e) := by
  intro x i; simp only [Function.comp_apply, after, links, turn_seq]
  let a := U (node x,i)
  let y := node x+step i
  let z := turn (U (y,i)) (v (y+step i))
  change ‖turn a z-_‖ < _
  apply lt_of_le_of_lt (norm_sub_le_norm_sub_add_norm_sub _ (turn a (v y)) _) _
  rw [← turn_sub,turn_norm,two_mul]; exact add_lt_add (g y i) (g _ _)
end YM.CF.Cube
