import YM.CF.BProof.Hearth.Pace
import YM.CF.BProof.Stint.Credit
/-! B-Pproj admissible field domain (c spacer fixed in purchases). -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Hearth
open Function Filter Fock Finset Branch Tenant Cube SU Tulip Lat Lattice Dial Spin Stint Fig Align
open scoped Topology BigOperators Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {N:Side} {a b l r d c:ℝ} {j:ℕ}
variable (P:Ready j a b l r) (F:Core j a b l r N)
structure Age (P:Ready j a b l r)(F:Core j a b l r N)(d:ℝ) : Prop where
 minN:P.minN≤N.val
 shelter:d≤P.hT
 pos : 0≤d
variable {P F}
namespace Age
variable (h:Age P F d)
include h
lemma rise (x:Counter (More N) d)(g:Geometry N) : F.θ (gauge g x.val) 1= twist (tradew N g) (F.θ x.val 1):=by obtain ⟨p,H⟩:= Core.earnsθ P; exact (H F h.minN h.shelter).cov.frame g x -- tune
lemma healthy (x:Counter (More N) d): IsStarProjection (F.θ x.val 1):= F.θp P x.val h.minN h.shelter x.property 1
lemma board (x:Counter (More N) d)(g:Geometry N){S:Support N}(q:BoardH F x.val S c): BoardH F (gauge g x.val) S c:=by
 let U:= tradew N g; have ht (u:Bool): twist U (bandCut S u)=bandCut S u:=by rw [twist_formula,(blockG S g u).symm.eq,mul_assoc,U.property.2,mul_one]
 have he:=twist_mono U q.holes; have hh:=twist_mono U q.dots; rw [map_smul,map_mul,map_mul,ht,←h.rise x g] at he; rw [map_smul,map_mul,map_mul,ht,map_sub,map_one,←h.rise x g] at hh; exact ⟨h.healthy ⟨_,x.property.cov g⟩,q.p,q.q,q.pq,he,hh,q.nice,q.bare⟩ -- q definalias
end Age
abbrev Piles (N:Side):=Support N
-- export discrete topology scoped
scoped instance (N:Side): TopologicalSpace (Piles N):= ⊥
scoped instance (N:Side): DiscreteTopology (Piles N):= ⟨rfl⟩
def dots (x:Site (More N)) (S T: Piles N):ℝ:= if x∈spot S ↔ x∈spot T then 0 else 2
lemma dots_pos (x:Site (More N))(S T:Piles N):0 ≤ dots x S T:=by unfold dots; split <;> norm_num
def apron(N:Side)(a d:ℝ): Feet N (Counter (More N) d × Piles N):= (iron N a d).double (fun _=>id) dots dots_pos
lemma kiln (N:Side)(a d:ℝ): Feet.Skid (iron N a d) (apron N a d) Prod.fst := Feet.doubleSkid ..
-- cuts allowed in any gauge
abbrev InRoad (F:Core j a b l r N)(d c:ℝ) := {p: Counter (More N) d × Piles N // BoardH F p.1.val p.2 c }
def usher {D:Type}(p:Feet N D)(s:D→ Prop)(Y:∀ g x,s x→s (p.st.drive g x)): Feet N (Subtype s) where
 st:={ F:=p.st.F
       home := p.st.home
       drive:=fun g x=>⟨p.st.drive g x.val,Y g x.val x.property⟩
       eval:=fun S x y=>p.st.eval S x.val y.val
       pos:= fun S x y=>p.st.pos S x.val y.val
       includeV:=fun h x y=> p.st.includeV h x.val y.val }
 town:=p.town
 index:=p.index
lemma usherG {D:Type}[TopologicalSpace D](p:Feet N D)(s:D→ Prop)(H:∀ g x,s x→s (p.st.drive g x)):Feet.Skid p (usher p s H) Subtype.val:=⟨continuous_subtype_val,fun _ _=>rfl,fun _ _ _=>le_rfl⟩
namespace Age
def beam (h:Age P F d)(c:ℝ): Feet N (InRoad F d c):=usher (apron N P.hT d) _ (fun i x v=> h.board x.1 i v)
lemma beamSkid (h:Age P F d)(c:ℝ): Feet.Skid (apron N P.hT d) (h.beam c) Subtype.val:=usherG ..
end Age
end YM.CF.BProof.Hearth
