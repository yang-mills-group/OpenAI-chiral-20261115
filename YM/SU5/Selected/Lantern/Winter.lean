import YM.SU5.Selected.Lantern.Wicks
import YM.SU5.FiniteGaugeData.Pannier.TallPea
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 450000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Pannier.Chancel.Lantern
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye RG
open Crest.Airy
open Reed (Fine)
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
local notation "I"=>Complex.I
variable {T q:Type*}[Fintype T][DecidableEq T][Fintype q][DecidableEq q]
  {n:Side} (M:Tulip.Male) {j k w:ℕ} (b:Bool){γ ε δ ξ η R E:ℝ}
  (p: Winter j δ n γ w ε){U : Pane n} (h:Guard U δ) (Z:T→ WRect (Single n) q)
  (A S:T→ Finset (Seat n))(g:∀ i,S i⊆A i)(l:∀ i,Distant w ((A i)ᶜ) (S i))
  (d:Pairwise (Disjoint on A))
local notation "F" => sp b j M U
local notation "G" a:max => modesIn n (S a)
local notation "K" a:max => modesIn n (A a)
private lemma modes_disjoint {S T:Finset (Seat n)}(h:Disjoint S T): Disjoint (modesIn n S) (modesIn n T) := disjoint_left.mpr (fun i x y=> disjoint_left.mp h ((modes_at ..).1 x) ((modes_at ..).1 y)) -- binder implicit
include p h g l d
-- Assemble. arbitrary copies, absolute off-block estimate supplied by same Winter; multiplicity one by disjointness, no geometry assumption across copies except each stays x-dist from its own boundary and B boxes disjoint; number of packets unconstrained.
theorem pooling (Z₀:∀ i, Contained (G i) (Z i))
    (z:∀ i, ‖( (1-F:Op (Single n)))* Z i‖≤ ξ) (e:∀ i, ‖Z i‖≤ R) (r:0≤R) (x:0≤ξ): ‖( (1-F:Op (Single n)))*globe Z‖ ≤ ξ+ε*R:=by
 classical
 let P':=1-F; let I0(i:T):= Vo (A i); let I'(i:T):=1-I0 i; let Q(i:T):=Vo (S i); let H:= ∑ i:T, I' i*P'*Q i; let V:=globe Z
 have hg{a:T}: Q a*Z a= Z a:=Z₀ _
 have hu{a q:T}(u:a≠q): Q a*Z q=0:= (Z₀ _).away (modes_disjoint ((d u).mono (g a) (g q)))
 have hv: H*V=globe (fun i=> I' i*P'*Z i):=by
    unfold V; rw [globe_action]; congr 1; funext i; unfold H; rw [ships_add,sum_eq_single i]; rw [Matrix.mul_assoc,hg]; intro j _ u; rw [Matrix.mul_assoc,hu u, Matrix.mul_zero]; simp -- tune parenthesized
 have hf: Pairwise (Disjoint on (fun i=> K i)):= fun a q h=> modes_disjoint (d h) -- implicit binder
 have hk(i:T): Contained (K i) (I0 i*P'*Z i):=by
    unfold Contained; rw [←Matrix.mul_assoc,←Matrix.mul_assoc, show cutM (K i)*I0 i=I0 i from (cutM_idp _).isIdempotentElem]
 have hZ:‖V‖ ≤ R:=globe_cost r (fun i=> (Z₀ i).grows (modes_monotone (g i))) hf e
 have hP:‖globe (fun i=> I0 i*P'*Z i)‖≤ξ:= globe_cost x hk hf (fun i=> by rw [Matrix.mul_assoc]; exact bound_shift (cutM_idp _) (z i))
 suffices ht: ‖H‖ ≤ ε by
    change ‖P'*V‖ ≤ _; rw [show P'*V= globe (fun i=> I0 i*P'*Z i)+H*V from ?_]; exact (norm_add_le ..).trans (add_le_add hP (charge_mul ht hZ))
    rw [hv]; unfold V; rw [globe_action,←globe_add]; congr 1; ext1 t; unfold I'; rw [Pi.add_apply,←Matrix.add_mul,←Matrix.add_mul, add_sub_cancel, Matrix.one_mul]
 apply p.vent (!b) M U h; intro i k
 -- I' mask off-broad, uses 1-F = str(!b)
 have how : hand (!b) (spar j M U)= P' := including b _
 have he(a:T): I' a*P'*Q a=Vo (A a)ᶜ * P'*Q a:=by rw [Vo_neg]
 have ht(a:T): (I' a*P'*Q a) i k= if node i.1.1∉ A a ∧ node k.1.1∈ S a then P' i k else 0 := by
    rw [he]; unfold Vo Q Vo cutM; rw [Matrix.mul_diagonal,Matrix.diagonal_mul]; split_ifs <;> simp_all
 by_cases q0:∃ a:T,node k.1.1∈ S a∧ node i.1.1∉ A a
 · obtain ⟨a,t,h⟩:= q0; refine Or.inr ⟨l a _ (mem_compl.mpr h) _ t,?_⟩
   unfold H; rw [how, Matrix.sum_apply, sum_eq_single a,ht a,if_pos ⟨h,t⟩]; intro t' _ u; rw [ht, if_neg (fun p=> disjoint_left.mp (d u) (g t' p.2) (g a t))]; simp
 left; unfold H; rw [Matrix.sum_apply]; exact sum_eq_zero fun a _=> (ht a).trans (if_neg (fun v=> q0 ⟨_,v.2,v.1⟩))

-- Pass active orientations b and cost/debris now. doesn't assume G support traces etc. atone. `x's norm ≤1` (not per-column premise).
theorem resupply (X:T→WRect (Single n) q) (T':Finset (Seat n))(Q₀:FC (Single n))
    (u:∀ i:T,Contained (G i) (X i))(Z₀:∀ i, Contained (G i) (Z i))
    (d₀:∀ i, Disjoint (A i) T')(P₀:IsStarProjection (spar j M U))
    (P':∀ i, hand (!b) (cutM (Tset n))*X i=X i)
    (z:∀ i, ‖( (1-F:Op (Single n)))* Z i‖≤ ξ) (e₁:∀ i, ‖Z i‖≤ R) (e₂:∀ i, ‖X i‖≤1)
    (e:∀ i, ‖(X i)ᴴ*(Z i)-1‖≤η) (q₀:Fine (Tset n) (modesIn n T') false Q₀)
    (r:0<R)(zz:0≤ξ)(gg:0≤η) (v₁: η+(ξ+ε*R) ≤ 1/3) (v₂:ξ+ε*R+(R*2)*(η+(ξ+ε*R)) ≤ E^3) :
    ∃ Y:T×q→ Ket (Single n), Chancel.Sheet (Tset n) (modesIn n T') (spar j M U) Q₀ b (fun i=> col (X i.1) i.2) Y (fun i=> col (Z i.1) i.2) (2*R) E:=by
 have hf: Pairwise (Disjoint on (fun i=> G i)):= fun a q h=> modes_disjoint ((d h).mono (g _) (g _)) -- implicit
 let H₀:=globe (fun i=> X i); let H₁:=globe (fun i=> Z i); exact support_w _ P₀ (X:=H₀) (Z:=H₁) (by unfold H₀; rw [globe_action]; exact congrArg globe (funext P')) (globe_hold (fun i=> (Z₀ i).grows (fun j t=> mem_compl.mpr (fun z=> disjoint_left.mp (modes_disjoint ((d₀ i).mono_left (g i))) t z)))) q₀ v₁ v₂ (globe_cost zero_le_one u hf e₂) (globe_cost r.le Z₀ hf e₁) (globe_grant gg hf u Z₀ e) (pooling M b p h Z A S g l d Z₀ z e₁ r.le zz)
end YM.CF.Pannier.Chancel.Lantern
open YM.CF.Pannier.Chancel.Lantern
#print axioms pooling
#print axioms resupply
