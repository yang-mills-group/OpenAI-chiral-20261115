import YM.SU5.Interaction.Source.Reduction
import YM.SU5.Exchange.Stack.Manor
import YM.CF.Buffered.Mark
/-!
The asymmetric site cube `windmill` (length 2m along each matter
axis, counting multiplicities on the torus) may be used *both* in
(126) (`millEquation`,`inwardE`) and in the bra identity (127). Here
we pay its nonphysical local-operator support and bra identity. Also show
its block trace takes the per-site readout literally.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Swell
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Skye Jet Scroll Finset
open RG MeasureTheory Salt Metric Drapes Tulip Lat Branch Cube Tenant Rill
open Buffered
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Tap Levier Moto Oath Font Haro Spire Dial
variable {N : Side}
local notation "Ω" => Single N

theorem millQ_cut (o : Site N) : millQ o=cutM (modesIn N {node o}) := by
  rw [millSt]
  ext i j
  have hv : Font.place_x i=node i.1.1:=rfl
  simp only [Tye.stock,cutM,modes_at,Matrix.diagonal_apply]
  split_ifs <;> (simp_all [Finset.mem_singleton])

lemma cut_absorb {I : Type*} [Fintype I] [DecidableEq I] {S T : Finset I} (h : S ⊆ T) : cutM T*cutM S=cutM S ∧ cutM S*cutM T=cutM S := by
  unfold cutM
  rw [Matrix.diagonal_mul_diagonal,Matrix.diagonal_mul_diagonal]
  constructor <;> (apply congrArg Matrix.diagonal; funext i; by_cases u:i∈ S <;> first | simp only [if_pos u,if_pos (h u),mul_one] | simp only [if_neg u, mul_zero,zero_mul])

lemma wind_modes_aux (B : ℕ) (X : Support (More N)) (L : List Axis)
    (x : Site N) (p : ∀ z : Site N, separation x z ≤ L.length * (3*B) → node z∈X) :
    let V := cutM (modesIn N X)
    V * squareSum millQ B L x * V = squareSum millQ B L x := by
  let V:=cutM (modesIn N X)
  induction L generalizing x with
  | nil =>
    change V * millQ x * V = _
    simp_rw [squareSum, millQ_cut]
    obtain ⟨u,v⟩:=cut_absorb (modes_monotone (singleton_subset_iff.mpr (p x (by simp))))
    exact Eq.trans (congrArg (· * V) u) v
  | cons i L h =>
    change V * squareSum millQ B (i::L) x * V = _
    unfold squareSum stripSum; rw [mul_sum,sum_mul]; apply sum_congr rfl; intro k u
    let y:= moveSite (x-B • step i) i (k+1)
    refine h y (fun z v=> p z ((separation_triangle x y z).trans ?_))
    have he:= add_le_add (leap_strip x i B _ (mem_range.mp u)) v
    rw [List.length_cons, add_mul]
    simpa only [add_comm (3*B:_), one_mul] using he

theorem wind_support (o : Site N)(B : ℕ)(l : ℕ)(h:24*B ≤ l) :
    let V:= cutM (modesIn N (offsetMask l o))
    V*windmill o B*V=windmill o B := by
  refine wind_modes_aux B (offsetMask l o) _ o ?_
  simp only [List.length_ofFn]; intro z hz
  apply halo_spec.mpr; refine ⟨node o,mem_singleton_self _,?_⟩
  rw [Hove.ζdist]; omega

lemma mill_tick (x : Site N) : tickA N * millQ x=millQ x*tickA N:=by
  rw [touchP,millQ_cut,cutM,cutM,Matrix.diagonal_mul_diagonal,Matrix.diagonal_mul_diagonal]; congr 1; ext; exact mul_comm ..

lemma wind_tick (o : Site N)(m : ℕ) : Commute (tickA N) (windmill o m):=by
  have H(x:Site N)(l:List Axis): tickA N*squareSum millQ m l x=squareSum millQ m l x*tickA N:=by
    induction l generalizing x with
    | nil=> exact mill_tick _
    | cons i l h=> unfold squareSum stripSum; rw [mul_sum,sum_mul]; exact sum_congr rfl fun i _ => h _
  exact H o _

lemma barS0_bra (o : Site N) (B : ℕ) (x : Orbit N) :
    acts (star (barS0 N B o x)) (mateK N) = 0 := by
  unfold barS0
  rw [star_sub,star_smul,star_one,act_sub,act_smul,act_one, StressExchange.sandwichV _ (Cascade.plus_P _) (wind_tick o B) (mateK N) (tickB N),sub_self]

/-- This is the full Spin and Slot sum, all generations. -/
def siteRead (x : Site N)(S:Op Ω) : ℂ := ∑ i:SpinIdx,∑ j:SU.Slot, S ((x,i),j) ((x,i),j)

theorem mill_read (x : Site N)(A : Op Ω) : Matrix.trace (A * millQ x)=siteRead x A := by
  rw [millQ_cut,Matrix.trace]
  change ∑ i : (Site N × SpinIdx) × SU.Slot, (A*cutM (modesIn N {node x})) i i = _
  rw [Fintype.sum_prod_type]
  rw [Fintype.sum_prod_type]
  rw [sum_eq_single x]
  · apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _
    simp [Matrix.diag,cutM,Matrix.mul_diagonal]
  · intro y _ t; refine sum_eq_zero fun i _=> sum_eq_zero fun j _=>?_
    have he : node (N:=N) y≠ node x:= unaryN.ne t
    simp [Matrix.diag,cutM,Matrix.mul_diagonal,he]
  simp

theorem wind_read (x : Site N)(A : Op Ω)(B : ℕ) :
    Matrix.trace (A * windmill x B) = squareSum (fun y=> siteRead y A) B (List.ofFn (id:Axis→Axis)) x := by
  let f : Op Ω →+ ℂ := ⟨⟨fun v=>Matrix.trace (A*v),by rw [mul_zero,Matrix.trace_zero]⟩,fun v w=>by dsimp only; rw [mul_add,Matrix.trace_add]⟩
  change f (squareSum millQ B _ x)=_
  rw [squareMap f]; simp_rw [show ∀ y, f (millQ y)=_ from fun y=> mill_read y A]

end YM.CF.Swell
