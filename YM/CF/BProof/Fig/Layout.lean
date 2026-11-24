import YM.CF.BProof.Fig.Moon
import YM.CF.BProof.Align.Hil

/-! Ordered frames specialize Page to Single N. time translation for B-gaps in
axis zero direction. Fourier diagonalization gen all axes. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Fig
open Function Filter Fock Finset Branch Tenant Cube SU Tulip Lat Lattice Dial Spin Align Stint
open Fir Laurent Rush Bloch Next.Free BZ
open scoped Topology BigOperators Matrix MatrixOrder InnerProductSpace Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {N:Side} {t:Bool}
def liftA (A: Op (Page N)): Op (Single N):= A ⊗ₖ (1:Stamp)
namespace liftA
lemma mono {A B: Op (Page N)}(h:A≤B): liftA A ≤ liftA B:=by
 rw [Matrix.le_iff,show liftA B-liftA A=liftA (B-A) from ?_]; exact (Matrix.le_iff.mp h).kronecker (Matrix.nonneg_iff_posSemidef.mp (zero_le_one' Stamp)) -- tune
 ext a b; simp [liftA,sub_mul]
lemma one :liftA (1:Op (Page N))=1:= Matrix.one_kronecker_one
lemma prod (A B:Op (Page N)): liftA (A*B)=liftA A * liftA B:=by unfold liftA; rw [op_kron_mul,mul_one]
lemma sub (A B:Op (Page N)): liftA (A-B)=liftA A - liftA B:=by ext i j; simp [liftA,sub_mul] -- tune
lemma smr (c:ℝ)(A:Op (Page N)):liftA (c • A)=c • liftA A:=by ext i j; simp [liftA]; ring
lemma ast (A:Op (Page N)): liftA (star A)=star (liftA A):=by unfold liftA; rw [op_star_kron,star_one]
def tone (A: UNI (Page N)): UNI (Single N):=⟨liftA A.val, Matrix.kronecker_mem_unitary A.property (unitary _).one_mem⟩
lemma twists (A: UNI (Page N))(B:Op (Page N)): liftA (twist A B)=twist (tone A) (liftA B):=by rw [twist_formula,twist_formula,prod,prod,ast]; rfl
end liftA
-- site lines translate
abbrev hop (N:Side)(i:Axis):Op (Page N):= jump (Lat.advance i) fun x:Site N=> seam (anticut N) x i • 1
def axisShift (N:Side)(i:Axis): Op (Single N):= liftA (Fig.hop N i)
lemma hop_formula (x y:Site N)(a b:SpinIdx)(i:Axis): Fig.hop N i (x,a) (y,b)= if Lat.advance i x=y then seam (anticut N) x i*(1:Op SpinIdx) a b else 0:= rfl -- tune
lemma axis_shift (i:Axis)(R:Single N): axisShift N i R= fun y=> if Lat.advance i R.1.1=y.1.1 then seam (anticut N) R.1.1 i*(1:Op (SpinIdx×Slot)) (R.1.2,R.2) (y.1.2,y.2) else 0:=by
 ext1 T
 obtain ⟨⟨x,b⟩,a⟩:=R; obtain ⟨⟨y,d⟩,c⟩:=T; unfold axisShift liftA; simp only [Matrix.kronecker_apply,hop_formula,ite_mul,zero_mul]; by_cases h:b=d <;> by_cases g:a=c <;> simp [Matrix.one_apply,h,g]
def bandSites (M: Support N)(u:Bool) := univ.filter (fun i:Single N=> i.1.1∈M ∧ i.1.2∈spHalf u)
@[simp] theorem mem_band (M:Support N)(u:Bool)(i:Single N): i∈bandSites M u ↔ i.1.1∈M ∧ i.1.2∈spHalf u:=by simp [bandSites]
def bandCut (M:Support N)(u:Bool): Op (Single N):= cutM (bandSites M u)
def cutSpin (N:Side)(u:Bool): Op (Page N):= jump (Equiv.refl _) (fun _=> pill u)
lemma lift_spin (u:Bool): liftA (cutSpin N u)= bandCut (univ:Support N) u:=by
 unfold cutSpin; ext ⟨⟨x,a⟩,b⟩ ⟨⟨y,c⟩,d⟩; by_cases h:x=y <;> by_cases g:a=c <;> by_cases e:b=d <;> simp [liftA,jump_apply,bandCut,cutM,pill,h,g,e]
lemma ticka (N:Side): bandCut (univ:Support N) true = tickA N := by
 ext ⟨⟨x,a⟩,b⟩ ⟨⟨y,c⟩,d⟩; change _=cutM (upperP N) (x,a,b) (y,c,d); by_cases h:x=y <;> by_cases g:a=c <;> by_cases e:b=d <;> simp [bandCut,cutM,h,g,e,upperP,spHalf]
lemma dusk (N:Side) : bandCut (univ:Support N) false=1-tickA N:=by
 rw [← ticka,bandCut,bandCut,← dim_cut, show bandSites (univ:Support N) false= (bandSites (univ:Support N) true)ᶜ from (by ext i; simp [spHalf])]
lemma cutMono (M:Support N)(u:Bool): bandCut univ u * bandCut M u = bandCut M u:=by
 apply op_columns; intro i; rw [act_mul,bandCut,bandCut,cut_basis]; split; rename_i H; rw [cut_basis,if_pos (show i∈bandSites univ u from by have ht:=(mem_band ..).mp H; simpa using ht.2)]; exact map_zero _
end YM.CF.BProof.Fig
