import YM.SU5.FiniteGaugeData.Nine.PivotF
import YM.SU5.FiniteGaugeData.Eight.Train
set_option autoImplicit false
set_option maxHeartbeats 460000
noncomputable section
namespace YM.CF.Window.Pivot
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric Laurent Bloch Next.Free
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Tenant Fock Tulip Dial Fir Ember Buffered Skye Scree Nacre
attribute [local instance] opCStarAlgebra
variable {N:Side} {i j:Axis}(a:Axis)(o: Cover)(p:ℤ)
open Brique Mir Phase RP
-- 3-axis SPATIAL parity, centers aligned chosen to preserve Ahead support and chiral tag positions. Spin & color NOT transformed.W.
abbrev pole (a:Axis)(o:Cover) := Buffered.plane a (o a)
def polarQ (o:Cover): Shape:= joinX (pole 2 o) (joinX (pole 1 o) (pole 0 o))
def tapeo (a:Axis)(p:ℤ)(N:Side) := prepU (Buffered.plane a p) 1 inert N
lemma palm_vis (x:Cover)(i:Axis): (polarQ o).motion x i = if i=3 then x i else 2*o i-x i:= by unfold polarQ; rw [palm,palm]; unfold pole; simp_rw [fling_move]; fin_cases i <;> (norm_num [Axis, Fin.ext_iff] <;> simp (config := {failIfUnchanged:=false}) [show (⟨2,by decide⟩:Fin 4)=2 from rfl] <;> omega)
lemma pole_inter (v:i≠j): joinX (pole i o) (pole j o)= joinX (pole j o) (pole i o):=by
 have he : (Signed.mirror i)*(Signed.mirror j)=(Signed.mirror j)*(Signed.mirror i):= by
    apply Signed.ext; · rfl
    funext i; simp only [Signed.mul_flip]; exact Bool.xor_comm ..
 have hv(a i:Axis)(x:a≠i):(Signed.mirror a).act (o i • step i :Cover)=o i • step i:=by funext j; unfold Signed.act Signed.mirror; by_cases p:a=j <;> simp_all [eq_comm]
 unfold pole Buffered.plane joinX; simp only [he,hv i j v,hv j i v.symm, add_comm]
private lemma adj (a b c:Shape) : joinX a (joinX b c)=joinX (joinX a b) c:=by unfold joinX; simp [Signed.act_mul,mul_assoc,add_assoc]
private lemma unitL (A:Shape):joinX (incX 1) A=A:=by simp [joinX,incX]
private lemma unitR (A:Shape):joinX A (incX 1)=A:=by simp [joinX,incX]
lemma polar_id : joinX (polarQ o) (polarQ o)=incX 1:=by
 let a:=pole 2 o; let b:=pole 1 o; let c:=pole 0 o
 have v(a:Axis): joinX (pole a o) (pole a o)=incX 1:= gaugeSquare ..; have hx: joinX (joinX b c) a=joinX a (joinX b c):=by rw [←adj, pole_inter o (by decide: (0:Axis)≠2),adj,pole_inter o (by decide:(1:Axis)≠ 2),←adj] -- let def
 change joinX (joinX a (joinX b c)) (joinX a (joinX b c))= _; rw [adj, ← adj a (joinX b c) a, hx, adj a a,v, unitL,adj, ← adj b c b,pole_inter o (by decide:(0:Axis)≠1),adj b b, v,unitL,v]
abbrev Port (o:Cover) (N:Side) := prepU (polarQ o) 1 inert N
abbrev piQu (o:Cover)(N:Side)(A:Op (Single N)):= twist (Port o N) A
lemma port_self(N:Side): Port o N * Port o N=1 := by rw [Port,kio, polar_id,mul_one, prep_one]
lemma port_split(N:Side): prepU (incX 1) ChiT inert N * Port o N= carR 0 (o 0) N*carR 1 (o 1) N *carR 2 (o 2) N:=by
 unfold Port carR; rw [kio,unitR,mul_one,kio,kio]; unfold polarQ pole; rfl
lemma flat_pull (i:Axis): Yg (pole i o) (1:Pane N)= 1:=by funext j; unfold Yg stir Lattice.pull Step.read; rw [Function.comp_apply]; split<;> simp -- tune
lemma sky_pull : Yg (polarQ o) (1:Pane N)=1:=by rw [polarQ,kor,kor,flat_pull,flat_pull,flat_pull]
lemma glue0 (A: Op (Single N)) : piQu o N (piQu o N A)=A:=by unfold piQu; rw [← Fock.twin, port_self,one_des]
variable (k:ℕ) (M:Tulip.Male)
local notation "G"=> prepU (incX 1) ChiT inert N
/-- Require purchases only from actual Finance. safe for enough phase; also at all Male with sufficient phase.
-/
structure Aptitude (k:ℕ)(N:Side) : Prop where
 paid(M:Tulip.Male)(a:Axis)(p:ℤ): twist (carR a p N) (funde k M N 1) = 1-funde k M N 1
lemma tall {k:ℕ}(p:1≤k):∃ m:ℕ,∀ N:Side,m≤N.val→Aptitude k N:=by
 obtain ⟨e,h,c,u⟩:= radiance k p; refine ⟨c,fun N v=> ⟨fun M a z=>?_⟩⟩; let V:= (1:Pane N); have he: stir inert (Buffered.plane a z) V=V:=by let o:Cover:=fun _=>z; exact flat_pull (N:=N) o a -- arg order o a?
 have hx:= funde_f (Buffered.plane a z) inert (pinLift a) (mirrorX a) V k p M e (u N v) (guard0 h.le); rw [he, show V= (1:Pane N) from rfl,profile_trivial] at hx; exact hx
lemma spin_sig (N:Side): prepU (incX 1) ChiT inert N*prepU (incX 1) ChiT inert N = 1:= by
 rw [kio,unitR, show ChiT*ChiT=1 from ?_, prep_one]; apply Subtype.ext; change ChiT.val*ChiT.val=(1:Op SpinIdx); rw [ChiT_vis,gammaOne];
lemma parity_edge (p: Aptitude k N): piQu o N (1-funde k M N 1)= twist (prepU (incX 1) ChiT inert N) (funde k M N 1):=by
 let G':= prepU (incX 1) ChiT inert N; apply (twist G').injective
 change twist (G) ((twist (Port o N)) (1-funde k M N 1))=twist (G) (twist (G) (funde k M N 1)); rw [← Fock.twin,port_split, ← Fock.twin,spin_sig,one_des]; simp only [Fock.twin,map_sub,map_one,p.paid M]; abel -- G'.eq not; tune
lemma pi_norm (P:Op (Single N)): ‖piQu o N P‖= ‖P‖:= twist_norm ..
#print axioms tall
#print axioms polar_id
end YM.CF.Window.Pivot
