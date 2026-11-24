import Gingham.Ruff.Pergola
import Gingham.Ruff.Bustle
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 500000
set_option maxRecDepth 4000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Gingham.Ruff
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal Classical
open Buffered Afterglow Satin Tapestry
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock
attribute [local instance] opCStarAlgebra
open Pastry


open Tower SlabMark
variable {p:BudgetPoint}{K:Calibration}

def frond (K:Calibration)(p:BudgetPoint):=
 ore (p.B+8+16*K.B.val) 0
lemma frond_sp(p:BudgetPoint)(K:Calibration): wisp p ⊆ frond K p:=fun _ h=>ore_up h (by omega)
lemma Frond_lobe {v:ℤ}(a:Axis)(p:BudgetPoint)
   (w: v=1∨v= -1): plow K a v (wisp p)⊆frond K p:=by
 intro x h; obtain ⟨y,t,rfl⟩:=plow_stays K a v _ h
 change y∈ore _ _ at t; rw [ore_mem, sub_zero, box_test] at t
 unfold frond; rw [ore_mem,sub_zero,box_test]
 constructor <;> intro i <;> rw [moves,ruler] <;> rcases w with (rfl|rfl)
   <;> have yL:= t.1 i <;> have yR:= t.2 i <;> split <;> omega

/-- None = Yoke, some a = current base (centered at 0 as a price). -/
abbrev Leaf:=Option Axis
abbrev Fleece (K:Calibration):=Leaf→Cluster K
abbrev leafpure : Leaf→Bool:=Option.isNone

def YokeTicket (z:ℂ)(F:Fleece K): Cluster K:= z • (F none)
def Ante (z:ℂ)(a:Axis)(F:Fleece K):= z • (F (some a))
def Spur(a:Axis)(v:ℤ)(F:Fleece K):Cluster K:=fun i=>relocate K a v (F (some a) i)

/-- Assemble (128), literally by full resolution shifts of currents. -/
def wingtip(z:ℂ)(F:Fleece K):Cluster K:=
 z • (F none + ∑a,(Spur a 1 F-Spur a (-1) F))

lemma wing_price {C:ℝ}{F:Fleece K}
   (t:∀a,Bouquet (wisp p) C (leafpure a) (F a))(z:ℂ):
 Bouquet (frond K p) (‖z‖*(9*C)) false (wingtip z F):=by
   have m(a v)(h:v=1∨v= -1):Bouquet (frond K p) C false (Spur a v F):=
      ((t (some a)).shiftW a v).expand (Frond_lobe a p h)
   have w : 9*C=C+(∑ _:Axis,(C+C)):= by rw [sum_const,card_univ,show Fintype.card Axis=4 from rfl]; simp only [nsmul_eq_mul];push_cast; ring
   rw [w]
   exact ( ((t none).dismount.expand (frond_sp p K)).addW
       (Bouquet.sumW univ (fun a _=>
         (m a 1 (.inl rfl)).subW (m a (-1) (.inr rfl))))).scaleW z

lemma wing_receipt{u:Side}(q:ruler K.B=2*(u.val:ℤ))
   (z:ℂ)(F:Fleece K)(i:Option ℕ)(m:Side):
 wingtip z F i m = z • GarlandBook.vase u (F none i m) (fun a=>F (some a) i m):=by
   have p₁:=ruler_offset K 1
   have p₂:=ruler_offset K (-1)
   have x: gaugeT K 1=(u.val:ℤ):=by omega
   have y: gaugeT K (-1)=-(u.val:ℤ):=by omega
   unfold wingtip GarlandBook.vase Spur relocate
   rw [x,y,Pi.smul_apply,Pi.smul_apply,Pi.add_apply,Pi.add_apply,Finset.sum_apply,Finset.sum_apply]
   rfl

def Ballet (l: List (Axis×ℤ))(X:Buffered.Family K): Buffered.Family K:=
 fun m=>maiden l (X m)
def Dancing (l:List (Axis×ℤ))(A:Cluster K):Cluster K:=
 fun i=>Ballet l (A i)
def stage: List (Axis×ℤ)→Finset Cover → Finset Cover
 | [],S=> S
 | (a,w)::l,S=> reflectedBox a w (stage l S)

variable {A:Cluster K}{C:ℝ}{H:Bool}{S:Finset Cover}
lemma dance_pose (b:Bouquet S C H A)(l):
 Bouquet (stage l S) C H (Dancing l A):= by
 induction l with
 | nil=> exact b
 | cons h _ ih=> exact ih.moveW h.1 h.2

lemma pose_scaled (l:List (Axis×ℤ))(z:ℝ){N:Side}(X:Mark N):
 maiden l ((z:ℂ)•X)= (z:ℂ)•maiden l X:=by
 induction l with
 | nil=>rfl
 | cons h l ih=>
   rcases h with ⟨a,w⟩
   rw [maiden,ih,maiden]
   ext1
   rw [reflMark, Pi.smul_apply,Fock.theta_smul, show star (z:ℂ)=(z:ℂ) by simp]; rfl

#print axioms wing_price

