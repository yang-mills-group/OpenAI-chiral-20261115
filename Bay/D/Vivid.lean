import Bay.D.Stalk
import YM.AnalyticBridge.VERIFIED_RESET_STEP.Lines
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Bay
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet Scroll Finset Palot Cadre Vow
open RG MeasureTheory Rue
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Tap Levier Thera Oath Font Spire Dial Rill
open Kennel Swell

namespace D
open Exterior Precision Nacre
open scoped ContDiff

open Work.F03 Extra.Iteration.Channel Zephyr.Chern Laurent

variable {n N:Side}{k:ℕ}{o:Seat N}

def paint(i:Pureton):ℝ:= flux (step i.1.val.1) (step i.1.val.2) * yolk i.2
lemma painted {m:ℕ} (i:Cella (More N)) (t:4*m+1<N.val)
  (h:separation i.1 1 ≤ m):brine (shear (Zephyr.Chern.stream N)) i = paint i.2:=by
 let x:=i.1
 let a:=i.2.1.val.1
 let b:=i.2.1.val.2
 let F:Edge (Seat N)→Øc:=fun j=>(Zephyr.Chern.stream N j) • yolk
 have e: collect group (shear (Zephyr.Chern.stream N))= F:=funext fun j=>by
    change Zephyr.Chern.stream N ((bondBody _).symm (bondBody _ j)) • yolk=_
    rw[Equiv.symm_apply_apply]
 have hx (u):rel (x+step u)=rel x + step u:= by rw [←rel_add _ m (by rw[step_size];exact t) _ h,wrap_step]
 rw[brine, faceCurl, ← fundamental,e,AnalyticBridge.VerifiedReset.Square.cochain_square]
 -- (F (x+...)...)
 change (F (x+step a,b)-F (x,b)-(F (x+step b,a)-F (x,a))) i.2.2=flux (step a) (step b)*yolk _
 simp only [PiLp.sub_apply, F,PiLp.smul_apply,smul_eq_mul,Zephyr.Chern.stream,twistAt,hx,
    flux_left, flux_switch (step b) (step a)] -- grouped? flux_left expands 
 ring

/-- Constant-curvature coefficient matrix. -/
def drain (A:Icey (Cella n))(i j:Pureton):ℂ:=∑ x : Site n, ∑ y:Site n, A (x,i) (y,j)
def mass(A : Icey (Cella n)) : ℝ:=∑ i,∑ j, ‖drain A i j‖^2
def sheet(n:Side)(v:Pureton→ℝ):Cella n→ℝ:=v ∘ Prod.snd
lemma pour (A:Icey (Cella n)) (v w:Pureton→ℝ):
    swirl A (sheet n v) (sheet n w) = swirl (drain A) v w:=by
 unfold swirl drain

 let F (x y:Site n)(i j:Pureton) := (v i * w j) • A (x,i) (y,j)
 -- rearrange RHS to i,x,y,j ; then x,i,y,j
 rw [Fintype.sum_prod_type]
 simp_rw [Finset.smul_sum]
 -- j x y → j y x → ...
 symm
 calc
   _ = ∑ i,∑ x,∑ y, ∑ j,F x y i j:= sum_congr rfl (fun i _=>sum_comm.trans (sum_congr rfl fun x _=>sum_comm))
   _ = _ :=sum_comm.trans (sum_congr rfl fun x _=>sum_congr rfl fun i _=> (Fintype.sum_prod_type (fun j:Cella n=> (v i * w j.2) • A (x,i) j)).symm)

/-- rough slicing constants on top. -/
def bytes:ℝ:=(1+∑i,|paint i|)^2
lemma bytes_pos :0<bytes:=by unfold bytes;have:=ton; positivity
variable {A:Icey (Cella n)}
lemma fill (i j:Pureton) : ‖drain A i j‖^2≤ mass A:=
 (single_le_sum (f:=fun k=>‖drain A i k‖^2) (fun _ _=>sq_nonneg _) (mem_univ j)).trans
     (single_le_sum (f:=fun x=>∑ k,‖drain A x k‖^2) (fun _ _=>by positivity) (mem_univ i))

lemma pigment :
   (swirl (drain A) paint paint).re ≤ bytes * Real.sqrt (mass A):=by
 let t:=∑ i,|paint i|
 have ht:0≤t:=by unfold t;positivity
 have h₁(i j):‖drain A i j‖≤ Real.sqrt (mass A):=(Real.le_sqrt_of_sq_le (fill i j))
 have h₂: ‖swirl (drain A) paint paint‖≤t^2 *Real.sqrt (mass A):=by
   unfold t; rw [sq]; simp_rw [mul_sum,sum_mul]
   -- order?
   exact (norm_sum_le ..).trans (sum_le_sum fun i _=>
      (norm_sum_le ..).trans (sum_le_sum fun j _=>by 
         rw[norm_smul,Real.norm_eq_abs,abs_mul,mul_comm |paint i|]
         exact mul_le_mul_of_nonneg_left (h₁ i j) (by positivity)))
 refine ((Complex.re_le_norm _).trans h₂).trans (mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _))
 change t^2≤(1+t)^2
 nlinarith only [ht]

lemma brightSheet{δ:ℝ}(t:0≤δ)
    (g:δ≤(splash A (sheet n paint)).re):
    (δ/bytes)^2 ≤ mass A:=by
 have hz:0≤ mass A:=by unfold mass; positivity
 rw[splash,pour] at g
 have h:δ/bytes ≤ Real.sqrt (mass A):=(div_le_iff₀' bytes_pos).mpr (g.trans pigment)
 rw [←Real.sq_sqrt hz]
 -- occurrence rhs mass only lhs δ.
 exact pow_le_pow_left₀ (div_nonneg t bytes_pos.le) h _

variable {p:BudgetPoint}{f:Pane N→ℂ}{A:Icey (Cella (More N))}{r L δ:ℝ}{c:ℂ}
/-- Constant curvature test exact on cells, no seam error. -/
lemma vivid (u:Skin p o k r L f c A)(t:0<r)
   (w: 4*(k+3+separation o 1)+1<N.val)
   (b:gem (f ∘ Zephyr.Chern.petals (Zephyr.Chern.stream N)) δ)
   (e:0≤δ):
    bud (f ∘ Zephyr.Chern.petals (Zephyr.Chern.stream N)) 2 =
       splash A (sheet _ paint) ∧
    (δ/bytes)^2 ≤ mass A:=by
 have he:Set.EqOn (brine (shear (Zephyr.Chern.stream N))) (sheet _ paint) (Lagoon k o):=by
   intro i ti
   apply painted i w
   apply (separation_triangle _ o _).trans 
   obtain ⟨a,h,p⟩:=halo_spec.mp (mem_product.mp ti).1
   replace h:=mem_singleton.mp h
   subst a;rw[separation_comm] at p;exact Nat.add_le_add_right p _
 have hg:= (stalk u t _ b.1).2.trans (u.rake.swirl_same he he)
 have hd:=b.2;rw[hg] at hd
 exact ⟨hg, brightSheet e hd.le⟩
end YM.CF.Bay.D
#print axioms YM.CF.Bay.D.vivid
