import Bay.D.Wickle
import Bay.D.Vivid
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
open Regis Regis.Head Etch Gleam Next.SectorChange Next.SectorChange.Gaussian
open Pressure Work.F03 ProbabilityTheory
local notation "T4"=>SU.group
open Resonance Brecht Circuit

variable {n:Side}
lemma dip_pour(A:Icey (Cella n))(U:Muff Pureton) :
    dip A (fun i j=>U i.2 j.2)=dip (drain A) U:=by
   -- straightforward sum. i→Pureton. j→Pureton. target RHS expanded.
 unfold dip drain
 conv_lhs =>
   rw [Fintype.sum_prod_type_right]
   enter [2,i,2,x]; rw[Fintype.sum_prod_type_right]
 simp only [sum_mul]
 exact sum_congr rfl fun i _=>sum_comm

abbrev reed(i j:Pureton):ℂ:= if i=j then 1 else 0
def relive(i j:Cella n):=reed i.2 j.2
lemma oboe(A:Icey (Cella n))(k l:Pureton):
 dip A (fun i j=> reed k i.2 *reed l j.2)=drain A k l:=by
 rw[dip_pour _ (fun i j=>reed k i*reed l j)];simp [dip,reed,mul_ite]

lemma oboes {s:Finset (Cella n)}{f:ℝ}{A:Icey (Cella n)}
   (u:Rake s f A):
   dips A (creamM A) (passes relive)= (2:ℂ)*mass A:=by
 have t(i j:Cella n):dip (creamM A) (passes relive i j)= 
    (2:ℂ)* star (drain A i.2 j.2):=by

   let V(i j:Pureton):= star (drain A i j)
   have q(i j):drain (creamM A) i j=V i j :=by simp[creamM,V,drain]
   have e:drain A j.2 i.2=drain A i.2 j.2:=sum_comm.trans (sum_congr rfl fun x _=>sum_congr rfl fun y _=> u.sym ..)
   rw[show (2:ℂ)*_= V i.2 j.2 + V j.2 i.2 from ?_,←q,←q,←oboe,←oboe]
   unfold dip passes relive
   simp_rw [mul_add,sum_add_distrib,mul_comm (reed j.2 _)]
   unfold V;rw[e,two_mul]
 have he:dips A (creamM A) (passes relive)=dip (drain A) (fun i j=> (2:ℂ)* star (drain A i j)):=by
   rw[←dip_pour]; unfold dips; simp_rw[t]
 rw[he]
 unfold dip mass; push_cast;rw[mul_sum]
 refine sum_congr rfl fun i _=>?_
 rw[mul_sum];refine sum_congr rfl fun j _=>?_
 erw[mul_left_comm, Complex.mul_conj']


lemma woodworth {s:Finset (Cella n)}{f r b B d:ℝ}{A:Icey (Cella n)}
 {F: Cella n → Cella n → ℂ}
   (u:Rake s f A)
   (c:0≤b)(t:b≤B)(v:0≤d)
   (h:∀i∈s,∀j∈s,‖(r:ℂ)^4*F i j-(b:ℂ)* relive i j‖≤d):
   ‖(r:ℂ)^8 * dips A (creamM A) (passes F) - 2*(b:ℂ)^2 *mass A‖≤ f*(f*(4*d*(B+d))):=by
 let G:=(r:ℂ)^4 • F
 let L:Cella n→Cella n→ℂ:= (b:ℂ) • relive
 have w(i j):‖L i j‖≤ B:=by
    unfold L relive reed
    change ‖(b:ℂ)* (if i.2=j.2 then 1 else 0)‖ ≤ B
    split
    · simpa only[mul_one, Complex.norm_of_nonneg c] using t
    simpa using c.trans t
 have hp:=passes_fee (F:=G) (G:=L) u (cream_fee u) (c.trans t) v h (fun i _ j _=>w i j)
 unfold G L at hp;rw[passes_smul,passes_smul,oboes u,
   show ((r:ℂ)^4)^2=(r:ℂ)^8 from by ring,←mul_assoc,mul_comm _ (2:ℂ)] at hp
 exact hp

end YM.CF.Bay.D
#print axioms YM.CF.Bay.D.oboes
