import Bay.E.Murres
import YM.SU5.FiniteGaugeData.Tower.Baggage

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


namespace Silk
open Buffered Lifted D StressExchange

open Buffered.Afterglow.Tower SlabMark
open Girt
open scoped YM.CF.Buffered

local notation "Ways" => Buffered.Family


variable {K:Buffered.Calibration}{S T:Finset Cover}{F G:ℕ→Ways K}{f g:Ways K}
lemma qbPlus (p:BQueue S F f)(q:BQueue S G g):
  BQueue S (fun i=>F i+G i) (f+g):=by
 obtain ⟨A,h,h1,h2⟩:=p.bdd
 obtain ⟨B,h',u,v⟩:=q.bdd
 refine ⟨fun i=>(p.whereTo i).add (q.whereTo i),p.landing.add q.landing,
      ⟨A+B,add_pos h h',pay_add h1 u,(h2.and v).mono fun i t=>pay_add t.1 t.2⟩,fun e h=>?_⟩
 have d:0<e/2:=by positivity
 filter_upwards[p.saved _ d,q.saved _ d] with i u v
 rw[show F i+G i-(f+g)= F i-f+(G i-g) from by abel]
 exact (add_halves e) ▸ pay_add u v -- substitution

lemma qbScale (z:ℂ)(p:BQueue S F f):BQueue S (fun i=>z • F i) (z • f):=by
 obtain ⟨A,h,h1,h2⟩:=p.bdd
 refine ⟨fun i=>InTest.smul z (p.whereTo i),InTest.smul z p.landing,
      ⟨_,by exact mul_pos (add_pos_of_nonneg_of_pos (norm_nonneg z) zero_lt_one) h,
       fun i x=> (pay_scale h1 z i x).trans (by nlinarith),
       h2.mono fun j u i x=>(pay_scale u z i x).trans (by nlinarith)⟩,fun e hv=>?_⟩
 have d:0<e/(‖z‖+1):=by positivity
 have t:e/(‖z‖+1)*(‖z‖+1)=e:=by field_simp
 filter_upwards[p.saved _ d] with i u
 rw[←smul_sub]
 exact fun j x=>(pay_scale u z j x).trans (by nlinarith)

lemma qbWider(p:BQueue S F f)(h:S⊆T):BQueue T F f:=⟨fun i=>(p.whereTo i).mono h,p.landing.mono h,p.bdd,p.saved⟩

lemma qbSum {ι:Type*}(A:Finset ι){x:ℕ→ι→Ways K}{z:ι→Ways K} (v:∀i∈A,BQueue S (fun n=>x n i) (z i)):
 BQueue S (fun n=>∑ i∈A,x n i) (∑ i∈A,z i):=by
 classical
 induction A using Finset.induction_on with
 | empty=>
   simp only[sum_empty]
   apply BQueue.stay .zero zero_lt_one
   exact fun i x=>le_of_eq_of_le (norm_zero) zero_le_one

 | insert i A h ih=>
    simp only [sum_insert h]
    exact qbPlus (v i (mem_insert_self ..)) (ih fun j b=>v j (mem_insert_of_mem b))

variable {o:Cover}{b:ℕ}{t d L:ℝ}
local notation "AΩ"=>Band o b
abbrev weave (K:Calibration)(f:LinksC→ℂ): Ways K:=scalar K (f ∘ Prod.fst)

lemma spun (K:Calibration){f:LinksC→ℂ}(u:SilkPay o b t d L f):
 InTest K true AΩ false (weave K f)∧pay (weave K f) L:=by
 refine ⟨.seed ⟨by simp,⟨u.meas.comp measurable_fst,L,fun i=>u.flat _⟩,fun i k p _ => u.seated _ _ p⟩,?_⟩
 intro i x
 change ‖f _ •(1:FC _)‖≤ L
 rw[norm_smul,norm_one,mul_one]
 exact u.flat _
lemma qbSpun (K:Calibration){Z:ℕ→LinksC→ℂ}{f:LinksC→ℂ}
 (v:∀i,SilkPay o b t d L (Z i))(u:SilkPay o b t d L f)(a:TendstoUniformly Z f atTop):
 BQueue AΩ (fun i=>weave K (Z i)) (weave K f):=by
 have n:0≤L:=(norm_nonneg _).trans (u.flat 1)

 refine ⟨fun i=>(spun K (v i)).1, (spun K u).1,
    ⟨L+1,by positivity,fun i x=>((spun K u).2 i x).trans (by linarith),
       Eventually.of_forall fun i j x=> ((spun K (v i)).2 j x).trans (by linarith)⟩, fun ε p=>?_⟩
 filter_upwards[Metric.tendstoUniformly_iff.mp a _ p] with i h j x
 change ‖(_ : ℂ) • (1:FC (Single (K.c j)))-(_ : ℂ) • 1‖≤ _
 rw [←sub_smul,norm_smul,norm_one,mul_one,norm_sub_rev,←dist_eq_norm]
 exact (h _).le

abbrev sword (K:Calibration)(i j:Beam S):Ways K:=fun n _=>unitBlade _ i j
lemma queSword (K:Calibration) (i j:Beam S):BQueue S (fun _:ℕ=>sword K i j) (sword K i j):=by
 apply BQueue.stay _ zero_lt_one
 · intro n v
   let N:=K.c n
   have w(k:Beam S): ‖create (basisC N k.1.1.val k.1.2 k.2)‖ ≤ 1:=by
     have ht: ‖ap N k‖=1:=by
       have t: ‖ap N k‖^2=1:=by rw [sq,←norm_mul,show ap N k*ap N k=1 from Rush.fee_one _,norm_one]
       nlinarith [norm_nonneg (ap N k)]
     rw [basisC,map_smul,norm_smul,show ‖Lifted.winding ..‖=1 from ht,one_mul,create_put]
     have y:=Pastry.tag_size ({sta N k})
     rw [poke, Poly.tag_once] at y
     exact y


   change ‖unitBlade N i j‖≤1
   rw[unitBlade]
   split; swap; · simp
   apply (norm_mul_le ..).trans
   rw [Fock.remove,norm_star]
   exact mul_le_one₀ (w i) (norm_nonneg _) (w j)
 by_cases u:i.1.2∈plusHalf ∧ j.1.2∉plusHalf
 · rw [show sword K i j = creation K i.1.1.val i.1.2 i.2 * removal K j.1.1.val j.1.2 j.2 from
         funext fun n=>funext fun v=>if_pos u]
   exact InTest.mul (InTest.creator (x:=_) i.2 u.1 i.1.1.property) (InTest.remover _ u.2 j.1.1.property)
 rw [show sword K i j=0 from funext fun n=>funext fun v=>if_neg u]
 exact .zero
end YM.CF.Bay.Silk
