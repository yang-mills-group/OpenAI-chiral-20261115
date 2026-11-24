import YM.SU5.Thin.Woods.Fabric
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


open Buffered Buffered.Afterglow Lamour.Bridge.Celeste.Clock
open Fabric YM.CF.Pannier.Chancel
namespace D
variable {K:Calibration}{N m:Side}{W:Fabric N→Prop}
 {ν:Mark N→ℂ}{u:List (Fabric N)}{p:ℕ}
variable (h:∀{x},W x→∀ i a,W (x.twistL i a))(t:∀ x,W x→AtSupport false x.S x.x)
    (y:Twosome K N ν)

include h t y in
lemma carousel (g:N=K.c m)(E B:Axis→ℕ)
 (v:∀i,2^(E i)*(B i+addgap K)≤ N.val)(D:Finset Axis)
 (f:Sylvan W p u)(q:∀i∈D,cows i (Fabric.Broad p u) (B i)):
 ∃ A:List (Fabric N),
    Sylvan W p A ∧ A.length=(∏i∈D, 2^E i)*u.length ∧
    ‖ν (buffet u)‖^(∏i∈D, (2^E i:ℕ)) ≤ ‖ν (buffet A)‖:=by
 induction D using Finset.induction_on generalizing u with
 | empty=> exact ⟨u,f,by simp,by simp⟩
 | @insert i D r ih=>
   obtain ⟨A,e,l,s,z⟩:= stand h t y g u i f (q i (mem_insert_self _ _)) (v i)
   obtain ⟨J,a,b,c⟩:= ih e (fun j hj=> z j (by rintro rfl; contradiction) _ (q j (mem_insert_of_mem hj)))
   refine ⟨J,a,?_,?_⟩
   · rw[prod_insert r,b,l]; ring
   rw[prod_insert r,pow_mul]
   exact (pow_le_pow_left₀ (by positivity) s _).trans c
def acres (K:Calibration)(B:Axis→ℕ):ℕ:=∏i,4*(B i+addgap K)
lemma acres_pos(K:Calibration)(B:Axis→ℕ):0<acres K B:= prod_pos fun i _=>Nat.mul_pos
    (by decide) (Nat.add_pos_right _ addgap_pos)

def Will (K:Calibration)(N:Side)(B:Axis→ℕ)(S:Finset (Seat N)):Prop:=
 (∀i,B i+addgap K ≤ N.val)∧ ∀i,cows i S (B i)

include h t y in
lemma villa (g:N=K.c m)(f:Sylvan W p u)
   (B:Axis→ℕ)(w:Will K N B (Fabric.Broad p u)):
   ∃ (a:ℕ) (J:List (Fabric N)),
    0<a ∧ (More N).val^4≤ a*acres K B ∧ Sylvan W p J∧J.length=a*u.length ∧
       ‖ν (buffet u)‖^a ≤ ‖ν (buffet J)‖:=by
 let Y(i:Axis):=B i+addgap K
 have py(i):0<Y i:=Nat.add_pos_right _ addgap_pos
 have fees(i):∃ℓ:ℕ, 2^ℓ*Y i≤N.val∧N.val*2≤(2^ℓ)*(4*Y i):=by
    have hone:1≤N.val/Y i:=(Nat.le_div_iff_mul_le (py i)).mpr ((one_mul _).trans_le (w.1 i))
    obtain ⟨r,x,v⟩:=exists_nat_pow_near hone (by decide:1<2)
    refine ⟨r,(Nat.le_div_iff_mul_le (py i)).mp x,?_⟩
    have z: N.val < 2^(r+1)*Y i:= (Nat.div_lt_iff_lt_mul (py i)).mp v
    exact (Nat.mul_le_mul_right 2 z.le).trans_eq (by ring)
 choose E e l using fees
 obtain ⟨A,k,d,z⟩:=carousel h t y g E B e univ f (fun i _=>w.2 i)
 refine ⟨∏i, 2^(E i), A,prod_pos (fun i _=>by positivity),?_,k,d,z⟩

 unfold acres;rw[←prod_mul_distrib,
    ←show ∏ _ : Axis,N.val*2=(More N).val^4 by simp [Axis]]
 exact Finset.prod_le_prod' (fun i _=>l i)
end D
end YM.CF.Bay
