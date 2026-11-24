import YM.SU5.Selected.Cor.Saloon
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 450000
set_option maxRecDepth 3000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Pannier.Chancel.Lantern
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye RG
open Crest.Airy
open Reed (Fine)
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
namespace Bulb
open Lifted (nodeC node_of)
namespace Mezz
variable (A: Mezz)
local notation "W₀" => A.W
local notation "D₀" => A.D.val
local notation "G₀" => A.G.val
-- axes order t,i,j,k
abbrev Cane := Tender.Mile A.D A.q.val
def wingP (b:Bool): ℕ := if b then 25*W₀ else 10*W₀
def staff1 (a:A.Cane):ℕ:=10*W₀ + G₀*a.val
def staff2 (b:Fin 2) (a:A.Cane) :ℕ:=10*W₀+G₀*(2*a.val+b.val)
def staff3 (b:Bool) (a:A.Cane):ℕ:= A.wingP b+G₀*a.val
variable (b:Bool)(i:A.Lot)(p:Fin 2)
def envelopeN (z:A.Lot) (s:Fin 2) (b:Bool) : Axis → ℕ := ![staff1 A z.2.1, staff2 A s z.2.2.1,staff3 A b z.2.2.2.1, A.forkD z.1]
def globeY (v:A.Lot× Fin 2)(b:Bool): Cover× Fin A.marks:= ⟨fun k=>(A.envelopeN v.1 v.2 b k:ℤ), v.1.2.2.2.2⟩
local notation "Z'" => (A.globeY (i,p) b).1
lemma grip (a:A.Cane): G₀*a.val < W₀:=by unfold W; exact lt_of_lt_of_eq (Nat.mul_lt_mul_of_pos_left a.isLt A.G.property) (by ring)
lemma staff1_pay {a:A.Cane}: 10*W₀ ≤ A.staff1 a ∧ A.staff1 a ≤11*W₀:= by have h:= A.grip a; unfold staff1; omega
lemma staff2_pay {a:A.Cane}: 10*W₀≤ A.staff2 p a ∧ A.staff2 p a ≤13*W₀:= by
 have h:= A.grip a; unfold staff2; have hv:G₀*(2*a.val+p.val) ≤ 3* W₀:=by have hp:p.val ≤1:= (by omega); have ht:= A.geo_g; nlinarith
 omega
lemma staff3_pay {a:A.Cane}: A.wingP b≤ A.staff3 b a ∧ A.staff3 b a < A.wingP b+W₀:=by have h:= A.grip a; unfold staff3; omega
lemma envelope_pay (a:Axis) {b:Bool}:A.envelopeN i p b a≤401*W₀:=by
 have h:= A.fork_range i.1; let f:= A.envelopeN i p b; have ht:=A.staff1_pay (a:=i.2.1); have hv:= A.staff2_pay (a:=i.2.2.1) p; have hp:= A.staff3_pay (a:=i.2.2.2.1) b; have hz:A.wingP b≤ 25* W₀:= by unfold wingP; cases b <;> simp <;> omega
 fin_cases a
 · change A.staff1 _ ≤_; omega
 · change A.staff2 _ _ ≤_; omega
 · change A.staff3 _ _ ≤_; omega
 change A.forkD _ ≤_; omega
-- injective split products b both. V can drop b by precomp. G later. keep Int/nat.
def mousse (v:(A.Lot× Fin 2) × Bool):= A.globeY v.1 v.2
lemma seedI : Injective A.mousse:= by
 rintro ⟨⟨⟨d,a,c,g,r⟩,v⟩,u⟩ ⟨⟨⟨d',a',c',g',r'⟩,v'⟩,u'⟩ h; obtain ⟨x,y⟩:= Prod.mk.inj h
 let f:= fun a bb c:ℕ=> a*bb+c; -- spare
 have hx:A.staff1 a=A.staff1 a':= by exact_mod_cast (show (A.staff1 a:ℤ) = A.staff1 a' from congrFun x 0) -- ofNat defeq
 have hv: A.staff2 v c=A.staff2 v' c':=by exact_mod_cast (show (A.staff2 v c:ℤ)=A.staff2 v' c' from congrFun x 1)
 have hg: A.staff3 u g=A.staff3 u' g':=by exact_mod_cast (show (A.staff3 u g:ℤ)=A.staff3 u' g' from congrFun x 2)
 have hp: A.forkD d=A.forkD d':=by exact_mod_cast (show (A.forkD d:ℤ)=A.forkD d' from congrFun x 3)
 replace hp:d=d':= Fin.ext (Nat.eq_of_mul_eq_mul_left A.D.property (Nat.add_left_cancel hp))
 have hz( X Y :ℕ): G₀*X=G₀*Y → X=Y:= Nat.eq_of_mul_eq_mul_left A.G.property
 replace hx:a=a':=Fin.ext (hz _ _ (Nat.add_left_cancel hx)); have hv:= hz _ _ (show G₀*(2*c.val+v.val)= _ from (Nat.add_left_cancel hv)); have hw:v=v':=Fin.ext (by omega); have ht:c=c':=Fin.ext (by omega)
 replace y:r=r':=y
 have q:u=u':=by
    have h:= A.staff3_pay (a:=g) u; have v:= A.staff3_pay (a:=g') u'; have k:= A.geo_w; clear x; cases u; cases u'; rfl; simp only [wingP,Bool.false_eq_true,ite_false,ite_true] at *; omega; cases u'; simp only [wingP,Bool.false_eq_true,ite_false,ite_true] at *; omega; rfl
 subst u'; replace hg:g=g':= Fin.ext (hz _ _ (Nat.add_left_cancel hg)); rw [hp,hx,y,hg,ht,hw]

-- stage enough along SN. take > widthK. not unrelated.
variable {N:Side} (h:A.Legate)(f:A.beams* (10:ℕ)<N.val)
include f
def detent (N:Side) (v:(A.Lot× Fin 2) × Bool) : Site N × Fin A.marks:= Prod.map (wrap N) id (A.mousse v)
local notation "γ" => A.detent N
lemma read_m (j:A.Lot)(p:Fin 2)(b:Bool)(i:Axis): ((γ ((j,p),b)).1 i).val=A.envelopeN j p b i:=by
 have h:=A.envelope_pay (b:=b) j p i; unfold beams at f; change ( (↑( (A.envelopeN j p b i:ℕ):ℤ):Per N)).val = _; rw [Int.cast_natCast,ZMod.val_natCast_of_lt (by omega)]
lemma seed_down (g:G₀ ∣ N.val)(d:D₀∣N.val): Beacons A.G A.D A.marks (γ):=by
 constructor
 · rintro ⟨⟨i,j⟩,b⟩ ⟨⟨i',j'⟩,b'⟩ p; apply A.seedI; apply Prod.ext
   · have h:=congrArg Prod.fst p; funext a; change (↑(A.envelopeN i j b a):ℤ) = (A.envelopeN i' j' b' a:ℤ); rw [←read_m A f,←read_m A f,h]
   exact congrArg (fun k: Site N× Fin A.marks=> k.2) p
 · exact g
 · exact d
 · rintro ⟨⟨i,j⟩,b⟩ a; rw [read_m A f]; have ht:G₀∣ W₀:= Dvd.dvd.mul_right (dvd_mul_left _ _) _ -- tune
   fin_cases a
   · change G₀∣10*W₀+G₀* _; exact dvd_add (ht.mul_left _) (dvd_mul_right ..)
   · change G₀∣10*W₀+G₀* _; exact dvd_add (ht.mul_left _) (dvd_mul_right ..)
   change G₀∣ A.wingP b + G₀* _; refine dvd_add ?_ (dvd_mul_right ..); cases b; exact ht.mul_left _; exact ht.mul_left _
 rintro ⟨⟨i,j⟩,b⟩; rw [read_m A f]; change D₀ ∣ 400*W₀+D₀*_; have ht:D₀∣W₀:= Dvd.dvd.mul_right (dvd_mul_right ..) _; exact dvd_add (ht.mul_left _) (dvd_mul_right ..)
-- include support labels (parameter K later). shifted any k approximation. 
omit f
variable (w:ℕ) (g:w ≤ A.W) (k: Cover) (u:Crest.Airy.Piece k w)
include g u
local notation "u'" => Z'+k
local notation "v'" => nodeC (u')
lemma rays : (∀ j≠(3:Axis),1 ≤ (v') j ∧ (v') j ≤ (80:ℤ)*W₀) ∧ A.Claw (v') b:=by
 have h':=(A.geo_w); have e(a:Axis):(v') a=2*(( (A.envelopeN i p b a:ℕ):ℤ)+k a)+1:=by
    simp only [nodeC,two_mul,two_smul,Pi.add_apply,globeY,Pi.one_apply]


 have h2:=A.staff2_pay (a:=i.2.2.1) p; have h3:= A.staff3_pay (a:=i.2.2.2.1) b; have hb:10*W₀≤ A.wingP b ∧ A.wingP b≤25*W₀:=by unfold wingP; split <;> omega
 have hf1:=u 0; have hf2:=u 1; have hf3:=u 2
 constructor
 · intro j w; simp_rw [e]; fin_cases j
   · change 1 ≤2*((A.staff1 _:ℤ)+k 0)+1 ∧ 2*((A.staff1 _:ℤ)+k 0)+1 ≤_; have hp:= (A.staff1_pay (a:=i.2.1)); omega
   · change 1 ≤2*((A.staff2 _ _:ℤ)+k 1)+1 ∧ 2*((A.staff2 _ _:ℤ)+k 1)+1 ≤_; omega
   · change 1 ≤2*((A.staff3 _ _:ℤ)+k 2)+1 ∧ 2*((A.staff3 _ _:ℤ)+k 2)+1 ≤_; omega
   exact False.elim (w rfl)
 unfold Claw; rw [e]; change _ ↔ 40*(W₀:ℤ) ≤2*((↑(A.staff3 _ _):ℤ)+_)+1; cases b; · rw [show A.wingP false =10*W₀ from rfl] at h3; simp; omega
 rw [show A.wingP true =25*W₀ from rfl] at h3; rw [eq_self,true_iff]; omega
lemma hourr: (v') 3= 2*((↑(A.forkD i.1):ℤ)+k 3)+1:=by
 change (( (2:ℕ) • (u') + (1:Cover))) 3=2*((Z' 3)+k 3)+1; simp only [two_smul,Pi.add_apply,Pi.one_apply]; ring
lemma rays_day : (v')∈ A.OuterPos:= by
 have ht:=(rays A b i p w g k u).1; refine mem_filter.mpr ⟨plant_test.mpr (box_test.mpr ⟨fun a=>?_,fun a=>?_⟩), (ht 0 (by decide)).1⟩
 all_goals
    rw [Pi.sub_apply]; by_cases p:a=3; · subst a; rw [hourr A b i _ w g k u,pal_z]; have hw:=A.fork_range i.1; have h:=u 3; have h₀:=A.geo_w; unfold vol; push_cast; omega
    rw [pal_tr A p]; specialize ht _ p; have hw:=A.geo_w; unfold vol; omega
lemma rays_V (z: Crest.Airy.depthE A.n A.marks (k 3)) : (v')∈ A.yard i.1 false:= by
 have ht:=(rays A b i p w g k u).1; apply (yard_test ..).mpr; rw [left_up,right_up,hourr A b i p w g k u]; change -(A.passW:ℤ) ≤ k 3 ∧ k 3≤0 at z; refine ⟨by omega,by omega,fun i h=>?_⟩; specialize ht i h; omega
lemma rays_X (z:Crest.Airy.depthL A.n A.marks (k 3)) : (v')∈ A.yard i.1 true:=by
 have ht:=(rays A b i p w g k u).1; apply (yard_test ..).mpr; rw [left_down,right_down,hourr A b i p w g k u]; change A.n ≤ k 3 ∧ k 3≤ (( ↑(A.n+A.passW):ℤ)) at z; refine ⟨by omega,by omega,fun i h=>?_⟩; specialize ht i h; omega
end Mezz
end Bulb
end YM.CF.Pannier.Chancel.Lantern
open YM.CF.Pannier.Chancel.Lantern.Bulb.Mezz
#print axioms seed_down
#print axioms rays_day
#print axioms rays_V
#print axioms rays_X
