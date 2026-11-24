import YM.SU5.FiniteGaugeData.Tower.TowerLaw
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K" => tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H i k I E)(s:ℕ)
/-!
# Propagate localized stencils at fixed physical distances

Meter: d in ℕ lattice gauge-site units, real-world thickening at level 0
fermion spacing is d/(2 L^s) at observing level s. ℓ = `reserve Λ l`. Need
both field arguments local in that convention (earlier alum proofs). These
estimates KEEP enough separation and also bound the total physical thickening
by strictly less than one ℓ budget (independent of #advances). Do not infer
product lifts on any closer pair without proof.
-/
section

variable (Λ:Preparation)(l:ℕ)
local notation "L₀"=> Λ.R.L.val
local notation "H₀"=> reserve Λ l
local notation "W₀"=> wingspan Λ l
lemma margin_good: 0< H₀ := by unfold reserve; omega
lemma expansion_bound:
 H₀+ L₀ * gross (aliasLaw Λ) (distanceLaw l) Λ.R.J ≤ L₀ * H₀:= Buffered.margin_step (Journey.prepared Λ l) Λ.R.coarse
lemma separated_sub {S T X Y:Finset Cover}{n:ℕ}(x:X⊆S)(y:Y⊆T)(a: Tower.separated n S T):Tower.separated n X Y:=fun i g j h=> a i (x g) j (y h)
lemma separated_symm{S T:Finset Cover}{n:ℕ}(p:Tower.separated n S T):Tower.separated n T S:=by
 intro y v x u q; apply p x u y v; obtain ⟨h,g⟩:= (Lattice.box_test.mp q); rw [Lattice.box_test]; constructor <;> intro i
 · specialize g i; simp only [Pi.sub_apply] at *; omega
 specialize h i; simp only [Pi.sub_apply] at *; omega

def Detached(Λ:Preparation)(l:ℕ): Finset Cover→Finset Cover→Prop := Tower.separated (2*reserve Λ l-1)
lemma mirror_detached {a:Axis}{z:ℤ}{S T:Finset Cover}(x:region a z H₀ S)(y:region a z H₀ T): Detached Λ l (reflectedBox a z S) T := by
 intro i t j v k; obtain ⟨i,u,rfl⟩:= mem_image.mp t
 have p:= (Lattice.box_test.mp k).1 a; rw [Pi.sub_apply,reflected_coord] at p
 have h:=x i u; have he:=y j v; have hx:=margin_good Λ l; omega
lemma Detached.act {S T:Finset Cover}(u:Detached Λ l S T):separated (2*(Advance.nearZero (aliasLaw Λ)+distanceLaw l)) S T:= fun i t j v m=> u i t j v (Push.GridApprox.box_larger m (by
 have h:= Journey.prepared Λ l; unfold Advance.nearZero; unfold Buffered.Margin r₃ r₁ at h; have hp:= Λ.R.L.property; have hr:= margin_good Λ l; have ht:2*(16+8*aliasLaw Λ+1+distanceLaw l)<2*(reserve Λ l):=by have w: 1+aliasLaw Λ ≤ Λ.R.L.val*(1+aliasLaw Λ):=Nat.le_mul_of_pos_left _ hp; rw [mul_assoc 100] at h; omega;
 omega))
lemma Detached.supersede {S T:Finset Cover}(u:Detached Λ l S T): Detached Λ l (W₀ S) (W₀ T):=by
 let q:=L₀*gross (aliasLaw Λ) (distanceLaw l) Λ.R.J
 let L:ℤ:=L₀
 let p:=H₀
 have he:0<L:=by unfold L; exact_mod_cast Λ.R.L.property
 have hm:p+q≤ L₀*p:=expansion_bound Λ l
 have hp':(2*p-1:ℕ)+1=2*p:= Nat.sub_add_cancel (by have h:=margin_good Λ l; unfold p; omega)
 intro x xP y yP v
 obtain ⟨j,b,hx⟩:=Finset.mem_biUnion.mp xP; obtain ⟨k,d,hy⟩:= Finset.mem_biUnion.mp yP
 obtain ⟨i₁,e,rfl⟩:= mem_image.mp b; obtain ⟨i₂,w,rfl⟩:=mem_image.mp d
 obtain ⟨x₀,r,rfl⟩:= mem_image.mp hx; obtain ⟨y₀,t,rfl⟩:=mem_image.mp hy
 apply u i₁ e i₂ w
 have ht:=Lattice.box_test.mp v
 have hz:=Lattice.box_test.mp r; have ha:=Lattice.box_test.mp t
 rw [Lattice.box_test]
 have hk (i:Axis): -((2*p-1:ℕ):ℤ) ≤ (i₁-i₂) i ∧ (i₁-i₂) i ≤ ((2*p-1:ℕ):ℤ):=by
    have he₁:=ht.1 i; have he₂:=ht.2 i
    have hv:=hz.1 i; have hu:=hz.2 i; have hyq:=ha.1 i; have hh:=ha.2 i
    change -((2*p-1:ℕ):ℤ) ≤ _ at he₁; change _≤ ((2*p-1:ℕ):ℤ) at he₂
    simp only [Pi.sub_apply,Pi.add_apply,Pi.smul_apply,nsmul_eq_mul,Pi.mul_apply,Pi.natCast_apply] at *
    change -(q:ℤ) ≤ _ at hv hyq; change _≤ (q:ℤ) at hu hh
    have hq:(q:ℤ)+p ≤ L*p:=by unfold L; exact_mod_cast (Nat.add_comm q p ▸ hm)
    have hs:((2*p-1:ℕ):ℤ)+1=2*p:=by exact_mod_cast hp'
    constructor
    · by_contra! v; have hd:i₁ i-i₂ i ≤ -(2*p:ℤ):=by omega
      change 0<(Λ.R.L.val:ℤ) at he; unfold L at *
      nlinarith [mul_le_mul_of_nonneg_left hd he.le]
    by_contra! v; have hd: (2*p:ℤ) ≤ i₁ i-i₂ i:=by omega
    unfold L at *; nlinarith [mul_le_mul_of_nonneg_left hd he.le]
 exact ⟨fun i=> (hk i).1,fun i=>(hk i).2⟩

-- explicit k-step support. upper-cover periods still require stage-dependent
-- hosting (turning Atlas pays) so don't claim with k or S moving through
-- the actual cutoffs except where sponsored.
def volumeAround : ℕ → Finset Cover → Finset Cover
 | 0,S=>S
 | i+1,S=>wingspan Λ l (volumeAround i S)

lemma around_succ (S:Finset Cover)(i:ℕ): volumeAround Λ l (i+1) S=volumeAround Λ l i (wingspan Λ l S):=by
 induction i with
 | zero=>rfl
 | succ i ih=> rw [volumeAround,ih,volumeAround]
lemma Around_detaches {S T:Finset Cover}(e:Detached Λ l S T)(n:ℕ):Detached Λ l (volumeAround Λ l n S) (volumeAround Λ l n T):=by
 induction n with
 | zero=> exact e
 | succ n ih=> exact ih.supersede Λ l
-- total deviation estimate; good for arbitrary coordinates. Propagating
-- physical radius ℓ on gauge lattice. Multiply by the chosen spacing to get
-- the bounded region.
lemma shield (S:Finset Cover)(i:ℕ){x:Cover}(t:x∈ volumeAround Λ l i S):∃ y∈S,∀ a:Axis,
 |(x-L₀^i • y) a|+ (H₀:ℤ)≤ L₀^i * (H₀:ℤ):=by
 let h:ℤ:=H₀
 have h': H₀+L₀*gross (aliasLaw Λ) (distanceLaw l) Λ.R.J ≤ L₀*H₀:=expansion_bound Λ l
 induction i generalizing x with
 | zero=> exact ⟨x,t,fun i=> by simp⟩
 | succ i ih=>
    obtain ⟨j,p,xP⟩:= mem_biUnion.mp t; obtain ⟨w,q,rfl⟩:=mem_image.mp p; obtain ⟨v,z,rfl⟩:= mem_image.mp xP; obtain ⟨y,yP,b⟩:=ih q
    refine ⟨y,yP,fun a=>?_⟩
    have hz:=b a; rw [pow_succ',mul_smul]
    let L:ℤ:=L₀; let r:=L₀*gross (aliasLaw Λ) (distanceLaw l) Λ.R.J
    have hc:0≤L:= Int.ofNat_zero_le _
    have H : |v a| ≤ (r:ℤ):= abs_le.mpr ⟨(Lattice.box_test.mp z).1 a,(Lattice.box_test.mp z).2 a⟩
    have H' : h+r≤L*h:=by unfold L h r; exact_mod_cast h'
    rw [pow_succ']; have eq: (v + L₀ • w - L₀ • L₀^i • y) a=v a+L*((w - L₀^i • y) a):=by simp only [Pi.add_apply,Pi.sub_apply,Pi.smul_apply,nsmul_eq_mul,Pi.mul_apply,Pi.natCast_apply,L]; ring
    rw [eq]; have hT:=_root_.abs_add_le (v a) (L*((w - L₀^i • y) a)); rw [abs_mul,abs_of_nonneg hc] at hT
    change _ + h ≤ L * L^i*h; change _+h ≤ L^i*h at hz; nlinarith [mul_le_mul_of_nonneg_left hz hc]
end
end YM.CF.Buffered.Afterglow.Tower
#print axioms YM.CF.Buffered.Afterglow.Tower.shield
#print axioms YM.CF.Buffered.Afterglow.Tower.Detached.supersede
