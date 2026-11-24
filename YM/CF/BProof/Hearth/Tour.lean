import YM.CF.BProof.Hearth.Scene

/-! Proposition B-Pproj incl alternative clan open condition. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.BProof.Hearth
open Function Filter Fock Finset Branch Tenant Cube SU Tulip Lat Lattice Dial Spin Stint Fig Align
open scoped Topology BigOperators Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator Classical
attribute [local instance] opCStarAlgebra
variable {N:Side}{j:ℕ}{d c a b l r ρ:ℝ} {P:Ready j a b l r}{F:Core j a b l r N}(h:Age P F d)
section
variable (x: Scope F d c)
local notation "X"=>x.1.val.1.val
local notation "S"=>x.1.val.2
local notation "Q"=>x.2.val
include h
lemma lease {q u:ℝ}(p:1≤j)(A:BoardH F 1 S c)(e:0≤q)(v:0≤ρ)(g:‖u‖≤1)(r:ℕ)(G:Picture N x.2 S q ρ u (r+r))(C:CloseH X q S (r+r))(w: ‖(F.θ X 1* pair Q - pair Q * cc (F.θ X 1))‖≤ρ)(z:Site (More N)): let T:= bay (terr (More N)) z r; ∃ y:Scope F d c, (∀ i∈T,i∈spot S ↔ i∈spot y.1.val.2) ∧ (∀ i∈leaks T, scenery (X i) (y.1.val.1.val i) ≤ q) ∧ (∀ i∈T, ‖Q i-y.2.val i‖≤q)∧ ‖bille F u y‖≤ρ:=by -- include
 intro T; by_cases B:Disjoint T (spot S)
 · let I:= F.θ X 1; have ht: Board ..:= x.1.property -- tune
   let y: InRoad F d c:= ⟨(x.1.val.1, ∅), empty_board ht.a ht.nice ht.bare⟩; refine ⟨(y,x.2),fun i hz=> ⟨fun z=>False.elim (disjoint_left.mp B hz z),fun z=>(show i∈spot S from False.elim (by change i∈spot (∅:Support N) at z; simp [spot] at z))⟩,fun i _=>?_,fun i _=>?_,?_⟩; change scenery (X i) (X i) ≤ _; simpa [scenery] using e; change ‖Q i-Q i‖≤_; simpa using e; exact plaza ht.a _ w u
 obtain ⟨o,t,hx⟩:= not_disjoint_iff.mp B; have hu:T⊆ bay (terr (More N)) o (r+r):= coverBay ((bay_mem r).mpr (by rw [(terr (More N)).sym]; exact (bay_mem r).mp t)); obtain ⟨W,Z,H⟩:= modelPicture h _ G p e g A v o hx T hu
 have hy : bay (terr (More N)) o (r+r)⊆ halo (r+r) (spot S):=by rw [tract]; exact Corona.halo_mono le_rfl (singleton_subset_iff.mpr hx)
 exact ⟨(⟨(⟨1,guard0 h.pos⟩,S),A⟩,W),fun _ _=>Iff.rfl,fun i g=> C _ (leaks_up (hu.trans hy) g),Z,H⟩
end
include P in
lemma buysP (c:ℝ)(q:0<c)(v:0≤ρ)(t:ρ<1)(x0:1≤j) : ∃ k:ℕ, ∃ p r':ℝ,0<p∧r'<1∧0<r'∧∀ {N d}{F:Core j a b l r N}(h:Age P F d)(x:Scope F d c), let S:=x.1.val.2; let U:=x.1.val.1.val; let V:=x.2; let A:= F.θ U 1; let B:=pair V.val; BoardH F 1 S c → ‖A*B-B*cc A‖≤ρ →CloseH U p S k → ∀ u:ℝ,‖u‖≤1→Picture N V S p ρ u k → ‖gapE F U S V.val u‖≤r' := by
 obtain ⟨p,T⟩:= tablePrice P q; obtain ⟨z,e,U⟩:= exists_between t; obtain ⟨r,G,hg⟩:=exists_between U; obtain ⟨K,f⟩:= purchases ((v.trans e.le)) G p
 let a':=(z-ρ)/4; have ht:0<a':=div_pos (sub_pos.mpr e) (by norm_num); obtain ⟨k,k'⟩:= ((tailPaid p).eventually (gt_mem_nhds ht)).exists; let v':=funding P.hT k; have hw:= funding_pos P.hT k; have hf:=p.funding; let C:=a'/(v'*p.cash); have hx : v' * C*p.cash=a':= by unfold C v'; field_simp
 have hp:0<C:=div_pos ht (mul_pos hw hf); refine ⟨(K+k)+(K+k), C,r,hp,hg,(v.trans_lt e).trans G,?_⟩; intro N d F h x S V Y A B Q vH W u hu w; let R:=shop h c; have H:Earn p R.mark R.mark.reverseV (bille F u) := T h u hu; apply f H R.town x; intro o; let X:= strip R.st (bay (terr (More N)) o K)
 obtain ⟨y,yP,yU,yh,B⟩:=lease h x x0 Q hp.le v hu (K+k) w W vH o; let a:=bille F u x; let l:=bille F u y; have hD: ‖(a-l)*X‖≤2*tailPay p k + a':=by rw [← hx]; exact cap_compare H k _ (mul_nonneg hw.le hp.le) (fun i g=> fees h x y o hp.le yP yU yh i g)
 have hh: ‖l*X‖≤ρ:= (stripCheap ..).trans B
 change ‖a*X‖≤z; rw [show a*X=(a-l)*X+l*X from (by rw [sub_mul,sub_add_cancel])]; exact (norm_add_le ..).trans ((add_le_add hD hh).trans (by unfold a' at *; linarith only [e,k']))
end YM.CF.BProof.Hearth
