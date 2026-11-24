import YM.SU5.Regis.Visitations
/-!
# Adapt cp8 Fabric powers recipe of Pannier/`Vintage`: for stencil prices & new housing, on THIS heat-course. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 260000
noncomputable section
namespace YM.CF.Lamour.Bridge.Celeste.Clock
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye CF.Pannier.Chancel Brace Velvet Hours Flare Cliplet RG Reed
open Py.Rate.Pannier
open Buffered.Afterglow
open Next.Rank.Thirst
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
variable {K:Calibration}{N m:Side}{j r p d t:ℕ}{M:Tulip.Male}{ε ξ σ C D:ℝ}
structure Fabric(N:Side) where
 x : Mark N
 S : Finset (Seat N)
 o : Seat N
 b : Seat N
namespace Fabric
variable (A:Fabric N)
def twistL(i:Axis)(z:ℤ): Fabric N:= ⟨reflMark i z A.x, hyphen i z A.S,(plane i z).anon N A.o,(plane i z).anon N A.b⟩
open Regis.Head
variable {I:Type*}[Fintype I]
/- replicate together simultaneous authorized locations or paint dual masks. Atlas assumption for CostCov. No hypotheses on E character here. -/
variable (W : Fabric N → Prop) (he:∀ {x:Fabric N}, W x → ∀ i z, W (x.twistL i z)) (hv:∀ x,W x→ AtSupport false x.S x.x)
variable {A}
def Broad (d:ℕ)(L:List (Fabric N)): Finset (Seat N) := L.foldr (fun x a=> Lattice.halo d x.S∪a) ∅
@[simp] lemma Broad_nil (p:ℕ): Broad p ([]:List (Fabric N))=∅:=rfl
@[simp] lemma Broad_more (L:List (Fabric N))(p:ℕ): Broad p (A::L)=Lattice.halo p A.S∪ Broad p L:=rfl
lemma Broad_append (p:ℕ)(L J:List (Fabric N)): Broad p (L++J)=Broad p L∪Broad p J:=by induction L with| nil=>simp| cons i L ih=> rw [List.cons_append, Broad_more,ih, Broad_more, union_assoc]
lemma Broad_turn (p:ℕ)(L:List (Fabric N))(i:Axis)(z:ℤ): Broad p (L.map (fun v=>v.twistL i z))= hyphen i z (Broad p L):=by
 induction L with
 | nil=> simp [hyphen]
 | cons s L ih=> rw [List.map_cons,Broad_more, Broad_more, ih]; unfold twistL; dsimp; unfold hyphen; rw [image_union]; exact congrArg (· ∪ _) (coal_halo i z s.S p).symm
lemma Broad_x (p:ℕ)(L:List (Fabric N))(A:Fabric N)(v:A∈L) : Lattice.halo p A.S ⊆ Broad p L:=by
 induction L with| nil=> simp at v| cons i L ih=> rw [Broad_more]; exact (List.mem_cons.mp v).elim (fun h=>h ▸ subset_union_left) (fun t=> (ih t).trans subset_union_right)
lemma sparse_face {S T:Finset (Seat N)}(g:Distant (d+1) S T)(i:Axis)(z:ℤ): Distant (d+1) (hyphen i z S) (hyphen i z T):=by
 intro x hx y hy; obtain ⟨x,h,rfl⟩:=mem_image.mp hx; obtain ⟨y,v,rfl⟩:= mem_image.mp hy; exact (g x h y v).trans_eq (s_sep (Signed.mirror i) (wrap (More N) (2 • (z • step i))) x y).symm
lemma SparseLock {S T:Finset (Seat N)}(p0:Disjoint (Lattice.halo d S) (Lattice.halo d T)): Distant (d+1) S T:=by
 intro i g j k; by_contra! h; exact disjoint_left.mp p0 (halo_spec.mpr ⟨_,g,show separation i j ≤ d from (by omega)⟩) (halo_spec.mpr ⟨_, k,(separation_self j).trans_le (Nat.zero_le _)⟩)
variable {L J:List (Fabric N)}
structure Sylvan (W: Fabric N → Prop)(p:ℕ)(L:List (Fabric N)):Prop where
 core (A:Fabric N)(v:A∈L):W A
 annex:L.Pairwise (fun i z=>Distant (p+1) i.S z.S)
variable {W} (u:Sylvan W p L)
namespace Sylvan
include u
include he in
lemma away(i:Axis)(z:ℤ): Sylvan W p (L.map (fun v=> v.twistL i z)):=by
 refine ⟨fun A w=>?_, List.pairwise_map.mpr (u.annex.imp fun g=> sparse_face g i z)⟩; obtain ⟨k,ψ,rfl⟩:= List.mem_map.mp w; exact he (u.core k ψ) i z
lemma tack (v:Sylvan W p J)(h:Disjoint (Broad p L) (Broad p J)): Sylvan W p (L++J):=⟨fun i g=>(List.mem_append.mp g).elim (u.core i) (v.core i), List.pairwise_append.mpr ⟨u.annex,v.annex,fun a e b g=>SparseLock (h.mono (Broad_x p L a e) (Broad_x p J b g))⟩⟩
end Sylvan
def buffet (L:List (Fabric N)): Mark N := (L.map Fabric.x).prod
lemma buffet_empty : buffet ([]:List (Fabric N))=1:=rfl
lemma buffet_more (L:List (Fabric N)): buffet (A::L)=A.x*buffet L:=by rw [buffet,List.map_cons,List.prod_cons]; rfl
lemma buffet_tack (L J:List (Fabric N)): buffet (L++J)=buffet L * buffet J:=by rw [buffet,List.map_append,List.prod_append]; rfl
lemma buffet_turn (L:List (Fabric N))(i:Axis)(z:ℤ):buffet (L.map fun i'=>i'.twistL i z)=reflMark i z (buffet L):=by induction L with| nil=> simp only [List.map_nil,buffet_empty]; exact funext fun k=> (theta_one _).symm| cons F L ih=> rw [List.map_cons,buffet_more, ih,buffet_more]; exact funext fun k=> (theta_mul ..).symm
include u hv in
lemma Sylvan.occupy : AtSupport false (Broad p L) (buffet L):=by
 induction L with
 | nil=>exact (show buffet ([]:List (Fabric N))=1 from buffet_empty) ▸ AtSupport.oneM _ -- rewrite direction
 | cons i L ih=>
   let hA:= u.core i List.mem_cons_self
   rw [buffet_more,Broad_more]; exact ((hv i hA).mono (subset_trans (fun x v=> halo_spec.mpr ⟨x,v,(separation_self _).le.trans (Nat.zero_le _)⟩) subset_union_left)).mulM ((ih ⟨fun k v=>u.core k (List.mem_cons_of_mem _ v), (List.pairwise_cons.mp u.annex).2⟩).mono subset_union_right)
variable {r₀ p₀ B l:ℕ}{ν:Mark N→ℂ}(a:Twosome K N ν)
lemma Sylvan.one (h:W A): Sylvan W p [A]:=⟨fun i hi=> (List.mem_singleton.mp hi).symm ▸ h,List.pairwise_singleton ..⟩
include a he hv
lemma stand (g:N=K.c m) (A:List (Fabric N)) (i:Axis)
    (f:Sylvan W p₀ A) (q:cows i (Broad p₀ A) B)(Vv:2^l*(B+addgap K)≤ N.val) :
    ∃ V:List (Fabric N),Sylvan W p₀ V ∧ V.length=2^l*A.length ∧ ‖ν (buffet A)‖^(2^l)≤ ‖ν (buffet V)‖ ∧ ∀ a,a≠i → ∀ s,cows a (Broad p₀ A) s → cows a (Broad p₀ V) s := by
 induction l generalizing B A with
 | zero=> exact ⟨A,f,by simp,by simp,fun a _ s u=>u⟩
 | succ l ih=>
    have ht:B+addgap K ≤ N.val:= Vv.trans' (Nat.le_mul_of_pos_left _ (pow_pos two_pos _)); obtain ⟨z,p,u,e⟩:=topLong (i:=i) g _ q ht; let s:= Heat.gaugeShift K.B z
    let U:= A.map fun a=> a.twistL i s; let Qw:= U++A; have h'': Broad p₀ Qw=hyphen i s (Broad p₀ A)∪ Broad p₀ A:=by unfold Qw U; rw [Broad_append,Broad_turn]; -- fix rfl
    have hp:Broad p₀ A⊆ band N i s K.ℓ:=p
    have hx: Sylvan W p₀ Qw := (f.away he i s).tack f (by rw [Broad_turn]; exact west K i s _ hp)
    have hw:= a i z (buffet A) ((f.occupy hv).mono hp)
    obtain ⟨Y,a',b,r,g'⟩:= ih Qw hx (B:=2*B+addgap K) (by rw [h'']; exact u) (by rw [pow_succ] at Vv; exact Vv.trans' (le_of_eq (by ring)))
    refine ⟨Y,a',?_,?_,fun a g t k=> g' a g t (h''.symm ▸ e a g t k)⟩
    · rw [b,pow_succ]; unfold Qw U; rw [List.length_append,List.length_map]; ring -- W/U let
    rw [pow_succ',pow_mul]; have he:reflMark i (Heat.gaugeShift K.B z) (buffet A)*buffet A=buffet Qw:=by unfold Qw U; rw [buffet_tack,buffet_turn] -- let
    rw [he] at hw; exact (pow_le_pow_left₀ (by positivity) hw _).trans r
-- spill all axes
lemma scatter (g:N=K.c m)(Vv:2^l*(B+addgap K)≤ N.val)(S:Finset Axis) (A:List (Fabric N))(f:Sylvan W p₀ A)
    (p:∀ a∈S,cows a (Broad p₀ A) B) : ∃ U:List (Fabric N), Sylvan W p₀ U ∧ U.length=(2^l)^S.card*A.length ∧ ‖ν (buffet A)‖^((2^l)^S.card) ≤ ‖ν (buffet U)‖:=by
 induction S using Finset.induction_on generalizing A with
 | empty=> exact ⟨A,f,by simp,by simp⟩
 | @insert i S x ih=>
    obtain ⟨U,hU,a₁,b,vL⟩:= stand (ν:=ν) he hv a g A i f (p i (mem_insert_self ..)) Vv
    obtain ⟨Z,gX,e,l'⟩:= ih U hU (fun s v=> vL s (fun h=>x (h ▸ v)) _ (p s (mem_insert_of_mem v))) -- extras
    rw [card_insert_of_notMem x,pow_succ']; refine ⟨Z,gX,?_,?_⟩
    · rw [e,a₁]; ring
    rw [pow_mul]; exact (pow_le_pow_left₀ (by positivity) b _).trans l'
omit a he hv
private lemma goldilock {x y:ℕ}(p:0<y)(v:y≤x):∃ k:ℕ, 2^k*y ≤ x ∧ x≤2*2^k*y:=by
  have he : x < 2^x*y:= lt_of_lt_of_le (Nat.lt_two_pow_self) (Nat.le_mul_of_pos_right _ p)
  let P(k:ℕ):= x ≤ 2*(2^k)*y
  have ht: ∃ k,P k:=⟨x,by unfold P; linarith⟩
  refine ⟨Nat.find ht,?_,Nat.find_spec ht⟩
  generalize e: Nat.find ht=k
  cases k with
  | zero=> simpa using v
  | succ k=> have h:=Nat.find_min ht (by omega : k < Nat.find ht); change ¬ x ≤ 2*2^k*y at h; rw [pow_succ']; omega
include a he hv
lemma trefoil (g:N=K.c m)(Vv:B+addgap K≤ N.val)(A:Fabric N)(f:W A)(p:∀ i,cows i (Lattice.halo p₀ A.S) B) :
    ∃ U: List (Fabric N), Sylvan W p₀ U ∧ 0<U.length ∧ U.length ≤ (More N).val^4 ∧
       (More N).val^4 ≤ U.length*(4*(B+addgap K))^4 ∧ ‖ν A.x‖^U.length≤ ‖ν (buffet U)‖:=by
 obtain ⟨k',a₁,l⟩:= goldilock (x:=N.val) (show 0 < B+addgap K from Nat.add_pos_right _ addgap_pos) Vv
 obtain ⟨U,f',H,hY⟩:= scatter (ν:=ν) he hv a g a₁ univ [A] (Sylvan.one f) (fun i b=>by simpa [Broad_more] using p i) -- whereF
 have hw:(univ: Finset Axis).card=4:=by simp [Axis]
 have hp:U.length=(2^k')^4:= by simpa [hw] using H
 refine ⟨U,f',?_,?_,?_,?_⟩
 · rw [hp]; positivity
 · change _ ≤ (N.val*2)^4; rw [hp]; apply pow_le_pow_left'; have hq:= a₁.trans' (Nat.le_mul_of_pos_right (2^k') (Nat.add_pos_right _ (show 0 < addgap K from addgap_pos))); omega
 · rw [hp,← mul_pow]; apply pow_le_pow_left'; change N.val*2 ≤_; apply le_trans (Nat.mul_le_mul_right 2 l); exact le_of_eq (by ring)
 rw [hp]; simpa only [hw,buffet_more,buffet_empty,mul_one] using hY
end Fabric
end YM.CF.Lamour.Bridge.Celeste.Clock
#print axioms YM.CF.Lamour.Bridge.Celeste.Clock.Fabric.trefoil