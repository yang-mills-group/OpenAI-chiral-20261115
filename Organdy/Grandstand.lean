import Organdy.Roast
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 260000
noncomputable section
namespace YM.CF.Organdy.Royal
open Lamour.Bridge.Celeste.Clock
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye CF.Pannier.Chancel Brace Velvet Hours Flare Cliplet RG Reed
open Py.Rate.Pannier
open Buffered.Afterglow
open Next.Rank.Thirst
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
variable {K:Calibration}{N m:Side}{j r p d t:ℕ}{M:Tulip.Male}{ε ξ σ C D:ℝ}
open Lamour.Bridge.Celeste
open Hookah
open Regis.Head Etch Regis.Head.Garland
open scoped Classical
open Scree

open Organdy Optic Scree Push.Local

structure Club (N:Side) where
 accepts : Hookah N→Prop
 title (A):accepts A→AtSupport false A.S A.x
 dance (A)(i:Axis)(d:ℤ):accepts A→ accepts (A.twistL i d)

variable {G:Club N} {A:Hookah N}
variable {L J:List (Hookah N)}
structure Romp (G:Club N)(p:ℕ)(L:List (Hookah N)):Prop where
 core (A:Hookah N)(v:A∈L):G.accepts A
 annex:L.Pairwise (fun i z=>Distant (p+1) i.S z.S)
variable (u:Romp G p L)
namespace Romp
include u
lemma away(i:Axis)(z1:ℤ): Romp G p (L.map (fun v=> v.twistL i z1)):=by
 refine ⟨fun A w=>?_, List.pairwise_map.mpr (u.annex.imp fun g=> sparse_face g i z1)⟩; obtain ⟨k,ψ,rfl⟩:= List.mem_map.mp w; exact G.dance _ _ _ (u.core k ψ)
lemma tack (v:Romp G p J)(h:Disjoint (Broad p L) (Broad p J)): Romp G p (L++J):=⟨fun i g=>(List.mem_append.mp g).elim (u.core i) (v.core i), List.pairwise_append.mpr ⟨u.annex,v.annex,fun a e b g=>SparseLock (h.mono (Broad_x p L a e) (Broad_x p J b g))⟩⟩
end Romp
include u in
lemma Romp.occupy : AtSupport false (Broad p L) (buffet L):=by
 induction L with
 | nil=>exact (show buffet ([]:List (Hookah N))=1 from buffet_empty) ▸ AtSupport.oneM _ -- rewrite direction
 | cons i L ih=>
   let hA:= u.core i List.mem_cons_self
   rw [buffet_more,Broad_more]; exact ((G.title _ hA).mono (subset_trans (fun x v=> halo_spec.mpr ⟨x,v,(separation_self _).le.trans (Nat.zero_le _)⟩) subset_union_left)).mulM ((ih ⟨fun k v=>u.core k (List.mem_cons_of_mem _ v), (List.pairwise_cons.mp u.annex).2⟩).mono subset_union_right)
variable {r₀ p₀ B l:ℕ}{ν:Mark N→ℂ}(wc:Twosome K N ν)
lemma Romp.one (h:G.accepts A): Romp G p [A]:=⟨fun i hi=> (List.mem_singleton.mp hi).symm ▸ h,List.pairwise_singleton ..⟩
include wc
lemma stance (g:N=K.c m) (A:List (Hookah N)) (i:Axis)
    (f:Romp G p₀ A) (q:cows i (Broad p₀ A) B)(Vv:2^l*(B+addgap K)≤ N.val) :
    ∃ V:List (Hookah N),Romp G p₀ V ∧ V.length=2^l*A.length ∧ ‖ν (buffet A)‖^(2^l)≤ ‖ν (buffet V)‖ ∧ ∀ a,a≠i → ∀ s,cows a (Broad p₀ A) s → cows a (Broad p₀ V) s := by
 induction l generalizing B A with
 | zero=> exact ⟨A,f,by simp,by simp,fun a _ s u=>u⟩
 | succ l ih=>
    have ht:B+addgap K ≤ N.val:= Vv.trans' (Nat.le_mul_of_pos_left _ (pow_pos two_pos _)); obtain ⟨z1,p,u,e⟩:=topLong (i:=i) g _ q ht; let s:= Heat.gaugeShift K.B z1
    let U:= A.map fun a=> a.twistL i s; let WW:= U++A; have h'': Broad p₀ WW=hyphen i s (Broad p₀ A)∪ Broad p₀ A:=by unfold WW U; rw [Broad_append,Broad_turn]; -- fix rfl
    have hp:Broad p₀ A⊆ band N i s K.ℓ:=p
    have hx: Romp G p₀ WW := (f.away i s).tack f (by rw [Broad_turn]; exact west K i s _ hp)
    have hw:= wc i z1 (buffet A) (f.occupy.mono hp)
    obtain ⟨Y,a',b,r,g'⟩:= ih WW hx (B:=2*B+addgap K) (by rw [h'']; exact u) (by rw [pow_succ] at Vv; exact Vv.trans' (le_of_eq (by ring)))
    refine ⟨Y,a',?_,?_,fun a g t k=> g' a g t (h''.symm ▸ e a g t k)⟩
    · rw [b,pow_succ]; unfold WW U; rw [List.length_append,List.length_map]; ring -- WW/U let
    rw [pow_succ',pow_mul]; have he:reflMark i (Heat.gaugeShift K.B z1) (buffet A)*buffet A=buffet WW:=by unfold WW U; rw [buffet_tack,buffet_turn] -- let
    rw [he] at hw; exact (pow_le_pow_left₀ (by positivity) hw _).trans r
-- spill all axes
lemma scattering (g:N=K.c m)(Vv:2^l*(B+addgap K)≤ N.val)(S:Finset Axis) (A:List (Hookah N))(f:Romp G p₀ A)
    (p:∀ a∈S,cows a (Broad p₀ A) B) : ∃ U:List (Hookah N), Romp G p₀ U ∧ U.length=(2^l)^S.card*A.length ∧ ‖ν (buffet A)‖^((2^l)^S.card) ≤ ‖ν (buffet U)‖:=by
 induction S using Finset.induction_on generalizing A with
 | empty=> exact ⟨A,f,by simp,by simp⟩
 | @insert i S x ih=>
    obtain ⟨U,hU,a₁,b,vL⟩:= stance (ν:=ν) wc g A i f (p i (mem_insert_self ..)) Vv
    obtain ⟨Z,gX,e,l'⟩:= ih U hU (fun s v=> vL s (fun h=>x (h ▸ v)) _ (p s (mem_insert_of_mem v))) -- extras
    rw [card_insert_of_notMem x,pow_succ']; refine ⟨Z,gX,?_,?_⟩
    · rw [e,a₁]; ring
    rw [pow_mul]; exact (pow_le_pow_left₀ (by positivity) b _).trans l'
omit wc
private lemma goldilock {x y:ℕ}(p:0<y)(v:y≤x):∃ k:ℕ, 2^k*y ≤ x ∧ x≤2*2^k*y:=by
  have he : x < 2^x*y:= lt_of_lt_of_le (Nat.lt_two_pow_self) (Nat.le_mul_of_pos_right _ p)
  let P(k:ℕ):= x ≤ 2*(2^k)*y
  have ht: ∃ k,P k:=⟨x,by unfold P; linarith⟩
  refine ⟨Nat.find ht,?_,Nat.find_spec ht⟩
  generalize e: Nat.find ht=k
  cases k with
  | zero=> simpa using v
  | succ k=> have h:=Nat.find_min ht (by omega : k < Nat.find ht); change ¬ x ≤ 2*2^k*y at h; rw [pow_succ']; omega
include wc

/-- pack chronological bundle, length dyadic. charge density *not* scaling with m' -/
lemma champagne (g:N=K.c m)(j:Axis)(A:List (Hookah N))(f:Romp G p₀ A)
 (m':ℕ)(c:A.length=2^m')
 (h:(2^m')*(B+addgap K)≤ N.val)
 (p:∀ y,y≠j→cows y (Broad p₀ A) B)
 {d:ℕ}(t:d+addgap K=(2^m')*(B+addgap K))
 (q:cows j (Broad p₀ A) d):
    ∃ U: List (Hookah N), Romp G p₀ U ∧ U.length ≤ (More N).val^4 ∧
       (More N).val^4 ≤ U.length*(4*(B+addgap K))^4 ∧
       ∃ k:ℕ, 0<k ∧ U.length=k*A.length ∧ ‖ν (buffet A)‖^k ≤ ‖ν (buffet U)‖:=by
 rw [←t] at h
 obtain ⟨k',a,l₁⟩:= goldilock (Nat.add_pos_right d (show 0<addgap K from addgap_pos)) h
 obtain ⟨D,v,e,z,b⟩:=stance wc g A j f q a
 rw [c,←pow_add] at e
 rw [t,←mul_assoc,←pow_add] at a
 let r:=k'+m'
 let F:= (univ : Finset Axis).erase j
 have b':∀ y∈F,cows y (Broad p₀ D) B:=fun y g=>b y (mem_erase.mp g).1 _ (p y (mem_erase.mp g).1)

 obtain ⟨U,u,w,y⟩:= scattering wc g a F D v b'
 have hw:F.card=3:=by unfold F; rw [card_erase_of_mem (mem_univ _)]; simp [Axis]
 rw [hw] at w y
 have hp:U.length=(2^r)^4:= by rw [w,e]; change (2^r)^3*2^r=_; rw [←pow_succ] -- simp pow_succ maybe acts on k'
 have hz:N.val≤2*2^r*(B+addgap K):=l₁.trans_eq (by rw [t];unfold r; rw [pow_add]; ring)
 refine ⟨U,u,?_,?_,2^k'*(2^r)^3,by positivity,?_,?_⟩
 · change _ ≤ (N.val*2)^4; rw [hp]; apply pow_le_pow_left'; have hq:= (show 2^r * (B+addgap K) ≤ N.val from a).trans' (Nat.le_mul_of_pos_right (2^r) (Nat.add_pos_right _ (show 0 < addgap K from addgap_pos))); omega
 · rw [hp,← mul_pow]; apply pow_le_pow_left'; change N.val*2 ≤_; apply le_trans (Nat.mul_le_mul_right 2 hz); exact le_of_eq (by ring)
 · rw [hp,c,mul_right_comm (2^k'),←pow_add];ring_nf; unfold r;ring
 rw [pow_mul]; exact (pow_le_pow_left₀ (by positivity) z _).trans y
#print axioms champagne

