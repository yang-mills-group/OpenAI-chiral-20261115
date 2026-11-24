import YM.SU5.Regis.Visitations
/-!
 Reflection replication with oriented ancestry but noEtch, adapt Hookah occupancy & travel.
 Leaf sup estimate transfers, and issue any stable certificate to checker receipts (e.g.
 bounds on weighted spin word prices *if* preserved under all foil moves).
 -/
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

namespace Hookah
open scoped Classical
variable {A0 A : Hookah N}
/-- Use planes paid by Twosome; can test with proofs covering more. -/
inductive Foil (A0:Hookah N) : Hookah N→Prop where
 | base : Foil A0 A0
 | mirror {A:Hookah N} (q : Foil A0 A)(i:Axis)(z:ℤ) : Foil A0 (A.twistL i z)
lemma Foil.reflect (p:Foil A0 A) (i:Axis)(z:ℤ) : Foil A0 (A.twistL i z) := p.mirror i z
structure Visa(A0 A : Hookah N): Prop where
 foil: Foil A0 A
 owner: AtSupport false A.S A.x
lemma Foil.preserve (p:Foil A0 A)(h:AtSupport false A0.S A0.x): AtSupport false A.S A.x:=by induction p with | base=> exact h | mirror p i z ih=> exact ih.refl i z
lemma Visa.reflect (p:Visa A0 A) (i:Axis)(z:ℤ): Visa A0 (A.twistL i z):= ⟨p.foil.reflect i z,p.owner.refl i z⟩
lemma Foil.presup (p:Foil A0 A)(h:∀ x, ‖A0.x x‖ ≤ C) : ∀ x, ‖A.x x‖ ≤ C:=by
 induction p with
 | base=> exact h
 | mirror e i z ih=> intro x; unfold twistL reflMark; dsimp only; unfold theta; rw [twist_norm,norm_cc]; exact ih _

variable {L J:List (Hookah N)}
structure Shellac (A0 : Hookah N)(p:ℕ)(L:List (Hookah N)):Prop where
 core (A:Hookah N)(v:A∈L):Visa A0 A
 annex:L.Pairwise (fun i z=>Distant (p+1) i.S z.S)
variable (u:Shellac A0 p L)
namespace Shellac
include u
lemma away(i:Axis)(z:ℤ): Shellac A0 p (L.map (fun v=> v.twistL i z)):=by
 refine ⟨fun A w=>?_, List.pairwise_map.mpr (u.annex.imp fun g=> sparse_face g i z)⟩; obtain ⟨k,ψ,rfl⟩:= List.mem_map.mp w; exact (u.core k ψ).reflect i z
lemma tack (v:Shellac A0 p J)(h:Disjoint (Broad p L) (Broad p J)): Shellac A0 p (L++J):=⟨fun i g=>(List.mem_append.mp g).elim (u.core i) (v.core i), List.pairwise_append.mpr ⟨u.annex,v.annex,fun a e b g=>SparseLock (h.mono (Broad_x p L a e) (Broad_x p J b g))⟩⟩
end Shellac
include u in
lemma Shellac.occupy : AtSupport false (Broad p L) (buffet L):=by
 induction L with
 | nil=>exact (show buffet ([]:List (Hookah N))=1 from buffet_empty) ▸ AtSupport.oneM _ -- rewrite direction
 | cons i L ih=>
   let hA:= u.core i List.mem_cons_self
   rw [buffet_more,Broad_more]; exact (hA.owner.mono (subset_trans (fun x v=> halo_spec.mpr ⟨x,v,(separation_self _).le.trans (Nat.zero_le _)⟩) subset_union_left)).mulM ((ih ⟨fun k v=>u.core k (List.mem_cons_of_mem _ v), (List.pairwise_cons.mp u.annex).2⟩).mono subset_union_right)
variable {r₀ p₀ B l:ℕ}{ν:Mark N→ℂ}(a:Twosome K N ν)
lemma Shellac.one (h:Visa A0 A): Shellac A0 p [A]:=⟨fun i hi=> (List.mem_singleton.mp hi).symm ▸ h,List.pairwise_singleton ..⟩
include a
lemma spray (g:N=K.c m) (A:List (Hookah N)) (i:Axis)
    (f:Shellac A0 p₀ A) (q:cows i (Broad p₀ A) B)(Vv:2^l*(B+addgap K)≤ N.val) :
    ∃ V:List (Hookah N),Shellac A0 p₀ V ∧ V.length=2^l*A.length ∧ ‖ν (buffet A)‖^(2^l)≤ ‖ν (buffet V)‖ ∧ ∀ a,a≠i → ∀ s,cows a (Broad p₀ A) s → cows a (Broad p₀ V) s := by
 induction l generalizing B A with
 | zero=> exact ⟨A,f,by simp,by simp,fun a _ s u=>u⟩
 | succ l ih=>
    have ht:B+addgap K ≤ N.val:= Vv.trans' (Nat.le_mul_of_pos_left _ (pow_pos two_pos _)); obtain ⟨z,p,u,e⟩:=topLong (i:=i) g _ q ht; let s:= Heat.gaugeShift K.B z
    let U:= A.map fun a=> a.twistL i s; let W:= U++A; have h'': Broad p₀ W=hyphen i s (Broad p₀ A)∪ Broad p₀ A:=by unfold W U; rw [Broad_append,Broad_turn]; -- fix rfl
    have hp:Broad p₀ A⊆ band N i s K.ℓ:=p
    have hx: Shellac A0 p₀ W := (f.away i s).tack f (by rw [Broad_turn]; exact west K i s _ hp)
    have hw:= a i z (buffet A) (f.occupy.mono hp)
    obtain ⟨Y,a',b,r,g'⟩:= ih W hx (B:=2*B+addgap K) (by rw [h'']; exact u) (by rw [pow_succ] at Vv; exact Vv.trans' (le_of_eq (by ring)))
    refine ⟨Y,a',?_,?_,fun a g t k=> g' a g t (h''.symm ▸ e a g t k)⟩
    · rw [b,pow_succ]; unfold W U; rw [List.length_append,List.length_map]; ring -- W/U let
    rw [pow_succ',pow_mul]; have he:reflMark i (Heat.gaugeShift K.B z) (buffet A)*buffet A=buffet W:=by unfold W U; rw [buffet_tack,buffet_turn] -- let
    rw [he] at hw; exact (pow_le_pow_left₀ (by positivity) hw _).trans r
-- spill all axes
lemma cascade (g:N=K.c m)(Vv:2^l*(B+addgap K)≤ N.val)(S:Finset Axis) (A:List (Hookah N))(f:Shellac A0 p₀ A)
    (p:∀ a∈S,cows a (Broad p₀ A) B) : ∃ U:List (Hookah N), Shellac A0 p₀ U ∧ U.length=(2^l)^S.card*A.length ∧ ‖ν (buffet A)‖^((2^l)^S.card) ≤ ‖ν (buffet U)‖:=by
 induction S using Finset.induction_on generalizing A with
 | empty=> exact ⟨A,f,by simp,by simp⟩
 | @insert i S x ih=>
    obtain ⟨U,hU,a₁,b,vL⟩:= spray (ν:=ν) a g A i f (p i (mem_insert_self ..)) Vv
    obtain ⟨Z,gX,e,l'⟩:= ih U hU (fun s v=> vL s (fun h=>x (h ▸ v)) _ (p s (mem_insert_of_mem v))) -- extras
    rw [card_insert_of_notMem x,pow_succ']; refine ⟨Z,gX,?_,?_⟩
    · rw [e,a₁]; ring
    rw [pow_mul]; exact (pow_le_pow_left₀ (by positivity) b _).trans l'
omit a
private lemma goldilock {x y:ℕ}(p:0<y)(v:y≤x):∃ k:ℕ, 2^k*y ≤ x ∧ x≤2*2^k*y:=by
  have he : x < 2^x*y:= lt_of_lt_of_le (Nat.lt_two_pow_self) (Nat.le_mul_of_pos_right _ p)
  let P(k:ℕ):= x ≤ 2*(2^k)*y
  have ht: ∃ k,P k:=⟨x,by unfold P; linarith⟩
  refine ⟨Nat.find ht,?_,Nat.find_spec ht⟩
  generalize e: Nat.find ht=k
  cases k with
  | zero=> simpa using v
  | succ k=> have h:=Nat.find_min ht (by omega : k < Nat.find ht); change ¬ x ≤ 2*2^k*y at h; rw [pow_succ']; omega
include a
lemma cavalcade (g:N=K.c m)(Vv:B+addgap K≤ N.val)(A:Hookah N)(f:Visa A0 A)(p:∀ i,cows i (Lattice.halo p₀ A.S) B) :
    ∃ U: List (Hookah N), Shellac A0 p₀ U ∧ 0<U.length ∧ U.length ≤ (More N).val^4 ∧
       (More N).val^4 ≤ U.length*(4*(B+addgap K))^4 ∧ ‖ν A.x‖^U.length≤ ‖ν (buffet U)‖:=by
 obtain ⟨k',a₁,l⟩:= goldilock (x:=N.val) (show 0 < B+addgap K from Nat.add_pos_right _ addgap_pos) Vv
 obtain ⟨U,f',H,hY⟩:= cascade (ν:=ν) a g a₁ univ [A] (Shellac.one f) (fun i b=>by simpa [Broad_more] using p i) -- whereF
 have hw:(univ: Finset Axis).card=4:=by simp [Axis]
 have hp:U.length=(2^k')^4:= by simpa [hw] using H
 refine ⟨U,f',?_,?_,?_,?_⟩
 · rw [hp]; positivity
 · change _ ≤ (N.val*2)^4; rw [hp]; apply pow_le_pow_left'; have hq:= a₁.trans' (Nat.le_mul_of_pos_right (2^k') (Nat.add_pos_right _ (show 0 < addgap K from addgap_pos))); omega
 · rw [hp,← mul_pow]; apply pow_le_pow_left'; change N.val*2 ≤_; apply le_trans (Nat.mul_le_mul_right 2 l); exact le_of_eq (by ring)
 rw [hp]; simpa only [hw,buffet_more,buffet_empty,mul_one] using hY
omit a
lemma Shellac.presup (H:∀ x,‖A0.x x‖≤C)(u:Shellac A0 p L)(v:0≤C) (U:Fields N) : ‖buffet L U‖ ≤ C^L.length:=by
 induction L with| nil=> simp [buffet]| cons i L ih=> rw [List.length_cons,pow_succ',buffet_more,Pi.mul_apply]; refine (norm_mul_le ..).trans (mul_le_mul ((u.core i List.mem_cons_self).foil.presup H U) (ih ⟨fun i t=> u.core i (List.mem_cons_of_mem _ t), (List.pairwise_cons.mp u.annex).2⟩) (norm_nonneg _) v)
end Hookah
end YM.CF.Lamour.Bridge.Celeste.Clock
#print axioms YM.CF.Lamour.Bridge.Celeste.Clock.Hookah.cavalcade
