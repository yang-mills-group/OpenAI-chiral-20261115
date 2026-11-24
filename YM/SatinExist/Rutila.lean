import YM.SatinExist.Taffy
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 260000
noncomputable section
namespace YM.CF.Lamour.Bridge.Celeste
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye Pannier.Chancel Brace Velvet Hours Flare Cliplet RG Reed
open Py.Rate.Pannier
open Buffered.Afterglow
open Next.Rank.Thirst
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
variable {K:Calibration}{N m:Side}{j r p d t:ℕ}{M:Tulip.Male}{ε ξ σ C D:ℝ}

open Sonnet
namespace SpotP
def SmallG (f:Mark N) : Prop:=∀ V,∃ k:ℂ, f V=k • 1 ∧ ‖k‖≤1
structure CupC(j r d:ℕ)(M:Tulip.Male) (ε ξ C D:ℝ) (A:Sonnet N):Prop where
 owner : AtSupport false A.S A.x
 slotT : A.o∈A.S
 pay : SmallG A.x
lemma CupC.reflect {A:Sonnet N}(c:CupC j r d M ε ξ C D A) (_:HaloTw j N)(i:Axis)(z:ℤ): CupC j r d M ε ξ C D (A.twistL i z):=by
 refine ⟨c.owner.refl i z,mem_image_of_mem _ c.slotT, fun V=>?_⟩; dsimp only [twistL,reflMark]; obtain ⟨k,h,u⟩:= c.pay (reflFields i z V)
 exact ⟨star k,by rw [h,theta_smul,theta_one],(norm_star k).le.trans u⟩
variable {A:Sonnet N}
variable {L J:List (Sonnet N)}
structure Sylvia (j r d p:ℕ)(M:Tulip.Male)(ε ξ C D:ℝ)(L:List (Sonnet N)):Prop where
 core (A:Sonnet N)(v:A∈L):CupC j r d M ε ξ C D A
 annex:L.Pairwise (fun i z=>Distant (p+1) i.S z.S)
variable (u:Sylvia j r d p M ε ξ C D L)
/-- two-Pane raw gauges of cost at most one. not changing matter weight here. -/
lemma larder (L:List (Sonnet N))(pL:Sylvia j r d p M ε ξ C D L): SmallG (buffet L) := by
 induction L with
 | nil=> intro V; exact ⟨1,(by rw [one_smul]; rfl),by simp⟩
 | cons i L ih=>
    intro V; obtain ⟨u,t,hu⟩:= (pL.core i List.mem_cons_self).pay V
    obtain ⟨b,e,hb⟩:= ih ⟨fun k v=>pL.core k (List.mem_cons_of_mem _ v), (List.pairwise_cons.mp pL.annex).2⟩ V
    refine ⟨u*b,?_,(norm_mul _ _).le.trans (mul_le_one₀ hu (by positivity) hb)⟩
    rw [buffet_more,Pi.mul_apply,t,e, Matrix.smul_mul, Matrix.mul_smul, one_mul,smul_smul]
namespace Sylvia

include u
lemma away(i:Axis)(z:ℤ)(g:HaloTw j N) : Sylvia j r d p M ε ξ C D (L.map (fun v=> v.twistL i z)):=by
 refine ⟨fun A w=>?_, List.pairwise_map.mpr (u.annex.imp fun g=> sparse_face g i z)⟩; obtain ⟨k,ψ,rfl⟩:= List.mem_map.mp w; exact (u.core k ψ).reflect g i z
lemma tack (v:Sylvia j r d p M ε ξ C D J)(h:Disjoint (Broad p L) (Broad p J)): Sylvia j r d p M ε ξ C D (L++J):=⟨fun i g=>(List.mem_append.mp g).elim (u.core i) (v.core i), List.pairwise_append.mpr ⟨u.annex,v.annex,fun a e b g=>Sonnet.SparseLock (h.mono (Broad_x p L a e) (Broad_x p J b g))⟩⟩
end Sylvia
include u in
lemma Sylvia.occupy : AtSupport false (Broad p L) (buffet L):=by
 induction L with
 | nil=>exact (show buffet ([]:List (Sonnet N))=1 from buffet_empty) ▸ AtSupport.oneM _ -- rewrite direction
 | cons i L ih=>
   let hA:= u.core i List.mem_cons_self
   rw [buffet_more,Broad_more]; exact (hA.owner.mono (subset_trans (fun x v=> halo_spec.mpr ⟨x,v,(separation_self _).le.trans (Nat.zero_le _)⟩) subset_union_left)).mulM ((ih ⟨fun k v=>u.core k (List.mem_cons_of_mem _ v), (List.pairwise_cons.mp u.annex).2⟩).mono subset_union_right)
variable {r₀ p₀ B l:ℕ}{ν:Mark N→ℂ}(h:HaloTw j N) (a:Twosome K N ν)
lemma Sylvia.one (h:CupC j r d M ε ξ C D A): Sylvia j r d p M ε ξ C D [A]:=⟨fun i hi=> (List.mem_singleton.mp hi).symm ▸ h,List.pairwise_singleton ..⟩
include h a
lemma stand (g:N=K.c m) (A:List (Sonnet N)) (i:Axis)
    (f:Sylvia j r₀ d p₀ M ε ξ C σ A) (q:cows i (Broad p₀ A) B)(Vv:2^l*(B+addgap K)≤ N.val) :
    ∃ V:List (Sonnet N),Sylvia j r₀ d p₀ M ε ξ C σ V ∧ V.length=2^l*A.length ∧ ‖ν (buffet A)‖^(2^l)≤ ‖ν (buffet V)‖ ∧ ∀ a,a≠i → ∀ s,cows a (Broad p₀ A) s → cows a (Broad p₀ V) s := by
 induction l generalizing B A with
 | zero=> exact ⟨A,f,by simp,by simp,fun a _ s u=>u⟩
 | succ l ih=>
    have ht:B+addgap K ≤ N.val:= Vv.trans' (Nat.le_mul_of_pos_left _ (pow_pos two_pos _)); obtain ⟨z,p,u,e⟩:=topLong (i:=i) g _ q ht; let s:= Heat.gaugeShift K.B z
    let U:= A.map fun a=> a.twistL i s; let W:= U++A; have h'': Broad p₀ W=hyphen i s (Broad p₀ A)∪ Broad p₀ A:=by unfold W U; rw [Broad_append,Broad_turn]; -- fix rfl
    have hp:Broad p₀ A⊆ band N i s K.ℓ:=p
    have hx: Sylvia j r₀ d p₀ M ε ξ C σ W := (f.away i s h).tack f (by rw [Broad_turn]; exact west K i s _ hp)
    have hw:= a i z (buffet A) (f.occupy.mono hp)
    obtain ⟨Y,a',b,r,g'⟩:= ih W hx (B:=2*B+addgap K) (by rw [h'']; exact u) (by rw [pow_succ] at Vv; exact Vv.trans' (le_of_eq (by ring)))
    refine ⟨Y,a',?_,?_,fun a g t k=> g' a g t (h''.symm ▸ e a g t k)⟩
    · rw [b,pow_succ]; unfold W U; rw [List.length_append,List.length_map]; ring -- W/U let
    rw [pow_succ',pow_mul]; have he:reflMark i (Heat.gaugeShift K.B z) (buffet A)*buffet A=buffet W:=by unfold W U; rw [buffet_tack,buffet_turn] -- let
    rw [he] at hw; exact (pow_le_pow_left₀ (by positivity) hw _).trans r
-- spill all axes
lemma scatter (g:N=K.c m)(Vv:2^l*(B+addgap K)≤ N.val)(S:Finset Axis) (A:List (Sonnet N))(f:Sylvia j r₀ d p₀ M ε ξ C σ A)
    (p:∀ a∈S,cows a (Broad p₀ A) B) : ∃ U:List (Sonnet N), Sylvia j r₀ d p₀ M ε ξ C σ U ∧ U.length=(2^l)^S.card*A.length ∧ ‖ν (buffet A)‖^((2^l)^S.card) ≤ ‖ν (buffet U)‖:=by
 induction S using Finset.induction_on generalizing A with
 | empty=> exact ⟨A,f,by simp,by simp⟩
 | @insert i S x ih=>
    obtain ⟨U,hU,a₁,b,vL⟩:= stand (ν:=ν) h a g A i f (p i (mem_insert_self ..)) Vv
    obtain ⟨Z,gX,e,l'⟩:= ih U hU (fun s v=> vL s (fun h=>x (h ▸ v)) _ (p s (mem_insert_of_mem v))) -- extras
    rw [card_insert_of_notMem x,pow_succ']; refine ⟨Z,gX,?_,?_⟩
    · rw [e,a₁]; ring
    rw [pow_mul]; exact (pow_le_pow_left₀ (by positivity) b _).trans l'
end SpotP
end YM.CF.Lamour.Bridge.Celeste
