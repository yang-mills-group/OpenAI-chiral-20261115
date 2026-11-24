import YM.SU5.FiniteGaugeData.Pannier.Sheds
import YM.SU5.FiniteGaugeData.Marked.Journey.Smokestack
/-!
# Twosome replicator. Consume actual-period Wick or Metered inputs without
requiring stride divisibility, furnish many supports in one period.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Pannier.Chancel
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye Cliplet RG Brace
open Py.Rate (sites)
open Py.Rate.Pannier
open Buffered.Afterglow Buffered.Afterglow.Journey
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
variable {K:Calibration}{N m n:Side}{B l: ℕ}
-- general with hn, easier transports
abbrev Twosome (K:Calibration)(N:Side)(X:Mark N→ℂ): Prop := ∀ a z, ∀ f: Mark N, AtSupport false (band N a (Heat.gaugeShift K.B z) K.ℓ) f → ‖X f‖^2≤‖X (reflMark a (Heat.gaugeShift K.B z) f*f)‖
def cows {N: Side}(x:Axis)(S: Finset (Seat N))(w:ℕ):= ∃ t:ℤ,∀ y∈S, Chord t w (y x)
lemma topLong {i:Axis}(G:N=K.c m)(D:Finset (Seat N))(g:cows i D B)(h:B+addgap K≤N.val) : ∃ z:ℤ, let s:= Heat.gaugeShift K.B z; let E:= hyphen i s D∪ D
           D ⊆ band N i s K.ℓ ∧ cows i E (2*B+addgap K) ∧ ∀ a:Axis,a≠i → ∀ d', cows a D d' → cows a E d':=by subst N; exact twice i g h -- undeclared
lemma west (K:Calibration)(a:Axis)(s:ℤ)(S:Finset (Seat N))(p:S⊆ band N a s K.ℓ):Disjoint (hyphen a s S) S:= by
 apply disjoint_left.mpr; intro x v q; have he:= margin_separate a s K.buffer x x ((image_subset_image p) v) (p q); rw [separation_self] at he; omega
namespace Cliplet
variable {ν:Mark n→ℂ}{M:Tulip.Male}{R:ℝ}{j k w d t:ℕ}{γ τ:ℝ}
structure StageTw (K:Calibration)(ν:Mark n→ℂ)(j:ℕ)(R:ℝ)(d:ℕ)(M:Tulip.Male) : Prop where
 heat : Twosome K n ν
 across : ∀ (i:Axis) (s:ℤ) b, twist (carR i s n) (sp b j M (1:Pane n))=sp (!b) j M (1:Pane n)
 hire : ∀ b (S:Finset (Seat n)),Sparse d S → HearthB R (sp b j M (1:Pane n)) S
variable (h:StageTw K ν j R d M)
namespace StageTw
include h
lemma stand (g:n=K.c m) (A:List (Cliplet n k)) (i:Axis)
    (f:Flight j M w d t γ τ A) (q:cows i (whereV A) B)(v:2^l*(B+addgap K)≤ n.val) :
    ∃ V:List (Cliplet n k),Flight j M w d t γ τ V ∧ V.length=2^l*A.length ∧ ‖ν (probe A)‖^(2^l)≤ ‖ν (probe V)‖ ∧ ∀ a,a≠i → ∀ s,cows a (whereV A) s → cows a (whereV V) s := by
 induction l generalizing B A with
 | zero=> exact ⟨A,f,by simp,by simp,fun a _ s u=>u⟩
 | succ l ih=>
    have ht:B+addgap K ≤ n.val:= v.trans' (Nat.le_mul_of_pos_left _ (pow_pos two_pos _)); obtain ⟨z,p,u,e⟩:=topLong (i:=i) g _ q ht; let s:= Heat.gaugeShift K.B z
    let U:= A.map fun a=> a.mirror i s; let W:= U++A; have h'': whereV W=hyphen i s (whereV A)∪ whereV A:=by unfold W U; rw [combine,Flight.reflect_consistent]; -- fix rfl
    have hp:whereV A⊆ band n i s K.ℓ:=p
    have hx: Flight j M w d t γ τ W := (f.reflect i s (h.across i s) h.hire).tack _ f (by rw [Flight.reflect_consistent]; exact west K i s _ hp) -- wtf
    have hw:= h.heat i z (probe A) (f.permit hp)
    obtain ⟨Y,a,b,r,g'⟩:= ih W hx (B:=2*B+addgap K) (by rw [h'']; exact u) (by rw [pow_succ] at v; exact v.trans' (le_of_eq (by ring)))
    refine ⟨Y,a,?_,?_,fun a g t k=> g' a g t (h''.symm ▸ e a g t k)⟩
    · rw [b,pow_succ]; unfold W U; rw [List.length_append,List.length_map]; ring -- W/U let
    rw [pow_succ',pow_mul]; have he:reflMark i (Heat.gaugeShift K.B z) (probe A)*probe A=probe W:=by unfold W U; rw [probe_combine,Flight.reflect_probes] -- let
    rw [he] at hw; exact (pow_le_pow_left₀ (by positivity) hw _).trans r
-- spill all axes
lemma scatter (g:n=K.c m)(v:2^l*(B+addgap K)≤ n.val)(S:Finset Axis) (A:List (Cliplet n k))(f:Flight j M w d t γ τ A)
    (p:∀ a∈S,cows a (whereV A) B) : ∃ U:List (Cliplet n k), Flight j M w d t γ τ U ∧ U.length=(2^l)^S.card*A.length ∧ ‖ν (probe A)‖^((2^l)^S.card) ≤ ‖ν (probe U)‖:=by
 induction S using Finset.induction_on generalizing A with
 | empty=> exact ⟨A,f,by simp,by simp⟩
 | @insert i S x ih=>
    obtain ⟨U,hU,a,b,vL⟩:= h.stand g A i f (p i (mem_insert_self ..)) v
    obtain ⟨Z,gX,e,l'⟩:= ih U hU (fun s v=> vL s (fun h=>x (h ▸ v)) _ (p s (mem_insert_of_mem v))) -- extras
    rw [card_insert_of_notMem x,pow_succ']; refine ⟨Z,gX,?_,?_⟩
    · rw [e,a]; ring
    rw [pow_mul]; exact (pow_le_pow_left₀ (by positivity) b _).trans l'
omit h
private lemma goldilock {x y:ℕ}(p:0<y)(v:y≤x):∃ k:ℕ, 2^k*y ≤ x ∧ x≤2*2^k*y:=by
  have he : x < 2^x*y:= lt_of_lt_of_le (Nat.lt_two_pow_self) (Nat.le_mul_of_pos_right _ p)
  let P(k:ℕ):= x ≤ 2*(2^k)*y
  have ht: ∃ k,P k:=⟨x,by unfold P; linarith⟩
  refine ⟨Nat.find ht,?_,Nat.find_spec ht⟩
  generalize e: Nat.find ht=k
  cases k with
  | zero=> simpa using v
  | succ k=> have h:=Nat.find_min ht (by omega : k < Nat.find ht); change ¬ x ≤ 2*2^k*y at h; rw [pow_succ']; omega
include h
lemma trefoil (g:n=K.c m)(v:B+addgap K≤ n.val)(A:Cliplet n k)(f:Perron j M w d t γ τ A)(p:∀ i,cows i A.broad B) :
    ∃ U: List (Cliplet n k), Flight j M w d t γ τ U ∧ 0<U.length ∧ U.length ≤ (More n).val^4 ∧
       (More n).val^4 ≤ U.length*(4*(B+addgap K))^4 ∧ ‖ν A.frame‖^U.length≤ ‖ν (probe U)‖:=by
 obtain ⟨k',a,l⟩:= goldilock (x:=n.val) (show 0 < B+addgap K from Nat.add_pos_right _ addgap_pos) v
 obtain ⟨U,f',H,hY⟩:= h.scatter g a univ [A] (Flight.alone f) (fun i b=>by simpa [whereV] using p i) -- whereF
 have hw:(univ: Finset Axis).card=4:=by simp [Axis]
 have hp:U.length=(2^k')^4:= by simpa [hw] using H
 refine ⟨U,f',?_,?_,?_,?_⟩
 · rw [hp]; positivity
 · change _ ≤ (n.val*2)^4; rw [hp]; apply pow_le_pow_left'; have hq:= a.trans' (Nat.le_mul_of_pos_right (2^k') (Nat.add_pos_right _ (show 0 < addgap K from addgap_pos))); omega
 · rw [hp,← mul_pow]; apply pow_le_pow_left'; change n.val*2 ≤_; apply le_trans (Nat.mul_le_mul_right 2 l); exact le_of_eq (by ring)
 rw [hp]; simpa only [hw,probe_cons,probe_nil,mul_one] using hY
end StageTw
end Cliplet
end YM.CF.Pannier.Chancel
#print axioms YM.CF.Pannier.Chancel.Cliplet.StageTw.trefoil
