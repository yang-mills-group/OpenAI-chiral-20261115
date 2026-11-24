import YM.SU5.Relativistic.Tropics
import YM.SU5.FiniteGaugeData.Marked.Journey.Smokestack
/-!
Adapt TallPea layout/scatter to ANY company of wedges. m differs per prop.
# Twosome replicator. Consume actual-period Wick or Metered inputs without
requiring stride divisibility, furnish many supports in one period.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Pannier.Chancel.ScreeV
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye Cliplet RG Brace
open Py.Rate (sites)
open Py.Rate.Pannier
open Buffered.Afterglow Buffered.Afterglow.Journey
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
variable {K:Calibration}{N m n:Side}{B l: ℕ}
variable {K₀:Calibration}{j k w d t l₀:ℕ}{R R' ε γ γ' τ:ℝ}{M:Tulip.Male}{ν:Mark n→ℂ}
variable (h:StageTw K ν j R d M)
include h
lemma conquest (g:n=K.c m) (A:List (Cliplet n k)) (i:Axis)
    (f:Company j M w d l₀ t γ γ' τ ε R' A) (q:cows i (whereV A) B)(v:2^l*(B+addgap K)≤ n.val) :
    ∃ V:List (Cliplet n k),Company j M w d l₀ t γ γ' τ ε R' V ∧ V.length=2^l*A.length ∧ ‖ν (probe A)‖^(2^l)≤ ‖ν (probe V)‖ ∧ ∀ a,a≠i → ∀ s,cows a (whereV A) s → cows a (whereV V) s := by
 induction l generalizing B A with
 | zero=> exact ⟨A,f,by simp,by simp,fun a _ s u=>u⟩
 | succ l ih=>
    have ht:B+addgap K ≤ n.val:= v.trans' (Nat.le_mul_of_pos_left _ (pow_pos two_pos _)); obtain ⟨z,p,u,e⟩:=topLong (i:=i) g _ q ht; let s:= Heat.gaugeShift K.B z
    let U:= A.map fun a=> a.mirror i s; let W:= U++A; have h'': whereV W=hyphen i s (whereV A)∪ whereV A:=by unfold W U; rw [combine,Flight.reflect_consistent]; -- fix rfl
    have hp:whereV A⊆ band n i s K.ℓ:=p
    have hx: Company j M w d l₀ t γ γ' τ ε R' W := (f.cloud i s (h.across i s)).tack _ f (by rw [Flight.reflect_consistent]; exact west K i s _ hp) -- wtf
    have hw:= h.heat i z (probe A) (f.permit hp)
    obtain ⟨Y,a,b,r,g'⟩:= ih W hx (B:=2*B+addgap K) (by rw [h'']; exact u) (by rw [pow_succ] at v; exact v.trans' (le_of_eq (by ring)))
    refine ⟨Y,a,?_,?_,fun a g t k=> g' a g t (h''.symm ▸ e a g t k)⟩
    · rw [b,pow_succ]; unfold W U; rw [List.length_append,List.length_map]; ring -- W/U let
    rw [pow_succ',pow_mul]; have he:reflMark i (Heat.gaugeShift K.B z) (probe A)*probe A=probe W:=by unfold W U; rw [probe_combine,Flight.reflect_probes] -- let
    rw [he] at hw; exact (pow_le_pow_left₀ (by positivity) hw _).trans r
-- spill all axes
lemma expend (g:n=K.c m)(v:2^l*(B+addgap K)≤ n.val)(S:Finset Axis) (A:List (Cliplet n k))(f:Company j M w d l₀ t γ γ' τ ε R' A)
    (p:∀ a∈S,cows a (whereV A) B) : ∃ U:List (Cliplet n k), Company j M w d l₀ t γ γ' τ ε R' U ∧ U.length=(2^l)^S.card*A.length ∧ ‖ν (probe A)‖^((2^l)^S.card) ≤ ‖ν (probe U)‖:=by
 induction S using Finset.induction_on generalizing A with
 | empty=> exact ⟨A,f,by simp,by simp⟩
 | @insert i S x ih=>
    obtain ⟨U,hU,a,b,vL⟩:= conquest h g A i f (p i (mem_insert_self ..)) v
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
-- no budget role of filling factor as a new prior. Plan explicit width equation.
include h
lemma prism (z:n=K.c m)(T:Axis){A B:ℕ}(p:A+addgap K≤ n.val)(g:B+addgap K≤ n.val)
    (L:List (Cliplet n k))(U:Company j M w d l₀ t γ γ' τ ε R' L)
    (hv:cows T (whereV L) A)(hx:∀ x≠ T, cows x (whereV L) B):
     ∃ f> (0:ℕ),∃ L':List (Cliplet n k), Company j M w d l₀ t γ γ' τ ε R' L' ∧ L'.length=f*L.length ∧ ‖ν (probe L)‖^f ≤ ‖ν (probe L')‖ ∧ (More n).val^4 ≤ f*(4*(A+addgap K))*(4*(B+addgap K))^3:=by
 obtain ⟨i,a,b⟩:= goldilock (show 0<A+addgap K from Nat.add_pos_right _ addgap_pos) p; obtain ⟨l,c,y⟩:= goldilock (show 0<B+addgap K from Nat.add_pos_right _ addgap_pos) g
 obtain ⟨W,hW,e,q,X⟩:= conquest h z L T U hv a
 obtain ⟨Y,H,d,v⟩:= expend h z c (Finset.univ.erase T) W hW (fun i u=> X i (mem_erase.mp u).1 B (hx i (mem_erase.mp u).1))
 have he:(Finset.univ.erase T).card=3:=by rw [Finset.card_erase_of_mem (mem_univ _)]; simp [Axis]
 rw [he,e] at d; rw [he] at v
 refine ⟨2^i*(2^l)^3,by positivity,Y,H,by rw [d]; ring,?_,?_⟩
 · rw [pow_mul]; exact (pow_le_pow_left₀ (by positivity) q _).trans v
 let P:= (More n).val; have hp: P=n.val*2:=rfl
 have ht: P ≤ 2^i*(4*(A+addgap K)):= hp.trans_le ((Nat.mul_le_mul_right _ b).trans_eq (by ring)); have hQ:P ≤ 2^l*(4*(B+addgap K)):= hp.trans_le ((Nat.mul_le_mul_right _ y).trans_eq (by ring))
 exact (show P^4=P*P^3 by ring).trans_le ((Nat.mul_le_mul ht (pow_le_pow_left' hQ 3)).trans_eq (by ring))
omit h
lemma Company.pcount {L:List (Cliplet n k)}(h:Company j M w d l₀ t γ γ' τ ε R' L)(p:0<k) : L.length ≤ (More n).val^4:=by
 let i:Fin k:=⟨0,p⟩
 let f(X:Cliplet n k):=X.birth i
 have hx: Set.InjOn f {a | a∈L}:=by intro a ha b hb ht; by_contra e; exact disjoint_left.mp (h.distinct ha hb e) ((h.granted a ha).enterAt i) ((show a.birth i=b.birth i from ht).symm ▸ (h.granted _ hb).enterAt i)
 classical
 have he: (L.toFinset.image f).card=L.length:=by rw [Finset.card_image_of_injOn, List.toFinset_card_of_nodup (h.nodup p)]; intro a t b u; exact fun w=>hx (List.mem_toFinset.mp t) (List.mem_toFinset.mp u) w
 refine he.symm.trans_le (Finset.card_le_univ _|>.trans_eq (site_card _))
end YM.CF.Pannier.Chancel.ScreeV
#print axioms YM.CF.Pannier.Chancel.ScreeV.prism
