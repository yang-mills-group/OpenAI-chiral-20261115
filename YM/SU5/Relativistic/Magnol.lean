import YM.SU5.Relativistic.Coraline
import YM.SU5.Relativistic.Berm
import YM.SU5.Relativistic.Sval
/-! # Concretion with caloric flags. Exact direct fields. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 590000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Papyrus.Franc.Meshy
open Function Filter NormedSpace Metric Fock Finset Thera MeasureTheory Lattice Cube Lat Fir Rush SU Scroll Skye Tulip Flare BPress.Spin.Blank
open Laurent Bloch Dial Jill Crest Crest.Shore Crest.Sleet Buffered
open Lifted Pea Omelet Afterglow Satin Pannier Pannier.Chancel Pannier.Chancel.ScreeV Cliplet RG Tenant Scree Loaves
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators ComplexOrder NNReal ENNReal Kronecker
attribute [local instance] opCStarAlgebra
open Py.Rate (sites)
open Afterglow.Tower Afterglow.Journey
variable {K:Calibration}{N m n:Side}{B l: ℕ}
variable {K₀:Calibration}{j k w d t l₀:ℕ}{R R' ε γ γ' τ:ℝ}{M:Tulip.Male}{ν:Mark n→ℂ}
variable {μ θ₁ Bx C':ℝ}(h:Twosome K n ν)(r:Muster γ n M)
include h r
lemma conquest (g:n=K.c m) (A:List (Cliplet n 1)) (i:Axis)
    (f:Battalion M k l₀ t γ τ μ θ₁ Bx C' A) (q:cows i (whereV A) B)(v:2^l*(B+addgap K)≤ n.val) :
    ∃ V:List (Cliplet n 1),Battalion M k l₀ t γ τ μ θ₁ Bx C' V ∧ V.length=2^l*A.length ∧ ‖ν (probe A)‖^(2^l)≤ ‖ν (probe V)‖ ∧ ∀ a,a≠i → ∀ s,cows a (whereV A) s → cows a (whereV V) s := by
 induction l generalizing B A with
 | zero=> exact ⟨A,f,by simp,by simp,fun a _ s u=>u⟩
 | succ l ih=>
    have ht:B+addgap K ≤ n.val:= v.trans' (Nat.le_mul_of_pos_left _ (pow_pos two_pos _)); obtain ⟨z,p,u,e⟩:=topLong (i:=i) g _ q ht; let s:= Heat.gaugeShift K.B z
    let U:= A.map fun a=> a.mirror i s; let W:= U++A; have h'': whereV W=hyphen i s (whereV A)∪ whereV A:=by unfold W U; rw [combine,Flight.reflect_consistent]; -- fix rfl
    have hp:whereV A⊆ band n i s K.ℓ:=p
    have hx: Battalion M k l₀ t γ τ μ θ₁ Bx C' W := (f.cloud i s r).tack _ f (by rw [Flight.reflect_consistent]; exact west K i s _ hp) -- wtf
    have hw:= h i z (probe A) (f.permit hp)
    obtain ⟨Y,a,b,r,g'⟩:= ih W hx (B:=2*B+addgap K) (by rw [h'']; exact u) (by rw [pow_succ] at v; exact v.trans' (le_of_eq (by ring)))
    refine ⟨Y,a,?_,?_,fun a g t k=> g' a g t (h''.symm ▸ e a g t k)⟩
    · rw [b,pow_succ]; unfold W U; rw [List.length_append,List.length_map]; ring -- W/U let
    rw [pow_succ',pow_mul]; have he:reflMark i (Heat.gaugeShift K.B z) (probe A)*probe A=probe W:=by unfold W U; rw [probe_combine,Flight.reflect_probes] -- let
    rw [he] at hw; exact (pow_le_pow_left₀ (by positivity) hw _).trans r
-- spill all axes
lemma expend (g:n=K.c m)(v:2^l*(B+addgap K)≤ n.val)(S:Finset Axis) (A:List (Cliplet n 1))(f:Battalion M k l₀ t γ τ μ θ₁ Bx C' A)
    (p:∀ a∈S,cows a (whereV A) B) : ∃ U:List (Cliplet n 1), Battalion M k l₀ t γ τ μ θ₁ Bx C' U ∧ U.length=(2^l)^S.card*A.length ∧ ‖ν (probe A)‖^((2^l)^S.card) ≤ ‖ν (probe U)‖:=by
 induction S using Finset.induction_on generalizing A with
 | empty=> exact ⟨A,f,by simp,by simp⟩
 | @insert i S x ih=>
    obtain ⟨U,hU,a,b,vL⟩:= conquest h r g A i f (p i (mem_insert_self ..)) v
    obtain ⟨Z,gX,e,l'⟩:= ih U hU (fun s v=> vL s (fun h=>x (h ▸ v)) _ (p s (mem_insert_of_mem v))) -- extras
    rw [card_insert_of_notMem x,pow_succ']; refine ⟨Z,gX,?_,?_⟩
    · rw [e,a]; ring
    rw [pow_mul]; exact (pow_le_pow_left₀ (by positivity) b _).trans l'
omit h r
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
include h r
lemma prism (z:n=K.c m)(T:Axis){A B:ℕ}(p:A+addgap K≤ n.val)(g:B+addgap K≤ n.val)
    (L:List (Cliplet n 1))(U:Battalion M k l₀ t γ τ μ θ₁ Bx C' L)
    (hv:cows T (whereV L) A)(hx:∀ x≠ T, cows x (whereV L) B):
     ∃ f> (0:ℕ),∃ L':List (Cliplet n 1), Battalion M k l₀ t γ τ μ θ₁ Bx C' L' ∧ L'.length=f*L.length ∧ ‖ν (probe L)‖^f ≤ ‖ν (probe L')‖ ∧ (More n).val^4 ≤ f*(4*(A+addgap K))*(4*(B+addgap K))^3:=by
 obtain ⟨i,a,b⟩:= goldilock (show 0<A+addgap K from Nat.add_pos_right _ addgap_pos) p; obtain ⟨l,c,y⟩:= goldilock (show 0<B+addgap K from Nat.add_pos_right _ addgap_pos) g
 obtain ⟨W,hW,e,q,X⟩:= conquest h r z L T U hv a
 obtain ⟨Y,H,d,v⟩:= expend h r z c (Finset.univ.erase T) W hW (fun i u=> X i (mem_erase.mp u).1 B (hx i (mem_erase.mp u).1))
 have he:(Finset.univ.erase T).card=3:=by rw [Finset.card_erase_of_mem (mem_univ _)]; simp [Axis]
 rw [he,e] at d; rw [he] at v
 refine ⟨2^i*(2^l)^3,by positivity,Y,H,by rw [d]; ring,?_,?_⟩
 · rw [pow_mul]; exact (pow_le_pow_left₀ (by positivity) q _).trans v
 let P:= (More n).val; have hp: P=n.val*2:=rfl
 have ht: P ≤ 2^i*(4*(A+addgap K)):= hp.trans_le ((Nat.mul_le_mul_right _ b).trans_eq (by ring)); have hQ:P ≤ 2^l*(4*(B+addgap K)):= hp.trans_le ((Nat.mul_le_mul_right _ y).trans_eq (by ring))
 exact (show P^4=P*P^3 by ring).trans_le ((Nat.mul_le_mul ht (pow_le_pow_left' hQ 3)).trans_eq (by ring))

omit h r
open Afterglow.Tower Tower.SlabMark
variable {k j w d l u T H:ℕ}{R γ τ γ' B E:ℝ}{K: Calibration}{M:Tulip.Male}
variable {n:Side}{z:Axis}{i:ℕ}{N:Side}

-- pre perturb. Tower with width on cover; Pack. keep dependencies fixed for all m by upper HT statement.

variable {δ η kR μ R':ℝ}
structure Galop (K:Calibration)(F:Buffered.Family K)(T:Finset Cover)(q:ℕ)(m:Side)(Kx:ℕ)(M:Tulip.Male)(l w:ℕ)(δ τ η μ kR R':ℝ): Prop where
 ticket:∃ L:List (Cliplet (K.c m) 1), L.length=q ∧ whereV L⊆ Satin.region T (K.c m) ∧ probe L= F m∧Battalion M Kx l w δ τ η μ kR R' L
variable {F Y:Buffered.Family K}{S S':Finset Cover}{q q':ℕ}
namespace Galop
variable {X : Mark (K.c n)→ℂ}
local notation "U" F:max s:max x:max=> Galop K F s x n k M w l δ τ η μ kR R'
lemma inverted (h:U F S q)(i:Axis)(s:ℤ)(b:Muster δ (K.c n) M): U (Tower.mirror K i s F) (reflectedBox i s S) q:=by
 obtain ⟨L,t,p,v,f⟩:= h.ticket
 refine ⟨L.map (fun a=>a.mirror i s),by rw [List.length_map,t],?_, by rw [Flight.reflect_probes,v]; rfl, f.cloud _ _ b⟩
 rw [Flight.reflect_consistent]; intro z t; obtain ⟨a,u,rfl⟩:= mem_image.mp t; obtain ⟨x,u',rfl⟩:=mem_image.mp (p u); rw [Shape.anno]; exact mem_image_of_mem _ (mem_image_of_mem ((plane i s).motion) u')
lemma migrate (h:U F S q)(i:Axis)(s:ℤ)(b:Muster δ (K.c n) M): U (relocate K i s F) (plow K i s S) q:= by
 have hp:= (h.inverted i 0 b).inverted i (gaugeT K s) b; rw [Tower.support_translation,sub_zero] at hp; exact hp

lemma line (p:U F S q)(v:U Y S' q') (d:Disjoint (region S (K.c n)) (region S' (K.c n))):U (F*Y) (S∪S') (q+q'):=by
 obtain ⟨A,t,h,z,f⟩:=p.ticket; obtain ⟨L,g,x,y,w⟩:=v.ticket; refine ⟨A++L,by rw [List.length_append,t,g],?_,by rw [probe_combine,z,y]; rfl, f.tack L w (d.mono h x)⟩
 rw [combine,Satin.region,image_union]; exact union_subset_union h x
lemma disjoint_later (e:Disjoint S S'): ∃ B:ℕ,∀ n:Side,B≤ n.val→ Disjoint (region S n) (region S' n):=by
 obtain ⟨B,v⟩:= disperse_wrap (S ∪ S'); refine ⟨B,fun n p=>?_⟩; apply Finset.disjoint_left.mpr; intro a h g; obtain ⟨x,htp,rfl⟩:=mem_image.mp h; obtain ⟨y,hx,hg⟩:=mem_image.mp g; have he:y=x:= v (More n) (show _ from p.trans (show n.val ≤ n.val*2 by omega)) (show y∈ (↑(S∪ S') : Set _) from mem_union_right _ hx) (show x∈ (↑(S∪ S'):Set _) from mem_union_left _ htp) hg; exact disjoint_left.mp e htp (he ▸ hx) -- duplicate h

end Galop

namespace Polder
local notation "θ"=>K.ℓ
local notation "V"=> ruler K.B
variable {z:Axis}

private lemma ladder (p:0< H)(B₀:Cover)(g:Between K z 0 (V*H) S)(u:Transom z S B₀ q): let A:=reflectedBox z (gaugeT K H) S; let T:=plow K z ↑H S
   Disjoint A T ∧ Between K z 0 (V*(H+H:ℕ)) (A∪T)∧Transom z (A∪T) B₀ q:=by
 intro A S'; let h:=V*H
 have hp:Between K z 0 h A:=by have he:= g.mirror K z (gaugeT K H); rw [ruler_offset,sub_zero,sub_self] at he; exact he
 have ht:Between K z h (V*(H+H:ℕ)) S':=by have ht:= g.relocate K z H; rw [add_zero] at ht; unfold h; push_cast; rw [mul_add]; exact ht
 have hf:0≤h:=by unfold h; have ht:=ruler_gene K.B; positivity
 refine ⟨?_,fun i v=> ?_,fun i t x w=>?_⟩
 · apply Finset.disjoint_left.mpr; intro i v w; have he: 0<K.ℓ:=(Nat.zero_le _).trans_lt K.buffer; have hx:=(hp i v).2; have hy:=(ht i w).1; omega
 · rcases mem_union.mp v with v|v
   · obtain ⟨a,e⟩:=hp i v; exact ⟨a,e.trans (by push_cast; rw [mul_add]; omega)⟩
   obtain ⟨a,e⟩:=ht i v; exact ⟨by omega,e⟩
 exact (mem_union.mp w).elim ((u.mirro z _) i t _) ((u.moved K z _) i t _)

-- proofs independent of w etc for support/timing: keep evidence for ANY stage with this starter
lemma express {s:ℕ}(p:0<s)(U:Between K z 0 (V*s) S)(x:Cover)(u':Transom z S x q)(v:InTest K true S false F)(N₀:ℕ):∃ (T:Finset Cover)(B:ℕ), Between K z 0 (V*(towerH s N₀:ℕ)) T ∧ Transom z T x q ∧
        InTest K true T false (thicket K z s F N₀) ∧
   ∀ n:Side,B≤ (K.c n).val→∀ k w l:ℕ,∀ (M:Tulip.Male)(δ τ η μ kR R':ℝ),Muster δ (K.c n) M → Galop K F S 1 n k M w l δ τ η μ kR R' → Galop K (thicket K z s F N₀) T (staveP N₀) n k M w l δ τ η μ kR R':=by
 obtain ⟨e,y,H⟩:= ladder p x U u'; let S1:=reflectedBox z (gaugeT K s) S; let S2:= plow K z s S; let Z:= S1∪ S2; let P(s:ℕ):=V*s; let F':=tripleWide K z s F
 obtain ⟨B,f⟩:=Galop.disjoint_later e
 have hp(n:Side)(p:B≤(K.c n).val)(k w l:ℕ)(M:Tulip.Male)(δ τ η μ kR R':ℝ)(b:Muster δ (K.c n) M)(t:Galop K F S 1 n k M w l δ τ η μ kR R'):
     Galop K F' Z 2 n k M w l δ τ η μ kR R':= (t.inverted _ _ b).line (t.migrate _ s b) (f _ p)
 have hu:InTest K true Z false F':= ((Tower.axial K z (gaugeT K s) v).mono subset_union_left).mul ((Tower.flow_port K z (gaugeT K s) v).mono subset_union_right)
 have hy:Between K z 0 (P (s+s)) Z:=y; have hQ:Transom z Z x q:=H
 induction N₀ with
 | zero=>
    have he:towerH s 0=s+s:=by unfold towerH staveP; omega
    exact ⟨Z,B,by rw [he]; exact hy,hQ,hu,hp⟩
 | succ n ih=>
    obtain ⟨T,F₀,l0,l1,v,t⟩:= ih
    let q':= P (s+s); let T':=plow K z (s+s:ℕ) T; have hR:P (towerH s (n+1))=q'+V*(towerH s n:ℕ):=by unfold q' P towerH staveP; push_cast; ring
    have he:Between K z q' (P (towerH s (n+1))) T':=by rw [hR]; have hx:= l0.relocate K z ↑(s+s); rw [add_zero] at hx; exact hx
    have hx: Disjoint Z T':= by
       apply Finset.disjoint_left.mpr; intro i v w; have h:=(he i w).1; have u:=(hy i v).2; change _ ≤ q' at u; have hp: 0<K.ℓ:=(Nat.zero_le _).trans_lt K.buffer; omega
    let qT:= P (towerH s (n+1)); have hr:P (s+s) ≤ qT:=by
       have ht:0≤ V*(towerH s n:ℕ):=by have he:=ruler_gene K.B; positivity
       change q'≤ qT; unfold qT; rw [hR]; omega
    let A:=Z∪T'
    obtain ⟨W,g⟩:=Galop.disjoint_later hx; refine ⟨A,W+B+F₀,fun i w=>?_,fun j x t p=>?_,(hu.mono subset_union_left).mul ((Tower.flow_port K z _ v).mono subset_union_right),fun i e k w l M δ τ η μ kR R' b g'=>?_⟩
    · rcases mem_union.mp w with v|v
      · exact ⟨(hy i v).1, (hy i v).2.trans hr⟩
      obtain ⟨h,e⟩:=he i v; refine ⟨?_,e⟩; have hx: 0≤q':= by unfold q' P; have ht:=ruler_gene K.B; positivity
      omega
    · exact (mem_union.mp p).elim (hQ _ x t) ((l1.moved K z _) _ x t)
    have h:=t i (by omega) k w l M δ τ η μ kR R' b g'; rw [show staveP (n+1)=2+staveP n from by unfold staveP; omega]; exact (hp i (by omega) _ _ _ _ _ _ _ _ _ _ b g').line (h.migrate z _ b) (g _ (by omega))
end Polder
end YM.CF.Papyrus.Franc.Meshy
#print axioms YM.CF.Papyrus.Franc.Meshy.Polder.express
