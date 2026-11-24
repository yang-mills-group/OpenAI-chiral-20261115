import YM.CF.Levier.CrestD
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 23000
noncomputable section
namespace YM.CF.Stake
open Function NormedSpace Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Kennel Laic Tenant Proa Broc MeasureTheory Urn Hake Levier
open Fir Matrix Phase
open scoped Matrix.Norms.L2Operator Topology BigOperators NNReal Classical ContDiff InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {j m:ℕ}{r d x:ℝ}{L:Side}{ι:Type*}
-- pre L for ANY WG ι not yet picked; ι in universe Type 0 consumed easily after L
abbrev AspectB (t: Odd L.val)(v:TailB)(K:WG ι)(S:ι→ Male)(T r C:ℝ)(k:ℕ)(j m:ℕ):Prop:=∀ x:ℝ,0<x→ x≤ T→ Urn.flower L (Urn.Sky L t j K S (!v.2)) (Urn.icyS j (!v.2) v.1 S) r (C * followV [] L) m k x
lemma price_t(v:TailB)(j:ℕ)(m:ℕ)(p:2 ≤ j)(h:Even j):∃ C:ℝ,0<C ∧∀ L:Side,∀ t:Odd L.val,∀ (K:WG ι)(S:ι→Male),Lively K→(∀ i n,K i n 1=0)→∃ T r:ℝ,0<T∧0<r∧∃ k:ℕ, AspectB t v K S T r C k j m:=by
 obtain ⟨C',a,T⟩:=Urn.giant (ι:=ι) j h p m; obtain ⟨B,x,V⟩:= Urn.workB (ι:=ι) j (!v.2) v.1 m (by omega)
 refine ⟨B*C',by positivity,fun L t K S u b=>?_⟩; obtain ⟨a',e,hA,hE,l,A⟩:= T L t _ K S u b
 obtain ⟨c,d,hc,hd,z,T⟩:= V S (@Urn.Sky ι L t j K S (!v.2)) L _ _ _ hA hE (mul_nonneg a.le (Vpos ..|>.le)) l A -- tune `@`; syntax
 refine ⟨d,c,hd,hc,z,fun x p y=>?_⟩; rw [mul_assoc]; exact T x p y
local notation "Mine"=> Levier.mineB
local notation "Pit"=> Levier.mineC
lemma legB (m:ℕ)(p:2 ≤ j)(h:Even j):∃ C:ℝ,0<C ∧∀ L:Side,∀ t:Odd L.val,∀ (K:WG ι)(S:ι→Male),Lively K→(∀ i n,K i n 1=0)→∃ T r:ℝ,0<T∧0<r∧∃ k:ℕ,∀ x:ℝ,0<x→x≤T→∀ c ∈ (univ:Finset TailB),∀ {N P:Side}(G:Ratio N P),G.count=L→k ≤ N.val →∀ p:Odd G.count.val,∀ i:ι,Street (badge _) (pinH G x true) (pinH G x false) m (L.val:ℝ)⁻¹ r (fun _=>C*followV [] L) (Mine (j:=j) G p x S K i c) :=by
 choose C u D using fun p':TailB=>price_t (ι:=ι) p' j m p h
 let X:ℝ:= ∑ i,C i
 refine ⟨X,sum_pos (fun i _=>u i) univ_nonempty,fun L t K S l n=> ?_⟩
 choose T R g f k V using fun p:TailB=> D p L t K S l n
 let A:= (univ:Finset TailB); let W:= A.inf' (show A.Nonempty from univ_nonempty) T; let Z:= A.inf' (show A.Nonempty from univ_nonempty) R
 refine ⟨W,Z,(lt_inf'_iff _).mpr (fun i _=>g i),(lt_inf'_iff _).mpr (fun i _=>f i), A.sup k,fun x q b v hv N P G hx h u' i=>?_⟩
 have hp:= V v x q (b.trans (inf'_le _ hv)); have hz:= hp i G hx ((le_sup hv).trans h)
 subst L; have hy:0<(G.count.val:ℝ):=Nat.cast_pos.mpr G.count.property
 exact (hz.desc (inf'_le _ hv) (by positivity)).prime (fun i=>mul_le_mul_of_nonneg_right (single_le_sum (fun i _=> (show 0<C i from u i).le) hv) (Vpos ..|>.le)) -- name collision u after subst
lemma legC(L:Side)(t:Odd L.val)(j:ℕ)(p:2 ≤ j)(h:Even j)(K:WG ι)(S:ι→Male)(u:Lively K)(v:∀ i n,K i n 1=0): ∃ r C e:ℝ,0<r∧0<C∧0<e∧∃ m:ℕ,∀ x:ℝ,0<x→x≤e→∀ i:ι,∀ {N P:Side}(G:Ratio N P),G.count=L→m ≤ N.val →∀ p:Odd G.count.val,∀ c:Grave,Crown (badge _) (pinH G x true) (pinH G x true) r C (Pit (j:=j) G p x S K i c):=by
 choose a C e w l v m H using fun i:Grave=> Urn.earnD j (!(carL i)) (!(beltG i)) i.1 i.2.1 L t K S u h (show 1≤j from by omega) v (carL i) (!(beltG i)) -- tune extra arg
 let X:Finset Grave:=univ; let T(H: Grave→ℝ):= univ.inf' univ_nonempty H
 refine ⟨T a, ∑ i,C i,T e,(lt_inf'_iff _).mpr (fun i _=> w i),sum_pos (fun i _=> l i) univ_nonempty,(lt_inf'_iff _).mpr (fun i _=>v i),X.sup m,fun x g h i N P G y z t c =>?_⟩
 let W:=(H c x g (h.trans (inf'_le _ (mem_univ c)))) i G y ((le_sup (mem_univ c)).trans z)
 subst L; exact (W.drop (inf'_le _ (mem_univ c))).books (single_le_sum (fun i _=>(l i).le) (mem_univ c))
end YM.CF.Stake
