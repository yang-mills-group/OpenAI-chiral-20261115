import GaugeFieldConstruction.CatoB4
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 340000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Scree.Ing
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree
open Skye Scree Vow Hake Jet Fock
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Peaks
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
open scoped YM.CF.Mew
open BasisI Roots GJ Mew Lattice.Corona.Hive
open Py.Rate.Pitching.Focus.CoeffArc
open Pastry 
namespace Iona
open Rio Grotto Isle Lattice.Corona
variable {I:Type}[Fintype I][LinearOrder I]{n: Side}
section
variable (α : Equiv.Perm (Seat n))(φ: Equiv.Perm (Hub n))(Ωu:Equiv.Perm (Force n))(e:Same4 α φ Ωu)
open Same4
variable (F F':XE I (InkD n) n) (K K':KK I (Copy n) n)(O: Cipher n→ₐ[ℝ] Cipher n)(σ σ':I→Seat n)(μ μ':I→ℝ)(s s':I→ List I)(G G':I→ Hub n)(P Q:List I)
local notation "Zρ" l:max=> ProgramL σ F K μ s G l
local notation "Zt" l:max=> ProgramL σ' F' K' μ' s' G' l
local notation "ψG"=> ProgramL
lemma plus_R (p q : Rio I n) : pureX (p+q)=pureX p+pureX q:=by
 change p.X+q.X+(p.Y+q.Y)= (p.X+p.Y)+(q.X+q.Y); abel
lemma PrevR (i:I)(g:i∈P)(j: PI I n)(p:j.1={i})(u:P.Nodup):∃ M:List I,M⊆P∧ i∉M∧ i∈P ∧ pureX (Zρ P) j= let X:= ProgramL σ F K μ s G M; pureX ((FrameT (RX F X) (BX K X)).insertΦ (G i) σ (s i) (μ i) i) j:=by
 induction P using List.reverseRecOn with
 | nil=> simp at g
 | append_singleton L k ih=>
    rw [show ProgramL σ F K μ s G (L++[k])=turnY σ F K μ s G (Zρ L) k from (by unfold ProgramL; rw[List.foldl_append]; rfl), turnY,plus_R,Pi.add_apply]
    have V:= (List.nodup_append.mp u); have hv:k∉ L:= fun g=> V.2.2 k g k (by simp) rfl
    rcases List.mem_append.mp g with g₁|g₁
    · have e:k≠ i:=by rintro rfl; exact hv g₁
      let X:=(FrameT (RX F (Zρ L)) (BX K (Zρ L))); let T:=(X.insertΦ (G k) σ (s k) (μ k) k)
      have z:pureX T j=0:= Classical.byContradiction (fun q=>e (Finset.mem_singleton.mp (p ▸ (staffKY σ _ _ (G k) (s k) _ k).1 j q|>.1))) -- parse
      rw [z,add_zero]; obtain ⟨M,t,h,_,χ⟩:=ih g₁ V.1; exact ⟨M,(List.Subset.trans t (List.sublist_append_left ..|>.subset)),h,g,χ⟩
    rw [List.mem_singleton.mp g₁] at p ⊢
    refine ⟨L,(List.sublist_append_left ..|>.subset),hv,(by simp),?_⟩; simp only; rw[show pureX (Zρ L) j=0 from ?_,zero_add]
    apply Classical.byContradiction; intro t; obtain ⟨i,t,r,_⟩:= bandy_r σ F K μ s G L j t; exact hv ((Finset.mem_singleton.mp (p ▸ r)) ▸ t)
-- cleaner assume disjoint list and no self. let simple unary form with expansion only on S via summation.Prev → through using Compare self φ. Need force analogous
lemma PrevF (i:I)(g:i∈P)(j: KI I n)(p:j.1={i})(u:P.Nodup):∃ M: List I,M⊆P ∧ i∉ M ∧ (ProgramL σ F K μ s G P).B j= let X:=ProgramL σ F K μ s G M; ((FrameT (RX F X) (BX K X)).insertΦ (G i) σ (s i) (μ i) i).B j:=by
 induction P using List.reverseRecOn with
 | nil=> simp at g
 | append_singleton L k ih=>
    let X:=(FrameT (RX F (Zρ L)) (BX K (Zρ L))); let T:=(X.insertΦ (G k) σ (s k) (μ k) k)
    rw [show ProgramL σ F K μ s G (L++[k])=turnY σ F K μ s G (Zρ L) k from (by unfold ProgramL; rw[List.foldl_append]; rfl), turnY]; change ∃ M: List I, M⊆_∧ i∉M∧ (Zρ L).B j+T.B j=_
    have V:=(List.nodup_append.mp u); have hv:k∉ L:=fun g=> V.2.2 k g k (by simp) rfl
    rcases List.mem_append.mp g with g₀|g₀
    · have e:k≠ i:=by rintro rfl; exact hv g₀
      rw [show T.B j=0 from Classical.byContradiction (fun q=>e (Finset.mem_singleton.mp (p ▸ ((staffKY σ _ _ (G k) (s k) _ k).2 j q)))),add_zero]; obtain ⟨M,m,q,d⟩:= ih g₀ V.1; exact ⟨M,(List.Subset.trans m (List.sublist_append_left ..|>.subset)),q,d⟩
    have e:i=k:= List.mem_singleton.mp g₀; -- subst i
    rw [e] at p ⊢; have h:(Zρ L).B j=0:=by by_contra h; obtain ⟨i,u,t⟩:= bandy_F σ F K μ s G L j h; exact hv ((Finset.mem_singleton.mp (p ▸ t)) ▸ u)
    exact ⟨L,(List.sublist_append_left ..|>.subset),hv,(by rw [h,zero_add])⟩
-- unsupported terms untouched.Q.Statement
lemma unchanged (p:Finset I)(d:∀ i∈P,i∉ p) : (∀ i: Hub n,(Zρ P).pureX (p,i)=0) ∧ ∀ i:Force n,(Zρ P).B (p,i)=0:=by
 constructor
 · intro i; by_contra h; obtain ⟨j,h,x,b⟩:=bandy_r σ F K μ s G P (p,i) h; exact d j h x
 intro j; by_contra h; obtain ⟨i,p,h⟩:=bandy_F σ F K μ s G P (p,j) h; exact d i p h
section
variable (x y:Orbit n)(i:I)(h:i∈ P)(k:i∈Q)(p:P.Nodup)(v:Q.Nodup)(D: s i =s' i)(d:μ i=μ' i)(t:G' i=φ (G i))
variable (hv:∀ j∈P,j∉s i)(ht:∀ j∈Q,j∉s i)
variable (g:goInR φ F F' O x.1 y.1 (s i).toFinset) (w:goInK Ωu K K' O x y (s i).toFinset)
include p v D d e t h k hv ht g
private lemma Spotα(L L':List I)(b:L ⊆ P)(c:L'⊆ Q): goInR φ (RX F (Zρ L)) (RX F' (Zt L')) O x.1 y.1 (s i).toFinset:=by
 rintro ⟨T,j⟩ r; have q': T⊆(s i).toFinset:=r
 change (F' (T,φ j) y.1+ pureX (Zt L') (T,φ j) y.1)=O (F (T,j) x.1 +pureX (Zρ L) (T,j) x.1)
 rw [(unchanged F K σ μ s G L T (fun j k x=> hv j (b k) (List.mem_toFinset.mp (q' x)))).1 j,(unchanged F' K' σ' μ' s' G' L' T (fun j k x=> ht j (c k) (List.mem_toFinset.mp (q' x)))).1 (φ j),Pi.zero_apply,Pi.zero_apply,add_zero,add_zero]; exact g (T,j) q'
lemma Cuff4 (A: Hub n): pureX (Zt Q) ({i},φ A) y.1=O (pureX (Zρ P) ({i},A) x.1):=by
 obtain ⟨L,b,k₀,q₀,V⟩:=PrevR F K σ μ s G P i h ({i},A) rfl p; obtain ⟨L',c,k₁,q₁,M⟩:=PrevR F' K' σ' μ' s' G' Q i k ({i},φ A) rfl v
 rw [V,M]; simp only[Isle.insertΦ]; rw[κpClip,κpClip]; rw[← D,← d,t]; rw[Finset.sum_apply,Finset.sum_apply,Finset.sum_apply,Finset.sum_apply,map_sum]; refine sum_congr rfl fun j _=>?_; exact MergeF α φ Ωu e _ _ _ _ O σ σ' i (G i) (μ i) _ _ (s i) (Spotα α φ Ωu e F F' K K' O σ σ' μ μ' s s' G G' P Q x y i h k p v D d t hv ht g _ _ b c) _ (poet_b _ _ (List.get_mem ..)) A -- type tune
include w
lemma Half4 (A:Force n): (ProgramL σ' F' K' μ' s' G' Q).B ({i},Ωu A) y=O ((ProgramL σ F K μ s G P).B ({i},A) x):=by
 obtain ⟨L,b,l₀,V⟩:= PrevF F K σ μ s G P i h ({i},A) rfl p; obtain ⟨L',c,l₁,M⟩:=PrevF F' K' σ' μ' s' G' Q i k ({i},Ωu A) rfl v
 have z: goInK Ωu (BX K (Zρ L)) (BX K' (Zt L')) O x y (s i).toFinset:=by
    rintro ⟨T,j⟩ u; change T⊆ _ at u; change (K' (T,Ωu j) y+(Zt L').B (T,Ωu j) y)=O (K (T,j) x+(Zρ L).B (T,j) x)
    rw [(unchanged F K σ μ s G L T (fun j k x=>hv j (b k) (List.mem_toFinset.mp (u x)))).2 j,(unchanged F' K' σ' μ' s' G' L' T (fun j k x=>ht j (c k) (List.mem_toFinset.mp (u x)))).2 (Ωu j),Pi.zero_apply,Pi.zero_apply,add_zero,add_zero]; exact w (T,j) u
 rw[V,M]; simp only; rw[← D,← d,t]
 let Z:=FrameT (RX F (Zρ L)) (BX K (Zρ L)); let Z':= FrameT (RX F' (Zt L')) (BX K' (Zt L')); change (∑ j:Isle.Path (s i),Kinc σ' (Z'.altuQ (φ (G i)) (s i) (μ i) i j)) ({i},Ωu A) y=O ((∑ j: Isle.Path (s i),Kinc σ (Z.altuQ (G i) (s i) (μ i) i j)) ({i},A) x)
 rw [Finset.sum_apply,Finset.sum_apply,Finset.sum_apply,Finset.sum_apply,map_sum]; refine sum_congr rfl fun j _=>?_
 exact MergeY α φ Ωu e _ _ _ _ O σ σ' i (G i) (μ i) _ _ (s i) z _ (poet_b _ _ (List.get_mem ..)) (Spotα α φ Ωu e F F' K K' O σ σ' μ μ' s s' G G' P Q x y i h k p v D d t hv ht g _ _ b c) A
#print axioms Half4
end
end
end Iona
end YM.CF.Scree.Ing
end
