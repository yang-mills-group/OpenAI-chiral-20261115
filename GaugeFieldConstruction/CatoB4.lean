import GaugeFieldConstruction.Sweets4
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
-- natural assignment. Reg pairs Al.T.Y. Need equality on indices subsets S. works only output unary.Proof.
variable (α : Equiv.Perm (Seat n))(φ: Equiv.Perm (Hub n))(Ωu:Equiv.Perm (Force n))(e:Same4 α φ Ωu)
variable (F F':XE I (InkD n) n) (K K':KK I (Copy n) n)(O: Cipher n→ₐ[ℝ] Cipher n)
open Same4
variable (σ σ':I→ Seat n)(k:I)(G:Hub n)(μ:ℝ)
variable (x x':Pane n)(U U':Orbit n)(S:List I)
local notation "C0"=> FrameT F K
local notation "C1"=> FrameT F' K'
local notation "Θ"=>θSet α
local notation "Ο"=>ΔX φ I
local notation "Ξ"=>ΔF Ωu I
abbrev goInR (x x':Pane n)(Z:Finset I): Prop:=∀ j:PI I n,j.1⊆ Z → F' (ΔX φ I j) x'=O (F j x)
abbrev goInK (U U':Orbit n)(Z:Finset I): Prop:=∀ j:KI I n,j.1⊆ Z → K' (ΔF Ωu I j) U'=O (K j U)
variable (W : goInR φ F F' O x x' S.toFinset)(V:goInK Ωu K K' O U U' S.toFinset)
section
local notation "Xκ"=> C0
variable (t:Sect I)(p:Night S t)
local notation "CZ"=> (Drab (I:=I) α φ Ωu e t.reg.length G)
local notation "QY" i:max=> (Legist G (Same4.Dusk I n) t.reg.length i)
include W e
lemma LeadWork (P:Hub n)(d:Heart P (Same4.Dusk I n) t.reg.length)(g: rosterF univ (fun i:Fin t.reg.length=> (FrameT F K).purseV S (d.val i))=[]) (D:Support (More n)): let d':=Drab α φ Ωu e t.reg.length P d; (oV (∏ i:Fin t.reg.length,(FrameT F' K').noteV S (boon t i) (d'.val i) (θSet α D))) (x', fun _=>(0,1,1))=O ((∏ i:Fin t.reg.length,(FrameT F K).noteV S (boon t i) (d.val i) D) x):=by
 intro u; unfold oV; rw[Finset.prod_apply,Finset.prod_apply,map_prod]; apply Finset.prod_congr rfl
 intro i U; let B:= d.val i; have h:u.val i=Ο B:=rfl; rw[h]; let R:=(C0).UV B; have g': (C1).UV (Ο B)=Θ R:=patchP α φ Ωu e _
 have hp:(C1).W (Ο B)=(C0).W B:=rfl
 have he:B.1 ⊆ S.toFinset:=by
    intro j a; by_contra p; have e:j∈ rosterF univ (fun i:Fin t.reg.length=>(FrameT F K).purseV S (d.val i)):= (roster_mem ..).2 ⟨i,mem_univ _, List.mem_filter.mpr ⟨(show j∈Cue I B.1 from (mem_sort ..).2 a),by simpa using p⟩⟩; rw [g] at e; simp at e
 change (FrameT F' K').noteV S _ (Ο B) _ x'= O ((FrameT F K).noteV S _ B D x); unfold noteV; rw[hp,g']; split; next v=> rw [if_pos ⟨v.1,(d_p ..).1 v.2⟩]; exact W B he
 next p=> rw[if_neg (fun g=>p ⟨g.1,(d_p ..).2 g.2⟩)]; exact (map_zero O).symm
omit W
include V
-- want Perm roster list tressV under Δ; toList permutations.Raw.N
omit V
private lemma ros_perm (P:Finset (KI I n)): let V':= xBand Ωu P; (rosterF P (C0).B).Perm (rosterF V' (C1).B):=by
 intro v; let ξ:=ΔF Ωu I
 have he:(P.toList.map ξ).Perm v.toList:=by
    apply (List.perm_ext_iff_of_nodup ((nodup_toList _).map ξ.injective) (Finset.nodup_toList _)).mpr
    intro i; rw[Finset.mem_toList]; -- tune by constructor
    constructor
    · intro h; obtain ⟨x,v,h⟩:=List.mem_map.mp h; exact mem_image.mpr ⟨x,Finset.mem_toList.mp v,h⟩
    intro h; obtain ⟨a,v,h⟩:= mem_image.mp h; exact List.mem_map.mpr ⟨a,Finset.mem_toList.mpr v,h⟩
 have h: ((P.toList.map ξ).map (C1).B)= P.toList.map (C0).B:= by rw[List.map_map]; rfl
 unfold rosterF; rw [← h]; exact ((he.map _).flatten)
lemma Boils (A:Finset (KI I n)) (g:Sect I): knowR (rosterF A (FrameT F K).B) S g.pack ↔ knowR (rosterF (xBand Ωu A) (FrameT F' K').B) S g.pack:=by
 have hx:=(ros_perm α φ Ωu e F F' K K' A); unfold knowR; simp_rw [hx.count_eq]
include V
lemma BackWork (A:Finset (KI I n))(p:(FrameT F K).tressV S A=[]): (FrameT F' K').oracle S t (xBand Ωu A) U'= O ((FrameT F K).oracle S t A U):=by
 let Q:= xBand Ωu A
 have ht:∀ i∈ A,(i: KI I n).1⊆ S.toFinset:=by
    intro i h y q; have a: y∈ rosterF A (C0).B := (roster_mem ..).2 ⟨_,h,(show y∈Cue I i.1 from (mem_sort ..).2 q)⟩
    by_contra v; have hx:y∈ (FrameT F K).tressV S A:=List.mem_filter.mpr ⟨a,by simpa using v⟩; rw [p] at hx; simp at hx
 unfold oracle; rw [← propext (Boils α φ Ωu e F F' K K' S A t)]; split; swap; · exact Eq.symm (map_zero ..)
 rw [Finset.prod_apply, Finset.prod_apply,map_prod]; unfold xBand; rw [prod_image]; apply Finset.prod_congr rfl; intro i p; exact V i (ht i p); exact (Ξ).injective.injOn
omit V e
private lemma singleVP (s:List I) : ψS σ (k::s) ∧ (k::s).toFinset={k} ↔ s=[]:=by
 constructor
 · rintro ⟨u,t⟩; have h:=List.nodup_cons.mp (List.Nodup.of_map σ u); cases s
   · rfl
   rename_i i j; exfalso; have k:i∈{k}:= t ▸ (List.mem_toFinset.mpr (List.mem_cons_of_mem _ (List.mem_cons_self ..))); exact h.1 ((Finset.mem_singleton.mp k) ▸ List.mem_cons_self ..)
 rintro rfl; simp [ψS]
private lemma own_Cost {E β :Type}[DecidableEq β][Zero E](i j:β)(F:E)(s:List I): clipK σ i (k::s) F ({k},j)= if s=[]∧j=i then F else 0:=by
 unfold clipK; split; next g=> rw[if_pos]; exact ⟨(singleVP σ k s).1 ⟨g.1,(congrArg Prod.fst g.2).symm⟩,congrArg Prod.snd g.2⟩
 next g=> rw [if_neg]; rintro ⟨a,d⟩; exact g ⟨((singleVP σ k s).2 a).1,Prod.ext ((singleVP σ k s).2 a).2.symm d⟩
include e p W
local notation "Ym"=> (C0).salt_Four G S t μ p k
local notation "Yn"=> (C1).salt_Four (φ G) S t μ p k
local notation "d"=> ((FrameT F K).UV)
private lemma nose (x:Heart G (FrameT F K).UV t.reg.length) : (rosterF univ (fun i:Fin t.reg.length=> (C1).purseV S ((CZ x).val i)))= rosterF univ (fun i:Fin t.reg.length=>(C0).purseV S (x.val i)):=rfl
-- clip.At matches exactly unary evaluation.All same Ctrl.
lemma MergeF (i:Hub n): Rinc σ' Yn ({k},φ i) x'= O (Rinc σ Ym ({k},i) x):=by
 unfold Rinc; rw [Finset.sum_apply,Finset.sum_apply,Finset.sum_apply, Finset.sum_apply,map_sum]; symm; apply Fintype.sum_equiv (CZ); intro a; let V':= CZ a
 let T:= rosterF univ (fun i:Fin t.reg.length=> (C0).purseV S (a.val i)); let C:=decide (t.pack≠[])
 let A:= Legist G (Same4.Dusk I n) t.reg.length a; let B:=Legist (φ G) (Same4.Dusk I n) t.reg.length V'
 change O ((clipK σ A (k::T) (if C then 0 else (Ym).termR a) ({k},i)) x) = (clipK σ' B (k::T) (if C then 0 else (Yn).termR V') ({k},φ i)) x'
 rw [own_Cost σ k A i _ T,own_Cost σ' k B _ _ T]; -- adjust order
 have hx:B= φ A:=bayZ α φ Ωu e t.reg.length G a; rw [hx] -- leaves conditions
 by_cases u : T=[] ∧ i=A
 · by_cases hv:C
   · simp_rw[if_pos (show C=true from hv),if_pos u,if_pos (show T=[]∧ φ i=φ A from ⟨u.1,congrArg φ u.2⟩)]; exact map_zero O
   rw[if_neg hv]; simp_rw[if_neg hv]; rw [if_pos u,if_pos (show T=[]∧ φ i=φ A from ⟨u.1,congrArg φ u.2⟩)]
   have h:= LeadWork α φ Ωu e F F' K K' O x x' S W t G a u.1 (∅:_)
   change O (μ • (_:Cipher n))= μ • (_:Cipher n); rw [map_smul]; have ht : θSet α ∅=∅:= image_empty _; rw[ht] at h; exact congrArg (fun i=> μ • i) h.symm
 rw [if_neg u, if_neg (show ¬(T=[]∧φ i=φ A) from fun g=>u ⟨g.1,φ.injective g.2⟩)]; exact map_zero O

omit W
include V
set_option maxHeartbeats 160000 in
lemma MergeY (W : goInR φ F F' O U.1 U'.1 S.toFinset)(i:Force n): Kinc σ' Yn ({k},Ωu i) U'= O (Kinc σ Ym ({k},i) U):=by
 unfold Kinc; rw [Finset.sum_apply,Finset.sum_apply,Finset.sum_apply,Finset.sum_apply,map_sum]; symm; apply Fintype.sum_equiv (CZ); intro a
 let Z:= Legist G (d) t.reg.length a; let D:=Drab α φ Ωu e t.reg.length G a; let X:= Legist (φ G) ((FrameT F' K').UV) t.reg.length D
 let v:=decide (t.pack≠[]); have hz: φ Z=X:= Eq.symm (bayZ α φ Ωu e t.reg.length G _);
 let B:=Bias (I:=I) α φ Ωu e Z X hz v; let L:= roost (Same4.Flak I n) Z v; let L':=roost (Same4.Flak I n) X v
 rw [Finset.sum_apply,Finset.sum_apply,Finset.sum_apply,Finset.sum_apply,map_sum]; apply Fintype.sum_equiv B; intro w
 let P:=w.val; let W':=(B w).val; have hp:L' (B w)=Ωu (L w):= cap_v α φ Ωu e Z X hz v w
 let T:= rosterF univ (fun i:Fin t.reg.length=> (C0).purseV S (a.val i)); let R':=(C0).tressV S P; let R₁:=(C1).tressV S W'
 change O (clipK σ (L w) (k:: (T++R')) ((Ym).termB a P) ({k},i) U)=clipK σ' (L' (B w)) (k::(T++R₁)) ((Yn).termB D W') ({k},Ωu i) U'
 rw[own_Cost σ k (L w),own_Cost σ' k, hp]; have he: R'.Perm R₁:= (ros_perm α φ Ωu e F F' K K' P).filter _
 have hv: T++R'=[]∧ i=L w ↔ T++R₁=[]∧ Ωu i=Ωu (L w):=by
    simp only[List.append_eq_nil_iff]; rw [← List.length_eq_zero_iff,show (R'=[])=(R₁=[]) from (by rw[← List.length_eq_zero_iff,← List.length_eq_zero_iff,he.length_eq]),Ωu.apply_eq_iff_eq]
 by_cases Hp:T++R'=[] ∧ i=L w
 · rw [if_pos Hp,if_pos (hv.mp Hp)]; obtain ⟨hm,h⟩:= List.append_eq_nil_iff.mp Hp.1
   have he:= BackWork α φ Ωu e F F' K K' O U U' S V t P h
   let A:=til (C0).U P; let Y:= ∏ j:Fin t.reg.length,(C0).noteV S (boon t j) (a.val j) A; let B':= til (C1).U W'; let X':=∏ j:Fin t.reg.length,(C1).noteV S (boon t j) (D.val j) B'
   have hB:B'=θSet α A:=til_Fp α φ Ωu e P
   have h₁:X' U'.1=O (Y U.1):=by unfold X'; rw[hB]; exact LeadWork α φ Ωu e F F' K K' O U.1 U'.1 S W t G a hm _
   change O (μ • (Y U.1 * oracle _ _ _ _ U))= μ • (X' U'.1 * oracle _ _ _ _ U'); change oracle _ _ _ W' U'= _ at he; rw[map_smul,map_mul,h₁,he]
 rw [if_neg Hp,if_neg (fun t=>Hp (hv.mpr t))]; exact map_zero _

end
end
end Iona
end YM.CF.Scree.Ing
end
