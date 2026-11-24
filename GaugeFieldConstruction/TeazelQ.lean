import GaugeFieldConstruction.SesameCq
import GaugeFieldConstruction.QuiffMQ
import GaugeFieldConstruction.PhonicsQ
import GaugeFieldConstruction.Barrera4
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
variable {I J:Type}[Fintype I][LinearOrder I][Fintype J][LinearOrder J]{n:Side}
variable (e:I↪J)(σ:I→Seat n)(σ':J→Seat n)
open Same4
local notation "Δ"=> PaintEV e
variable (F:XE I (InkD n) n)(K:KK I (Copy n) n) (F':XE J (InkD n) n)(K':KK J (Copy n) n)
variable (S:List I)
local notation "S'"=> List.map e S
variable (l m:ℕ)(a:l=m)(p:Hub n)
private lemma singleVPQ (k:I)(s:List I) : ψS σ (k::s) ∧ (k::s).toFinset={k} ↔ s=[]:=by
 constructor
 · rintro ⟨u,t⟩; have h:=List.nodup_cons.mp (List.Nodup.of_map σ u); cases s
   · rfl
   rename_i i j; exfalso; have k:i∈{k}:= t ▸ (List.mem_toFinset.mpr (List.mem_cons_of_mem _ (List.mem_cons_self ..))); exact h.1 ((Finset.mem_singleton.mp k) ▸ List.mem_cons_self ..)
 rintro rfl; simp [ψS]
variable (k:I)
private lemma own_CostQ {E β :Type}[DecidableEq β][Zero E](i j:β)(F:E)(s:List I): clipK σ i (k::s) F ({k},j)= if s=[]∧j=i then F else 0:=by
 unfold clipK; split; next g=> rw[if_pos]; exact ⟨(singleVPQ σ k s).1 ⟨g.1,(congrArg Prod.fst g.2).symm⟩,congrArg Prod.snd g.2⟩
 next g=> rw [if_neg]; rintro ⟨a,d⟩; exact g ⟨((singleVPQ σ k s).2 a).1,Prod.ext ((singleVPQ σ k s).2 a).2.symm d⟩
variable (r:SpiritRQ e F F' S.toFinset)(b:SpiritFQ e K K' S.toFinset)
variable (s:Sect I)(s': Sect J) (g:Night S s)(g':Night (S.map e) s')
variable (w:MapLexQ e s s')(μ:ℝ)
-- no clip outside range. generic sum
section
variable {U A E:Type}[Fintype U][Fintype A][AddCommMonoid E](e':A ↪ U)(f:A→E)(v:U→E)
private lemma lampEQ (b:∀ i∉Set.range e',v i=0)(a:∀i,v (e' i)= f i):∑ j,f j=∑ i,v i:=by
 rw [←Finset.sum_subset (s₁:= univ.map e') (subset_univ _) (fun i _ u=> b i (fun h=> (by obtain ⟨j,rfl⟩:=h; exact u (mem_map.mpr ⟨j,mem_univ _,rfl⟩)))),sum_map]; simp_rw[a]
end
local notation "ν_"=> s.reg.length
local notation "Υ_"=> s'.reg.length
local notation "Yp"=> (FrameT F K)
local notation "Yq"=> (FrameT F' K')
local notation "Tκ"=> (FrameT F K).salt_Four p S s μ g k
local notation "Tγ"=> (FrameT F' K').salt_Four p (List.map e S) s' μ g' (e k)
local notation "Zr"=> Heart p (Dusk I n) ν_
local notation "Zt"=> Heart p (Dusk J n) Υ_
include w r
local notation "WR"=> iκQ e ν_ Υ_ p (ChpQ e s s' w)
lemma RiseBQ (i:Hub n): Rinc σ Tκ ({k},i)= Rinc σ' Tγ ({e k},i) :=by
 unfold Rinc; rw [Finset.sum_apply,Finset.sum_apply]; let X:=S.toFinset; have he:X.image e=(List.map e S).toFinset:=by ext; simp [X]
 let C:=decide (s.pack≠[]); let Kb:=decide (s'.pack≠[]); have h_b: Kb=C:=by unfold C Kb; rw [w.powers]; simp
 apply lampEQ WR
 · intro j H; let L:=rosterF univ (fun i:Fin Υ_=> (FrameT F' K').purseV S' (j.val i)); let Z:=Legist p (Dusk J n) Υ_ j
   change clipK σ' Z (e k::L) _ ({e k},i)= _; rw [own_CostQ σ',if_neg]; intro e; exact H (surjC (X:=X) _ _ _ _ _ _ (fun i=>he.symm ▸ (rangeRQ F' K' _ _ p e.1 i))) -- e mismatch
 intro j; let v:=(WR) j; let L:=rosterF univ (fun i:Fin Υ_=> (Yq).purseV S' (v.val i)); let L':=rosterF univ (fun i:Fin ν_=> (Yp).purseV S (j.val i)); let Z:=Legist p (Dusk J n) Υ_ v; let Z':= Legist p (Dusk I n) ν_ j
 change clipK σ' Z (e k::L) (if Kb then 0 else (Tγ).termR v) ({e k},i)=clipK σ Z' (k::L') (if C then 0 else (Tκ).termR j) ({k},i); rw [own_CostQ,own_CostQ,h_b,show Z=Z' from anchorQ ..]; have q:L=[]↔ L'= []:=(archPQ e F K F' K' S _ _ _ _ j).symm
 by_cases t:L'=[]∧i=Z'; swap; · rw [if_neg t,if_neg (show ¬(L=[]∧i=Z') from fun u=>t ⟨q.1 u.1,u.2⟩)]
 rw [if_pos t,if_pos (show L=[]∧i=Z' from ⟨q.2 t.1,t.2⟩)]; split; · rfl
 next _ => exact congrArg (fun y:InkD n=> μ • y) (ΩSaleQ e F K F' K' S p r _ _ w j ∅ t.1).symm
include b
lemma BeamKQ (i:Force n): Kinc σ Tκ ({k},i) = Kinc σ' Tγ ({e k},i):=by
 unfold Kinc; rw[Finset.sum_apply,Finset.sum_apply]; let X:=S.toFinset; have he:X.image e=(List.map e S).toFinset:=by ext; simp[X]
 let C:=decide (s.pack≠[]); let Kb:=decide (s'.pack≠[]); have h_b: C=Kb:=by unfold C Kb; rw [w.powers]; simp
 apply lampEQ WR
 · intro j H; rw[Finset.sum_apply]; apply sum_eq_zero; intro i' _
   let L:=rosterF univ (fun i:Fin Υ_=> (FrameT F' K').purseV S' (j.val i)); let Z:=Legist p (Dusk J n) Υ_ j; let Q:=roost (Flak J n) Z Kb i'
   change clipK σ' Q (e k::(L++_)) _ ({e k},i)= _; rw [own_CostQ σ',if_neg]; intro v; exact H (surjC (X:=X) _ _ _ _ _ _ (fun i=>he.symm ▸ rangeRQ F' K' _ _ p (List.append_eq_nil_iff.mp v.1).1 i)) -- ξ tune
 intro j; let v:=(WR) j; let L:=rosterF univ (fun i:Fin Υ_=> (Yq).purseV S' (v.val i)); let L':=rosterF univ (fun i:Fin ν_=> (Yp).purseV S (j.val i)); let Z:=Legist p (Dusk J n) Υ_ v; let Z':= Legist p (Dusk I n) ν_ j
 have hz:Z'=Z:=(anchorQ ..).symm; let P:=iρQ e Z' C Kb h_b Z hz
 rw [Finset.sum_apply,Finset.sum_apply]; symm; apply lampEQ P
 · intro j H; let Q:=roost (Flak J n) Z Kb j
   change clipK σ' Q (e k::(L++ (Yq).tressV S' j.val)) _ ({e k},i)= _; rw [own_CostQ σ',if_neg]; intro v; exact H (surjH e Z' C Kb h_b Z hz (X:=X) j (fun i y=>he.symm ▸ rangeKQ F' K' _ (List.append_eq_nil_iff.mp v.1).2 i y)) -- tune e
 intro j'; let y:=P j'; have ⟨h,h'⟩:= portQ e Z' C Kb h_b Z hz j'; let Q:=roost (Flak J n) Z Kb y; let D':=roost (Flak I n) Z' C j'; let Y:= til (Flak J n) y.val; let D:= til (Flak I n) j'.val; let A:= (FrameT F K).tressV S j'.val; let B:=(FrameT F' K').tressV S' y.val
 change clipK σ' Q (e k :: (L++B)) ((Tγ).termB v y.val) ({e k},i)=clipK σ D' (k::(L'++A)) ((Tκ).termB j j'.val) ({k},i); rw[own_CostQ,own_CostQ,show Q=D' from h]; have H:L++B=[] ↔ L'++A=[] :=by simp only[List.append_eq_nil_iff]; exact and_congr (archPQ e F K F' K' S _ _ _ _ j).symm (archFQ e F K F' K' S _).symm
 by_cases g:L'++ A=[] ∧ i=D'; swap
 · rw [if_neg g,if_neg (show ¬(L++ B=[]∧i=D') from fun u=>g ⟨H.1 u.1,u.2⟩)]
 · rw [if_pos g, if_pos (show L++B=[]∧i=D' from ⟨H.2 g.1,g.2⟩)]
   obtain ⟨h₀,h₁⟩:= List.append_eq_nil_iff.mp g.1 -- g name macro capture Tκ
   change μ • (oV (∏ i:Fin Υ_,(Yq).noteV S' (boon s' i) (v.val i) Y)*(Yq).oracle S' s' y.val)= _
   rw [show Y=D from h', ←(show (∏ i: Fin ν_, (Yp).noteV S (boon s i) (j.val i) D)=_ from ΩSaleQ e F K F' K' S p r _ _ w j D h₀), ←(show (Yp).oracle S s j'.val=(Yq).oracle S' s' y.val from StepYQ e F K F' K' S b _ _ w _ h₁)] -- tune
   rfl
#print axioms RiseBQ
#print axioms BeamKQ
end Iona
end YM.CF.Scree.Ing
end
