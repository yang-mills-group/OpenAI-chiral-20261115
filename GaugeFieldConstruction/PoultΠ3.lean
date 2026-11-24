import GaugeFieldConstruction.«PlateΠ3»
import GaugeFieldConstruction.Sommar
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 60000
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
open Pastry Grotto
namespace Ivey
open Sault Leaf Sour
open Ladder3 Drapes Tenant Palot Rue Iona
attribute [local instance] loreM loreN
variable {n: Side}{I α β γ G:Type}[LinearOrder I][Fintype I][Fintype α][Fintype β][Fintype γ]
-- old bank
namespace ShoreQ
open Tuner
variable (P:BudgetPoint)
namespace Argos
variable (Q:LeaseQ γ n)(C:Factor3 n)(F:RegLime I α n)
-- keyfree ΦX.L.Budget
section
variable {k:ℕ}(Z:BudgetPoint)(p d:ℕ)(t:Fin p→γ)(i:Fin d →α)(V:Support (More n))(W: Orbit n)
-- ISSUE Φ d contract.G.Fun p d.V (raw; simple).
abbrev BodyX (A:FC (Dwell n))(K:α → Cipher n): FC (Dwell n):= discount p d • scar A ((List.ofFn fun j=> K (i j))++(List.ofFn fun j=> Q.issue (t j) V W))
lemma ScaEq (y:Hub n)(A:Heart C.H Q.H p)(u:Heart y F.S d) : filmic F C Q p d A y u V W=BodyX Q p d A.val u.val V W (C.issue V W) (fun j=> F.K j V W):=by
 let X:= C.issue V W; let Y:= loomR F C Q p d A y u; let S(i:α⊕γ):= stamps F Q V i W
 change discount p d • scar X (Y.map S) = _; unfold BodyX Y loomR; rw[List.map_append,List.map_ofFn,List.map_ofFn]; rfl
lemma Scaτ (A:FC (Dwell n))(D:List (Cipher n))(k:ℂ):scar (k • A) D=k • scar A D:=by induction D with|nil=>rfl|cons i L ih=> rw[scar,scar,ih,τq]
lemma ψScar(h:Fock.Sector Finset.univ false (C.issue V W))(A:List (Cipher n)): Fock.Sector Finset.univ false (scar (C.issue V W) A):= by
 induction A with|nil=>exact h|cons i L ih=>
    rw[scar]; unfold bump; rw [sub_eq_add_neg]; refine (ih.mul (life (fineShape i))).add ?_; -- tune.
    rw[←neg_one_smul ℂ]; exact ((life (fineShape i)).mul ih).scale _
lemma ScaLight (K:α→ Cipher n)(h:Fock.Sector univ false (C.issue V W)): (fair (BodyX Q p d t i V W (C.issue V W) K)).val= Sault.rind (BodyX Q p d t i V W (C.issue V W) K):=by
 unfold fair; let L:= BodyX Q p d t i V W (C.issue V W) K
 have ht: Fock.Sector univ false L:=(ψScar C V W h _).scale _
 rw [dif_pos (light_e ht)]
-- H masks.T kernel placements.C.
section
open Fin
lemma body_rate (A:FC (Dwell n))(K:α→ Cipher n)(a:α→ℂ): BodyX Q p d t i V W A (fun j=> a j • K j)=(∏ j:Fin d,a (i j)) • BodyX Q p d t i V W A K:=by
 unfold BodyX; simp_rw [scar_append]
 let f:= scar A (List.ofFn fun j=>Q.issue (t j) V W)
 rw [show scar _ _= ((∏ j:Fin d,a (i j)) • scar f (List.ofFn fun j=>K (i j))) from ?_,smul_comm]
 let s:=List.ofFn i; rw[← show (s.map K)= List.ofFn fun j=>K (i j) from List.map_ofFn ..] -- tune
 rw [show List.ofFn (fun j=>a (i j) • K (i j))=s.map (fun j=>a j • K j) from (by unfold s; rw[List.map_ofFn]; rfl), scar_one, show s.map a=List.ofFn fun j=> a (i j) from List.map_ofFn .., List.prod_ofFn]
-- fiber list fx appoint
variable {δ:Type}[DecidableEq δ](P:α→δ)
private lemma scar_fiber (A:FC (Dwell n))(K:α→Cipher n)(k: Fin d→δ) : scar A (List.ofFn fun i=> ∑ j:α with P j = k i,K j)= ∑ L: (Fin d→α) with (P ∘ L=k), scar A (List.ofFn (K∘ L)):=by
 induction d with
 | zero=> simp only [List.ofFn_zero,scar]; -- RHS filter includes all; show T.
          rw[sum_eq_single (fun j=> j.elim0)]
          · intro i h p; exact False.elim (p (Subsingleton.elim ..))
          intro t; exact False.elim (t (mem_filter.mpr ⟨mem_univ _,Subsingleton.elim ..⟩)) -- tune
 | succ d ih=>
    let x(t:Fin (d+1)→α):=scar A (List.ofFn (K∘ t)); let g(t):=if P∘ t=k then x t else 0
    let V:= Fin.consEquiv (fun _:Fin (d+1)=>α)
    let s : Fin d→δ:= k ∘ Fin.succ
    rw [sum_filter,←Equiv.sum_comp V g,Fintype.sum_prod_type,List.ofFn_succ,scar]; -- tune rw g
    let b:Finset α:= univ.filter (fun j=> P j=k 0)
    change bump (scar _ (List.ofFn fun i=>∑ j:α with P j = s i,K j)) (((Dough (Dwell n)).val) _)= _
    rw [map_sum,σb,ih s, sum_filter (s:= (univ:Finset α))] -- tune with multiple IH (k). bump→ Σ ℓ
    apply sum_congr rfl; intro j _; by_cases ht:P j=k 0
    · rw [if_pos ht,σq,sum_filter]; refine sum_congr rfl (fun i _=>?_)
      have hm:P∘ V (j,i)=k↔P∘ i=s:= ⟨fun e=>funext (fun x=>by simpa [V,Function.comp, s,consEquiv] using congrFun e (Fin.succ x)),fun e=>funext (Fin.cases (by simp[V,comp,consEquiv,ht]) (fun v=> by simpa[V,comp,s,consEquiv] using congrFun e v)) ⟩
      unfold g; simp only [hm]; split_ifs <;> try rfl
      unfold x; simp [V,List.ofFn_succ, comp, consEquiv, scar]; rfl -- tune
    rw [if_neg ht]; symm; apply sum_eq_zero; intro i _; apply if_neg; intro h; apply ht; simpa [V, comp, consEquiv] using congrFun h 0
lemma body_view (K:α→Cipher n)(A:FC (Dwell n))(h: Fin d→δ): discount p d • scar A ((List.ofFn fun i=> ∑ j:α with P j = h i,K j)++(List.ofFn fun j=>Q.issue (t j) V W))=∑ L:(Fin d→α) with (P ∘ L=h),BodyX Q p d t L V W A K:=by unfold BodyX; simp_rw [scar_append]; rw [scar_fiber, Finset.smul_sum]; rfl
#print axioms body_view
end
end
end Argos
end ShoreQ
end Ivey
end YM.CF.Scree.Ing
end
