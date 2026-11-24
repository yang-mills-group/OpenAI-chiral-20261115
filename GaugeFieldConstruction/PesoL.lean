import GaugeFieldConstruction.BrotH
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
variable {n:Side} {α β I M:Type}[LinearOrder I][Fintype I][Fintype α][Fintype β]
section arb
variable {c:Side}[DecidableEq α]{E:Type}[AddCommMonoid E][Module ℂ E]
variable (σ:I→Site c)(x:Key I)(L:List I)(i:α)(F:E)
lemma can_single (y:α): Canz σ E (clipK σ i L F) x y= if ψS σ L∧ y=i then carR x L • F else 0 :=by
 unfold Canz; split; next v=>
    have p:L.toFinset ∈ realm_C σ:= mem_filter.mpr ⟨mem_univ _,pays_z σ v.1⟩ -- tune
    rw [sum_eq_single_of_mem _ p, clipK,if_pos (show ψS σ L∧_= _ from ⟨v.1,by rw [v.2]⟩),stack_eq L v.1]; intro j _ h; unfold clipK; rw[if_neg (fun a=>h (congrArg Prod.fst a.2)),smul_zero]
 next h=> exact sum_eq_zero fun a _=> by unfold clipK; rw[if_neg (fun p=>h ⟨p.1,congrArg Prod.snd p.2⟩),smul_zero]
lemma can_pour (L:Finset α)(F:α→dues I β→E):Canz σ E (∑ i∈L,F i) x = ∑ i∈ L,Canz σ E (F i) x:=by
 funext i; induction L using Finset.induction_on with
 | empty=> simp only [sum_empty,puff_zero,Pi.zero_apply]; exact puff_zero ..
 | insert a L u ih=> rw[sum_insert u,sum_insert u,puff_add,Pi.add_apply,ih]
end arb
section loom
variable {p:BudgetPoint}{S:α→ Support (More n)}{z:β→Force n}(σ:I→Seat n)
section
variable {γ:Type*}{A:Type}[NormedCommRing A][NormedAlgebra ℂ A][CompleteSpace A]
lemma pipeR_kin (R:Force n)(x:Key I→ Force n→ A) (W x':Key I→A)(h:River W):River W:=h -- tune junk
lemma sparkKin (Ω:Support (More n))(a:Key I→Force n→A)(f g:Key I→Force n→A) (p:∀ i,River (fun z=>a z i))(h:∀ i,Kin σ (fun z=>f z i) (fun z=>g z i)): Kin σ (fun z=>sparkJet Ω (a z) (f z)) (fun z=>sparkJet Ω (a z) (g z)):=by
 have H(x:Force n→ A): PourUp id x=x:=by funext i; simp[PourUp,sum_filter]
 have e(x y:Force n→ A) : sparkJet Ω x y=∑ S:Finset (Force n),∑ b:Force n, if PriceI (Sum.elim id id) Ω (S.disjSum {b}) then (∏ i∈S,x i)*y b else 0:=by
    have q:=prize_line Ω id id (n:=n) x y; rwa[H,H] at q
 have k(S:Finset (Force n)):River (fun z=>∏ i∈S,a z i):=by
    induction S using Finset.induction_on with
    | empty=> simp only [prod_empty]; exact zeroR _
    | insert i S h ih=> simp_rw [prod_insert h]; exact (p _).mul_T ih
 simp_rw[e]; apply loft_bank; intro i w; apply loft_bank; intro v a; split; exact Kin.mulT (Kin.refl _ (k i)) (h v); exact Kin.refl _ (zeroR _)
end
lemma KinClip {D E:Type}[DecidableEq α][NormedAddCommGroup E][NormedSpace ℂ E][CompleteSpace E](i j:α)(F:D→ E)(x:D)(l:List I):Kin σ (fun z=>(Canz σ (D→E) (clipK σ i l F) z j x)) (fun z=>if j=i then carR z l • F x else 0):=by
 simp_rw [can_single]
 by_cases h:j=i
 · subst j; by_cases w:ψS σ l
   · simp only [w,true_and,↓reduceIte]; exact Kin.refl _ (arc0 l (F x))
   simp only [w,false_and,↓reduceIte,Pi.zero_apply] -- Pi.zero_apply
   exact ⟨zeroR _,arc0 l (F x),fun i p=> (tip_0 _).trans (noStem σ l i w p (F x)).symm⟩
 simp only [h,and_false,↓reduceIte,Pi.zero_apply]; exact Kin.refl σ (zeroR _)
-- first def single ready. actual footprints.M.Transaction.Sem at Kernel.u.
namespace Grotto
variable (A:Grotto I S z)
local notation "L0"=> Heart A.anchor S A.needs
local notation "T"=> Legist A.anchor S A.needs
local notation "K0" i:max=> Base z (Legist A.anchor S A.needs i) A.flag
local notation "T0" i:max=> roost z (Legist A.anchor S A.needs i) A.flag
-- sem untrim.Portal Lens.$flag derivative ≠ mark. If extra mode=  derivative.
variable (p:BudgetPoint)(x:Key I)
-- use defs for op sem
abbrev goReg (P:Pane n)(g:L0):= if !A.flag && decide (Disjoint ((T g).val.2) (flags p.threshold P)) then carR x (A.fromR g) • (A.termR g P) else (0:Cipher n)
def goBoat (v:β→ Cipher n)(U:Orbit n)(i:L0) := let h(b:Finset β):= carR x (A.fromB i b) • (A.termB i b U); profileT z (T i) A.flag (flags p.threshold U.1) (fun P=>(∏ j∈P\ ashC (T i) z P,v j)*h (ashC (T i) z P))
-- exact differential insertion
noncomputable def cashVector (M:β→Cipher n)(U:Orbit n) := (∑ i:L0, A.goReg p x U.1 i) * hum (flags p.threshold U.1) z M + ∑ i:L0,A.goBoat p x M U i
variable (U:Orbit n)(v:Rue.FleetS p.threshold U.1)
local notation "Ω"=>flags p.threshold U.1
include v
lemma BringR : Kin σ (fun z=> exponentL p (Canz σ _ (Rinc σ A) z) U.1) (fun z=>∑ i:L0, A.goReg p z U.1 i):=by
 let Kfine(i:L0):= if A.flag then 0 else A.termR i
 let Z(z:Key I)(i:L0):=exponentL p (Canz σ _ (clipK σ (T i) (A.fromR i) (Kfine i)) z) U.1
 -- use vertical sum.Lift_P.def
 have H(z:Key I): exponentL p (Canz σ _ (Rinc σ A) z) U.1=∑ i:L0,Z z i:=by
    rw [Rinc,can_pour]; unfold Z exponentL; -- tune.Composibility
    rw [sum_comm]; apply sum_congr rfl; intro y _
    simp_rw [numbE]; by_cases px:pingS p.threshold y.val.2 U.1
    · simp only [Set.indicator_of_mem (s:={t:Pane n|pingS p.threshold y.val.2 t}) (a:=U.1) px,Finset.sum_apply]; rfl
    simp only [Set.indicator_of_notMem (s:={t:Pane n|pingS p.threshold y.val.2 t}) (a:=U.1) px,sum_const_zero]
 simp_rw[H]
 apply loft_bank; intro i g
 by_cases a:A.flag
 · have e(z):Z z i=0:=by unfold Z exponentL; refine sum_eq_zero (fun u p=>?_); rw [can_single]; simp only [Kfine,if_pos a, smul_zero,ite_self,numbE]; simp
   simp_rw[e,goReg,a]; simp only [Bool.not_true,Bool.false_and,Bool.false_eq_true,↓reduceIte]; exact Kin.refl σ (zeroR _)
 have e(z): Z z i= if pingS p.threshold (T i).val.2 U.1 then (Canz σ _ (clipK σ (T i) (A.fromR i) (A.termR i)) z (T i) U.1) else 0:=by
    unfold Z exponentL; rw [sum_eq_single (T i)]; · simp only [Kfine, if_neg a]; rfl -- indicator same
    · intro j _ h; rw[can_single,if_neg (fun u=> h u.2)]; unfold numbE; simp
    simp
 simp_rw[e,goReg]; by_cases ht:Disjoint (T i).val.2 Ω
 · have hw:=(Rue.shoreK _ _ v _).1 ht; simp_rw[if_pos (show (!A.flag && decide (Disjoint (T i).val.2 Ω)) = true from (by simp [ht,Bool.eq_false_iff.mpr a])),if_pos hw] -- tune
   simpa only [if_pos rfl, ↓reduceIte] using KinClip σ (T i) (T i) (A.termR i) U.1 (A.fromR i)
 have p0:¬pingS p.threshold (T i).val.2 U.1:=fun t=>ht ((Rue.shoreK _ _ v _).2 t); simp_rw[if_neg p0]; simp [ht]; exact Kin.refl σ (zeroR _)
end Grotto
end loom
end YM.CF.Scree.Ing
end
