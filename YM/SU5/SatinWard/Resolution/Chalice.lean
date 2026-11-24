import YM.CF.Nacre.Sift
import YM.SU5.SatinWard.Resolution.Mimic
import YM.SU5.Hiro.Crisp
set_option autoImplicit false
set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.QuadClock
open Neon
open Py
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Ione Moto Taxi Hove Haro Vow Bake Lilt Prism Rue Larch Push.AbsoluteSums.Trees Salt Jet
open scoped YM.CF.Mew
variable {N n B:Side}
open Tap Waxy Ione.Clock StressFlux SU


namespace SignSlot
open Buffered Swell Porticus Hest Nacre StressExchange Merino.Brooch
local notation "K0"=> Op SU.Slot
variable {p:BudgetPoint}

open Sour
open Lifted
variable (K:Buffered.Calibration)(M:Pal)(j:Axis) (A:Op SU.Slot)
variable (x:Cover) {U:Fields (K.c N)}
-- family, no-gauge and literal. suppress winding product certified for arbitrary period even crossing boundary.
abbrev gardenFlower (K:Buffered.Calibration)(o:Cover)(j:Axis) (A:Op SU.Slot) :Buffered.Family K:= fun N=> onsiteSensor (wrap (K.c N) o) (petal j⊗ₖ A)
local notation "senM"=> petal j ⊗ₖ A
local notation "Ki"=> SpinIdx × SU.Slot
local notation "Σg"=> (univ:Finset Ki)
private lemma frame(x:Site N) (F:Single N→ FC (Single N))(z:∀ u,u.1.1≠x→ F u=0): (∑ y: Single N,F y)=∑ i:Ki,F ((x,i.1),i.2):=by
 rw [show (∑ y:Single N,F y)= _ from Fintype.sum_prod_type F]; rw [Fintype.sum_prod_type (fun i: Site N × SpinIdx=>∑ j:SU.Slot,F (i,j)),Finset.sum_eq_single x];
 · symm; rw [Fintype.sum_prod_type]
 · intro i _ v; exact sum_eq_zero (fun _ _=> sum_eq_zero (fun _ _=> z _ v))
 simp
local notation "Uρ"=> (Σg.filter fun i=> i.1∈plusHalf)
local notation "Wρ"=> (Σg.filter fun i=> i.1∉plusHalf)
lemma gardenForm : gardenFlower K x j A = ∑ i∈ Uρ,∑ l∈ Wρ, (petal j⊗ₖ A) i l • (creation K x i.1 i.2 * removal K x l.1 l.2):=by
 funext N V; unfold gardenFlower; rw [spin_current]; let n:= K.c N; let y:= wrap n x; let c(i:Ki):Single n:= ((y,i.1),i.2); let T:= bud_k y y y senM; let Q(a b:Single n):= T a b • (put a*takeF b)
 have hp(i i': Ki):T (c i) (c i')= (petal j ⊗ₖ A) i i' := by unfold T; rw [latticeFieldEstimates y]; simp only [seed_k,c, Matrix.of_apply, and_self, ↓reduceIte] -- Hove.portB
 have hv (a b:Single n):T a b≠0→ a.1.1=y ∧ b.1.1=y:=by
    unfold T; rw [latticeFieldEstimates]; intro h; change (if y=a.1.1∧ y=b.1.1 then _ else 0:ℂ)≠0 at h
    split at h
    next g=>exact ⟨g.1.symm,g.2.symm⟩
    next g=> exact False.elim (h rfl)
 have hz (i l:Ki)(p:T (c i) (c l)≠0):i.1∈ plusHalf ∧ l.1∉ plusHalf:=by
    unfold T at p; rw [← spin_center y A j, touchP] at p -- `p` uses T
    rw [← dim_cut,Fock.cutM,Fock.cutM,Matrix.mul_diagonal,Matrix.diagonal_mul] at p; by_cases u:i.1∈ plusHalf; swap; · rw [if_neg (mt (fun h=> (Window.mem_Tset ..).1 h) u),zero_mul,zero_mul] at p; exact False.elim (p rfl)
    refine ⟨u, fun v=>?_⟩; rw [if_neg (show ¬c l∈ (Tset n)ᶜ from Finset.notMem_compl.mpr ((Window.mem_Tset ..).2 v)),mul_zero] at p; exact p rfl
 have h₀(j:Single n):∑ i,Q j i=∑ i:Ki,Q j (c i):=frame y _ fun i w=> by unfold Q; rw [ not_not.mp (mt (fun h=>(hv j i h).2) w),zero_smul]
 change (∑ i:Single n, ∑ k:Single n,Q i k)= _
 have hf(j:Single n)(p:j.1.1≠ y):(∑ i,Q j i)=0:= sum_eq_zero (fun i _=> by unfold Q; rw [ not_not.mp (mt (fun h=>(hv j i h).1) p),zero_smul])
 rw [frame y _ hf]; simp_rw [h₀]; simp only [Finset.sum_apply,Pi.smul_apply] -- tune
 rw [Finset.sum_filter]; apply sum_congr rfl; intro i _; split; swap; next h=> apply sum_eq_zero; intro l _; unfold Q; rw [not_not.mp (mt (fun p=> (hz i l p).1) h),zero_smul]
 next h=>
 rw [Finset.sum_filter]; apply sum_congr rfl; intro l _; split; swap; next g=> unfold Q; rw [not_not.mp (mt (fun p=>(hz i l p).2) g),zero_smul]
 next t=>
 unfold Q; rw [hp]; apply congr_arg; unfold creation removal basisC; simp only [Pi.mul_apply,basisC,map_smul,Fock.remove,star_smul,create_put,Matrix.smul_mul, Matrix.mul_smul]; let w:=Lifted.winding n x; have he:‖w‖=1:=Rush.fee_norm _; have ht:w*star w=1:=by rw [Complex.star_def,Complex.mul_conj,Complex.normSq_eq_norm_sq,he,one_pow,Complex.ofReal_one]
 change _=star w • (w • _); rw [smul_smul,mul_comm, ht,one_smul]; rfl
lemma gardenShot : InTest K false {nodeC x} false (gardenFlower K x j A):=by rw [gardenForm]; refine InTest.sum _ _ (fun i h=> InTest.sum _ _ fun l t=> .smul _ (.mul (.creator i.2 (mem_filter.mp h).2 ?_) (.remover l.2 (mem_filter.mp t).2 ?_))) <;>simp
lemma gardenTint (p:∀ g:SU.E,Commute A (matter g).val) (g:Seat N→SU.E)(o:Site N): twist (tradew N g) (bud_k o o o senM)= bud_k o o o senM:=by
 let Y:= seed_k o o senM; rw [latticeFieldEstimates o]
 have he (x y:Site N × SpinIdx):Nacre.ni x y Y= if o=x.1∧ o=y.1 then (petal j x.2 y.2) • A else 0:=by
    unfold Y Nacre.ni; by_cases h:o=x.1∧o=y.1 
    all_goals try rw [if_pos h]
    all_goals try rw [if_neg h]
    all_goals ext i l; simp [Matrix.of_apply,h,seed_k,Hove.portB,Matrix.kroneckerMap_apply,smul_eq_mul] <;> exact fun d=> (d (h.1.symm.trans h.2)).elim
 ext ⟨x,i⟩ ⟨y,l⟩; change Nacre.ni x y (twist (tradew N g) Y) i l= Nacre.ni x y Y i l; rw [Nacre.twistW,he]; split; swap; · simp
 next h=>
 have hh:x.1=y.1:=h.1.symm.trans h.2; let a:= matter (g (node o))
 rw [Matrix.mul_smul,Matrix.smul_mul]; have hx:terse x=node o:= congrArg Cube.node h.1.symm; rw [hx,show terse y=node o from congrArg Cube.node h.2.symm]; rw [(p _|>.symm.eq), mul_assoc, (matter _).property.2,mul_one] -- tune 
lemma gardenPrice (p:∀ g:SU.E,Commute A (matter g).val) (o:Site N) : covariant (onsiteSensor o senM):=by intro g x; rw [spin_current o A j (simultaneous g x),dg_cov,gardenTint _ _ p g o]
end SignSlot
end YM.CF.QuadClock
