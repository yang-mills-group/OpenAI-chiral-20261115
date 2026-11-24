import YM.CF.Yaw.Moss
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Yaw
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Eire Jet Scroll Push.AbsoluteSums.Trees
variable {ι:Type}
local notation "bay"=> Stilo.bay
open PetalP
variable {N P B:Side}(S:StepData (Domain N B) (Domain P B)){r D:ℕ}
open Rush Scroll Paige Vault Phase Acorn Spire
variable {A:Side}{j k:ℕ}{o:Odd A.val}{Y:Pricing j A o (Thread j)}{e:ℝ}{q:Grasp Y B e}{I:Aim (mid P B)}{M:Male}{α K K' t a d C H:ℝ}
variable (V: ∀ A:Support (Domain P B),Lend P B e A)(X:Tints P B e)
local notation "V'"=> Domain P B
local notation "L'"=> Oboe (Single (mid P B))
variable (K_ : Support (Domain P B))(G:Ids (mid P B))(g:Sweep (mid P B))
local notation "p''"=> (k+1:ℝ)
local notation "Ark"=> Shred V (actS g K_)
local notation "κ"=> K_
variable {W:Support (Domain P B)→ℝ} (v:∀ i:(Shred V (actS g K_)),Hive.fits (landX k K' K_ e) (home_n _) K_ (press_s V K_ G g i))(t_:Support (Domain P B) × Support (Domain P B))
variable {A:Type}[Fintype A][DecidableEq A](Q:ι→ Track (Stilo.Harper A) ℝ)
abbrev loadH (F: PetalP ι)(u:ℝ):ℝ:= ∑ i:F.slots,F.led i*u^(F.roll i).length
lemma loda(Q:PetalP ι)(X:ℝ)(A:Q.slots): ((Q.roll A).map fun _=> X).prod=X^(Q.roll A).length:=by generalize Q.roll A =l; induction l with| nil=>simp| cons u L ih=>rw [List.map_cons,List.prod_cons,List.length_cons,ih,pow_succ']
include v
lemma duty_p(h:0≤W t_.1):(0 ≤ (root_g k V K_ g t_ W).led) := fun i=> by unfold root_g; dsimp only; split; apply mul_nonneg (mul_nonneg (by positivity : (0:ℝ)≤ k+1) h) (mul_nonneg (by positivity) (v i).2.2.2.2.pos); exact le_rfl
lemma host_l (h:∀ Y,W Y≠0 → κ⊆ Y∧ Grove (terr _) Y) (i:(root_g k V κ g t_ W).slots)(p':(root_g k V κ g t_ W).led i≠0): Grove (terr _) t_.1 ∧ Grove (terr _) t_.2∧ κ⊆t_.1∧κ⊆ t_.2 ∧ ∀ j∈(root_g k V κ g t_ W).roll i, Hive.home_n _ j.2∈ t_.2:=by
 unfold root_g at p'; dsimp only at p'; split at p'; next hq=>
    obtain ⟨x,t⟩:= h t_.1 (right_ne_zero_of_mul (left_ne_zero_of_mul p')); obtain ⟨h,y,j,p,v⟩:= v i; rw [←hq]; exact ⟨t,y,x,h,p⟩ -- name
 contradiction
lemma hire_l (a d q A C D:ℝ)(u:0≤d)(h:0≤W) (p:(∑ i:Support V', Acorn.cost a K_ i *W i) ≤ C)(w:(∑ j:Ark, Hive.hireC q d K_ (press_s V K_ G g j)) ≤ D) : (∑ Y:Support V' × Support V', Acorn.cost a K_ Y.1*Acorn.cost q K_ Y.2*loadH (root_g k V κ g Y W) d)≤ ((k+1:ℝ)^2*C)*D:=by
 let R:= (∑ i:Support V',Acorn.cost a κ i*W i); let L:= (∑ i:Ark, Hive.hireC q d K_ (press_s V K_ G g i)); have hx:0≤R:=sum_nonneg fun i _=> mul_nonneg (rent_pos ..).le (h i); have ht:0≤L:=sum_nonneg fun i _=>mul_nonneg (mul_nonneg (rent_pos ..).le (pow_nonneg u _)) (v i).2.2.2.2.pos
 refine le_trans ?_ (mul_le_mul (mul_le_mul_of_nonneg_left (show R ≤ C from p) (by positivity :0 ≤ (k+1:ℝ)^2)) w ht (mul_nonneg (by positivity) (hx.trans p))); unfold loadH R; rw [Fintype.sum_prod_type,Finset.mul_sum (a:= (k+1:ℝ)^2),sum_mul]; apply sum_le_sum; intro i _; refine le_of_eq ?_; simp_rw [Finset.mul_sum]; change (∑ j:Support V',∑ l:Ark,_) = ∑ j:Ark,_; rw [sum_comm]; refine sum_congr rfl fun j _=>?_ ; rw [sum_eq_single (orig_r V κ g j)]; swap
 · intro y q' g'; rw [if_neg g'.symm]; ring
 · rw [if_pos rfl]; unfold hireC; change _= (k+1:ℝ)^2* (Acorn.cost a κ i* W i)*(Acorn.cost q κ (orig_r V κ g j)*d^(list_s V κ g j).length* score_k V κ g j); ring -- swap order notes
 simp
end YM.CF.Yaw
