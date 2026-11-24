import YM.SU5.SatinWard.Resolution.SpokeZ
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
variable {N n B₀:Side}
open Tap Waxy Ione.Clock StressFlux SU
namespace ShapeLab
open Module
local notation "EndC"=> Op SU.Slot
variable {ι:Type}[Fintype ι][DecidableEq ι]

-- End and turns. Preliminary rank receipts. Don't replace operator norm on preparation.
namespace SoulField
open Mezzo
variable {j:Axis}{U V:UNI SU.Slot}(h:Registrar U)(v:Registrar V)
local notation "Jι"=> Wage3

namespace Treaty
local notation "M"=> TuneM
local notation "I"=> (Fin 3)
local notation "C"=> Complex.I
variable (b:Bool)(i j:Fin 3)(z:Soul)
local notation "Tp" b:max=> ribbon b
noncomputable abbrev Xb :M:=ribbon b z
-- generator algebra: full entry decomposition. finite proof.
def voiceRow (A:TuneM):= (A 0 0).re -- remove
private lemma mem_diag (X:M)(t:star X=X)(a:I): (X a a).im=0:=by have ht:=Matrix.ext_iff.mpr t a a; change star (X a a)= X a a at ht; exact Complex.conj_eq_iff_im.mp ht
abbrev pairHit(A:TuneM)(i j: I):TuneM:= (A i j).re • earM i j+(A i j).im • peakMark i j
private theorem scoreTotal (X:M)(t:star X=X) :
 X=(X 0 0).re • earL 0 + (X 1 1).re • earL 1 + (X 2 2).re • earL 2 + pairHit X 0 1+pairHit X 0 2+pairHit X 1 2:=by
 ext1 i j -- Matrix.ext. may `ext1` multiple row? tune
 let U(i j : Fin 3):=star (X j i); have hx(i j: Fin 3):U i j=X i j:= Matrix.ext_iff.mpr t i j
 have uα(i j:I):(X i j).re=(X j i).re:=by simpa [U,Complex.star_def] using congrArg Complex.re (hx j i)
 have vα(i j:I):(X i j).im=-(X j i).im:=by exact neg_eq_iff_eq_neg.mp (by simpa [U,Complex.star_def] using congrArg Complex.im (hx j i))
 have w(i:I):i=0∨i=1∨i=2:=(show ∀ i:I,i=0∨i=1∨i=2 from by decide) i
 apply Complex.ext
 all_goals rcases w i with u|u|u <;> subst i <;> rcases (w j) with q|q|q <;> subst j <;> norm_num [earL,earM,peakMark,Matrix.single_apply,pairHit,show (2:Fin 3)≠ 0 from (by decide),show (2:Fin 3)≠1 from (by decide),show (0:Fin 3)≠ 2 from (by decide),show (1:Fin 3)≠ 2 from (by decide),mem_diag X t] -- omega fin.mod
 all_goals first| exact uα .. | exact vα ..

lemma treatment (z:Soul)(p:z∈depth) : patchH b (ribbon b z) (ribbon_star ..)∈ rotationHull:=by
 let X:= ribbon b z; let v:= ribbon_star b z; let a:I:=0; have h:(X 0 0).re=-((X 1 1).re+(X 2 2).re):=by
    let u:=(depth_iff z).1 p b; change (Matrix.trace X).re= 0 at u; rw [Matrix.trace] at u; change (∑ i:I,X i i).re=0 at u; rw [Fin.sum_univ_succ] at u; norm_num [Fin.sum_univ_succ] at u; linarith
 let F(t:I):=(X t t).re • (pivotL b t-pivotL b 0); let G(i j):= (X i j).re • buyerV b i j+(X i j).im • sellerV b i j
 have hp(i j:I): ribbon b (G i j)=pairHit X i j∧ ribbon (!b) (G i j)=0:=by unfold G; rw [map_add,map_smul,map_smul,map_add,map_smul,map_smul]; unfold buyerV sellerV; rw [patch_here, patch_here,patch_away,patch_away,smul_zero,smul_zero,add_zero]; exact ⟨rfl,rfl⟩ -- binder map_smul rewrites duplicate via simp.
 rw [show patchH b X v= F 1+ F 2 + G 0 1 + G 0 2 + G 1 2 from ?_]; swap
 · apply duplicate b
   · simp_rw [map_add,hp _ _ |>.1,F,map_smul,map_sub,pivotL,patch_here]; let s:= scoreTotal X v; rw [h] at s -- h rewrites unrolled RHS. handle LHS `simp` Danger.Gauge.
     refine s.trans ?_; module -- rw wrong X occurrences.R(…).
   simp_rw [map_add,(hp _ _).2, F,map_smul,map_sub,pivotL, patch_away,sub_zero,smul_zero,add_zero]
 have hr(i j:I)(h:i≠j):G i j∈rotationHull:= Submodule.add_mem _ (Submodule.smul_mem _ _ (at_toll b i j h)) (Submodule.smul_mem _ _ (underK b i j h))
 exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.smul_mem _ _ (walls b 1 0)) (Submodule.smul_mem _ _ (walls b 2 0))) (hr 0 1 (by decide))) (hr 0 2 (by decide))) (hr 1 2 (by decide))
lemma clearance : rotationHull= depth:=by
 apply le_antisymm contained; intro x h; have hp: patchH true (ribbon true x) _+patchH false (ribbon false x) _∈rotationHull:=Submodule.add_mem _ (treatment true x h) (treatment false x h)
 exact ((patches x).symm ▸ hp) -- `rw` both parts tune
-- for any real z.Mark corner.
lemma swing_zero (z:Soul) {U:UNI SU.Slot}(p:Registrar U): rotor p z-z∈ depth:= (depth_iff _).2 (fun i=>by rw [map_sub,genConcert,sub_self])
variable (X:Soul→ₗ[ℝ]Soul)(f:∀ (U:UNI SU.Slot)(p: Concert U)(z:Soul), X (rotor p.gate z)=rotor p.gate (X z))
include f
lemma readingTr (u:z∈ depth) : X z ∈ depth:=by
 rw [←clearance] at u; let D:= depth.comap X; change z∈ D; apply le_trans (show rotationHull ≤ D from ?_) le_rfl u; refine Submodule.span_le.mpr (fun x hx=>?_); obtain ⟨U,e,p,r,rfl⟩:=hx; change X _∈ depth; rw [map_sub,f U e]; exact swing_zero ..
lemma readingCore (u:z∈pureHeart): X z∈pureHeart:=by
 apply purity; intro g p _; rw [←f g p z]; exact congrArg (fun z=> X z) (purist z u p.gate)
omit f
-- if belongs pureHeart, reconstruct, invariant. relationship. Keep support for Θ.B.Label.Control.Need size bound of reconstruction (CLM). use later.
lemma coreRecover (h:z∈pureHeart): z=reconstructH z:=by
 let Z:Soul→ₗ[ℝ]Soul := {toFun x:=x- reconstructH x,map_add' x y:=by unfold reconstructH; simp_rw [map_add,add_div,add_smul]; module,map_smul' x y:=by unfold reconstructH; simp only [map_smul, smul_sub, smul_add, RingHom.id_apply]; module}
 have hp:pureHeart ≤ Z.ker:=by
    refine Submodule.span_le.mpr (fun z hx=>?_); obtain ⟨b,u⟩:= (show ∃ b:Bool,z=genCore b from (by have h:z=genCore true∨ z=genCore false:= Set.mem_insert_iff.mp hx; rcases h with h|h; exact ⟨_,h⟩; exact ⟨_,h⟩)); change z-reconstructH z=0; rw [u]; unfold reconstructH; cases b<;> rw [core_bill]; · rw [show generation true (genCore false)=0 from core_other false]; norm_num
    rw [show generation false (genCore true)=0 from core_other true]; norm_num
 exact sub_eq_zero.mp (show Z z=0 from hp h)
lemma core_cc(u:z∈pureHeart): cc (Reg z).val=(Reg z).val:=by
 rw [coreRecover z u,reconstructH, map_add,map_smul,map_smul,Submodule.coe_add,Submodule.coe_smul,Submodule.coe_smul]; rw [cc_add, cc_rsmul, cc_rsmul]; have hp(b:Bool): cc (Reg (genCore b)).val=(Reg (genCore b)).val:=valid_arm b _ cc_one; rw [hp,hp]
 -- might more. rewrite directly
#print axioms readingTr
end Treaty
end SoulField
end ShapeLab
end YM.CF.QuadClock
