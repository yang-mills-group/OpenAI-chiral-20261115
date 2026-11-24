import GaugeFieldConstruction.Cupok4
import GaugeFieldConstruction.GibraltarA
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Py.Rate
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
open Ione Beau Haro Cascade Fief
open scoped Mew
open Wray Oath Feu Feu.Corset Nor Yaw Pig Oise Jade Plume Push.AbsoluteSums
open Trees Lich.Muster Jet
set_option linter.flexible false
open Eire Girt
open VolumeRate
namespace Pitching
open Vow Bake Larch
namespace Focus
open Oath Roots Riant
open Oath Roots Riant TableF Lenten Layout Fren
open SectorNext.Remainder.Scales Stockpile
open CoeffArc
open Scree.Ing Scree.Ing.Iona Scree.Ing.Grotto Lattice.Corona.Hive Scree.Ing.Rio
open Lor Sault Scree.Ing.Ivey Scree.Ing.Ivey.ShoreQ
variable (R: Patch)(k:ℕ)
local notation "C0"=>sizeK R.L 0
local notation "C1"=>sizeK R.L 1
local notation "C2"=>sizeK R.L 2
lemma danceNew3 : let w(x):=Flow4 k (radiusB x); let p(x):=Eta4 k (radiusB x); BoreP w ∧ BoreP (fun x=>(p x)⁻¹)∧ BoreP fun x=> Cube_M (radiusB x):=by
 intro w p; have g:= BoreP.radius_c
 have hz:BoreP fun x=>cubeCt (radiusB x):=by unfold cubeCt; simp_rw[Nat.cast_add,Nat.cast_one]; exact ((g.join g|>.join (BoreP.still 1)).self _)
 have he:BoreP w:=by
    unfold w Flow4 Lattice.Corona.Hive.yardZ yard_M; push_cast; exact ((((BoreP.still _).grip (((BoreP.still _).grip ((BoreP.still _).grip (BoreP.radius_c.join (BoreP.still 1)))).join (BoreP.still 9))).self 4).grip (BoreP.still _)) -- parentheses tune
 refine ⟨he,?_,?_⟩
 · unfold p Eta4; simp_rw [inv_div,div_eq_mul_inv]; exact (((he.grip hz).join (BoreP.still _)).grip (BoreP.still _))
 simp_rw[Cube_M, div_eq_mul_inv]; exact hz.grip (BoreP.still _)
variable {Z ℓ:ℝ→ℝ}
private lemma Chill_rightB (F G:ℝ→ℝ)(p:Chill_v F)(g:BoreP G):Chill_v (fun i=> F i*G i):=by simp_rw[mul_comm _ (G _)]; exact p.leanB g
lemma BootCl (d:Chill_v Z)(v:sizeK R.L 1 ℓ) (g:∀ᶠ x in atTop,0≤Z x∧0≤ℓ x): Chill_v (Speedy Z ℓ k)∧∀ᶠ x in atTop, Boot4 (radiusB x) (Speedy Z ℓ k x) (Eta4 k (radiusB x)) (ℓ x) (Z x) (Flow4 k (radiusB x)):=by
 obtain ⟨f,e,K⟩:=danceNew3 k
 have hp: Chill_v (Speedy Z ℓ k):=(d.noteR (Chill_v.coin (v.tint (f.creditK R.L)))).cheap _; have hx:= (hp.leanB K).spine_a.eventually (ge_mem_nhds (by norm_num: (0:ℝ)<1)); have ht:= (((v.tint (sizeK.mild R.L 4)).tint (e.creditK R.L))).spine.eventually (ge_mem_nhds (by norm_num: (0:ℝ)<1))
 refine ⟨hp,?_⟩; filter_upwards [hx,ht,g] with i h t g
 let R':= Speedy Z ℓ k i; let Y:=Z i; let F:= Flow4 k (radiusB i); let L:=ℓ i; let p:=Cube_M (radiusB i)*R'; let A:=advanceC (ℓ i) (Eta4 k (radiusB i)); have H:0≤F:=by unfold F Flow4 Lattice.Corona.Hive.yardZ; positivity
 have J:0≤ R':=mul_nonneg (by norm_num) (add_nonneg g.1 (mul_nonneg g.2 H))
 change p ≤ 1 at h; change A≤ 1 at t
 refine ⟨g.2, h,J,t,?_⟩
 have U': stolon (radiusB i) R' (Eta4 k (radiusB i)) (ℓ i) ≤ L*3:=by
    apply mul_le_mul_of_nonneg_left _ g.2; change 2*p +A≤3; linarith
 apply (le_trans (add_le_add_right (add_le_add (mul_le_of_le_one_left g.1 t) (mul_le_mul_of_nonneg_right U' H)) (Y+L*F)))
 change Y + L*F +(Y+L*3*F)≤4*(Y+L*F); nlinarith only[g.1,show Y=Z i from rfl]
lemma ΨAc (a:Chill_v Z)(e:sizeK R.L 1 ℓ) (g:∀ᶠ x in atTop,0≤Z x∧0≤ℓ x) (p:BoreP (fun x=>ℓ x/QLife R x)) : Chill_v (fun x=> GrayC Z ℓ k x/QLife R x) :=by
 have b:= (BootCl R k a e g).1; obtain ⟨f,u,H⟩:=danceNew3 k
 let P:=fun x=>Eta4 k (radiusB x); let w(x):=advanceC (ℓ x) (P x); let Q:= QLife R
 have hy: BoreP (fun x=>(ℓ x/Q x)*4*(P x)⁻¹):= (p.grip (BoreP.still 4)).grip u
 have hb:Chill_v w:= Chill_v.coin ((e.tint (sizeK.mild R.L 4)).tint (u.creditK R.L)); let G(x):=(ℓ x/Q x)*(2*(Cube_M (radiusB x)*Speedy Z ℓ k x)+w x)
 have he: Chill_v G:= ((b.leanB H|>.cheap 2).noteR hb).leanB p
 refine ((a.leanB hy).noteR (Chill_rightB _ _ he f)).trend ?_; filter_upwards with x; apply Eq.le; apply congrArg abs; unfold GrayC; unfold G Rio.advanceC stolon w P Q Rio.advanceC; ring -- tune
#print axioms ΨAc
end Focus
end Pitching
end YM.CF.Py.Rate
end
