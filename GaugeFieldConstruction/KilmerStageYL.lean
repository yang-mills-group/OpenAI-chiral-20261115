import GaugeFieldConstruction.LeitYL
import GaugeFieldConstruction.NightAtlasYL
import GaugeFieldConstruction.LehuaImprovedMars
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical

open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
open Designs Twah Prototype
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
open Regis.Head Regis.Head.Brecht
namespace Spine
open Aria Casting Six
open CF.Velvet CF.Pannier.Chancel Pitching.Focus
open YM.CF.Oath.BellPrice CF.Fief
open Oath
open Papal AUbard
open Papal FrameP Yoke.Promena WorldJ Frugal CF.Scroll MirrorCost
open Py Yoke.Promena
open CF.Neon CF.XGarden CF.XGarden.MastTin CF.XGarden.MastTin.ArtCart
open CF.TableF CF.TableF.Lenten CF.XGarden CF.XGarden.Shield
open WorldJ
open scoped YM.CF.Mew
open Pitching.Focus.CoeffArc TableF TableF.Lenten TableF.Lenten.Layout TableF.Lenten.Layout.Fren
open Ing Ing.Ivey CF.XGarden.MastTin
open CF.Pastry CF.Hive
open CF.Scroll
namespace RosterJ
namespace BoonsθJ
open JetCurry JetCurry.TrekJ ProbeθJ Yoke SelectionAnalysis
open Repertoire 

namespace Shower
open SignetS
open YM.GaugeFieldConstruction YM.GaugeFieldConstruction.Ember YM.GaugeFieldConstruction.Ember.Volumetric FirstPackMars Stage Calibration Phys Calibration.Floor
open NSF.Table.Pairing
attribute [local instance] Ember.iG Ember.iF Ember.iX Ember.iU Ember.iT2 Ember.iW2 Ember.iV Ember.iS
variable (G:CloudsL)
variable {n:ℕ}{S: City} {P0:Axis→Empire.Across} {L:Sheds S P0} {Cu: Supplies L} {u:ℕ→Carat}
-- axis carried thru. CPI covariance proper. Suit has ALL axes declared, no H3 tilt for phase yet
open NSF.Boundary NSF.OS.Semigroup -- no OS namespace clash
open NSF.LD
-- (137)-->(138) variant: projection joint on actual POS. norm displacement criterion; everything commutes on same Hil. use E2 costs, no invocation of L1 for chosen x until after L3!
variable (a:Axis)(p: Points n)(F:Fin n→ ΧiMars)
open Set Complex
open PlaneL
open YM.GaugeFieldConstruction.Fathom Points Bulb
variable {m:ℕ}(y:Points m)(V: Fin m→ΧiMars)(k: Fin n)(b:Fathom.Bulb)(r:ℝ)
lemma ledgeUpYL (q:E4)(m':Points m)(t':ℝ): ledgeYL (k.castAdd m) a r (apartYL q p m') t'= apartYL q (ledgeYL k a r p t') m':=by
 ext1 i; unfold apartYL; let N:= NSF.Points.across q m'; refine Fin.addCases (fun i=>?_) (fun i=>?_) i
 · rw [brightLYL]; by_cases s:i=k
   · subst i; simp [ledgeYL, mirDirYL, NSF.Points.direction, brightLYL]
   have he:i.castAdd m≠ k.castAdd m:=fun h=> by have v:=congrArg Fin.val h; exact s (Fin.ext v)
   simp [ledgeYL,mirDirYL, NSF.Points.direction, he, s, brightLYL]
 rw [brightRYL]; have he: Fin.natAdd n i≠ k.castAdd m:=ne_of_gt (show k.val < n+i.val from lt_of_lt_of_le k.2 (by omega))
 simp [ledgeYL,mirDirYL, NSF.Points.direction,he,brightRYL]
-- add before cast
lemma crownH_YL (n m:ℕ): n+1+m=n+m+1:=by omega
lemma YappendYL {X:Type*}(n m:ℕ)(F: Fin n→ X)(V:Fin m→X)(s:X):Fin.append (Fin.cons s F) V=(Fin.cons s (Fin.append F V)) ∘ (Fin.cast (crownH_YL n m)):=by
 ext1 i; refine Fin.addCases (fun i=>?_) (fun i=>?_) i
 · refine Fin.cases ?_ ?_ i
   · rw [Fin.append_left,Function.comp_apply,show Fin.cast (crownH_YL n m) ((0:Fin (n+1)).castAdd m)=0 from Fin.ext rfl]; rfl
   intro j; rw [Fin.append_left, Function.comp_apply,show Fin.cast (crownH_YL n m) (j.succ.castAdd m)=(j.castAdd m).succ from Fin.ext rfl]; simp
 rw [Fin.append_right,Function.comp_apply,show Fin.cast (crownH_YL n m) (Fin.natAdd (n+1) i)= (Fin.natAdd n i).succ from ?_]; simp
 apply Fin.ext; change n+1+i.val=n+i.val+1; omega
lemma crownF_YL {n m:ℕ}(h:m=n)(F:Fin n→ ΧiMars)(x:Points n):G m (points (x.ofLp ∘ Fin.cast h)) (F ∘ Fin.cast h)=G n x F:=by subst m; rfl
lemma KioskYL (q:E4)(z:E4): gluedYL (YM.Points.cons z p) y= points ((YM.Points.cons z (gluedYL p y)).ofLp ∘ Fin.cast (crownH_YL n m)):=congrArg points (YappendYL n m _ _ z)
lemma CrownAddYL (W:ΧiMars)(z:E4)(q:E4): G _ (apartYL q (YM.Points.cons z p) y) (Fin.append (Fin.cons W F) V)= G _ (YM.Points.cons z (apartYL q p y)) (Fin.cons W (Fin.append F V)):=by unfold apartYL; rw [KioskYL p _ q, YappendYL,crownF_YL] -- unused q binder causes lints
-- eventually separated spectator across ANY compact stage. topology ℕ ↑.
lemma exteriorRunYL (Z:Set E4)(z:IsCompact Z):∀ᶠ i:ℕ in atTop, ∀ k:Fin m, NSF.Points.across (EarYL i) y k ∉ Z:=by
 obtain ⟨b,h⟩:= ((z.image (show Continuous (fun x:E4=>x timeAxis) by fun_prop)).bddAbove)
 refine eventually_all.mpr fun k=>?_ ; filter_upwards [tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop (b-y k timeAxis))] with i p v
 have he:= h (Set.mem_image_of_mem _ v)
 change (y k + (i:ℝ) • basis timeAxis) timeAxis ≤ b at he; simp at he; linarith
lemma calmPathYL (F':ℝ→Points n)(fc:Continuous F')(h:∀ i∈α0_YL,BreatherMars b k (F' i))(v:y∈conf m):∀ᶠ i:ℕ in atTop,∀ j∈α0_YL, BreatherMars b (k.castAdd m) (apartYL (EarYL i) (F' j) y):=by
 have he:∀ᶠ i:ℕ in atTop,∀ a:Fin n,∀ l:Fin m,NSF.Points.across (EarYL i) y l ∉ (fun x:ℝ=>F' x a) '' α0_YL:= eventually_all.mpr fun a=> exteriorRunYL y _ (isCompact_Icc.image ((show Continuous (fun p:Points n=>p a) by fun_prop).comp fc))
 filter_upwards [he, exteriorRunYL y b.run b.c] with i t u j p
 let N:=NSF.Points.across (EarYL i) y; have hv:=h j p; change BreatherMars b _ (gluedYL (F' j) N)
 refine ⟨GlueConfYL (F' j) N hv.bounds (NSF.Points.across_in _ v) (fun a l e=> t a l (⟨j,p,e⟩)),(brightLYL ..).symm ▸ hv.home,?_⟩ -- trans err
 intro z; refine Fin.addCases (fun a e=>?_) (fun l e=>?_) z
 · rw[brightLYL]; exact hv.apart a (fun h=> e (congrArg _ h))
 rw[brightRYL]; exact u l
#print axioms calmPathYL
end Shower
end BoonsθJ
end RosterJ
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
