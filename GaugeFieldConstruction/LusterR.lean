import GaugeFieldConstruction.LunaraR
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
attribute [local instance] opCStarAlgebra
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
variable {P:Spine}
namespace Shower
variable {I:Type}[Fintype I][DecidableEq I]{cost:ℕ→P.Test→ℂ}(C: ∀ j:Axis, Porch P cost j)
section
variable (S:I→ScreensJ P)(p:∀ i, AttainedR 0 (S i))
variable (j:Axis)(σ:I→PermWallJ P)(A:I→P.Slabs j)
local notation "δ" i:max=> StallJ P (σ i)
abbrev AskR (P:Spine){I:Type}(x:I→Axis→marks (timeMesh P.par)):= clearAbove x
abbrev BodyΘ (P:Spine){I:Type} (S:I→ScreensJ P)(j:Axis)(σ:I→PermWallJ P)(i:I):= S i j (σ i) (σ i)
variable (k:Axis)(τ:I→PermWallJ P)(L L':List I)(e:L.Perm L')
local notation "X" j:max σ:max=> StageR σ (C j) (BodyΘ P S j σ)
local notation "T" j:max σ:max L:max=> OpenR j σ L
local notation "ζ"=> (T j σ L) ∩ (T k τ L')
variable (v:I→P.VMark)
include p e
lemma eau_rR : Sharing (X j σ) (X k τ) L L' ((OpenR j σ L) ∩ (OpenR k τ L')) [] []:=by
 intro x u; have u': x = x:=rfl
 choose m eS using p
 have he (j:Axis)(σ:I→PermWallJ P)(L:List I)(g:AskR P x∈ OpenR j σ L):∃ h:ℕ→ℂ,Tendsto h atTop (𝓝 ((X j σ).ranking L x [])) ∧ ∀ᶠ v:ℕ in atTop,∀ᶠ l:ℕ in atTop,∀ y:I→ Cover,(∀ i,P.vtile l (y i)=x i)→ h v=cost l (Porch.poseTiles P y (fun i=>P.conveying v (l-v) (m i v)) L):=by
    choose F H h using fun i=>eS i j (σ i) (σ i)
    let W(i:ℕ)(l:I):=F l i
    have he:= (price_conR σ (C j) L x).continuousAt.tendsto.comp (tendsto_pi_nhds.mpr (show ∀ i:I,Tendsto (fun v=> W v i) atTop (𝓝 (BodyΘ P S j σ i)) from H))
    refine ⟨_,he,?_⟩; filter_upwards [eventually_all.mpr h] with v h
    let B:= StageR σ (C j) (W v)
    change ∀ᶠ _ in atTop,∀ y:I→ Cover,_→B.ranking L x []=_
    have hx(i:I): P.Habitable j (m i v) v (-Xφ σ i) (-Xφ σ i+Xτ σ i) (W v i):=by
      rw [show -Xφ σ i= (0:P.VMark) j-(σ i).val from (zero_sub _).symm, show _+ Xτ σ i=(0:P.VMark) j + (σ i).val from ?_]; exact h i
      unfold Xτ Xφ; abel
    apply (C j).fee_hives _ hx _ L (B.plane_enough _ ?_)
    unfold B; rw [on_rR]; exact g
 obtain ⟨h,H,t⟩:=he j σ L u.1; obtain ⟨a,d,w⟩:=he k τ L' u.2
 refine tendsto_nhds_unique_of_eventuallyEq H d ?_
 filter_upwards [t,w] with v u c
 obtain ⟨r,U,W,e'⟩:=(u.and (c.and (eventually_all.mpr fun i:I=> mint_voxel (P:=P) (x i)))).exists
 choose y g using e'
 rw [U _ g,W _ g]; exact congrArg (cost r) ((e.map _).prod_eq) -- recast
lemma Shore_R (u:L.Nodup) : Set.EqOn ((X j σ).reading L) ((X k τ).reading L') ((OpenR j σ L) ∩ (OpenR k τ L')):=by
 refine (Sharing.smooth _ _ _ _ u (e.nodup_iff.mp u) _ ?_ (eau_rR C S p j σ k τ L L' e)).mono subset_closure
 rw [←on_rR σ (C j) (BodyΘ P S j σ),←on_rR τ (C k) (BodyΘ P S k τ)]; exact (smooth_highway ..).inter (smooth_highway ..)
-- mesh plenum via family_sync h
omit e
variable (L':Axis→ List I)(Γ':Axis→ I→ PermWallJ P)(hm:∀ j,L.Perm (L' j))
include hm
lemma Billing_R (u:L.Nodup)(e:AskR P v∈ OpenR j σ L)(a:∀ i, AskR P v∈ OpenR i (Γ' i) (L' i)) : (X j σ).reading L (AskR P v)=(X j σ).ranking L v []:=by
 let H:= (OpenR j σ L) ∩ ⋂ i:Axis, OpenR i (Γ' i) (L' i)
 let B:= (X j σ)
 have h(j:Axis)(σ:I→PermWallJ P) (l:List I):IsOpen (OpenR j σ l):=by rw [← on_rR σ (C j) (BodyΘ P S j σ)]; exact smooth_highway ..
 rw [show (X j σ) = B from rfl, show AskR P v=clearAbove v from rfl, B.reading_exact L v]; apply B.family_sync L u H ((h ..).inter (isOpen_iInter_of_finite (fun i=>h ..))) _ _ _ (And.intro e (Set.mem_iInter.mpr a))
 intro i; let z:=i.val; refine ⟨(C z).H, (X z (Γ' z)), L' z,fun u p'=>?_⟩; exact eau_rR C S p j σ z (Γ' z) L (L' z) (hm z) u ⟨p'.1,Set.mem_iInter.mp p'.2 z⟩
end
end Shower
end BoonsθJ
end RosterJ
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
