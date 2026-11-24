import GaugeFieldConstruction.CherubL
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
open SignetS
-- width budget: min rack with Plethora in place independent of X. Bound ratio to p⁻¹ and polynomial wages. (Width use W includes n factor but Enough).
def widthSucL (P:Spine)(i:ℝ≥0)(k:ℕ):Prop:= StallJ P (AutoPadR P k)<(i:ℝ)
lemma vacantWL (i:ℝ≥0)(u:0 < i):∃ k,widthSucL P i k:=( (SecondEraJ P).eventually (gt_mem_nhds (show 0<(i:ℝ) from u))).exists
noncomputable def scaleWL (P:Spine)(i:ℝ≥0):= if h:0 < i then Nat.find (vacantWL i h (P:=P)) else 0
noncomputable def PaidPadL (P:Spine): AllocatedL P where
 pad i:=AutoPadR P (scaleWL P i)
 cent {p} hp:=by rw [scaleWL,dif_pos hp]; exact Nat.find_spec (vacantWL _ hp)
lemma usageWL (P:Spine)(i:ℝ≥0)(hi:0 < i)(k:ℕ)(h:k< scaleWL P i): (i:ℝ) ≤ PlethoraJ P k:=by rw [scaleWL,dif_pos hi] at h; exact le_of_not_gt (Nat.find_min (vacantWL _ hi) h)
lemma rateWL (P:Spine):∃ c:ℝ,0<c∧∀ k:ℕ,PlethoraJ P k * (2:ℝ)^k ≤ c :=by
 obtain ⟨n,h⟩:= eventually_atTop.mp ((PetitionJ (P:=P) 2 (by norm_num) (by exact_mod_cast (lt_of_lt_of_le (by norm_num:2<3) P.par.R.coarse))).eventually (ge_mem_nhds zero_lt_one))
 let f(k:ℕ):= PlethoraJ P k * (2:ℝ)^k; let c:=∑ i ∈ Finset.range (n+1), f i
 have ht(i:ℕ):0≤ f i:= mul_nonneg (PledgeJ P i).le (by positivity)
 have hc:0≤c:=Finset.sum_nonneg fun i _=>ht _
 refine ⟨1+c,by linarith,fun i=>?_⟩
 by_cases v:i≤n
 · exact (single_le_sum (f:=f) (fun i _=>ht i) (mem_range.mpr (by omega))).trans (le_add_of_nonneg_left zero_le_one)
 exact (h i (by omega)).trans (le_add_of_nonneg_right hc)
lemma ΨSlashL (P:Spine): ∃ c:ℝ,0<c ∧ ∀ i:ℝ≥0,i∈ Set.Ioo 0 1→ (2:ℝ)^(scaleWL P i)≤ c*(i:ℝ)⁻¹:=by
 obtain ⟨c,h,t⟩:= rateWL P; let c':=max (2*c) 1; refine ⟨c',lt_of_lt_of_le zero_lt_one (le_max_right ..),?_⟩; intro i g; have h₁: 0<(i:ℝ):=g.1; have h₂:(i:ℝ)<1:=g.2
 generalize w:scaleWL P i=A; cases A with
 | zero=> rw[pow_zero]; apply le_trans (le_max_right ..); exact le_mul_of_one_le_right (zero_le_one.trans (le_max_right ..)) ((one_le_inv₀ h₁).2 h₂.le)
 | succ n=>
    have hp: (i:ℝ)*(2:ℝ)^n≤ c:= (mul_le_mul_of_nonneg_right (usageWL P i g.1 n (by omega)) (by positivity)).trans (t n)
    rw[pow_succ, ←div_eq_mul_inv]; apply (le_div_iff₀ h₁).2; rw[mul_comm _ (i:ℝ)]
    rw[←mul_assoc]; calc
       _ ≤ c*2:= mul_le_mul_of_nonneg_right hp (by norm_num)
       _ ≤ _:= by rw[mul_comm]; exact le_max_left ..
-- buoy rate Pe
lemma liftRackL {cost:ℕ→P.Test→ℂ}{j:Axis}(C:Porch P cost j)(k:P.Slabs j):‖LadderRackMars C k‖≤‖k‖:=by
 let U' := (C.canopy.track.aviator C.canopy.list)
 apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _); intro x
 exact (Submodule.norm_orthogonalProjectionOnto_apply_le U' _).trans (((C.ρ k).le_opNorm _).trans (mul_le_mul_of_nonneg_right (C.watch_le k) (norm_nonneg _))) -- tune name
open YM.GaugeFieldConstruction YM.GaugeFieldConstruction.Ember YM.GaugeFieldConstruction.Ember.Volumetric
attribute [local instance] iG iF iX iU iT2 iW2 iV iS
variable {cost:ℕ→P.Test→ℂ}{j:Axis} (C:Porch P cost j) (A:AllocatedL P)(R:ΧiMars→ₗ[ℂ]ScreensJ P)
lemma flagLiftL p x: ‖RimTimeL C R A p x‖ ≤ ‖shadowL (j:=j) R A p x‖:=by
 let E:= C.BrightHab.E (slitL A p); have hp:‖E‖≤1:=C.BrightHab.shrinks _; let L:=LadderRackMars C (shadowL R A p x)
 change ‖E.comp (L.comp E)‖ ≤ _; apply (ContinuousLinearMap.opNorm_comp_le ..).trans; apply (mul_le_of_le_one_left (norm_nonneg _) hp).trans; apply (ContinuousLinearMap.opNorm_comp_le ..).trans; exact (mul_le_of_le_one_right (norm_nonneg _) hp).trans (liftRackL C _)
structure SailsArtL (R:ΧiMars→ₗ[ℂ]ScreensJ P) (A:AllocatedL P) :Prop where
 rate (x:ΧiMars) (j:Axis): ∃ (B:ℝ)(n:ℕ), 0<B ∧ ∀ p:ℝ≥0,p∈Set.Ioo 0 1→ ‖shadowL (j:=j) R A p x‖ ≤ B*(p:ℝ)⁻¹^n
lemma cinnabarL {cost:ℕ→P.Test→ℂ}(C:Porch P cost timeAxis)(t:CloudsL){X:CloudsL}(D:SurfCheckL X)(w:SailsArtL R A): NSF.Bid.Piece (SmallRimL C R A t D) where
 price v:= by obtain ⟨x,rfl⟩:=D.TinCanL.surjective v; obtain ⟨b,n,h,z⟩:= w.rate x timeAxis; refine ⟨b,n,h,fun p e=>?_⟩; change ‖RimTimeL C R A p (D.TinCanL.symm _)‖≤ _; rw [LinearEquiv.symm_apply_apply]; exact (flagLiftL C A R p x).trans (z p e)
#print axioms ΨSlashL
#print axioms cinnabarL
end Shower
end BoonsθJ
end RosterJ
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
