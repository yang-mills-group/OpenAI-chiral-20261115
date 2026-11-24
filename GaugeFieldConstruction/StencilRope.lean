import YM.SU5.Registration.Ink.Potential
import YM.SU5.SatinWard.Resolution.IslandU
import YM.SU5.Assay.RawLag
import GaugeFieldConstruction.StencilValise
import YM.SU5.Registration.Rasp.PitchJet
import YM.SU5.Same.PrismReality

/-!
# Divergence of the billed point current inside the W-order domain

Proven from the levy equation at strict wall; `valise` uses Tw= duration symbol. Smeared
reconstruction on rapid domain over actual Ash & actual preparation. `levyTapeSt` a Wait argument via its call; companion application on actual `levy` of the ship. Sign & orientation fixed
as in the two contact conventions (+Eu mass but actual star Weyl); not Eu-only perturbative.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 330000
set_option maxRecDepth 8000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase
open MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound
open Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker
open scoped ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy
open Tapestry Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open CF.Velvet CF.Pannier.Chancel
open Spine Aria Casting Six OS.Semigroup OS.Semigroup.Balloon
open MacroGrid SatinNucleus SatinJets DoseTravel Set
open OS.Semigroup.Gear
namespace Discipline
variable (P:Spine) (x:P.Spectrum0 3)
local notation "ν"=> P.advocate 3 x 3
local notation "B!"=> P.ManyF 3 ν
local notation "T_Δ"=> P.seasons 3 ν
open _root_.YM.SatinRegistration _root_.YM.SatinWFixed Carton
open _root_.YM.SatinJets _root_.YM.SatinJets.Drums
open _root_.YM.Boundary _root_.YM.CF.Buffered.Afterglow.Hierarchy
open Seld MeshClock.Carousel Six
-- precision coordinates time-last, species first. banner orientation in §. Mirror needed for reading star but not this price.L
abbrev takeDerivative (j:Axis): Test4→L[ℂ] Test4:= if j=(3:Axis) then timeJet 3 else -Seld.shade (basis j)
lemma take_feet (j:Axis)(f:Test4) : tsupport (takeDerivative j f) ⊆ tsupport f:=by
 unfold takeDerivative; split; next h => exact time_reach 3 f
 next h => exact Set.Subset.trans (tsupport_comp_subset (g:=fun x:ℂ=> -x) (by simp) (Seld.shade (basis j) f)) (SchwartzMap.tsupport_lineDerivOp_subset ..)
private lemma polar_support (j:Axis)(t:ℝ)(u:j≠3): polarBase (axisLn j t)= t • basis j:=by
 let w:= (axisLn j t); apply Mink.ext_by
 · change YM.spatial (YM.position _ 0)=_; rw [YM.spatial_position]; ext x; by_cases h:x.castSucc=j<;>simp [spacePart, w, axisLn, spatial,basis_eq,h]
 · change YM.time _= _; simp only [polarBase, Cheer.shore,time_position]; simp [timeAxis,time,u,Ne.symm u]
lemma twist_point (j:Axis)(u:j≠3)(t:ℝ)(A:(P.ManyF 3 ν).Op): P.locate 3 ν (axisLn j t) A = optx T_Δ A (t • basis j):=by
 let τ:=t • basis j; have he(p:Vantage): P.cartage 3 ν p=M T_Δ (polarBase p):=(P.cart_plank x p).symm
 unfold locate optx; rw [he, he, polar_support j t u, show -(axisLn j t)=axisLn j (-t) from by unfold axisLn; rw [Pi.single_neg],polar_support _ _ u,neg_smul]
local notation "DK_" => radial T_Δ
variable {G:Type*}[AddCommGroup G][Module ℂ G] (V: Carton (P.seasons 3 (P.advocate 3 x 3)) G)
variable (J:Axis → ℝ→ℝ→ (P.ManyF 3 (P.advocate 3 x 3)).Op)(qα:Axis→G)(p:∀ i l,0<l→V.bar l (qα i)=J i l l)(y: ∀ i, (P.seasons 3 (P.advocate 3 x 3)).Credits 0 (J i))
variable (O:G)(Λ:ℂ)(hq:Λ≠0)
-- divergence sign witness. no adjust normalization by tuning x.
noncomputable abbrev opStR (H:Hilbert) : NormedSpace ℝ H.Op:= inferInstance
local instance (priority:=high) stR (P:Spine)(i:Axis)(x:P.Spectrum0 i):NormedSpace ℝ (P.ManyF i x).Op:= opStR (P.ManyF i x)
noncomputable abbrev levyTapeSt (T:ℝ→ ℝ → (P.ManyF 3 (P.advocate 3 x 3)).Op)(l r:ℝ)(m:Axis):= if m=3 then deriv (currentTemp T l r) 0 else fderiv ℝ (fun z:Vantage=> P.locate 3 (P.advocate 3 x 3) z (T l r)) 0 (axisLn m 1)
variable (hX:∀ (l:ℝ≥0),0<l→ (∑ j:Axis, levyTapeSt P x (J j) l l j)= Λ • V.bar l O)
  (W: ∀ (l:ℝ≥0),0<l→∀ j:Axis,j≠3→ DifferentiableAt ℝ (fun z:Vantage=> P.locate 3 (P.advocate 3 x 3) z (J j l l)) 0)
include p y W
lemma billing_derivation (f:Test4)(i:Axis)(a:ℝ≥0)(q:0<a):
  valise (T_Δ) (levyTapeSt P x (J i) a a i) f= valise (T_Δ) (V.bar a (qα i)) (takeDerivative i f):=by
 unfold takeDerivative levyTapeSt; split_ifs with u; swap
 · rw [p i a q]; let τ(v:Vantage):= P.locate 3 ν v (J i a a); let d:= axisLn i 1; apply val_space
   have hm(t:ℝ) : axisLn i t=t • d:=by unfold d axisLn; rw [←Pi.single_smul',smul_eq_mul,mul_one]
   have he:= (W a q i u).hasFDerivAt.hasLineDerivAt d; unfold HasLineDerivAt at he
   simpa only [←twist_point P x i u,hm,one_smul,zero_add] using he
 let s:= a/2; have hs:0<s:=half_pos q; let h:= qα i; let A:= V.bar s h; let B:=J i s s; have he: A=B:= p i _ hs
 rw [baryTime _ (J i) (y i) a s hs (add_halves a)]
 have h': V.bar a h= (T_Δ).E s * B *(T_Δ).E s:=by rw [←he]; exact (congrArg (fun a=> V.bar a h) (add_halves a)).symm.trans (V.coherent h s hs s) -- (T_Δ).E parse! local write (T_Δ).
 exact val_rope T_Δ f _ _ (roped_action T_Δ s hs _ _ h')
include hX hq
lemma checkout (l:ℝ≥0)(ht:0<l)(f:Test4): valise T_Δ (V.bar l O) f= (Λ⁻¹:ℂ) • ∑ i:Axis,valise T_Δ (V.bar l (qα i)) (takeDerivative i f):=by
 let L:=(valMeasure T_Δ f); have hz:= congrArg L (hX l ht); rw [map_smul,map_sum] at hz
 have h(i): L (levyTapeSt P x (J i) l l i)=valise T_Δ (V.bar l (qα i)) (takeDerivative i f):= billing_derivation P x V J qα p y W f i l ht
 simp_rw [←h]; rw [hz,smul_smul, inv_mul_cancel₀ hq,one_smul]; rfl -- tune
lemma erase_heat_st (f:Test4): V.operator O f = Λ⁻¹ • ∑ i:Axis,V.operator (qα i) (takeDerivative i f) :=by
 ext1 t; apply Subtype.ext; change (V.black O f t).val= (((Λ⁻¹:ℂ) • (∑ i:Axis,V.operator (qα i) (takeDerivative i f)) t):DK_).val; rw [Submodule.coe_smul_of_tower,LinearMap.sum_apply, Submodule.coe_sum]; apply tendsto_nhds_unique_of_eventuallyEq (V.watches O t f) ((tendsto_finset_sum Finset.univ fun i (_:i∈ Finset.univ)=>V.watches (qα i) t (takeDerivative i f)).const_smul (Λ⁻¹:ℂ))
 filter_upwards [self_mem_nhdsWithin] with i u; have hb:= DFunLike.congr_fun (checkout P x V J qα p y O Λ hq hX W i u f) t.val; rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply] at hb; exact hb
#print axioms erase_heat_st
end Discipline
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
end
