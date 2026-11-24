import ZecaSilver
import ZecaQuilt
import ZecaFroth
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 400000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
namespace Spine
open Aria Casting Six OS.Semigroup OS.Semigroup.Balloon
open MacroGrid SatinNucleus SatinJets

variable (P:Spine) (x:P.Spectrum0 3)


local notation "ξ"=>P.advocate 3 x 3
local notation "S"=>P.seasons 3 ξ
local notation "G"=>P.ManyF 3 ξ
local notation "ε"=>P.physicalEnergy 3 ξ
local notation "Ω"=>P.heaven 3 ξ
local notation "ν"=>P.nv 3 ξ
local notation "E"=>(P.seasons 3 ξ).E
open Hierarchy.Seld.Zeca
open Hierarchy.Seld (parabola M)

open DoseTravel Set

local notation "MH"=> Hierarchy.Seld.Zeca.Moment

variable (A:ℕ→P.Apron)
variable {FaY:P.Nib 3 (P.advocate 3 x 3)}{CaY: Hierarchy.Seld.Zeca.Moment (P.ManyF 3 (P.advocate 3 x 3))}
lemma sold_equity (i:P.Iguana 3 ξ FaY A)(b:P.Bought 3 ξ CaY A):P.Truth 3 ξ FaY CaY:=by
  obtain ⟨k,g,t⟩:=b
  constructor;intro u v s z;rw [←t.translation u v s z]; ext1 y
  exact tendsto_nhds_unique ((i.nib.dye u v s z).seeks y)
                             ((g.dye u v s z).seeks y)
local notation "N"=>Hierarchy.Seld.Zeca.Moment.notch S
lemma notchedTruth (h:P.Truth 3 ξ FaY CaY):
     P.Truth 3 ξ (P.notchD ξ FaY) (N CaY):=by
  constructor; intro u v t p
  let a:=(u:ℝ)/2; let b:=(v:ℝ)/2
  let s:=a.toNNReal; let z:=b.toNNReal
  have A:0<a:=half_pos t
  have B:0<b:=half_pos p
  have e:(s:ℝ)=a:=Real.coe_toNNReal _ A.le
  have v₀:(z:ℝ)=b:=Real.coe_toNNReal _ B.le
  have q:0<s:=show (0:ℝ)<s from e ▸ A
  have r:0<z:=show (0:ℝ)<z from v₀ ▸ B

  have w:s+s=u:= NNReal.eq <| by rw [NNReal.coe_add,e]; unfold a; ring
  have g:z+z=v:=NNReal.eq <| by rw [NNReal.coe_add,v₀]; unfold b; ring
  change Stellar.ladle _ _ _ (FaY a b)=_
  rw [show FaY a b= _ from (congrArg₂ FaY e.symm v₀.symm).trans (h.translation s z q r),
      Stellar.ladle]
  exact (Hierarchy.Seld.Zeca.Moment.billNotch _ CaY s z q r).trans (congrArg₂ ((N CaY).cost (S)) w g)

def nibbled (i:ℕ)(D:MH G):MH G:= (Hierarchy.Seld.Zeca.Moment.notch (S))^[i] D
lemma nib_truth (h:P.Truth 3 ξ FaY CaY) (i:ℕ):
 P.Truth 3 ξ (P.pitchJar ξ FaY i) (P.nibbled x i CaY):=by
 induction i with
 | zero=>exact h
 | succ i g=>rw [nibbled,pitchJar,iterate_succ_apply',iterate_succ_apply'];exact P.notchedTruth x g
lemma nib_copy (D:MH G) (e:D.Copy (S) CaY) (i:ℕ):
 (P.nibbled x i D).Copy (S) CaY:=by
 induction i with
 | zero=>exact e
 | succ i g=>rw [nibbled,iterate_succ_apply'];exact Hierarchy.Seld.Zeca.Moment.notchCopy _ _ _ g

lemma e_self (a:ℂ): (P.essence ξ a CaY).Copy (S) CaY:=by
 intro f
 exact ⟨_, Hierarchy.Seld.Zeca.Moment.ts_smul a f,(P.essence_op ξ a CaY f).trans (map_smul (CaY.field S) a f).symm⟩

lemma Flares {c r n:ℕ→ℕ}{w:Lead.Clan→Prism}
 {D:P.Cilium x}
 (p:P.foraged x A c r n w D)
 (b:P.Bought 3 ξ CaY A)(j:Lead.Clan) : (D j).Copy (S) CaY:=by
 obtain ⟨FaY,i,g⟩:=p
 have t:=P.sold_equity x A i b
 let d:ℂ:=purePrice j
 let V:=P.essence ξ d CaY
 have h:P.Truth 3 ξ (P.spark x j FaY) V := P.True_essence ξ d CaY t
 let Y:=fun i:ℕ=>P.nibbled x (i+1) V
 let z:=w j
 apply Hierarchy.Seld.Zeca.Moment.copy _ _ z.support z Y
 swap; · intro u; exact P.nib_copy x V (P.e_self x d) (u+1) -- t ∀i only, arg l?
 intro u p
 rw [← (g j).2.translation u u p p]
 refine Finset.sum_congr rfl (fun i _=> congrArg (w j i • ·)
     ((P.nib_truth x h (i+1)).translation u u p p))

#print axioms Flares

#print sold_equity