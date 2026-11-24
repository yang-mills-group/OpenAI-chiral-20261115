import GaugeFieldConstruction.CloverSymmetryAxis
import GaugeFieldConstruction.IoneΛL
import GaugeFieldConstruction.DreamVU

/-!
# Covariant selection rule
At every pair configuration, for both orders and on any two covariant `boisterL` readout
families (in particular the elected vacuum). The spins on the measure coordinates are
not implicitly identified with the free ones: C is in the spin-two space after paying
`caller` of the SO(4) Ticket, and all the currents under consideration here have the
`LowInc` provenance. Full extension first, then W-distributions, no contact costs at
imaginary time zero for this order of product.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 15000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.GaugeFieldConstruction.Ember.Volumetric
open Calibration Raw Cauchy Phys Apit Stage Fathom Function Set Filter Module Empire Hulse Salam Palace
open Floor Carat Dawn Sailing Angles Points Bulb Analysis MeasureTheory Complex Finset
open scoped Topology BigOperators Matrix.Norms.Frobenius ComplexConjugate ContDiff Kronecker InnerProductSpace
attribute [local instance] iG iF iX iU iT2 iW2 iV iS
variable {S:City}{P:Axis→Across}{L:Sheds S P}{C:Supplies L}{u:ℕ→Carat}
namespace FirstPackMars.CloverRule
open Loft Cell NSF.Boundary NSF.Work.C20 NSF.LD
open YM.Boundary (Probe Probe.bar Joint Test4 Distn)
attribute [local instance] floatA floatY
attribute [local instance 30000] topx topg
open Stage.CloverSymmetry
variable (p:Ticket u C)
variable (Z:CloudsL)
variable (H:SurfCheckL Z) (V : SurfCheckL.boisterL p Z)

/-- keep imports independent of the legacy preparation for positions -/
abbrev sepCost (k: Points 2) (X Y : ΧiMars) : ℂ := Z 2 k ![X,Y]
-- Adapt VisPriceVU (includes the estimator API in its closure).
private def readLeft (k:Points 2)(y:ΧiMars) : ΧiMars→ₗ[ℂ]ℂ:= (Z 2 k).toLinearMap ![0,y] 0
private lemma leftAt(k:Points 2)(y x:ΧiMars) : readLeft Z k y x=sepCost Z k x y:=by
 rw [readLeft,MultilinearMap.toLinearMap_apply]; congr 1; ext1 i; fin_cases i <;> simp [sepCost]
private def readRight (k:Points 2)(x:ΧiMars):ΧiMars→ₗ[ℂ]ℂ:= (Z 2 k).toLinearMap ![x,0] 1
private lemma rightAt (k:Points 2)(x y:ΧiMars):readRight Z k x y=sepCost Z k x y:=by
 rw [readRight,MultilinearMap.toLinearMap_apply]; congr 1; ext1 i; fin_cases i <;> simp [sepCost]
def sepRead (k : Points 2) : (UV four) →ₗ[ℂ] (UV four) →ₗ[ℂ] ℂ where
  toFun := readRight Z k
  map_add' x y := LinearMap.ext (fun z => by
    rw [LinearMap.add_apply,rightAt,rightAt,rightAt]
    simp_rw [←leftAt]
    exact map_add .. )
  map_smul' c x := LinearMap.ext (fun z => by
    rw [LinearMap.smul_apply,rightAt,rightAt]
    simp_rw [←leftAt]
    exact map_smul .. )
lemma sepPay (k:Points 2)(X Y): sepRead Z k X Y = sepCost Z k X Y := rightAt ..
abbrev payFrame := (p.path.caller four).c
lemma journeyCharge (s : SO) x : compassPiMars p s ((payFrame p) x) = (payFrame p) (ledger All four s x) := by
 rw [LedgerBridgeMars]; dsimp only []; rw [LinearEquiv.symm_apply_apply,p.active]
include V
lemma travelSep (k:Points 2) (c:k∈conf 2) (s:SO)(x y):
    sepCost Z k ((payFrame p) x) ((payFrame p) y) =
    sepCost Z (motionMoonMars s k) ((payFrame p) (ledger All four s x)) ((payFrame p) (ledger All four s y)) := by
  have h := V 2 ![(payFrame p) x,(payFrame p) y] k c s
  rw [show compassPiMars p s ∘ ![(payFrame p) x,(payFrame p) y] =
      ![compassPiMars p s ((payFrame p) x), compassPiMars p s ((payFrame p) y)] from (by funext i; fin_cases i <;> rfl), journeyCharge, journeyCharge] at h
  exact h.symm

lemma timeCost (t:ℝ) (k:Points 2) (p0:k 0=0) (p1:k 1=t • basis 3) (c:k∈ conf 2)
    {v} (hv : v∈ orbitSpin2) (w : CogPV) : sepCost Z k ((payFrame p) v) ((payFrame p) (LowIncPV w)) = 0 := by
  let f := (sepRead Z k).compl₁₂ (payFrame p).toLinearMap ((payFrame p).toLinearMap ∘ₗ LowIncPV)
  have he : f v w = 0 := by
    apply axialCost f _ hv
    intro s h v w
    let g:= signMot s h.1
    have hx : motionMoonMars g k=k := by
      apply PiLp.ext; intro i; fin_cases i
      · change Ortho.motion s.ortho (k 0) = k 0; rw [p0,map_zero]
      change Ortho.move s.ortho (k 1) = k 1; rw [p1,holdsBasis s h]
    have u:= travelSep p Z V k c g v (LowIncPV w); rw [hx, lowCost, ← Stage.mirror s h.1, ← Stage.mirror s h.1] at u
    change sepRead Z _ _ _ = sepRead Z _ _ _; simp only [sepPay]; exact u
  exact (sepPay Z k ((payFrame p) v) ((payFrame p) (LowIncPV w))).symm.trans he

include H
theorem strictCost (k:Points 2) (c:k∈ conf 2) {v} (hv : v∈ orbitSpin2) (w : CogPV) :
    sepCost Z k ((payFrame p) v) ((payFrame p) (LowIncPV w)) = 0 := by
  let s := -(k 0)
  let x := NSF.Points.across s k
  have ht: x∈conf 2 := NSF.Points.across_in _ c
  have h:x 0=0 := add_neg_cancel (k 0)
  obtain ⟨g,t,he⟩:= upToTime (x 1)
  calc
    _= sepCost Z x ((payFrame p) v) ((payFrame p) (LowIncPV w)) := (H.even s (![(payFrame p) v,(payFrame p) (LowIncPV w)]) k c).symm
    _= sepCost Z (motionMoonMars g x) ((payFrame p) (ledger All four g v)) ((payFrame p) (LowIncPV (ledger All three g w))) := by rw [travelSep p Z V x ht g v, lowCost] -- tune
    _=0:= timeCost p Z V t (motionMoonMars g x) (by change Ortho.motion g.val (x 0)=0; rw [h,map_zero]) he (NSF.Points.move_in _ ht) (keepRotation g hv) _

omit V p in
lemma sepExchange (x y:ΧiMars)
    (h : ∀ k∈ conf 2, sepCost Z k x y=0) (k:Points 2) (t:k∈conf 2) :
    sepCost Z k y x=0 := by
  let S:=Equiv.swap (0:Fin 2) 1
  have u:= H.symmetry S (![y,x]) k t
  rw [show (![y,x]) ∘ S = (![x,y]) from by funext i; fin_cases i <;> simp [S]] at u
  exact u.symm.trans (h _ (NSF.Points.rearrange_in _ t))

variable {n:ℕ}
variable {A:CloudsL}(G:SurfCheckL A)
local notation "S_A"=> SurfRimL A
variable {W:NSF.Boundary.Surface (SurfRimL A)} {F:NSF.Boundary.Waves (SurfRimL A)} {N:W.Aurora drapeL}
variable (hF:F.Region (SurfRimL Z))(nt:F.NonTangentialFree W)(wX:N.FullBody F)

omit V p
include H hF wX
/-- Same entries after rotation to the relativistic distribution. Actually before padding
removal the entire tube entries already vanish. -/
theorem zeroPad (v:Fin n→ΧiMars)
    (h:∀ x∈conf n,Z n x v = 0) (x:Full n)(hx:x∈tube n):
    N.emit (G.TinCanL ∘ v) x = 0 := by
  refine ΛLaneL (X:=N.emit (G.TinCanL ∘ v)) (wX.hol n _) ?_ hx
  intro y hy
  rw [show N.emit _ _ = _ from ΥLiveΛL G H hF wX v hy]; exact h _ (ΜConfΛL hy)

include nt
theorem zeroDistrib (v:Fin n→ΧiMars) (h:∀ x∈conf n,Z n x v = 0) :
    W.W n (G.TinCanL ∘ v)=0 := by
  let T:= G.TinCanL ∘ v
  ext1 f; change W.W n T f = 0
  haveI:= awaits (light n)
  refine tendsto_nhds_unique_of_eventuallyEq (nt.corner _ _ f) tendsto_const_nhds ?_
  filter_upwards [self_mem_nhdsWithin] with t q
  have h0(i:Points n) : F.restricted T t i=0 := by rw [← wX.pure n T i t q]; exact zeroPad Z H G hF wX v h _ (roseΛ (etched q) _)
  change (∫ i,F.restricted T t i * f i)=0; simp_rw [h0]
  simp

end FirstPackMars.CloverRule
end YM.GaugeFieldConstruction.Ember.Volumetric
end
