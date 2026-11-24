import SatinFixedContrastNovember4
import SatinThinReproofEnd

/-!
# Raw components (post-issue)

Supplements the canonical split assertions in SatinThinQuiz{Pair,Margin}. The prices there
use the canonical `Six.Comparison` at measurement height t, NOT the before-advancement split.

In fact in this raw scheme we can present the computation (even for all the smears)
so BOTH actual pure marginal inputs needed in computing the factorized predictions are
known, literally ZERO at t, piece by piece. The presentation can of course vary with t.
No claim of convergence of the *decompositions* in some norm.

Keep track of the support of all the pieces. Elementary key to the decomposition: act
with the localized pocket pulse not just to charge the standing matter legs -- take
a difference on the GAUGE legs additionally, without having to change the actual mark.
-/

set_option autoImplicit false
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Six
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock
open Satin
attribute [local instance] opCStarAlgebra
open Mir Haro Tap Dial Cascade Girt Pastry
open Afterglow Tapestry Tower

variable (K:Calibration)
local notation "Ξ" => Dome K
-- located, each piece's chosen gauge difference and matter phase
structure PulsePiece (D:Finset Cover) where
 g : Cover→SU.E
 θ : ℂ
 G : Dome K
 B : Dome K
 link : PureGauge K G
 matter : PureMatter K B
 lhere : G∈bay K D true
 mhere : B∈bay K D true
 price : θ≠1
 tilt : pennant K g B= θ • B
 localOn : ∀ i:Cover,i∉ D → g i=1
-- no Phase relation required for `link`.

variable {K}
namespace PulsePiece
variable {D:Finset Cover} (κ : PulsePiece K D)
def rawLink : Dome K := pennant K κ.g κ.G - κ.G
def costed : Dome K := κ.rawLink * κ.B
lemma rawGauge : PureGauge K κ.rawLink := (gaugePlane K).sub_mem (pennantPure K κ.g κ.link) κ.link
lemma rawHere : κ.rawLink ∈ bay K D true := (bay K D true).sub_mem (pennantLocal K D κ.g κ.lhere) κ.lhere
-- omit need for an expectation with continuity, positivity, normalization. Even works on
-- any test-space extension of the pure marginal satisfying that *pure Ward* property.
variable (E: Dome K →ₗ[ℂ]ℂ)
lemma ward_link {V:Finset Cover}(q:Disjoint D V){F:Dome K}(p:PureGauge K F)(h:F∈bay K V true) (w:GaugeWard K E) : E (κ.rawLink*F)=0:=by
 have hg : ∀ i∈V, κ.g i=1:= fun i h=> κ.localOn i (fun z=> Finset.disjoint_left.mp q z h)
 unfold rawLink; rw [_root_.sub_mul,map_sub,← fixed_local K V κ.g hg h] -- now also rewrites in second term; undo
 rw [←map_mul,w _ _ (gaugePure_mul K κ.link p),fixed_local K V κ.g hg h,sub_self]
lemma ward_matter {V:Finset Cover}(q:Disjoint D V){F:Dome K}(p:PureMatter K F)(h:F∈bay K V true) (w:MatterWard K E) : E (κ.B * F)=0:=by
 have hg : ∀ i∈V, κ.g i=1:= fun i h=> κ.localOn i (fun z=> Finset.disjoint_left.mp q z h)
 have ht:=w κ.g _ (matterPure_mul K κ.matter p)
 rw [map_mul,κ.tilt,smul_mul_assoc,fixed_local K V κ.g hg h,map_smul,smul_eq_mul] at ht
 by_contra a
 exact κ.price (mul_right_cancel₀ a (ht.trans (one_mul _).symm))
lemma link_zero(w:GaugeWard K E) : E κ.rawLink=0:= by unfold rawLink; rw [map_sub,w _ _ κ.link,sub_self]
lemma matter_zero(w:MatterWard K E) : E κ.B=0 := by simpa only [mul_one] using κ.ward_matter E (V:=∅) (Finset.disjoint_empty_right ..) (pure_unit K).2 (Subalgebra.one_mem _) w

end PulsePiece
variable (K)
lemma spanning_pulses (W:Bool)(S T D L:Finset Cover)(u:S∪T ⊆ D)(h:D ⊆ L)(d:Disjoint S T) {x:Dome K}
    (p:x.val ∈ DressedPair K W S T D)(e:x∈ enclave K):
    x∈ Submodule.span ℂ (Set.range (PulsePiece.costed (K:=K) (D:=L))) := by
  let g:Cover→SU.E:=fun i=>if i∈T then SU.central else 1
  let θ:=phaseName W
  have ha:∀ i∈S,g i=1:= fun i v=> if_neg fun h=> Finset.disjoint_left.mp d v h
  have hb:∀ i∈T,g i=SU.central:=fun i v=> if_pos v
  let Q:= Submodule.span ℂ {x|∃ (G B:Dome K), PureGauge K G ∧ PureMatter K B ∧
    G∈bay K D true ∧ B∈bay K D true ∧ pennant K g B= θ • B ∧ x=G*B}
  -- same reasoning as `illuminated_dressed`, but keep bay.
  have he:DressedPair K W S T D≤ Q.map (screenHall K).val.toLinearMap:=by
    refine Submodule.span_le.mpr ?_
    rintro z ⟨w,t,x,h,rfl⟩
    let c:Dome K:=⟨scalar K w,broadCompile K D (.seed t)⟩
    have hx: InTest K true D false x:= (raw_test K W S T h).1.mono u
    let l:Dome K:=⟨x,broadCompile K D hx⟩
    have Hc:pennant K g l=θ • l:=appointed K D g _ _ (pocket_charge K W S T D g u ha hb h) (show InTest K true D false (θ • x) from InTest.smul _ hx)
    exact ⟨c*l,Submodule.subset_span (show _∈_ from ⟨_,_,⟨D,w,t,rfl⟩,(show PureMatter K l from (raw_test K W S T h).2),InTest.seed t,hx,Hc,rfl⟩),rfl⟩
  obtain ⟨X,H,t⟩:=he p
  have v:x∈ Q:= (show X=x from Subtype.ext t) ▸ H
  let Z:= (pennant K g).toLinearMap - θ • (LinearMap.id : Dome K →ₗ[ℂ] Dome K) -- syntax
  let R:= Submodule.span ℂ (Set.range (PulsePiece.costed (K:=K) (D:=L)))
  have hl(i:Cover)(t:i∉ L):g i=1:= if_neg fun z=> t (h (u (mem_union_right S z)))
  have ht: Q≤R.comap Z:=by
    refine Submodule.span_le.mpr ?_
    rintro z ⟨G,B,a,b,p,q,y,rfl⟩
    let m: PulsePiece K L:= ⟨g,θ,G,B,a,b,tallerBay _ _ _ h p,tallerBay _ _ _ h q,pname_ne W,y, hl⟩ -- order
    change pennant K g (G*B) - θ • (G*B) ∈ R
    rw [map_mul,y, mul_smul_comm, ←smul_sub, ← _root_.sub_mul]; exact R.smul_mem _ (Submodule.subset_span (show _∈ _ from ⟨m,rfl⟩))
  have hp:pennant K g x - θ • x ∈ R:= ht v
  rw [(colorFixed K).1 e g, show x - θ • x=(1-θ) • x from by rw [sub_smul,one_smul]] at hp
  have ht:=R.smul_mem (1-θ)⁻¹ hp
  rwa [inv_smul_smul₀ (sub_ne_zero.mpr (Ne.symm (pname_ne W)))] at ht
end YM.CF.Buffered.Afterglow.Six
#print axioms YM.CF.Buffered.Afterglow.Six.spanning_pulses
