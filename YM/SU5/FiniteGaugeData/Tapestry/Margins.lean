import YM.SU5.FiniteGaugeData.Tapestry.Rafters
import YM.SU5.FiniteGaugeData.Tapestry.Chintz
import YM.SU5.FiniteGaugeData.Tapestry.Chalice
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 560000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tapestry
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock
open Satin
attribute [local instance] opCStarAlgebra
open Py Py.Rate LocalLimit Preparation Journey Vale FullBill
open Nacre Mir Phase RP
open Altitude Heat Pastry
open PiTensorProduct (tprod)

/-!
# Stretched across the physical readings, Z and probes

What the shape budget buys: One volume, enough for COHERENT SUPPORT on the
native torus. Operator bounds (Ward) and differences, readers with the same
election. These estimates all pay on `x` with `Pocket(...,C, x)` for any such
outer Toll system. This directly permits linear combinations in prepared
comparisons, as well as thinnings on supports/heights.
-/
set_option quotPrecheck false
variable {Λ: Preparation} {l : ℕ} (Y:Course Λ (VolumeCape.Dream.Nimbus l)) (H:Real.exp 1 ≤ Λ.x)
variable {a b:ℕ→ℕ} {I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ} {L:Rack Λ l}{B:Clay Λ l} (D:Exhibition Y H a b I E L B)
variable (S:BillOfWork)(n i k:ℕ)
local notation "κ"=> tent Y H
local notation "V"=> frameBudget S Λ l n
local notation "Ω" i:max=> side Y i n
local notation "i₁" t:max => a (WedgeStage.vol t)
local notation "k₁" t:max => b (WedgeStage.uv t)
local notation "μ"=> propeller
local notation "η" t:max=> spread (frameBudget S Λ l t)
local notation "P"=> Pocket (tent Y H) S n
open Exhibition

lemma textureBudget (p:Pay Y n i k) (x:Cloud (Dome κ)){u} (t:Pocket (tent Y H) S n u x):
    AtSupport false (region (frameBudget S Λ l n) (side Y i n)) (attire (breathing Y H n i k x)):=by
 induction t with
 | stone x t=> exact wearH Y H i k n S x p t
 | no=> rw [map_zero,attire_none]; exact AtSupport.zeroM
 | shade z e t=> rw [map_smul,attire_scale]; exact t.smulM _
 | blend _ _ u v=> rw [map_add,attire_add]; exact u.addM v
 | fully _ _ v=> exact v
-- specify clock once and cone estimates entirely.
lemma shaping (x:Cloud (Dome κ)){u}(p:Pocket (tent Y H) S n u x): Exhibition.vistaFinish Y H n D x∈ bay (tent Y H) (frameBudget S Λ l n) true:= by
 induction p with
 | stone x t=> unfold motif pureShot vistaFinish; rw [Decking.reckon_paid _ _ _ t, D.comparedVista Y H n S x]; exact locatesBadge ..
 | no=>rw [map_zero]; exact Subalgebra.zero_mem _
 | shade z e t=> rw [map_smul]; exact Subalgebra.smul_mem _ t z
 | blend _ _ u v=> rw [map_add]; exact Subalgebra.add_mem _ u v
 | fully _ _ v=> exact v

-- give multi-reader bounds and support/representation uniform inside cone (no further K schedule)
structure Allows (x:Cloud (Dome (tent Y H)))(C r:ℝ) : Prop where
 affordable : Pay Y n i k
 appears : AtSupport false (region (frameBudget S Λ l n) (side Y i n)) (attire (breathing Y H n i k x))
 rangeLimit : ‖breathing Y H n i k x‖ ≤ spread (frameBudget S Λ l n) * Hank Y H S n B*C
 grip : ‖breathing Y H n i k x - roving Y H n i (D.vistaFinish Y H n x)‖ ≤ r*(spread (frameBudget S Λ l n)*ArcFee Y H S n B)*C
 reading : ‖taking Y H i k x - D.vistaTake Y H x‖ ≤ r*Garland Y H D S n*C
namespace Allows
-- true operator comparison. no change of axes type.
lemma nativeComparisons {r:ℝ}{x C}(p: Allows Y H D S n i k x C r) (W: Fields (side Y i n)):
    ‖attire (breathing Y H n i k x) W‖≤ spread (frameBudget S Λ l n) * Hank Y H S n B*C ∧
    ‖attire (breathing Y H n i k x) W - exhibit Y H n i (D.vistaFinish Y H n x).val W‖≤ r*(spread (frameBudget S Λ l n)*ArcFee Y H S n B)*C:=
 ⟨le_trans (Ward.pay (breathing Y H n i k x) W) p.rangeLimit,le_trans (Ward.pay (breathing Y H n i k x-roving Y H n i (D.vistaFinish Y H n x)) W) p.grip⟩
lemma reportedBudget {C:ℝ}{t:WedgeStage}{x}(p:Allows Y H D S n (i₁ t) (k₁ t) x C (propeller t.vol))(q:Pocket κ S n C x):
    ‖Journey.compass Y (i₁ t) (k₁ t) n (attire (breathing Y H n (i₁ t) (k₁ t) x)) - E n ((D.vistaFinish Y H n x).val)‖ ≤ μ t.vol * Garland Y H D S n*C:=by
  have h:=p.reading; rw [vistaCall Y H n _ D q.funded,taking_phys _ _ _ _ _ _ p.affordable q.funded] at h; exact h
end Allows
namespace Exhibition
lemma wearQ_practice(B:Finset Cover)(x : Swatch B) : ‖wearStep Y H B n i x‖ ≤ spread B*‖x‖:= Ward.save _ (present_bound Y H n i B x)
lemma horizon : ∀ᶠ t in followStage, Pavilion Y S n (i₁ t) (k₁ t) ∧ ∀ (x : Cloud (Dome κ))(C:ℝ), Pocket (tent Y H) S n C x → Allows Y H D S n (i₁ t) (k₁ t) x C (propeller t.vol):=by
 filter_upwards [D.stage_cost Y H S n] with i q
 obtain ⟨h,p⟩:= q
 let m:=i₁ i; let k:=k₁ i
 let F(x:Employee S):= costumeAt Y H m k n S x; let Z:= breathing Y H n m k
 let f:= ArcFee Y H S n B; let A:=Hank Y H S n B
 let v:= wearStep Y H (frameBudget S Λ l n) n m
 let g: Cloud (Dome κ) →ₗ[ℂ] Ward (side Y m n):= (roving Y H n m).toLinearMap.comp (D.vistaFinish Y H n)
 let V'(x:Employee S) := outfitView Y H n S x B
 have ja (x:Employee S)(a: Clocked (K:=tent Y H) S n x): Z (motif κ S x)=v (F x):=(breathing_pure Y H n m k _ a).trans (comparedOutfit Y H m k n S x h.admit)
 have jb (x:Employee S)(a: Clocked (K:=tent Y H) S n x): g (motif κ S x)=v (V' x):=by
   change roving Y H n m (D.vistaFinish Y H n (motif κ S x))=_; unfold motif pureShot vistaFinish; rw [Decking.reckon_paid _ _ _ a,D.comparedVista Y H n S x]; exact rovingBadge ..
 have hp:0 ≤ η n:= Nat.cast_nonneg _; have hx:0≤ μ i.vol:= by unfold propeller; positivity
 refine ⟨h,fun x C t=> ⟨h.payZ,textureBudget Y H S n m k h.payZ x t, t.bequeath Z (mul_nonneg hp (Hank_pos ..)) (fun x t=> ?_), t.bequeath (Z-g) (mul_nonneg hx (mul_nonneg hp (ArcFee_pos ..))) (fun x u=> ?_), t.bilAsk _ _ (mul_nonneg hx (Garland_pos ..)) (fun x u=> (p x).2.2 u)⟩⟩ -- args order D H? check textureBudget below
 · rw [ja x t,mul_assoc]; exact (wearQ_practice Y H n m _ _).trans (mul_le_mul_of_nonneg_left (p x).1 hp)
 change ‖Z _-g _‖ ≤ _; rw [ja x u, jb x u,show v (F x)- v (V' x)=v (F x-V' x) from (v.toLinearMap.map_sub (F x) (V' x)).symm]; exact (wearQ_practice Y H n m _ _).trans ((mul_le_mul_of_nonneg_left (p x).2.1 hp).trans_eq (by ring))
end Exhibition
end YM.CF.Buffered.Afterglow.Tapestry
#print axioms YM.CF.Buffered.Afterglow.Tapestry.Exhibition.horizon
#print axioms YM.CF.Buffered.Afterglow.Tapestry.Allows.reportedBudget
#print axioms YM.CF.Buffered.Afterglow.Tapestry.Allows.nativeComparisons
#print axioms YM.CF.Buffered.Afterglow.Tapestry.shaping
