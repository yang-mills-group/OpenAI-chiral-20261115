import YM.SU5.FiniteGaugeData.Tapestry.Well
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 460000
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
# The trajectory really respects the invariant / singlet tests

Finite claims on the EXACT paying trajectory. Fix the gauge in the torus at the
observing level even if the final advance is already performed before. The
GPhysical used to test (torus lookups of relevant Γ choices) at that n already
gives the correct one at the lower levels. Then the mixed mark used in the
numerator on *all* actual arguments is covariant. This verifies the choice of
physical observable algebra on cover and on limit -- not assuming a gauge/law
extension across periods. Also useful reader identity for ANY of the (even)
marks, after interaction/view gauge arguments. And the limiting B & E commute
with these actions appropriately, now for all polynomials.
-/
set_option quotPrecheck false
section harmony
variable {n:Side}(v:Seat n→SU.E)
abbrev AllFrame (u:Cover→SU.E) : Prop:= v ∘ wrap (More n)=u -- abbrev for capsule
abbrev Partners (x y: Ward n):= Harmony v (attire x) (attire y)
variable {x X y Y: Ward n} (p:Partners v x X) (t:Partners v y Y)
include p t
lemma Partners.addM : Partners v (x+y) (X+Y):=by intro W; rw [attire_add,attire_add,Pi.add_apply,Pi.add_apply,map_add,p W,t W]
lemma Partners.mulM : Partners v (x*y) (X*Y):=by intro W; rw [attire_mul,attire_mul,Pi.mul_apply,Pi.mul_apply,map_mul,p W,t W]
omit t
lemma Partners.scaleM (u:ℂ): Partners v (u • x) (u • X):=by intro W; rw [attire_scale,attire_scale,Pi.smul_apply,Pi.smul_apply, twist_scalar, p W]
omit p
lemma noPartners : Partners v (0:Ward n) 0:=fun W=> (map_zero _).symm
end harmony

section
variable {Λ: Preparation} {l : ℕ} (Y:Course Λ (VolumeCape.Dream.Nimbus l)) (H:Real.exp 1 ≤ Λ.x)
variable (i k n:ℕ)(u:GPhysical)
local notation "K"=> tent Y H
local notation "Z" n:max => side Y i n
local notation "fired" n:max => restrictG Λ n u
local notation "Q" n:max => Vale.apt (Y.ir i) Λ.block Λ.R.L n
variable (t:Seat (side Y i (n+1)) →SU.E)
lemma parents_fit (p:AllFrame t (restrictG Λ (n+1) u)):AllFrame (scaleG (Q n) t) (restrictG Λ n u) := by
  rw [gaugeHarmony]; funext i'; unfold parentGauge scaleG; simp only [Function.comp_apply,Ratio.embed_wrap]; exact congrFun p _
variable {v:Seat (side Y i n)→ SU.E} (h:AllFrame v (restrictG Λ n u))
include h
lemma partnered (x:Dome K): Partners v (roving Y H n i x) (roving Y H n i (pennant K (restrictG Λ n u) x)):=by
  obtain ⟨S,p⟩:=findsBay (tent Y H) x; exact truePrinting S (restrictG Λ n u) Y H n i (pennantTrace (tent Y H) S (restrictG Λ n u) p) (fun i _=>congrFun h i)
local notation "σ" => tidalDressing Y H i k
variable (p:Pay Y n i k)
include p
lemma localPartnership (f:ℕ→Dome K): Partners v (Decking.finish (tidalDressing Y H i k) n f) (Decking.finish (tidalDressing Y H i k) n (rainyTail Λ K u f)):=by
  induction n with
  | zero=> exact partnered Y H i 0 u h (f 0)
  | succ n ih=>
     let z(f):Ward (side Y i n):= Decking.finish (σ) n f
     let u':=z f; let g:= rainyTail Λ K u f; let w:= z g
     have hx: Partners v (music Y n i k u') (music Y n i k w):=by
       unfold Partners music; rw [flowing, flowing]; exact ascendHarmony Y n i k (p:=p) (Ward.signs w) v (Ward.signs u').env (ih (parents_fit Y i n u v h) ⟨p.1,(by have he:=p.2; omega)⟩)
     exact Partners.mulM v hx (partnered Y H i _ u h (f (n+1))) -- tune order
lemma paidPartners (f:Cloud (Dome K))(q:f∈shorter (Dome K) n): Partners v (breathing Y H n i k f) (breathing Y H n i k (rainfall Λ K u f)):=by
 apply boarded (P:={f|Altitude.Enough n f}) (M:=fun f=> Partners v (breathing Y H n i k f) (breathing Y H n i k (rainfall Λ K u f))) ?_ ?_ ?_ ?_ q
 · intro f t; change Partners v (breathing Y H n i k (pureShot K f)) (breathing Y H n i k (rainfall Λ K u (pureShot K f))); rw [rainfallPure, breathing_pure _ _ _ _ _ f t,breathing_pure _ _ _ _ _ _ (rainyEnough Λ K n u t)]; exact localPartnership Y H i k n u h p f
 · rw [map_zero,map_zero,map_zero]; exact noPartners v
 · intro x y i j p q; rw [map_add,map_add,map_add]; exact p.addM v q
 intro r x t z; rw [map_smul,map_smul,map_smul]; exact z.scaleM v r

lemma paid_chorales (f:Cloud (Dome K))(q:f∈shorter (Dome K) n): taking Y H i k f=taking Y H i k (rainfall Λ K u f):=by rw [taking_phys _ _ _ _ _ f p q,taking_phys _ _ _ _ _ _ p (raining_height Λ K n u q)]; exact trueHarmony Y n i k p v (paidPartners Y H i k n u h p f q)
omit h
lemma paid_coherence (x:Cloud (Dome K)) {a:Bool}{V:Set RSpace}{S:Set ℕ} (q:x∈well Λ K l a V S)(t:x∈shorter (Dome K) n): covariant (attire (breathing Y H n i k x)):=by
 intro g; obtain ⟨u,e⟩:= iceExtension Λ n (g∘wrap (More (side Y i n))); have he:=paidPartners Y H i k n u e.symm p x t; rw [(well_spec ..).mp q|>.2 u] at he; exact he
omit p
-- every assertion of psd/full resolution polynomial eventually in regime needing no clipping
lemma consistentLimit (x:Cloud (Dome K))(q:x∈ FiniteGaugeDataPoly K): ∀ᶠ k in atTop, x∈shorter (Dome K) (Y.uv k)∧Pay Y (Y.uv k) i k:=by
  obtain ⟨s,v⟩:=curve.mp q; exact ((Y.uv_grows.tendsto_atTop.eventually_ge_atTop s).mono fun k p=> climbs (Dome (tent Y H)) p v).and ((eventually_ge_atTop _).mono fun k p=> ⟨p,le_rfl⟩)

namespace Exhibition
variable {a b:ℕ→ℕ} {I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ} {L:Rack Λ l}{B:Clay Λ l} (D:Exhibition Y H a b I E L B)
local notation "Ψ"=> vistaDressing Y H D
lemma enrollmentTheme (f:sequenceOf K): (D.vistaDressing Y H).finish n (rainyTail Λ K u f)=pennant K (restrictG Λ n u) ((D.vistaDressing Y H).finish n f):=by
  induction n with
  | zero=>rfl
  | succ n ih=>
    rw [Decking.finish,Decking.finish,ih,gaugeHarmony Λ n u]; change liftD Y H n D (pennant K (parentGauge Λ (restrictG Λ (n+1) u)) _) * pennant K (restrictG Λ (n+1) u) (f (n+1))=_; rw [pennantNatural,map_mul]; rfl
lemma vistaRain (x:Cloud (Dome K))(p:x∈shorter (Dome K) n): vistaFinish Y H n D (rainfall Λ K u x) = pennant K (restrictG Λ n u) (vistaFinish Y H n D x):=by
 apply boarded (P:={f|Altitude.Enough n f}) (M:=fun x=>_) ?_ ?_ ?_ ?_ p
 · intro f t; change vistaFinish Y H n D (rainfall Λ K u (pureShot K f)) = _; rw [rainfallPure]; unfold pureShot vistaFinish; rw [Decking.reckon_paid _ _ _ t,Decking.reckon_paid _ _ _ (rainyEnough Λ K n u t)]; exact D.enrollmentTheme Y H n u f
 · simp
 · intro a b t w q g; rw [map_add,map_add,map_add,map_add,q,g]
 intro c x h u; rw [map_smul,map_smul,map_smul,map_smul,u]

lemma finishCoherent (x:Cloud (Dome K)){v:Bool}{V:Set RSpace}{S:Set ℕ}(t:x∈ well Λ K l v V S)(p:x∈shorter (Dome K) n): vistaFinish Y H n D x∈enclave K:=by
 rw [colorFixed]; intro R; obtain ⟨u,e⟩:= iceExtension Λ n R; rw [←e,←D.vistaRain Y H n u x p,(well_spec ..).mp t|>.2 u]
lemma stateCoherent (x:Cloud (Dome K))(p:x∈ FiniteGaugeDataPoly K): vistaTake Y H D (rainfall Λ K u x)=vistaTake Y H D x:=by
  obtain ⟨n,p⟩:=curve.mp p; rw [vistaCall Y H n _ D (raining_height Λ K n u p),vistaCall Y H n _ D p,vistaRain _ _ n u D x p,planetGauge]
end Exhibition
end
end YM.CF.Buffered.Afterglow.Tapestry
#print axioms YM.CF.Buffered.Afterglow.Tapestry.paidPartners
#print axioms YM.CF.Buffered.Afterglow.Tapestry.paid_coherence
#print axioms YM.CF.Buffered.Afterglow.Tapestry.Exhibition.stateCoherent
#print axioms YM.CF.Buffered.Afterglow.Tapestry.Exhibition.finishCoherent
