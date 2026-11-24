import YM.SU5.Reconstruction.Brazier.Purchase
import YM.SU5.Reconstruction.Brazier.Rising
/-! Actual single-field theory reading χ now on the punctured finite sharp FT tape; even Ward charges bought here with its Borel witnesses. All observation queries per bill vs the SAME normalized thermal policy. -/
set_option autoImplicit false
set_option synthInstance.maxSize 31000
set_option maxRecDepth 6200
set_option maxHeartbeats 400000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.Brazier
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry Altitude Exhibition Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation SlabMark MeshClock
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
variable {L : Rack Λ l} {B : Clay Λ l} (Z : Exhibition Y H i k I E L B)
variable (j : Axis) (C : Arena Y H G.history.circuit j 0 false)
  (χ : displayAlgebra Y H V G.history G.clipped j false C →⋆ₐ[ℂ] ℂ)
local notation "Gt" => marks (timeMesh Λ)
local notation "t₀" => insideAt Λ l (tent Y H)
local notation "D" => Domain Y H G
local notation "A"=> Ark.Ht Y H G.history.circuit j 0 false C
local notation "Π"=>Aurora Y H V G.history j false C
local notation "Kx" t:max=> vistaFinish Y H t Z
local notation "Px" => LightBudget.prepaid Y H V G j C
namespace Labor
open Fervor Tarmac SingleFrame Hearth Fortune
open Fock Lat Laurent Wilson Cube Finset Branch Scree RG Spire Vale Pastry Peaks Dial Phase
 Lifted Skye Tapestry.Exhibition Tapestry.Altitude Tenant Rush Tulip
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
variable {r:Hearth Y H G j} {m u:ℕ}
variable (T:Finset Tarmac)(g e:ℝ)
local notation "W₀"=> Y.uv u
local notation "X₀"=> Altitude.Cloud (Dome (tent Y H))
local notation "φ"=> Hearth.spanMark Y H G j r
local notation "up"=> Hearth.upper Y H G j r
local notation "low"=> Hearth.lower Y H G j r
noncomputable def Pole (m u:ℕ)(x:Altitude.Cloud (Dome (tent Y H))) : Pane (Journey.side Y m (Y.uv u)) → FC (Single (Journey.side Y m (Y.uv u))) := collapse (Tag Y H m u x)
lemma Pole_local (x:Altitude.Cloud (Dome (tent Y H))) (S:Finset Cover)(p:AtSupport false (Satin.region S _) (faceOf Y H m u (Y.uv u) x)) : AtSupport false (Satin.region S _) (toMark (Pole Y H m u x)) := narrow p
noncomputable def conduit (m u:ℕ)(r:Hearth Y H G j) : Pane (Journey.side Y m (Y.uv u)) → FC (Single (Journey.side Y m (Y.uv u))) := Pole Y H m u (Hearth.upper Y H G j r)*Pole Y H m u (Hearth.lower Y H G j r)
local notation "μ"=> Pole Y H m u
local notation "Q₁"=>conduit Y H G j m u r
local notation "μp"=>capAccount Y m u
local notation "Tk"=> taking Y H m u
noncomputable def calculate (m u:ℕ)(r:Hearth Y H G j)(x:Altitude.Cloud (Dome (tent Y H))) : ℂ := capAccount Y m u (Pole Y H m u x*conduit Y H G j m u r)/capAccount Y m u (conduit Y H G j m u r)
variable {T g e} (p:Routing Y H V G Z j C χ T g e m u r)
local notation "Φ"=>frameCharge Y m u
include p
lemma traverses {w:ℕ} (v:r.roof+w ≤ Y.uv u): WatchCost Y H G j r m u w ∧ ∀ a∈ T,∀ x:Altitude.Cloud (Dome (tent Y H)), ∀ b:ℝ, Pocket (tent Y H) a.book a.roof b x→ InsideCost Y H G j r a x m u w:=
 ⟨r.boots Y H G j m u p.actual ⟨p.finance.1,v⟩, fun a h x b t=> InsideCost_m a h t⟩ -- embed
where
 InsideCost_m (a:Tarmac) (h:a∈T){x:Altitude.Cloud (Dome (tent Y H))}{b:ℝ}(t:Pocket (tent Y H) a.book a.roof b x): InsideCost Y H G j r a x m u w := insideNow Y H G j r m u a (p.clearance a h).1 (p.clearance a h).2 ⟨p.finance.1,v⟩ t -- order
lemma pole_gate : Pole Y H m u (r.spanMark Y H G j)=conduit Y H G j m u r:=by
 obtain ⟨N,hN⟩:= Nat.exists_eq_add_of_le p.finance.2
 have hv : faceOf Y H m u (Y.uv u) (r.spanMark Y H G j)= faceOf Y H m u (Y.uv u) (r.upper Y H G j) * faceOf Y H m u (Y.uv u) (r.lower Y H G j):=hN.symm ▸ ((traverses Y H V G Z j C χ p (v:= hN.ge)).1.owns : faceOf Y H m u (r.roof+N) φ= faceOf Y H m u (r.roof+N) up * faceOf Y H m u (r.roof+N) low)
 exact funext fun v=>congrFun hv (v,v)
lemma processMark {a:Tarmac}(h:a∈T)(x:Altitude.Cloud (Dome (tent Y H))) {b:ℝ}(q:Pocket (tent Y H) a.book a.roof b x): Pole Y H m u (x*r.spanMark Y H G j)= Pole Y H m u x * conduit Y H G j m u r:=by
 obtain ⟨N,hN⟩:= Nat.exists_eq_add_of_le p.finance.2
 have hv : faceOf Y H m u (Y.uv u) (x*r.spanMark Y H G j)= faceOf Y H m u (Y.uv u) x * faceOf Y H m u (Y.uv u) φ:=hN.symm ▸ ((traverses Y H V G Z j C χ p hN.ge).2 a h x b q).insertion
 rw [← pole_gate Y H V G Z j C χ p]; exact funext fun v=>congrFun hv (v,v)
structure Trusted (m u:ℕ)(r:Hearth Y H G j) : Prop where
 bills: Integrable (frameCharge Y m u (conduit Y H G j m u r)) (priorY Λ Y m u)
 measure: capAccount Y m u (conduit Y H G j m u r)≠0
 allotment: topBond Y m u=capAccount Y m u 1
 partNonzero: topBond Y m u≠0 -- change name
 predicted : capAccount Y m u (conduit Y H G j m u r)/capAccount Y m u 1=taking Y H m u (r.spanMark Y H G j)
 orientationU : Buffered.covariant (toMark (Pole Y H m u (r.upper Y H G j)))
 orientationL : Buffered.covariant (toMark (Pole Y H m u (r.lower Y H G j)))
lemma entrusts : Trusted Y H G j m u r:=by -- argument order implicit? `{r}` used implicit.G
 obtain ⟨N,hN⟩:= Nat.exists_eq_add_of_le p.finance.2
 have hx : Tapestry.Pay Y (Y.uv u) m u:=⟨p.finance.1,le_rfl⟩
 obtain ⟨x,h,z⟩:= bond_budget Y H m u φ (climbs _ p.finance.2 (r.spanFunded Y H G j)) hx
 change Integrable (Φ (μ φ)) _ at x; change Tk φ=μp (μ φ)/_ at z
 rw [pole_gate Y H V G Z j C χ p] at x z; have hv:= SingleFrame.uncondition Y H m u hx; have hg: capAccount Y m u (conduit Y H G j m u r)≠0:=fun t=> p.solvent (z.trans (by rw [t,zero_div]))
 have hy:= (traverses Y H V G Z j C χ p hN.ge).1
 exact ⟨x,hg,hv.symm,h,(by rw [hv,z]),preserve_gauge (hN.symm ▸ hy.rightGauge : Buffered.covariant (faceOf Y H m u (Y.uv u) up)),preserve_gauge (hN.symm ▸ hy.leftGauge : Buffered.covariant (faceOf Y H m u (Y.uv u) low))⟩
structure Spending (r:Hearth Y H G j)(m u:ℕ)(x:Altitude.Cloud (Dome (tent Y H))) : Prop where
    payment : Integrable (frameCharge Y m u (Pole Y H m u x*conduit Y H G j m u r)) (priorY Λ Y m u)
    pairing : Pole Y H m u (x*r.spanMark Y H G j) = Pole Y H m u x * conduit Y H G j m u r
    pressure : calculate Y H G j m u r x=scored Y H G j m u r x
    visa (U:Set RSpace)(h:x∈ questions Λ l K true U): Buffered.covariant (toMark (Pole Y H m u x))
lemma fire {x:Altitude.Cloud (Dome (tent Y H))} {a:Tarmac}(t:a∈T){b:ℝ}(q:Pocket (tent Y H) a.book a.roof b x): Spending Y H G j r m u x:=by
 have hp:= p.clearance a t
 have he:(x*φ)∈shorter (Dome K) r.roof:=mul_mem (climbs _ hp.1.later.le q.funded) (r.spanFunded Y H G j)
 obtain ⟨d,h,v⟩:= bond_budget Y H m u (x*φ) (climbs _ p.finance.2 he) ⟨p.finance.1,le_rfl⟩
 change Integrable (Φ (μ (x*φ))) _ at d; change Tk (x*φ)=μp (μ (x*φ))/_ at v
 have hu:=processMark Y H V G Z j C χ p t x q; have hy:= entrusts Y H V G Z j C χ p
 rw [hu] at d v; refine ⟨d,hu,?_,fun U h=>?_⟩
 · rw [interpreting, v,← hy.predicted,← hy.allotment, div_div_div_cancel_right₀ h]; rfl -- tune formula name
 obtain ⟨N,hN⟩:= Nat.exists_eq_add_of_le p.finance.2
 exact preserve_gauge (hN.symm ▸ (((traverses Y H V G Z j C χ p hN.ge).2 a t x b q).gaugeCost U h) : Buffered.covariant (faceOf Y H m u (Y.uv u) x))
end Labor
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.Brazier
