import YM.SU5.May.FloeRanks
import YM.SU5.One.Coda
import YM.SU5.May.FloeCore
import YM.SU5.May.FloeCourse
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 32000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.Screened.FloeRoom
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open SlabMark MeshClock Tilted WindRose
open Fock Lat Laurent Wilson Cube Finset Branch Scree RG Spire Vale Pastry Peaks Dial Phase Lifted Skye Tapestry.Exhibition Tapestry.Altitude Tenant Rush Tulip
open PolarArchives Brazier
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
variable {Λ:Preparation}{l:ℕ} (Y:Course Λ (VolumeCape.Dream.Nimbus l)) (H:Real.exp 1 ≤ Λ.x)
variable {i k : ℕ→ℕ} {I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ} (V:Universal Y H i k I E)
  (G : GroundExtension (i:=i) (k:=k) (E:=E) Y H)
local notation "v₁" n:max => i (G.rows n)
local notation "v₂" n:max => k (G.columns n)
local notation "T" n:max => Therapies.paceFloor Y H G n
open LocalLimit.Intermediate Harbour
open Hygrometry Hygrometry.MeterFunding
open May.Floe
open Push.SectorMeasure
open Advance.Depths
variable (κ:ℕ){U : Finset Cover}
local notation "𝗠" i:max j:max=> Journey.side Y i j
variable (m t s R:ℕ) (P:Ramp)
variable (F:Intermediate.Room R→ Corr (Λ.Ctor (Y.ir m) R))(z: Intermediate.Room R)
lemma cliff_topper (k:s<R)(u:R≤ Y.uv t)(e:campus Y m t R F)(a:phaseMoney Y m t R F z)(f:Mark (Journey.side Y m s))(p: Envelope f):
  ContinuousAt (assembleNext Y m t s R F z f) (1,1):=by
 let A:=patternA Y s m t; have ht:A.patch.Branches A.kernel SU.group:= (installed Y u e a).branch s k
 obtain ⟨_,h⟩:=(YM.OneRegulator.quiet_branch _ _ ht (t:=fun x:ℕ=>0) tendsto_const_nhds).exists; let w:= (installed Y u e a)
 have hZ:= (h _ _ A rfl rfl 1 (fun i=> by rw [WilsonStartup.face_one,Gauge.chord_one]))
 apply Tower.One.ascend_continuous_here (Vale.apt (Y.ir m) Λ.block Λ.R.L s) _ _ _ _ (Journey.legal Λ) _ _ (threshold Y).1 (threshold Y).2 _ _ A ((Y.voyage m).ownership s).paid.bill ht p
 intro y; exact YM.OneRegulator.density_here A ht _ 1 y hZ.1 hZ.2
open Therapies
lemma drawStill {a:ℕ} (p:0<a)(u:s+a ≤ R) (v:R≤ Y.uv t)(e:campus Y m t R F)(h: phaseMoney Y m t R F z)(f:Mark (Journey.side Y m s)){V':Finset Cover}
    (g : AtSupport false (Satin.region U (Journey.side Y m s)) f) (c:AtSupport false (Satin.region V' (Journey.side Y m s)) (P.bill f)) : ContinuousAt (climb Y m t s R F z f a) (1,1):=by
 cases a with
 | zero=> omega
 | succ a=> exact cliff_topper Y m t (s+a) R F z (by omega) v e h _ ((ascent Y m t s R F z P v e h g c a (by omega)).1.env)
noncomputable def dotCurrency (f:Mark (Journey.side Y m s)):ℂ:= SpinPrice (relV Λ.U (freshBook Y m t s) (1:Pane (Journey.side Y m s))) (f (1,1))
-- Applies ALSO to the particular z, across arbitrary β. `PoseField` factor `(P.bill...)` matched.
lemma one_bill (f:Mark (Journey.side Y m s))(β:ℝ) (V:Ids (Journey.side Y m s)): Directly Y m t s β (1,V) f= dotCurrency Y m t s f:= top_bill (y':=(1,V)) Y m t s (Hygrometry.flat_flag (Y.meter.a s)) β f
/-- CARE: not presuming any radius, spend only when issued `Kea.Pad`. Geometry support ALL helpers. -/
lemma dotSufficient (f:Mark (Journey.side Y m s))(h:covariant f) (t':ContinuousAt f (1,1))(u:Kea.Pad Λ.K.j (Journey.side Y m s))(δ:ℝ)(p:0<δ): Sufficient Y m t s δ f (dotCurrency Y m t s f):=by
 let Z:=freshBook Y m t s; have F:Hom.InterestX _ (Journey.side Y m s) Z:= (projectA Y m t).last.sound s
 obtain ⟨X,v₀,hq⟩:= pier_eligible Λ.U Λ.W.pearl Λ.V.note (cardV Y m s) Λ.dpos (solvable (Λ:=Λ)) _ (Papal.roofage Y m s) (Y.meter.a s) (Λ.V.L.path (Y.uv t-s)) Λ.K.top.clip (tariffP Y m t s) Z f F u (dotCurrency Y m t s f) δ (by unfold dotCurrency; rw [freeze_anchor]; exact (by simp [p, Z])) (t'.comp (f:=fun U:Pane (Journey.side Y m s)=>(U,U)) (continuousAt_id.prodMk continuousAt_id)) h
 exact ⟨X,v₀.1,hq,v₀.2⟩
local notation "vβ" f:max g:max j:max z:max=> temper (projectA Y f g) j Λ.δ j z
local notation "Π" => blankMenu Y m s
lemma blanked (z:Intermediate.Room s) (x:0<s)(u:s≤Y.uv t)(h:phaseMoney Y m t s (blankMenu Y m s) z) : Integrable (tap Y m t s (vβ m t s z)) (city _) := by
 apply Env.integrableX; suffices t:Envelope (denZ (Harbour.screen Y m t s Π z s) Λ.U ((Y.voyage m).CapeT s)) by rw [launchGram_eq] at t; exact t
 -- senior grant at previous stage.
 cases s with
 | zero=> omega
 | succ s=> obtain ⟨X⟩:= (installed Y u (sprung Y m t (s+1)) h).grant s (Nat.lt_succ_self _); exact Girt.enter_p X
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.Screened.FloeRoom
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.Screened.FloeRoom.drawStill
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.Screened.FloeRoom.blanked
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.Screened.FloeRoom.dotSufficient
