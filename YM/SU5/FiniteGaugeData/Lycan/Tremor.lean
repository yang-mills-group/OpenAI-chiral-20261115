import YM.SU5.FiniteGaugeData.Lycan.Lit
/-! # sign measurement at actual worlds. End WP24 -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 410000
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.LyraBill
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Window.Brique
open Reed (Fine)
attribute [local instance] opCStarAlgebra
set_option quotPrecheck false
open Heat Quest Fock.Brique
open Nacre Heat Charm Chrono Journey
open Py Py.Rate LocalLimit Preparation Journey Fiber Vale VolumeCape FullBill
open SalonG
open Quest.Chaperone
open Steam
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l)) {g:ℝ}{u v:ℕ→ℕ}
open Eight YM.SU5.FiniteGaugeData.CodaT YM.SU5.FiniteGaugeData.Cuprite.Spirit YM.SU5.FiniteGaugeData.Cuprite.Spirit.Vapors Fock.Relief Rhythm.Hush Rhythm.CodaT Dial Aria Reduction.Drama.Pack
open Rhythm.Dolores Rhythm.Ergo Hills Gamer Fock.Reduction Turnist Alts Alts.Emblem Window.Presidio.Nigra
namespace Chiffon
open Moorend Rhythm.CodaT
open Reduction.Loyd Reduction.Dijon Reduction.Loyd.Art Reduction.Celeste
namespace Sesame
open Reduction Lycan Niagara Chisel Largo Mirage Cascade Ember PolarF Onyx
open Stationary Mir Royal
namespace Venice
-- all choices. all axes arcs.
variable (h:Real.exp 1≤Λ.x){I:ℕ→Family (tent Y h)→ℕ→ℂ}{E:ℕ→ Family (tent Y h)→ℂ}(K:Universal Y h u v I E)
variable {P:Call Λ l}{J:Wicket Λ l}(R:Rolled Y h u v J P)(A:∀ a:Axis,Repertory Y h K R a)
variable (S':RadioCity.Hypothesis Λ l g Y)(P':Titan Λ){ε:ℝ}(σ:Window.Family)(a b c:ℤ)
local notation "Kₜ"=> tent Y h
local notation "ΛF"=> ℕ→W Kₜ→ₗ[ℂ]ℂ
abbrev deskV(n:ℕ)(t:ℤ):Cover:=(n+1) • (t • step 3)
abbrev VClock(t:ℤ):Gaia:= Window.corner t
lemma Spot : Run fuao deskV VClock := by
 refine ⟨fun i=>by unfold fuao; positivity,tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop,fun v=>?_ ,fun a b p=>?_⟩
 · apply tendsto_const_nhds.congr'; filter_upwards with i; apply PiLp.ext; intro j; have h:0<(i:ℝ)+1:=by positivity
   change (VClock v) j=(riseX (fuao i) (deskV i v)) j; by_cases x:j=3<;> simp [x,VClock,riseX,moor,Window.corner,fuao,deskV]; field_simp
 have hp:=congrArg (fun x:Gaia=> x 3) p; simp [VClock,Window.corner] at hp; exact Eventually.of_forall fun i=> congrArg _ hp
abbrev σTap(n:ℕ)(a:ℤ)(x:Axis): W Kₜ:= γLift σ (deskV n a) x (Royal.fuao n) Kₜ
local notation "T"=> signedCost σ a b c
abbrev Tapage(n:ℕ):= σTap Y h σ n a 0*σTap Y h σ n b 1*σTap Y h σ n c 2
abbrev budJ(n:ℕ):Finset Cover:= {(nodeC (deskV n a)),nodeC (deskV n b),nodeC (deskV n c)}
lemma Loc(n:ℕ):Locator Kₜ (Tapage Y h σ a b c n) (budJ a b c n):= locate_join _ _ (locate_join _ _ (locate_sub _ (loco_s ..) (by simp [budJ])) (locate_sub _ (loco_s ..) (by simp [budJ]))) (locate_sub _ (loco_s ..) (by simp [budJ]))
include S' P'
/-- BP-observables have DESTINED SIXM receipt. Fixed families, every Sphere and so EACH selected and unselected. -/
lemma likeV : Sim Y h K R A (fun Φ i s=> Φ s (Tapage Y h σ a b c i)) (- (signedCost σ a b c:ℂ)) := by
 rw [←Window.left_price]; exact Fortune₃ Y Spot σ h K R A S' P' a b c _ _ _
lemma nectarE(t:a<b)(v:b<c): ∀ᶠ i:ℕ in atTop,∀ᶠ s:ℕ in atTop,∀ (Φ:ΛF),Sphere Y h K R A Φ→ let W:= Φ s (Tapage Y h σ a b c i); W.re <0 ∧ W≠ Window.dexPrice (VClock a) (VClock b) (VClock c) (dimf σ:ℂ) 0 1 2 :=by
 have he:0<T:= cost_pos _ (Int.cast_lt.mpr t) (Int.cast_lt.mpr v); let P:= likeV Y h K R A S' P' σ a b c (T/2) (half_pos he); filter_upwards [P] with i p; filter_upwards [p] with s q Φ H W; have hv:= (abs_le.mp ((Complex.abs_re_le_norm _).trans (q Φ H))).2; change (W- -(T:ℂ)).re≤_ at hv; rw [Complex.sub_re,Complex.neg_re,Complex.ofReal_re] at hv; have ha:W.re <0:=by linarith
 exact ⟨ha,fun k=>ha.not_ge (by rw [k]; unfold VClock; rw [dexPrice_sign]; exact he.le)⟩ -- k use nn cast
#print axioms Loc
#print axioms likeV
#print axioms nectarE
end Venice
end Sesame
end Chiffon
end YM.CF.Buffered.Afterglow.Hierarchy.LyraBill
