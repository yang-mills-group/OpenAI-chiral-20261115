import GaugeFieldConstruction.ErosMΛ
import GaugeFieldConstruction.PithBootUL
import GaugeFieldConstruction.BrigandL
/-!
 # All orders, all slots. Mink stress Ward IN ANALYTIC CONTOUR.
 Analytically reconstructed, reading *time ordered across inserted contour* stress flux, with ties by continuous Eu boundary after removing diagonals.

 Dν over relative-linear stuff for future notes. Distribution theorem in next part.
 Contour law precisely Mink generator sign: V spacetime translations (p up) φ(y) V^-1 = φ(y+p); D=(d/dy). Wickclock = −I. then
 ∂^coord_ν = ∫∑ TE_{aν} ∇_a b  γ_ν
            = −η_{νν} ∑ γ_a ∫T^{aν} ∂_a b,
 using sharp T^ contrav = Eu with clock-index i factors both. Thus top temporal flux weight (before insertion, lower Eu clocks, b increasing from zero): +I for ν=time (as i H in commutator orientation), and −I for space (Mink sign η_νν), not postulating charges in these formulas. Cost W words earlier Eu times left.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 15000
set_option maxHeartbeats 300000
noncomputable section
-- analytic global germs & basis recognition
namespace YM.NSF.Boundary
open YM.Boundary Mink Function Set Filter MeasureTheory Complex
open scoped Topology BigOperators ContDiff InnerProductSpace
open NSF.Work.C20
variable {n:ℕ}
lemma ΛShaftL : Convex ℝ inside:=by
 intro x hx y hy s t a b e
 simp only [inside,Set.mem_setOf_eq] at hx hy ⊢
 rw [clock_add,clock_mul,clock_mul,rest_add,rest_mul,rest_mul]
 calc _≤‖s • spatial x‖ + ‖t • spatial y‖:= norm_add_le ..
      _< _:= by rw [norm_smul,norm_smul,Real.norm_of_nonneg a,Real.norm_of_nonneg b]; by_cases h:0<s
                · exact add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left hx h) (mul_le_mul_of_nonneg_left hy.le b)
                exact add_lt_add_of_le_of_lt (mul_le_mul_of_nonneg_left hx.le a) (mul_lt_mul_of_pos_left hy (by linarith))
lemma ΛArcFieldL (n): Convex ℝ (fields n):=by
 unfold fields; refine convex_iInter fun i=> convex_iInter fun j=> convex_iInter fun p=>?_ 
 let K(i:Fin n): Points n→L[ℝ] E4:= PiLp.proj 2 (fun _:Fin n=>E4) i; let H:= (K j).toLinearMap-(K i).toLinearMap
 exact ΛShaftL.linear_preimage H
lemma ΛStockL (n): IsPreconnected (tube n):=by
 let A:Full n→ₗ[ℝ] Points n:={
    toFun:=shade
    map_add' x y:=by apply Points.flatten.injective; ext i; simp [shade];
    map_smul' a x:=by apply Points.flatten.injective; ext i; simp[shade]; }
 exact ((ΛArcFieldL n).linear_preimage A).isPreconnected
lemma ΛProfileL : rate n∈east n:=by simpa using dawns (light n) (show (0:ℝ)<1 from one_pos)
lemma ΛLaneL {X:Full n→ℂ}(hp:AnalyticOnNhd ℂ X (tube n))(p:∀ x∈ordered n,X (wickSlice n x)=0) : Set.EqOn X 0 (tube n):=by
 let x:=place 0 (rate n); have u : x ∈ ordered n :=by change readings x ∈ east n; rw [readings_place]; exact ΛProfileL
 have he:= (ordered_open n).mem_nhds u
 apply hp.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const (ΛStockL n) (wick_tube u)
 apply complex_germ (hp _ (wick_tube u)) analyticAt_const (wick_span n)
 intro m; exact ((show X ∘ wickSlice n =ᶠ[𝓝 x] ((0:Full n→ℂ) ∘ wickSlice n) from by filter_upwards [he] with y hy; exact p y hy).iteratedFDeriv ℝ m).eq_of_nhds
-- full real ν direction
open GaugeFieldConstruction.Stage.Cell
def realDirΛ (k:Fin n)(a:Axis):Full n:= glow (YM.NSF.Points.direction k a) 0
lemma wickDirΛL (k:Fin n)(a:Axis): Wickγ a • wickSlice n (YM.NSF.Points.direction k a) = realDirΛ k a:=by
 ext1 ⟨i,j⟩; unfold realDirΛ glow Wickγ; simp only [PiLp.smul_apply, smul_eq_mul,wick_apply]; by_cases p:j=a<;>by_cases h:a=timeAxis<;>by_cases s:i=k<;> simp_all [YM.NSF.Points.direction,PiLp.single_apply,basis_eq] -- tune
#print axioms ΛLaneL
end YM.NSF.Boundary
namespace YM.GaugeFieldConstruction.Ember.Volumetric
open Calibration Raw Cauchy Phys Apit Stage Fathom Function Set Filter Module Empire Hulse Salam Palace
open Floor Carat Dawn Sailing Angles Points Bulb Analysis MeasureTheory Complex Finset
open scoped Topology BigOperators Matrix.Norms.Frobenius ComplexConjugate ContDiff Kronecker InnerProductSpace
attribute [local instance] iG iF iX iU iT2 iW2 iV iS
variable {S:City}{P:Axis→Across}{L:Sheds S P}{C:Supplies L}{u:ℕ→Carat}
namespace FirstPackMars
open Loft Cell NSF.Boundary NSF.Work.C20
attribute [local instance] floatA floatY
attribute [local instance 30000] topx topg
variable (p:Ticket u C)
variable {A Z:CloudsL}(H:SurfCheckL A)(G:SurfCheckL Z)
variable {Y:NSF.Boundary.Surface (SurfRimL A)}{D:∀ i, Blanket i}{F:NSF.Boundary.Waves (SurfRimL A)}{N:Y.Aurora D}
variable (hz:F.Region (SurfRimL Z))(hv:N.FullBody F)
variable (e: PathUL (TotalStarsMars p) (fun n V x => Z n x V))
variable {n:ℕ}(V:Fin n→ΧiMars)
local notation "M_ν" => H.TinCanL
abbrev ΑΛL (V:Fin n→ΧiMars): Full n→ℂ:=fun x=> @Surface.Aurora.emit _ _ _ _ Y D N (M_ν ∘ V) x
variable (k:Fin n)(a:Axis){x:Points n}(uX:x∈NSF.Work.C20.ordered n)
abbrev TouchMΛ (w:Full n):ℂ:= fderiv ℂ (ΑΛL H (N:=N) V) w (realDirΛ k a)
include hv
lemma ΑSenseΛL : AnalyticOnNhd ℂ (ΑΛL H (N:=N) V) (tube n):= hv.hol n _
lemma ΥFeelΛL : AnalyticOnNhd ℂ (TouchMΛ H (N:=N) V k a) (tube n):= by
 let R:=realDirΛ k a; intro z q; exact ((ContinuousLinearMap.apply ℂ ℂ R).analyticAt _).comp ((ΑSenseΛL H hv V z q).fderiv)
include G uX hz
lemma ΥLiveΛL : ΑΛL H (N:=N) V (wickSlice n x)= Z n x V :=by
 let L:Fin n→LoftRimL.Token:= fun i=>⟨0,BookRimL 0 (V i)⟩
 have hp:= emit_table G.PlannerL.toSymmetric (show (SurfRimL Z).respects (SurfRimL A) from fun i=> le_of_eq ((H.FlagsL i).trans (G.FlagsL i).symm)) hz hv L uX
 rw [surfReadL,show elementalL ∘ L=V from funext fun i=>BookRichL ..] at hp
 unfold ΑΛL; rw [show M_ν ∘ V=fun i=> (SurfRimL A).pin (L i).1 ((SurfRimL A).project (L i).1 (L i).2) from ?_]; · exact hp
 ext1 i; rw [← H.tinRiseL,H.HingeRiseL]; exact congrArg H.TinCanL (BookRichL 0 _).symm
 -- better explicit substitution
lemma PhasePressΛL : TouchMΛ H (N:=N) V k a (wickSlice n x)= Wickγ a * Analysis.D (mirDirYL k a) (fun x=> Z n x V) x:=by
 have ht: ΑΛL H (N:=N) V ∘ wickSlice n =ᶠ[𝓝 x] fun x => Z n x V:=by filter_upwards [(ordered_open n).mem_nhds uX] with y hy; exact ΥLiveΛL H G hz hv V hy
 let E:=ΑΛL H (N:=N) V; let w:= wickSlice n x; let J:= fderiv ℂ E w
 have hp: fderiv ℝ (fun x=> Z n x V) x= J.restrictScalars ℝ ∘L wickSlice n:= (((((ΑSenseΛL H hv V w (wick_tube uX)).differentiableAt.hasFDerivAt).restrictScalars ℝ).comp x (wickSlice n).hasFDerivAt).congr_of_eventuallyEq ht.symm).fderiv
 rw [TouchMΛ,← wickDirΛL,map_smul]; unfold Analysis.D; rw [hp]; rfl
omit G uX hz hv in
lemma ΜConfΛL : NSF.Work.C20.ordered n⊆conf n := by intro i hi; convert clear (show readings i∈east n from hi) (NSF.Boundary.trace i); rw [place_same]
lemma ΜRescaleΛL (r:ℂ)(W:ΧiMars): TouchMΛ H (N:=N) (Function.update V k (r • W)) k a (wickSlice n x) = r * TouchMΛ H (N:=N) (Function.update V k W) k a (wickSlice n x):=by
 rw [PhasePressΛL H G hz hv _ _ _ uX, PhasePressΛL H G hz hv _ _ _ uX, mul_left_comm]
 congr 1
 let U(x):= Z n x (Function.update V k W); have hz(x) :Z n x (Function.update V k (r • W))= r * U x := (Z n x).map_update_smul V k r W
 simp_rw [hz]; have d:DifferentiableAt ℝ U x:= ((G.sm _).contDiffAt ((conf_open _).mem_nhds (ΜConfΛL uX))).differentiableAt (by simp)
 unfold Analysis.D; rw [fderiv_const_mul d]; rfl -- tune
-- Conservation & translation identity (any k and contour)
local notation "Τh" => TouchMΛ H (N:=N)
include G e
omit uX
lemma CosmicConServeΛL {w:Full n}(z:w∈tube n): (∑ i:Axis, Τh (Function.update V k (SkylineΜΛ p i a)) k i w)=0:=by
 let Φ(w:Full n):=∑ i:Axis,Τh (Function.update V k (SkylineΜΛ p i a)) k i w
 have he(x:Points n)(u:x∈NSF.Work.C20.ordered n): Φ (wickSlice n x)=0:=by
    unfold Φ; simp_rw [SkylineΜΛ, ΜRescaleΛL H G hz hv V _ _ u, PhasePressΛL H G hz hv _ _ _ u]
    let E(i:Axis):=Analysis.D (mirDirYL k i) (fun x=> Z n x (Function.update V k (TotalStarsMars p i a))) x
    have h(i:Axis): ((Wickγ i)⁻¹*(Wickγ a)⁻¹)*(Wickγ i*E i)=(Wickγ a)⁻¹*E i:=by field_simp [wickLiveL]
    change (∑ i:Axis, ((Wickγ i)⁻¹*(Wickγ a)⁻¹)*(Wickγ i*E i))=0; simp_rw [h]; rw [← mul_sum]; have ht:(∑ i:Axis,E i)=0:= (SolidUL _ x k _ _ _ (fun n V=> (G.sm V).continuousOn) e).resolve_right (fun h=> h (ΜConfΛL u))
    rw [ht,mul_zero]
 exact ΛLaneL (show AnalyticOnNhd ℂ Φ (tube n) from fun w p'=> by apply Finset.analyticAt_fun_sum; intro i _; exact ΥFeelΛL H hv _ _ _ w p') he z

include uX
-- all contours (μν stress). Write Γ in real E test notation. Interpretation in comment above DOES mean actual N interior and its RE-ORDERED slope costs, not optional Eu estimator. Further precise tie limit next.
lemma ΛGenerateL (b:Fathom.Bulb)(hb:BreatherMars b k x): Τh V k a (wickSlice n x)=∑ i:Axis, (-(MinkΛM a:ℂ)*Wickγ i) * (∫ y:E4,(Analysis.D (basis i) b.f y) • Z _ (YM.Points.cons y x) (Fin.cons (SkylineΜΛ p i a) V)):=by
 rw[PhasePressΛL H G hz hv _ _ _ uX, BindMUL a x b k (TotalStarsMars p) _ V (fun n V=>(G.sm V).continuousOn) e hb,Finset.mul_sum] -- tune
 apply sum_congr rfl; intro i _
 let r:=(Wickγ i)⁻¹*(Wickγ a)⁻¹; let f(z:E4):ℂ:= Analysis.D (basis i) b.f z • Z _ (YM.Points.cons z x) (Fin.cons (TotalStarsMars p i a) V)
 rw [show (fun z:E4=>Analysis.D _ b.f z • Z _ (YM.Points.cons z x) (Fin.cons (SkylineΜΛ p i a) V))=(fun z:E4=> r * f z) from ?_, integral_const_mul]
 · change Wickγ a* (∫ z,f z)= _; rw [← mul_assoc _ r,← ΦMinkΛ]; unfold r; field_simp [wickLiveL]
 ext1 z; let y:= Z (n+1) (YM.Points.cons z x); let A:=TotalStarsMars p i a
 have h(v:ΧiMars):Fin.cons (α:=fun _=>ΧiMars) v V= Function.update (Fin.cons A V) 0 v:= (Fin.update_cons_zero ..).symm
 have ht:y (Fin.cons (r • A) V)= r • y (Fin.cons A V):= by conv_lhs=> rw [h,(y.map_update_smul _ _ r A)]; rw[← h A]
 change _ • y _= r*(Analysis.D _ _ _ • y _); rw[show y (Fin.cons (SkylineΜΛ p i a) V)=r • _ from ht]; exact smul_comm ..
#print axioms ΛGenerateL
#print axioms CosmicConServeΛL
end FirstPackMars
end YM.GaugeFieldConstruction.Ember.Volumetric
