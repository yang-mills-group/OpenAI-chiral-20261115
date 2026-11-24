import Ridgetop.Nosy
import Ridgetop.Traces
import YM.SU5.Circuit.Regale
import Risa.Cultural
import Compass.Prime
import YM.AnalyticBridge.VERIFIED_RESET_STEP.Channels
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.flexible false
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 305000
noncomputable section
namespace YM.Gleam.Luster
open Function Lattice MeasureTheory Finset RG Wilson Tree Filter Metric Exterior Precision Next.Rank.Spindle Pressure Work.F03 Next.SectorChange Next.SectorChange.Gaussian
open Fineness Matrix
open scoped Matrix BigOperators Classical ContDiff Topology MatrixOrder ENNReal Kronecker Matrix.Norms.Frobenius
variable {c n : Side}{r:Ratio c n}{T:Forest r}{G:Gauge}{p:BudgetPoint}{q:Clip}{v t η C S w δ β κ ξ Λ v' ν θ ω':ℝ}{U:Config G n}{A:Support c}{m:ℕ} {R:Rules G} {Z:PathData G}{b:Cell n}{H:Bed}{F:Finset T.Free}{J:ChartRatio G}
variable {X Y:fieldDir G n 1}{D:Finset (Cell n)}
variable (B:Z.Bounds q η C S) (P:Attached H Z)(L:Floor H q n δ w)(D':LocalRatio J)
namespace Risa
open Regis ProbabilityTheory
open _root_.YM.Regis.Head AnalyticBridge.VerifiedReset StressFlux Lattice.PlaqAxes Virgo _root_.YM.CF.Scree
namespace Ridgetop
open _root_.YM.Regis.Circuit _root_.YM.CF.Onyx _root_.YM.Stationary -- syntax
variable {ν:ℕ→Side}{M:ℕ→Bed}{R':ℕ→ℝ}{U W:ℕ→ Cover}{x:Gaia}
variable (I J':PlaqAxes)
private def skyhook (i:PlaqAxes)(a b:Bool):Cover:= (if a then -step i.val.1 else 0) + if b then -step i.val.2 else 0
private lemma cultural(z:Cover)(a b:Bool): pla (wrap n z) I a b=(wrap n (z+skyhook I a b),plaquette I):=by refine Prod.ext ?_ rfl; cases a<;>cases b<;>simp [pla,skyhook,atFace,digs,Lattice.Step.vec,← add_assoc]
lemma broadfaq(z₀ w₀:Cover)(X:ℝ): (X:ℂ)^4 * boreV H (wrap n z₀) (wrap n w₀) I J'= cosmos (fun a b=>cosmos (fun u v=>magnify H X (plaquette I) (plaquette J') ((z₀+skyhook I a b)-(w₀+skyhook J' u v)) n)):=by
 have h(a b u v:Bool): (X:ℂ)^4*rimble n H (pla (wrap n z₀) I a b) (pla (wrap n w₀) J' u v)=magnify H X (plaquette I) (plaquette J') (z₀+skyhook I a b-(w₀+skyhook J' u v)) n:=by
    let P:=z₀+skyhook I a b; let Q:=w₀+skyhook J' u v
    unfold magnify; apply congrArg _
    rw [cultural,cultural,rimflare n H (wrap n P) (wrap n Q) (P-Q) ((map_sub _ _ _).symm), rimflare n H (wrap n (P-Q)) 0 (P-Q) (sub_zero _)]
 unfold boreV; simp_rw [← h]
 unfold cosmos; simp only [Complex.real_smul]; ring
variable (Troll:Yard ν R') (roller:Tendsto (fun d=>riseX (R' d) (U d-W d)) atTop (𝓝 x))(e:x≠0)
include Troll roller
lemma rose_lift(a:Cover): Tendsto (fun d=>riseX (R' d) (U d-W d+a)) atTop (𝓝 x):=by
 -- add tends0. work clm _ supply via moor. 
 have he(d): riseX (R' d) (U d-W d+a)= riseX (R' d) (U d-W d) + (R' d)⁻¹ • riseX 1 a:=by
    ext i; change ((((U d-W d+a) i):ℤ):ℝ)/_=_/_+(R' d)⁻¹*((a i:ℝ)/1)
    simp only [Pi.add_apply,Int.cast_add,div_one]; ring
 simp_rw [he]; convert roller.add ((tendsto_inv_atTop_zero.comp Troll.high).smul_const (riseX 1 a)) using 1 <;> first | rfl| rw [zero_smul ℝ,add_zero]
include e
lemma shin (K:∀ d,(M d).covered θ C)(p':0<θ)(h:0<C)(V:∀ d,Floor (M d) q (ν d) δ C): Tendsto (fun d=> (R' d:ℂ)^4*boreV (M d) (wrap (ν d) (U d)) (wrap (ν d) (W d)) I J') atTop (𝓝 (specter I J' x)):=by
 simp_rw [broadfaq]
 have he(a b u v0: Bool): Tendsto (fun d=>magnify (M d) (R' d) (plaquette I) (plaquette J') (U d+skyhook I a b-(W d+skyhook J' u v0)) (ν d)) atTop (𝓝 (specter I J' x)):=by
    apply mercury I J' Troll _ e K V p' h
    simp_rw [show ∀ d, U d+skyhook I a b-(W d+skyhook J' u v0)=U d-W d+(skyhook I a b-skyhook J' u v0) from (fun d=> by abel)]
    exact rose_lift Troll roller _
 apply tend_com Troll roller -- use helper external
 exact fun a b=> by apply tend_com Troll roller; exact he a b
where
 tend_com(Troll:Yard ν R')(roller:Tendsto (fun d=>riseX (R' d) (U d-W d)) atTop (𝓝 x)){f:Bool→Bool→ℕ→ℂ}{p:ℂ}(h:∀a b,Tendsto (f a b) atTop (𝓝 p)): Tendsto (fun d=>cosmos (fun a b=>f a b d)) atTop (𝓝 p):=by
   unfold cosmos; convert ((((h false false).add (h false true)).add ((h true false).add (h true true))).const_smul ((4:ℝ)⁻¹)) using 1 -- `tendsto.const_smul` tune parenthesis
   simp only [Complex.real_smul]; push_cast; push_cast; congr 1; ring
#print axioms shin
end Ridgetop
end Risa
end YM.Gleam.Luster
