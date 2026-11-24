import YM.CF.BProof.Solar.Sign
import YM.CF.BProof.Solar.Local
import YM.CF.BProof.Fog.Fro
set_option autoImplicit false
noncomputable section
set_option synthInstance.maxSize 28000
namespace YM.CF.BProof.Bide
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Scroll Thera Branch Laic Cube
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Urn Hake Levier Spire Scree Stilo Hive
attribute [local instance] opCStarAlgebra
open MeasureTheory Skye
local instance mCast (I : Type) [Fintype I] [DecidableEq I] : MeasurableSpace (Op I) := borel _
local instance bCast (I : Type) [Fintype I] [DecidableEq I] : BorelSpace (Op I) := ⟨rfl⟩
variable {N:Side} (s t:Sweep N)
namespace Chalk
open RG Law Window.Unfit
open scoped ComplexOrder
abbrev mirror (i: Axis):=Fixed.reflectTest (N:=N) i false
variable {R:Support (More N)}{F G:Obs N}{K C:ℝ} (i:Axis)
abbrev un (F: Obs N):= mirror i F * F
lemma move_m (u:Envelope F) : Envelope (mirror i F):= Girt.pole_w (X:=FC (Single N)) (F ∘ Fixed.reflConfig N i) (fun p=> Reed.reverseW (Fixed.reflectP N i) false p) (by unfold Reed.reverseW; exact (continuous_const (y:=Reflect.chord false)).smul (Fock.theta_cont (Fixed.reflectP N i))) (Law.pull (q:=Fixed.reflConfig N i) u ((Fixed.reflConfig_cont ..).measurable)) -- not defeq
lemma shineE (u:Envelope F): Envelope (un i F):= Girt.kitE (mirror i F) F (·*·) (continuous_fst.mul continuous_snd) (move_m i u) u
lemma mirror₀ (F:Obs N)(q:Pane N): mirror i F q =theta (Fixed.reflectP N i) (F (Fixed.reflConfig N i q)):= one_smul ..
lemma dMirror (F G:Obs N)(q:Pane N): ‖mirror i F q-mirror i G q‖= ‖F (Fixed.reflConfig N i q)-G (Fixed.reflConfig N i q)‖ :=by
 rw [mirror₀,mirror₀]; let U:=Fixed.reflectP N i; let f:= lotB false true U; change ‖f _-f _‖ =_; rw [←map_sub]; exact pay_s true _ _
lemma pay_m (p:Paid F C) : Paid (mirror i F) C:= by intro x; rw [mirror₀]; exact le_trans (pay_s true (Fixed.reflectP N i) (F (Fixed.reflConfig N i x))).le (p _)
lemma diffU (u:Paid F C)(v:Paid G C)(x: Pane N): ‖un i F x-un i G x‖ ≤ C*(‖F x-G x‖+ ‖F (Fixed.reflConfig N i x)-G (Fixed.reflConfig N i x)‖):=by
 let U:=mirror (N:=N) i; let y:=Fixed.reflConfig N i x; rw [←dMirror i F G,mul_add]; change ‖U F x*_ -U G x*_‖ ≤ _; calc
   _ = ‖U F x*(F x-G x) + (U F x-U G x)*G x‖:=by rw [mul_sub,sub_mul]; congr 1; abel
   _ ≤ _ := (norm_add_le ..).trans (add_le_add ((norm_mul_le ..).trans (mul_le_mul_of_nonneg_right (pay_m i u x) (norm_nonneg _))) ((norm_mul_le ..).trans (by rw [mul_comm C]; exact mul_le_mul_of_nonneg_left (v _) (norm_nonneg _)))) -- tune
variable {X:Orbit N→Phys N}
abbrev y_p (X:Orbit N→ Phys N)(F:Obs N)(x:Orbit N):=Window.Unfit.taste X (fun i=>F i.1) x
abbrev normcost (F G: Obs N)(x:Pane N):= ‖F x-G x‖
lemma yE (p:Envelope X)(h:Envelope F):Envelope (y_p X F):= Window.Unfit.env_taste _ _ (Window.Unfit.lower F h) p
lemma fee' (h:Envelope F)(k:Envelope G):Envelope (normcost F G):= Girt.kitE F G (fun f g=> ‖f-g‖) ((continuous_fst.sub continuous_snd).norm) h k
local notation "τμ" => city N
local notation "Ytw"=> prior SU.group (More N)
set_option maxHeartbeats 650000 in
lemma price (p:Envelope X)(u:0<K)(pk:∀ x, ‖X x‖ ≤ K)(hx:0≤ C)(a:Envelope F)(b:Envelope G)(c:Paid F C)(d:Paid G C) : ‖Fixed.functional X (un i F)- Fixed.functional X (un i G)‖ ≤ (2*C*K)*(∫ x:Pane N,normcost F G x ∂prior SU.group (More N)) := by
 let f:=y_p X (un i F); let g:=y_p X (un i G); let D(u:Orbit N):=normcost F G u.1; let whR := Fixed.reflectOrbit (N:=N) i; let E:=D ∘ whR; have h:= fee' a b
 have hy(z:Orbit N): ‖f z-g z‖ ≤ (D z+ E z)*(C*K):=by
   let H:= X z; let U:= un i F z.1; let W:=un i G z.1; change ‖inner ℂ _ (acts U H)- inner ℂ _ (acts W H)‖ ≤ _ ; rw [←inner_sub_right]; rw [←act_sub]; apply (norm_inner_le_norm ..).trans; rw [(Dial.tickB N).2,one_mul]; refine (Graph.spentS ..).trans ((mul_le_mul (diffU i c d _) (pk _) (norm_nonneg _) (mul_nonneg hx (by positivity))).trans_eq ?_); unfold D E normcost whR; dsimp only [Function.comp_apply,Fixed.reflectOrbit]; rw [Fixed.flash_reflect]; ring
 have hdD: Measurable D:= h.meas.comp measurable_fst; have hfD: Integrable D τμ:= Law.pay (Girt.snap (X:=fun x:Orbit N=>x.1) h measurable_fst)
 have he: MeasurePreserving whR τμ τμ:= Fixed.preserve_reflectOrbit i
 let W:=∫ u,D u ∂ τμ
 change ‖(∫ i,f i ∂ τμ) - (∫ i,g i ∂ τμ)‖ ≤ _; rw [←integral_sub (Law.pay (yE p (shineE i a))) (Law.pay (yE p (shineE i b)))]; refine (norm_integral_le_integral_norm ..).trans ((integral_mono ((Law.pay (yE p (shineE i a))).sub (Law.pay (yE p (shineE i b)))).norm ((hfD.add (he.integrable_comp_of_integrable hfD)).mul_const (C*K)) hy).trans_eq ?_); rw [integral_mul_const,integral_add' hfD (he.integrable_comp_of_integrable hfD),show ∫ i, E i∂ τμ=W from Law.apply_pres he hdD]; change (W+W)*_= _; rw [show W= ∫ i,normcost F G i∂Ytw from Law.apply_pres (measurePreserving_fst ..) h.meas]; ring -- tune
end Chalk
end YM.CF.BProof.Bide
