import YM.SU5.SatinWard.Resolution.ShoreE
import YM.CF.Tap.Cerf
import YM.CF.Scroll.Kent
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 350000
noncomputable section
namespace YM.CF.LitCurrent
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour
open Stax Skye Jet Scroll Finset Palot Cadre Vow RG Rive Nor Hake MeasureTheory
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical Kronecker
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Dial Rill
open Kennel Swell StressExchange
variable {N:Side}{X Y:SOp N}{o:Seat N}{a b c d v:ℝ}{r:ℕ}
local notation "Γ" => Single N
open Buffered _root_.Zephyr.Chern
open IndexMag Chamber Surplus
namespace AuroraX
local notation "I"=> _root_.Zephyr.Chern.IS
-- think spin gen.L.K using Rotor; physical.S.center in Full:
local notation "H"=> Coats _root_.Zephyr.Chern.IS
local notation "ι" => _root_.Zephyr.Chern.IS
local notation "V"=> snow SU.Slot
open _root_.Zephyr.Chern.Silk
lemma riseSum (F:H): Summable (fun x:Cover=> seam x F):=u_all _ (fun x y=>(F x y).fast.sum)
lemma wave_floor (F: H): ∑' x:Cover,seam x F= flash 0 F:=by
 ext i j; rw [v_all _ (riseSum F) i j]; change ∑' x:Cover,(F i j).co x = Silk.E 0 (F i j); rw [E_eq]; simp [vista,UnitAddTorus.mFourier,fourier_eval_zero] -- lemma mFourier @ zero t
lemma focusRibbon (b:Axis)(F:H): (fun x:Cover=> ((x b:ℂ) • seam x F))=(fun x:Cover=>seam x ((-Complex.I) • Δ b F)):=by
 funext x; rw [map_smul,seam_Δ, smul_smul,rune,←mul_assoc,neg_mul,Complex.I_mul_I,neg_neg,one_mul]
lemma flashPeak {j:ℕ}{r:Male→Streams}(p:Looming j r)(M:Male) : flash 0 (snow SU.Slot (r M))=1- Ember.bins SU.Slot:=by
 rw [←rad_zero,p.flash_snow M SU.Slot 0 (show Jill.Bound Real.pi 0 by unfold Jill.Bound; simp [Real.pi_pos.le]), tmap_zero]; exact boot_o .. -- maybe role Type
local notation "Ζ" => Complex.I
lemma flashMode {j:ℕ}{r:Male→Streams}(p:Looming j r)(M:Male)(h:1≤ j)(b:Axis): flash 0 (Δ b (snow SU.Slot (r M)))= boom b:=by
 have hx: slide 0 (dropD b (r M))= Pi.single b.succ 1:=by
    funext x; refine Fin.cases ?_ (fun x=>?_) x
    · rw [show slide 0 (dropD b (r M)) 0=0 from p.normal ..]; simp
    change Silk.E 0 (Silk.D b (r M x.succ))=_; rw [p.tangent h]; by_cases hb:b=x; · subst x; simp
    simp [Pi.single_apply,hb,Ne.symm hb] -- E resolves SU.E not Zephyr.E. neq use Ne.symm
 let B:=Tap.boom b; rw [Δsnow,map_smul,shadeF,hx,wand_single,← Matrix.smul_kronecker (2:ℂ)⁻¹]
 let z:=Cg b.succ; have ht: Fir.zen (step b) = Ζ • gammaOp b:=by unfold Fir.zen; rw [sum_eq_single b]; simp; intro _ _ u; simp [u]; simp
 unfold Tap.boom Tap.taxi; rw [ht,Matrix.mul_smul]; apply congrArg (fun a:Op SpinIdx=> a⊗ₖ (1:Op SU.Slot)); simp [Cg,one_div] -- names Δsnow global.E
-- in limit.Any in hx.ρ
variable {J:Type}{m:J→ Male}{X₀:Streams}{F:Filter J}{h0:Male→Streams}{k:ℕ} [F.NeBot](p:Looming k h0)(e:∀ u, Arrives F (fun j=> h0 (m j) u) (X₀ u)) (h:1 ≤ k)
local notation "σA"=>snow SU.Slot X₀
include p e
lemma atBreaker : flash 0 (snow SU.Slot X₀)=1-Ember.bins SU.Slot:=by
 ext i j; let U:=arrives_snow e i j; exact tendsto_nhds_unique_of_eventuallyEq (U.E 0) tendsto_const_nhds (Eventually.of_forall (fun a=>congrFun (congrFun (flashPeak p (m a)) i) j))
include h
lemma peakNote (x:Axis): flash 0 (Δ x σA)=boom x:=by
 ext i j; let u:= Arrives.D (arrives_snow e i j) x; exact tendsto_nhds_unique_of_eventuallyEq (u.E 0) tendsto_const_nhds (Eventually.of_forall (fun a=>congrFun (congrFun (flashMode p (m a) h x) i) j))
#print axioms peakNote
end AuroraX
end YM.CF.LitCurrent
