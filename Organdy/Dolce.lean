import Organdy.Andante
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.flexible false
set_option synthInstance.maxSize 24000
set_option maxRecDepth 6000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Organdy.Royal
open Buffered Buffered.Afterglow
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Pastry Tenant Tower

open VacuumSelection


open Lamour.Bridge.Celeste Lamour.Bridge.Celeste.Clock
open CF.Pannier.Chancel Hookah Tapestry

open Yoke Yoke.Bazaar
open Optic
open Larva (Chip Domaine dint)
open Hookah.Rake
open Pressure Worth BProof
open Papal




section
/- Public price testimony over the Test algebra. -/
variable {K:Calibration}
abbrev panel (K:Calibration)(f:Dome K)(r:ℕ)(a:ℝ):=
  let h:=(a:ℂ) • f
  aureole K timeAxis (-(r:ℤ)) h * h
lemma fraction (f:Dome K)(r:ℕ)(a b:ℝ):
 panel K f r (a*b) = ((a^2:ℝ):ℂ) • panel K f r b:=by
 apply Subtype.ext
 change mirror K _ _ (((a*b:ℝ):ℂ) • f.val)* (((a*b:ℝ):ℂ) • f.val)= (((a^2:ℝ):ℂ) •
    (mirror K _ _ ((b:ℂ) • f.val)* ((b:ℂ) • f.val)))
 rw [Complex.ofReal_mul,mul_smul,mirror_scale,Complex.star_def,Complex.conj_ofReal,
    Algebra.smul_mul_assoc, Algebra.mul_smul_comm,smul_smul, Complex.ofReal_pow,pow_two]
end
def glitz (P:Spine)(z:P.Test){j:Axis}(h:P.Spectrum0 j)(s r:ℕ)(a:ℝ):ℝ:=
    (P.singleState j s h (panel P.calibration z r a)).re

lemma fraction_glitz (P:Spine)(z:P.Test){j:Axis}(h:P.Spectrum0 j)(s r:ℕ)(a b:ℝ):
 glitz P z h s r (a*b)= a^2* glitz P z h s r b:=by unfold glitz;rw [fraction,map_smul,smul_eq_mul,Complex.re_ofReal_mul]


variable {P:Spine}{s:ℕ}{c:Cuts}
local notation "H" => P.calibration
local notation "gu" => guineas P s
local notation "w✽" => webX (gu)
local notation "g'" => (shaft P s+6)
local notation "A'" => premium argent c.γ
local notation "ℰ"=> meterC (gu)
local notation "h'"=> knock (gu)
local notation "S'"=> station P s

local notation "w✤" => walkF (gu)
local notation "ε₁" => yieldt (gu)


variable {I:Type}{u:Ultrafilter I}{d:Stores}{i k:I→ℕ}
 {X:Suits P s i}{F:PackE I P}{x:Lot P}
local notation "uf" => (↑u:Filter I)
local notation "W" => raw P s i k X
local notation "G'" => (∀v,Treasure (tunnel P s i v))


variable {A: ∀v,Treasure (tunnel P s i v)}
 (m:AmberMood P c s)
 (p:Parade (↑u:Filter I) P c d s i k X F x)
 (q:∀v, aims P c s (i v) (k v) (raw P s i k X v) (A v))

variable {j:Axis} {r:ℕ}
include m p q

lemma sees_light (Z:P.Register)(z:P.Test)(e:z.val=x .horn)(h:P.Spectrum0 j)
 (R:Plait w✽ (2*r)){v:ℝ}
 (t:Tendsto (lunar P s i k A (2*r)) uf (𝓝 v))(t':|v|≤ (c.cost*clipper gu)^2):
 |glitz P z h s r gu - v| ≤ lakeZ gu:=by
 refine Virgin.stable m.chest t' ?_
 have a0:((shaft P s+6:ℕ):ℝ) ≤ w✽:=by
    have l:(shaft P s:ℝ)+20≤w✽:=m.aisle.depth
    push_cast
    linarith only [l]
 have r':10*(2*r + (shaft P s+6) +10) ≤ walkF gu :=m.aisle.yard R a0
 intro a y
 let f:=panel P.calibration z r gu
 let b:P.Test := 1 + (a:ℂ) • f
 let V:=1+(a:ℂ)•(fun j=>planeM (W j) gu r)
 let S:=haloS r (station P s)
 let F₁:= 1+(a:ℂ)• (fun v=>shadow H r gu (F .horn v))
 have b₂:f.val=shadow H r gu (x .horn):=by rw [←e];exact rfl
 have a₁: Gallon uf P s i S V F₁ b.val:=by
    change Gallon uf P s i S V F₁ (1+(a:ℂ)• f.val)
    rw [b₂]
    exact Bolt.identity.add ((p.plated r gu).scale a)

 have fund:=fabulous (j:=j) p.rate (torch m p q y t)
 have d:=festival Z p.rate fund b a₁
     (Eventually.of_forall fun n=>framed _ m.port (q n).1 r' j)
     (frames r' j) h
 apply le_trans _ d
 apply le_trans _ (Complex.re_le_norm _)
 simp only [b,map_add,single_one,map_smul,smul_eq_mul,Complex.add_re,
      Complex.one_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
 exact le_rfl
#print axioms sees_light
