import Bay.D.Cello
import Bay.D.Incense
import Bay.D.Cordial
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Bay
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet Scroll Finset Palot Cadre Vow
open RG MeasureTheory Rue
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Tap Levier Thera Oath Font Spire Dial Rill
open Kennel Swell

namespace D
open Exterior Precision Nacre
open scoped ContDiff
open Regis Regis.Head Etch Gleam Next.SectorChange Next.SectorChange.Gaussian
open Pressure Work.F03 ProbabilityTheory
local notation "T4"=>SU.group
open Buffered Lamour.Bridge.Celeste.Clock Fabric
open Py Py.Rate LocalLimit Preparation Buffered.Afterglow Papal
open Vale clocks
open YM.CF.Pannier.Chancel Journey Tower Tower.SlabMark VacuumSelection Tapestry
open scoped ComplexOrder NNReal ENNReal

variable {K:Calibration}{x:ℝ}{j:Axis}
lemma gaps_cost (B m:ℕ)(h:1 ≤ m):
  acres K (gaps B j m) ≤ m*(4*(B+addgap K))^4:=by

  let y i:= if i=j then m else 1
  let p:=4*(B+addgap K)
  have e: ∏_i:Axis, p=p^4:=by simp [Axis]
  have hy:∏i:Axis,y i=m:=Fintype.prod_ite_eq' j (fun _=>m)
  apply (Finset.prod_le_prod' (g:=fun i=>y i*p) ?_).trans
  · rw [prod_mul_distrib,hy,e]
  intro i _
  unfold y gaps p
  split_ifs with f
  · have : addgap K ≤ m*addgap K:=Nat.le_mul_of_pos_left _ h
    rw[mul_left_comm m 4,mul_add]
    nlinarith only [this]
    -- w=m so actually gaps B j m time m*B? gaps B j m puts w*Q=m*B. target B*m. 
  simp only[one_mul, le_refl]

def Able(K: Calibration) (x:ℝ):Prop:=0<x ∧ 8*oar x*(4*(atRate 12 x+addgap K))^4 ≤ grit x
open Cake
theorem able (K: Calibration):∀ᶠ x in atTop, Able K x :=by
 have h:Sugar (-400) oar:= by
    unfold oar Sugar thinRate
    rw[show (-400/200000:ℝ)=-(1/500) by norm_num]
    exact Sleigh.Paddled.park _
 have hp:= ((h.icing 8).stew
      ((((bowl 12).honey ((spice (addgap K :ℝ)).raise (by norm_num: (0:ℝ)≤12))).icing 4).bake 4 (b:=48) (by norm_num))
      (d:=-352) (by norm_num)).food (b:=-300) (by norm_num)
 exact ((eventually_gt_atTop (0:ℝ)).and hp)
lemma gravel {m B:ℕ}(p:Able K x)(q:B ≤ atRate 12 x)(h:1 ≤ m):
 Pebble K x (gaps B j m) ≤ m*grit x:=by
   have h₀:0≤oar x:=by have :=p.1; unfold oar;positivity
   have e : (acres K (gaps B j m):ℝ) ≤ (m:ℝ)*(4*(B+(addgap K:ℝ)))^4:= by exact_mod_cast (gaps_cost (K:=K) (j:=j) _ _ h)
   apply le_trans (mul_le_mul_of_nonneg_left e (by positivity:0≤8*oar x))
   rw[mul_left_comm]
   gcongr
   exact le_trans (b:=8*oar x*(4*(atRate 12 x + (addgap K:ℝ)))^4) (by gcongr) p.2

variable {P:Preparation}{l:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus l))
 (H:Real.exp 1≤P.x)(s:ℕ)
local notation "Κ" => Journey.tent Y H
local notation "Ω" => hat P.R.L P.x s
local notation "N" i:max => Papal.count Y s i
lemma transferCAST(M n:Side)(h:M=n)(a:Mark M): (h ▸ a:Mark n)=arrange _ _ h a:=by
 subst n; rfl
lemma y_sharp(i k:ℕ)(f:Buffered.Family Κ): sharp Y H s i k f=
 Journey.compass Y i k s
 (arrange _ _ (Journey.terrain Y H (Y.ir i) s) (f (momentm Y i s))):=by
 unfold Journey.sharp Journey.listen Journey.send
 apply congrArg
 apply transferCAST
#check count_grows

/-- sharp cost of dyadic time chambers on each canopy lease, using anisotropic housing. initial support S fixed at s! -/
lemma eclat (t B:ℕ)(S:Finset Cover)
 (r:Feeling Κ j t B S)(q:taps Κ*t≤B)(v:B≤ atRate 12 Ω)
 (p: Able Κ Ω)(n:ℕ):
 ∀ᶠ i:ℕ in atTop, ∀ (k:ℕ)(c:Canopy Y s i k H)
   (o d:Seat (N i)) (F:Pane (N i)→ℝ)(Z:Chalk (More (N i)) ℝ)(z:ℂ)
   (a:Lease Y s i k o d F Z)(u:‖z‖≤thetaB Ω)
   (f:Buffered.Family Κ),
   Staff (Tunic o d F z)
      (arrange _ _ (Journey.terrain Y H (Y.ir i) s) (f (momentm Y i s))) S 1 →
  ‖sharp Y H s i k (singing Κ j t f n)‖≤Real.exp (((2^n:ℕ):ℝ)*(z.re*beans Y s i k Z + tilt Ω)):=by
 let m:=2^n
 obtain ⟨T,w,h⟩:=treble _ _ _ _ r n
 let D:= gaps B j m
 have l:∀ᶠ i:ℕ in atTop,∀a, D a+addgap Κ ≤ (N i).val:= by
   exact (eventually_all ..).2 fun a=> (count_grows Y s).eventually_ge_atTop _
 filter_upwards [(momentum Y s).eventually h,l] with i g y k c o d F Z z a u f e
 rw [y_sharp]
 obtain ⟨L,b,a₀,h₁,g₁⟩:=g _ _ _ _ (fun u=>Tunic.rev u) e

 rw [a₀]
 have V:=gravel (j:=j) (m:=2^n) p v (by simpa only[Nat.one_le_iff_ne_zero] using (pow_ne_zero n (show (2:ℕ)≠0 by decide)))
 refine (c _ _ _ _ _ a u L b D (Feeling.slots _ _ _ _ w q y h₁)).trans
    (Real.exp_monotone ?_)
 rw [g₁]
 unfold Fly tilt
 unfold D m
 linarith only [V]
