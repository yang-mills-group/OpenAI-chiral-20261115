import Gingham.Ruff.Orb
import SatinThinReport
set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py.Rate.LocalLimit.Preparation
open Neon
open Py
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Ione Moto Taxi Hove Haro Vow Bake Lilt Prism Rue Larch Push.AbsoluteSums.Trees Salt Jet
open scoped YM.CF.Mew

set_option autoImplicit false
open Mew QuadClock Roots Rive Oise


open QuadClock FullBill Pitching Focus Buffered Afterglow Journey
open QuadClock FullBill Pitching Focus Buffered Afterglow Journey
variable {P:Preparation}{ℓ:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus ℓ))
attribute [-instance] instDecidableEqLex
namespace Yoke
open Tapestry Advance Papyrus Papyrus.Franc
variable {n:Side}

open Py.Rate.Pannier CF.Pannier Chancel Rous Pressure Worth Worth.Pays Graph
open Regis Head.Garland
local notation "N" s:max i:max=> side Y i s
local notation "h" s:max => hat P.R.L P.x s
variable (s i k:ℕ){w z ρ:ℝ} (V:ShelterCost w Y s i k)
local notation "σ" => Real.sqrt (hat P.R.L P.x s)
local notation "CC" =>RootBook Y i k s
local notation "ℰ" =>meterC (hat P.R.L P.x s)
local notation "VV0" => ((Y.voyage i).CapeT s)
include V
lemma glows_at (L:GlowCost w ρ Y s i k)
 (t:Orbit (N s i))(M:FC (Single (N s i)))(q:Bright ρ M (Real.exp z)) :
   let X:=RootBook Y i k s
   ‖letterRead M (denZ X P.U VV0 t)‖ ≤ Real.exp (z+glowRise Y 0 s i k 0)*shadeY Y s i k 0 (gateC (h s)) t:=by

 intro X; let d:=dleaf P.R.L (h s); let S:= (Y.voyage i).CapeT s; let N':= sites (N s i); let E:=3*d*N'; let A:= Cascade.angleFin X.J.M (N s i) P.K.j; let g:= atFrame Y s i t; let Z:=metroStress P.K.j X S t g
 let K:=X.path.inChannels X.funds X.p X.beta t.1; let U:= X.v.re; let f:= meterC (h s); let Y':=gateC (h s) *flakes (shieldC (h s)) t.1
 have hp:= L.buys _ z q _ X.F X.slip X.K (existingMarket Y s i k V.load.paid) t g
 let W:= ‖letterRead M (denZ X P.U S t)‖; have hX:Real.exp (-U)* W ≤ Real.exp (-K)*Real.exp (E+A+z+w*Z):=by
    change ‖letterRead M (Complex.exp (-X.v)•denZ X P.U S t)‖ ≤_ at hp; rwa [(letterRead M).map_smul_of_tower,norm_smul, Complex.norm_exp,Complex.neg_re] at hp
 change W≤ Real.exp (z+(4*0*(_ :ℝ)+6*f*N'+A+U))*Real.exp (-K +0* _ + Y'); rw [mul_zero,zero_mul,zero_add,zero_mul, add_zero,←Real.exp_add];
 calc _ ≤ Real.exp U*(Real.exp (-K)*Real.exp (E+A+z+w*Z)):= (mul_le_mul_of_nonneg_left hX (Real.exp_pos U).le).trans' (le_of_eq (by rw [←mul_assoc, ←Real.exp_add, add_neg_cancel,Real.exp_zero,one_mul]))
      _ ≤ _:= by rw [←Real.exp_add (-K),←Real.exp_add]; apply Real.exp_monotone; have hz:w*Z≤ f*N'+Y':= V.effort t; have hQ:0 ≤ N':= zero_le_one.trans (sites_pos _);
                 have hv:0≤f:= (BProof.coin_pos ..).le; unfold E; linarith only [hz,mul_le_mul_of_nonneg_right V.load.health.2.1 hQ,mul_nonneg hv hQ] -- unfolding?


/-- One pressure sample (no sparse insertion assumption). -/
lemma amulet
  (L:GlowCost w ρ Y s i k)
  (g:(Y.voyage i).kick ≤ k)
  {W:Mark (N s i)}(hp:Envelope W)(GS:Shines ρ W (Real.exp z)):
  ‖Journey.compass Y i k s W‖ ≤ Real.exp (z+14*ℰ*sites (N s i)):=by
 let V':= (Y.voyage i).CapeT s; let L':= city (N s i); let N':=N s i; let G:=CC; let A:= sites N'; let u:=glowRise Y 0 s i k 0; let θ:=gateC (h s); let b:=Papal.gBaseR Y s i k; let w:= G.v.re; let C:= Cascade.angleFin G.J.M N' P.K.j; let v':=Scales.merit P.R.L (h s)
 let X(x:Orbit N'):= letterRead (W (x.1,V' x)) (denZ G P.U V' x); let Y':= ‖coined Y i k s‖; let E:=ℰ; have hb:Real.exp (b+C-v'*A) ≤ Real.exp (-w)*Y':=by have hb:=V.load.vast; simp only [VLine,compensated,norm_mul,Complex.norm_exp,Complex.neg_re] at hb; exact hb
 have hE' : 0 < Y':= by by_contra! y; exact (Real.exp_pos _|>.not_ge) (hb.trans (mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _|>.le) y))
 obtain ⟨hR,hD⟩:= shade_prior Y V.load V.load.ready V.load.willing
 change ‖(∫ x,X x∂L')/ _‖ ≤ _; rw [norm_div,div_le_iff₀ hE']; refine le_trans (norm_integral_le_integral_norm X) ?_
 have hm: Integrable X L':= mark_integrable (Papal.roofage Y i s).bill hp (Marks.can_read _ _ _ _ (Y.each_level i k s g V.load.paid))
 refine le_trans (integral_mono_ae hm.norm (hR.const_mul (Real.exp (z+u))) ?_) ?_; swap
 · rw [MeasureTheory.integral_const_mul]; refine le_trans (mul_le_mul_of_nonneg_left hD (Real.exp_pos _).le) (?_); let K:=z+14*E*A;
   change _≤ Real.exp K * Y'; rw [show K=(K+w)+(-w) from (by ring), Real.exp_add (K+_ ), mul_assoc (Real.exp (K+w))]; refine le_trans ?_ (mul_le_mul_of_nonneg_left hb (Real.exp_pos _|>.le)); rw [←Real.exp_add (z+u),← Real.exp_add]; apply Real.exp_monotone; have ht:v'≤E:=V.load.health.1; unfold u glowRise K; linarith only [mul_le_mul_of_nonneg_right ht (show 0≤A from zero_le_one.trans (sites_pos _))]

 exact Eventually.of_forall fun x=>glows_at Y s i k V L _ _ (GS (x.1,V' x))

#print axioms amulet
