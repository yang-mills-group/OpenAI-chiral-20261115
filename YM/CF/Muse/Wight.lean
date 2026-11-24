import YM.CF.Muse.Inlet
set_option autoImplicit false
set_option maxHeartbeats 460000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Oath
open Nor
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
variable{N P B:Side}{S:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S}{K:Teller SU.group}{G:Ratio (mid N B) (mid P B)}{R:Patch}{L:ChartRatio SU.group}
variable {d e η t z g b c A B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L)
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
variable {x y0 β:ℝ}(pp:BudgetPoint){t₀ v v₁ p11 p22 p3 p4:ℝ}
local notation "SN"=> Site (Domain N B)
open Cascade
open Fief
open Yaw Pig
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Wray Prism Font
local notation "B_"=> (More N)
local notation "S₁"=> (Domain N B)
local notation "dN"=> Directions SU.group (More N)
open PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir Siete
open Haro Feu Feu.Corset Nor
variable {ε δ vC C:ℝ}(Xc:SkyC k C)
open Footprint
local notation "Jr"=> preCost
abbrev tollB(s:ℝ)(e₁:ℝ)(M a:ℝ)(n t:ℕ):ℝ:= Real.exp (s*preCost (t+90+5))* ledgerP k n e₁ *harp C Xc n t M a
abbrev gritY (p:ℝ):= p⁻¹^5
abbrev Lgrit (e:ℝ):= e⁻¹^15*(Nat.factorial 15:ℝ)*Real.exp e
lemma expG (p:ℝ)(h:0<p)(V:Side)(x:ℕ)(g:V.val≤ x^3): Real.exp (-p*x) ≤ Lgrit p *gritY V.val:=by
 let t:= polynomial_cost h (Nat.cast_nonneg x) 15
 let A:ℝ:=V.val; let C:=Lgrit p; have hp: A≤ (x:ℝ)^3:=by unfold A; exact_mod_cast g
 have hz:0 < A:=by unfold A; positivity
 have he:A ≤ (1+x:ℝ)^3:=hp.trans (pow_le_pow_left₀ (Nat.cast_nonneg _) (by linarith) _) -- tune
 rw [gritY,neg_mul,Real.exp_neg, inv_pow]
 change (Real.exp (p*x))⁻¹ ≤ C*(A^5)⁻¹
 rw [←div_eq_mul_inv]; apply (le_div_iff₀ (by positivity)).2; rw [inv_mul_le_iff₀ (Real.exp_pos _),mul_comm]
 refine le_trans (pow_le_pow_left₀ hz.le he _) ?_; rw [←pow_mul]; exact t -- tune
-- preL coarse.Ang budgets. 
abbrev peakT (e g b:ℝ):=b^4 + Real.exp (e*g)*(e*g)
variable (p a B1 vT u K₁ E h κ δ₄:ℝ)
local notation "FA"=> (Real.exp (-p*(u:ℝ))) -- shadow
-- given normalized receipts.H equivalent scale. all factors stated even constants.Pre-L. 
abbrev StatQ(B z p g δ t:ℝ):= B*(p*(t+Real.exp (p*δ)*(p*δ)))*g*z -- rename
abbrev Vows(g s t:ℝ):= g*(s+t)
abbrev topZ (B O Lκ L S A:ℝ):=A*(Lκ*(O+1+S))+L*A + B*(A*2) -- tune easier
lemma hoopB (Side α δ A s γ L z:ℝ) (d:0≤ Side)(u:Side ≤1)(a:0≤A)(hα:0≤α)(hv:α≤1)(v:0≤z)(hδ:Real.exp (A*δ)*(A*δ)≤Side)(g:0≤ δ): α*(A*(1+Real.exp (A*δ)*(A*δ)))*z ≤ A*2*z:=by
 let R:=Real.exp (A*δ)*(A*δ); have he :0≤ R:=mul_nonneg (Real.exp_pos _).le (mul_nonneg a g)
 apply mul_le_mul_of_nonneg_right _ v; refine (mul_le_of_le_one_left (mul_nonneg a (le_trans zero_le_one (le_add_of_nonneg_right he))) hv).trans (mul_le_mul_of_nonneg_left ?_ a); linarith only [hδ,u]
abbrev leafZ (B s A Lκ :ℝ):= A*(B+1+s)+ Lκ*A
abbrev firmZ (B s A Lκ L :ℝ):= leafZ B s A Lκ + L*A*2
lemma warpPay (d l α u A B s R L z t O Δ κ:ℝ)(Qφ:Prop)[Decidable Qφ] (hl:l ≤1)(hp:0 ≤ l)(hx:α≤ 1)(hA:0≤ A)(hα:0 ≤ α)(hm:0≤B)(hb:d≤ B*l)(ht:0 ≤ s)(hv:t ≤ l)(ha:0 ≤ d)(ht':0≤t)(hR:κ≤L*l)(g:0≤κ)(y:0≤z)(e:0 ≤ L)(v:0≤R)(hZ:¬ Qφ→ α≤ R*l) : let Y:= α*(A*(d+t+s*l))*z + κ*(A*α*z); let X:=α*(A*(1+t))*z; (if Qφ then Y else X) ≤ firmZ B s A L R*l*z:=by
 intro Y X; have hc:0 ≤ leafZ B s A L:=by unfold leafZ; positivity
 split; next h=>
   refine le_trans (b:= leafZ B s A L*l*z) ?_ (by apply mul_le_mul_of_nonneg_right _ y; unfold firmZ; exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity)) hp)
   have hg: d+t+s*l ≤ (B*l+l)+s*l:= by gcongr
   have hm:A*α*z ≤ A*z:=mul_le_mul_of_nonneg_right (mul_le_of_le_one_right hA hx) y
   calc
     Y ≤ A*((B*l+l)+s*l)*z + L*l*(A*z):= add_le_add (mul_le_mul_of_nonneg_right (le_trans (mul_le_of_le_one_left (by positivity: 0≤A*(d+t+s*l)) hx) (mul_le_mul_of_nonneg_left hg hA)) y) (mul_le_mul hR hm (by positivity) (by positivity))
     _ = _:=by unfold leafZ; ring
 next u=>
   have h':1+t ≤ 2:=by linarith only [hl,hv];
   refine le_trans (b:= R*l*(A*2)*z) (mul_le_mul_of_nonneg_right (mul_le_mul (hZ u) (mul_le_mul_of_nonneg_left h' hA) (by positivity) (by positivity)) y) (mul_le_mul_of_nonneg_right ?_ y)
   calc
      _ = R*A*2*l:=by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hc) hp -- tune
lemma feedB(P p α L v o J D R A:ℝ)(hp:0≤P)(hv:0≤p)(hz:0 ≤ v)(h:o ≤ L)(t: L ≤1)(hy: R≤J*L*v)(hA: D ≤ A*v)(h1:0≤ o)(hR:0 ≤ R)(h₃:0 ≤ D)(hJ: 0 ≤ J) : P*R+o*p*(P*(D+R)) ≤ (P*J+p*(P*(A+J)))*L*v:=by
 have hh:J*L≤J:=mul_le_of_le_one_right hJ t
 calc
    _ ≤ P*(J*L*v) + L*p* (P*(A*v+J*v)):= add_le_add (mul_le_mul_of_nonneg_left hy hp) (mul_le_mul (mul_le_mul_of_nonneg_right h hv) (mul_le_mul_of_nonneg_left (add_le_add hA (le_trans hy (mul_le_mul_of_nonneg_right hh hz))) hp) (by positivity) (mul_nonneg (h1.trans h) hv))
    _ = _:=by ring
end YM.CF.Oath
