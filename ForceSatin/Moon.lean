import ForceSatin.Porta
import ForceSatin.Falcon
set_option autoImplicit false
set_option maxHeartbeats 520000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py
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
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Nor
open Chaff Gloss Maize Tye RP RP.Str
open Brace
namespace Rate
open Pitching Focus CF.Mint
namespace LocalLimit
open Preparation
variable {P:Preparation}{l:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus l))
variable {h z:ℝ}
open Buffered
open CF.Pannier.Damask
open YM.CF.Velvet
open Pannier
namespace Papal
local notation "ℶ" => hat P.R.L P.x
local notation "💠" => P.K.j
open CF.Papyrus.Franc Verses CF.Pannier.Chancel Checkers Flint Gleam Gleam.Luster Gleam.Luster.Almanac Grade Graph
local notation "pio"=> P.R.L
open CF.Window CF.Velvet CF.Pannier.Damask

open CF.Papyrus.Franc.SatinForce
open Pannier
local notation "nₛ" s:max i:max => count Y s i
local notation "χf" x:max => parcelF x
open CF.Lamour CF.Lamour.Bridge.Celeste Afterglow Journey

open _root_.YM.Gleam.Luster.Risa Gentle Tiling
open BProof (scaleY PL)
open _root_.YM.Work.F03 _root_.YM.Regis
local notation "Uₛ" s:max i:max k:max => gram Y s i k
local notation "Kₛ" s:max k:max => Y.uv k - s
local notation "π₀"=> P.K.top.clip

-- uniform scalar exponents charges
open _root_.YM.Next.Rank.Spindle
open Gentle.Solace Rail
open _root_.YM.Regis.Resonance Lull
open Fineness
namespace Moon
abbrev branchExp (m:ℕ):ℝ:=0.1*micr/((m:ℝ)+1)
abbrev ledgerV (m:ℕ)(x:ℝ):ℝ:= x^(branchExp m)
abbrev staple (x:ℝ):ℝ:= x^(0.2*micr) -- per pure term
abbrev spry (x:ℝ):ℝ:= x^(-(8*micr))
abbrev voucher (x:ℝ):ℝ:= x^(0.1*micr) -- coeff sums ≤ X^.10µ AND path lengths per term ≤ X^.10µ
abbrev fabric (x:ℝ):ℝ:= 2*Real.sqrt x -- multiplier front bound. β' fits via matchedX
abbrev ivy (b:ℝ)(m:ℕ):ℝ:=180^m*1*(1+b)^m -- spin wallet
abbrev bark (m:ℕ):ℕ:= 120*(m+1)
structure Celery (L:Side)(m:ℕ)(q:Clip)(R:Rules SU.group)(x b:ℝ):Prop where
 range :1≤ x
 sec :colorCash SU.group ≤ radiusB x
 charm : 0 ≤ tuition L x
 onTree (z:Side)(h:z.val ≤ walls L x) : suitedFee z.val (sax x) ≤ tuition L x
 radius: tuition L x ≤ R.c
 sax_p: 0 ≤ sax x
 -- mask may take smaller FIXED threshold; allow per term ∀ t with rate*p ≤ t ≤ p (otherwise lower)
 cap : fabric x * temp x ≤ ledgerV m x
 perk : (2*ledgerV m x)^m*ivy b m≤ staple x -- also free (ivy>=1)
 cusp : (2*ledgerV m x)^m*(m*(Lull.loan*chordAllowance q 4))*ivy b m≤ staple x -- lip
 curvature : ((m*(2*ledgerV m x)^m) * ((Lull.loan:ℝ)*(fabric x * slotError R (colorCash SU.group) (tuition L x))) + (m*(flange*(voucher x * tuition L x))) * (2*ledgerV m x)^m) * ivy b m ≤ spry x
 finu : (ledgerV m x ^ bark m)⁻¹*(2*((m:ℝ)*PBound (chordAllowance q 4) (m+bark m))) * ivy b m≤ spry x
 wick : (1 + ↑m * PBound (chordAllowance q 4) m)*ivy b m≤ staple x
 sales : voucher x * staple x ≤ waxGlow x ∧ voucher x * spry x ≤ failFoam x
lemma branch_p(m:ℕ):0 < branchExp m:= by unfold branchExp micr; positivity
lemma branch_grade(m:ℕ): branchExp m * m ≤ 0.1*micr:=by
 have e: branchExp m*((m:ℝ)+1)=0.1*micr:= by unfold branchExp; field_simp -- maybe no goals
 linarith only [e,branch_p m]
lemma bark_grade(m:ℕ): - branchExp m * (bark m:ℝ) = -(12*micr):=by unfold branchExp bark; push_cast; field_simp; ring
lemma slot_zero (R:Rules SU.group)(m:ℕ)(v:ℝ):0 ≤ slotError R m v:=by unfold slotError faceCutError; have hp:=SU.group.colorScale_pos; have ho:=R.positive; positivity
lemma trunkHw (L:Side)(R:Rules SU.group)(m:ℕ): Grade (-(0.8:ℝ)) (fun x=> slotError R m (tuition L x)):=by
 have e:= ((tuition_b L).pwr 2).grow (by norm_num : (-2/5:ℝ)*(2:ℕ)≤ -(0.8:ℝ)); exact (e.scaleB _).plus (e.scaleB _)
private lemma Grade_go {a b:ℝ}{f:ℝ→ℝ}(h:Grade a f)(u:a<b):∀ᶠ x:ℝ in atTop,f x≤ x^b:= (h.cost_p u).mono fun _ h=> (le_abs_self _).trans h
-- grant REAL powers.b
lemma celestial (L:Side)(R:Rules SU.group)(q:Clip) (b:ℝ)(m:ℕ):∀ᶠ x:ℝ in atTop, Celery L m q R x b:=by
 let a:= 0.1*micr; let d:ℝ:= -2/5; have hd:Grade d (tuition L):= tuition_b _; have rv:= (branch_p m)
 have ht: Grade (1/2) fabric:=by unfold fabric; simp_rw [Real.sqrt_eq_rpow]; exact (Grade.pitch (1/2)).scaleB _
 let g (x:ℝ):= (2*ledgerV m x)^m; have hg:Grade a g:= (( ((Grade.pitch (branchExp m)).scaleB 2).pwr m )).grow (branch_grade m)
 let e:= 1+ (m:ℝ)* PBound (chordAllowance q 4) m; let u:ℝ:= m*((Lull.loan:ℝ)*chordAllowance q 4); let i:=ivy b m
 let v(x:ℝ):= (ledgerV m x ^ bark m)⁻¹; let F(x):=fabric x * slotError R (colorCash SU.group) (tuition L x); have hF:Grade (1/2+-0.8) F:= ht.mul (trunkHw L R _); have hU:=hF.scaleB Lull.loan; have hβ:Grade (a+d) (fun x=>voucher x*tuition L x):= (Grade.pitch a).mul hd
 have ne:Grade (-(12*micr)) v:=by
    apply Grade.cash (f:=fun x=>(x^(-(branchExp m)))^ (bark m)) (by rw [← bark_grade]; exact (Grade.pitch _).pwr (bark m))
    filter_upwards [eventually_gt_atTop (0:ℝ)] with x h; rw [Real.rpow_neg h.le,inv_pow]
 filter_upwards [paceSize L,(hd.roots (by norm_num [d])).eventually (ge_mem_nhds R.radius),Work.E08.eventual_radiusB (colorCash SU.group),gain_a,eventually_ge_atTop (1:ℝ), Grade_go (ht.mul Grade.temp_b) (show (1/2+-1/2:ℝ) < branchExp m by linarith only [rv]),Grade_go (hg.mul (Grade.block i)) (b:=0.2*micr) (by norm_num [a,micr]),Grade_go ((hg.mul (Grade.block u)).mul (Grade.block i)) (b:=0.2*micr) (by norm_num [a,micr]),Grade_go ((((hg.scaleB (m:ℝ)).mul hU).plus ((((hβ.scaleB flange).scaleB m).mul hg).grow (by norm_num [a,d,micr]))).mul (Grade.block i)) (b:=-(8*micr)) (by norm_num [a,d,micr]), Grade_go ((ne.mul (Grade.block (2*((m:ℝ)* PBound (chordAllowance q 4) (m+bark m))))).mul (Grade.block i)) (b:=-(8*micr)) (by norm_num [micr]), Grade_go (Grade.block (e*i)) (b:=0.2*micr) (by norm_num [micr]), Grade_go ((Grade.pitch a).mul (Grade.pitch (0.2*micr))) (b:=0.35*micr) (by norm_num [a,micr]), Grade_go ((Grade.pitch a).mul (Grade.pitch (-(8*micr)))) (b:=-(6*micr)) (by norm_num [a,micr])] with x h e y v h1 h2 h3 h4 h5 h6 h7 h8 h9
 exact ⟨h1,y,h.1.le,fun z=>h.2 z.val z.property,e,v.2.le.trans v.1,h2,h3,h4,h5,h6,h7,h8,h9⟩
lemma ivyFloor {b:ℝ} (h:0≤b)(m:ℕ):1≤ ivy b m:= by unfold ivy; rw [mul_one]; exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (one_le_pow₀ (by linarith))
lemma stipend {x β y:ℝ}(u:1≤x)(b:matchedX x β) (v:|y|≤ fabric x): |y*coupling β| ≤ 4:=by
 have h:= b.1; let H:=Real.sqrt x; let Z:=Real.sqrt β; have hy:0<x:=zero_lt_one.trans_le u; have hp:0<β:= (half_pos hy).trans_le h; have hZ:0<Z:=Real.sqrt_pos.mpr hp; have he: H ≤2*Z:= by nlinarith only [Real.sqrt_nonneg x, Real.sqrt_nonneg β,h,Real.sq_sqrt hp.le,Real.sq_sqrt hy.le,hZ] -- H notation not unfolds
 rw [abs_mul,abs_of_nonneg (coupling_pos hp).le]; change |y| * Z⁻¹ ≤ _; rw [← div_eq_mul_inv]; exact (div_le_iff₀ hZ).2 (v.trans (show 2*H ≤ _ from (by linarith only [he])))
#print axioms celestial
end Moon
end Papal
end LocalLimit
end Rate
end YM.CF.Py
