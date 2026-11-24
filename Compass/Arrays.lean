import Compass.Hall
import Compass.Prime
import Compass.Starglass
import Compass.Spokes
import Compass.Poetry
import Compass.Reynolds
import Compass.Bullion
import YM.CF.Neon.Ten
import Compass.Hubs
import YM.CF.Ione.Jost
import Compass.Lode
import YM.CF.Brood.Tips
import YM.CF.Coal.Vice
import YM.CF.Moto.Band
import YM.CF.Moto.Kearn
import Compass.Jazz
import Compass.Needle
import Compass.Sloop
import YM.Push.LOCAL_SPLITTING.Orientation
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Compass
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
variable{N P B:Side}{S:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S}{K:Teller SU.group}{G:Ratio (mid N B) (mid P B)}{R:Patch}{L:ChartRatio SU.group}
variable {d e η t z g A B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L)
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
variable {x y0 β:ℝ}(pp:BudgetPoint){t₀ v v₁ p11 p22 p3 p4:ℝ}
local notation "SN"=> Site (Domain N B)
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
local notation "ζ"=> (radiusB x)
open Trees Footprint Iva Eire
open Jade
-- certify.WAGES off all granted tasks
variable {u Hh pK qK a γ vS dS kL w:ℝ}{r p i:ℕ}{X: GramM (mid N B)}{Y: GramM (mid P B)}{U:Grasp V.U B d}
open Oath Feu Feu.Corset Haro Nor Siete PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir
open Moto
open Vow Lilt Larch Bake Rue
open Prism Hove Oise
variable {Nq:Side}
open Ione
open scoped Mew
local notation "Ck"=> carriers Nq
open Neon
open Moto Neon Ione
-- currents.P
variable {Nq:Side}
lemma taxInvS(s: staff Nq):taxK (s⁻¹)=taxK s:=tax_inv ..
private lemma tax_spec(s:staff Nq):(taxK s) = if tariffX s.val.s then -1 else 1:=rfl
lemma det_inv(s:Signed):detX s⁻¹ = detX s:=by have h:=det_p s s⁻¹; rw [mul_inv_cancel,det_i] at h; cases a:detX s <;>cases b:detX s⁻¹ <;> first|rfl|(exfalso; rw [a,b] at h; contradiction)
-- any stabilizer signed rotation lifted at node: choose t s.t. anon node. a.mills & wrap.Needs solve 2b shift mod 2N. use Tofu & b vector. for v=signed, choose translate. use product of Sweep rotation and translator from transits.
lemma stabilizes(o:Site Nq)(s:Signed)(p:Anchored s)(t:Bool):∃ v:staff Nq,v.val.s=s∧v.val.charge=t ∧ orbitT v o=o:=by
 let v:staff Nq:=⟨⟨s,0,t⟩,p⟩; let y:=orbitT v o; let u:Sweep Nq:=⟨1,y-o,false⟩; let U:staff Nq:=⟨u,Anchored.one⟩ -- orbitT U y=o. x=y
 refine ⟨v*U,mul_one _,Bool.xor_false _, (camaraderie v U o).symm.trans (yu ?_)⟩
 unfold orbitT; rw [node_inspire,←sitU,sitA]; change affine 1 ((assembly Nq).root (-( (1:Signed)⁻¹.act (y-o)))) (Cube.node y)= Cube.node o; rw [inv_one,Signed.act_one,map_neg,map_sub]; simp only [affine,Signed.act_one,Cube.node]; abel
-- uniqueness of Axon $D_0. 
variable (Q:BudgetPoint){L_:ℕ}(uQ:10≤Q.B)(uL:1<L_)
local notation "C"=> mid N B
include uQ uL
lemma Axon_only (F:RegBudget (mid N B))(i:Site (mid N B))(X Y:ArcΦ){A B' h:ℝ}(p:Axon L_ i Q F h A X)(t:Axon L_ i Q F h B' Y):X=Y:=by
 let Z:=Φrap _ i 10
 have h:coverNumber Q.B Z.val.2≤1:= (Corona.cover_mono (Corona.halo_mono uQ (Subset.refl _)) _).trans (AnalyticBridge.CouplingShape.ballPaid ..)
 have hl:chose L_ Q Z:= (Nat.pow_le_pow_left h 3).trans_lt (by rw [one_pow]; exact uL)
 have he:= (p.flair Z hl).2; have hv:= (t.flair Z hl).2; rw [if_pos rfl] at he hv; exact he.symm.trans hv
lemma shapeGlyph (F:RegBudget (mid N B))(i:Site (mid N B))(h:ℝ)(hhV:1≤h)(M:ArcΦ)(b:ℝ)(Y: Axon L_ i Q F h b M)
    (p:∀ t:staff (mid N B), orbitT t i=i → backing t F=taxK t • F)
    (g: 4≤(More (mid N B)).val)(Z:∀ m:Scree.Hub (mid N B),chose L_ Q m→ Nonwrapping m.val.2 m.val.1) :
    ∀ t:staff (mid N B),orbitT t i=i→ tiltA t.val M=taxK t • M:=by
 intro t u; let a:= (taxK t); let b':= backing t F
 have hA : (a:ℂ) • F=b':= (deal_budget a F).trans (p t u).symm
 have hP:=hhV
 let E':=charge_ν (a:ℂ) L_ i F M Q b (zero_le_one.trans hP) Y
 have he: Axon L_ (inspire t.val i) Q F h b M:=by rw [show inspire t.val i=i from u]; exact Y
 apply (Axon_only Q uQ uL b' i _ _ (cargo Q t.val F i M t.property L_ he hP g Z))
 rw [←hA,←deal_arc]; exact E'
lemma rime (W:RegBudget (mid N B))(i:Site (mid N B))(h:ℝ)(M:ArcΦ)(b:ℝ)(Y:Axon L_ i Q W h b M)(ph:1≤h)(p:∀ t:staff (mid N B),orbitT t i=i→backing t W= taxK t • W)(g: 4≤(More (mid N B)).val)(Z:∀ m:Scree.Hub (mid N B),chose L_ Q m→Nonwrapping m.val.2 m.val.1): HasCrystal M.1:=by
 let he:=shapeGlyph Q uQ uL W i h ph M b Y p g Z
 intro s q hs j l
 obtain ⟨z,x,f,q'⟩:=stabilizes i s hs q
 have ht:= congrFun (congrFun (congrArg Prod.fst (he z q')) (Lattice.PlaqAxes.rotate s j)) (Lattice.PlaqAxes.rotate s l)
 let A(t:PlaqAxes):= Lattice.PlaqAxes.rotate (z.val).s⁻¹ t
 open AnalyticBridge.VerifiedReset Lattice.PlaqAxes in
 change (dirS z.val.s (A (rotate s j))* dirS z.val.s (A (rotate s l))) • Spire.payZ z.val⁻¹ (M.1 (A (rotate s j)) (A (rotate s l)))= taxK z • M.1 _ _ at ht -- parentheses precedence
 have hz(t:PlaqAxes): A (Lattice.PlaqAxes.rotate s t)=t:=by unfold A; rw [x]; exact Lattice.PlaqAxes.rotate_inv ..
 rw [hz,hz,tax_spec] at ht
 have hk:(wageZ z.val⁻¹) = SkateGlyph s q:=by change z.val.charge.xor (detX z.val.s⁻¹)=_; rw [f,x,det_inv]; rfl
 unfold Spire.payZ at ht; rw [hk,x] at ht; exact ht.symm
-- Dome vanish: only proper subgroup needed
lemma hole (W:RegBudget (mid N B))(i:Site (mid N B))(h:ℝ)(M:ArcΦ)(b:ℝ)(Y:Axon L_ i Q W h b M)(ph:1≤h)(p:∀ t:staff (mid N B),orbitT t i=i→backing t W= taxK t • W)(g: 4≤(More (mid N B)).val)(Z:∀ m:Scree.Hub (mid N B),chose L_ Q m→Nonwrapping m.val.2 m.val.1): M.2=0:=by
 let X:=M.2
 have hp(s:Signed)(t:detX s=false)(s0:Anchored s): driftH s false false (spinU false s) X = (if tariffX s then (-1:ℝ) else 1) • X:=by
    obtain ⟨z,u,m,w⟩:=stabilizes i s⁻¹ s0.rev false
    have ht:= congrArg Prod.snd (shapeGlyph Q uQ uL W i h ph M b Y p g Z z w)
    change driftH (z.val.s⁻¹) z.val.charge _ _ X= taxK z • X at ht
    simp_rw [show (z.val⁻¹).s=z.val.s⁻¹ from rfl,u,m,tax_spec,u] at ht; rw [inv_inv,t,taxInv] at ht; exact ht
 have hr: Hove.seedsP X:=by
    let A':=Φrap _ i 10; have hh:chose L_ Q A':= (Nat.pow_le_pow_left ((Corona.cover_mono (Corona.halo_mono uQ (Subset.refl _)) _).trans (AnalyticBridge.CouplingShape.ballPaid ..) : coverNumber Q.B A'.val.2≤1) 3).trans_lt (by rw [one_pow]; exact uL)
    have he:= (Y.flair A' hh).2; rw [if_pos rfl] at he; unfold X; rw [←he]; exact Hove.true_P i _
 open Tap in
 suffices χ: X=0 from χ
 let T:=X.1
 have hX:T=0:=first_s _ hr.1 (by intro s t y; have h:=congrArg Prod.fst (hp s t y); cases f:tariffX s; exact (show _=_ from (by rw [f] at h; have h':twist (Tap.twoU (stSpin t) false) T=(1:ℝ) • T:=h; exact h'.trans (one_smul _ _))); rw [f] at h; have h':twist (Tap.twoU (stSpin t) false) T= (-1:ℝ) • T:=h; exact h'.trans (neg_one_smul _ _))
 have he (s:Signed)(i:Axis)(t:Bool)(M X: Tap.Pal)(p0: axPay s i • M=(if t then (-1:ℝ) else 1) • X): M=Scroll.hush (t.xor (s.flip i)) X:=by cases h:s.flip i <;>cases t <;>simp [axPay,StressFlux.sign,h] at p0 ⊢ <;> first|assumption|exact neg_eq_iff_eq_neg.mp p0
 refine Prod.ext hX (Prod.ext (funext (vector_s X.2.1 hr.2.1 ?_)) (funext (vector_s X.2.2 hr.2.2 ?_)))
 all_goals intro s t hs i; let u:=hp s t hs
 · exact he s i _ _ _ (congrFun (congrArg Prod.fst (congrArg Prod.snd u)) _)
 exact he s i _ _ _ (congrFun (congrArg Prod.snd (congrArg Prod.snd u)) _)
#check shapeGlyph
end YM.CF.Compass
