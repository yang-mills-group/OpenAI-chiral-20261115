import YM.CF.Py.Dusk
set_option autoImplicit false
set_option maxHeartbeats 1050000
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
variable{B:Side}{K:Teller SU.group}{R:Patch}{L:ChartRatio SU.group}
variable {d e η t z g A B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L)
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
variable {x y0 β:ℝ}(pp:BudgetPoint){t₀ v v₁ p11 p22 p3 p4:ℝ}
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
local notation "ζ"=> (radiusB x)
open Trees Footprint Iva Eire
open Jade
variable {U:Grasp V.U B d}{W:GivenX V U}
variable (a α:ℝ)(p i N0:ℕ)(T:Month x a i p N0 V W)
-- ultra-weak diagonal. enough for Wick plus true RG any number of scales.
open CF.Mint
variable {N:Side}(q:Chi)(J:Robes N V W) (h:ℝ) (Ta:Warm V U W N0 J.n i p q J.k J.d J.roomX a h)
abbrev seat_u (Y:Robes N V W)(x:ℝ)(n:ℕ):Side:=⟨Y.h+grainZ V W n x+1,Nat.zero_lt_succ _⟩
lemma seat_size: T.q= grainZ V W N0 x → T.q ≤ (seat_u V J x N0*N).val:=by
 intro p; apply le_trans _ (Nat.le_mul_of_pos_right _ N.property); change _≤ J.h+grainZ V W N0 x+1; omega
abbrev crest (x:ℝ)(m:ℕ): ℝ:= (radiusB x:ℝ)^m
def leash (x:ℝ)(v:ℕ)(Q:ℝ→ℝ):Prop:= crest x v *‖Q x‖≤ (radiusB x:ℝ)⁻¹
lemma leadL (z:ℕ)(K:Side)(F:ℝ→ℝ)(u:sizeK K 1 F):∀ᶠ x in atTop,leash x z F:=by
 let v:= ((sizeK.Bcash K).powC (z+1)).tint u; filter_upwards [Work.E01.radiusB_tendsto.eventually_gt_atTop 0,v.spine.norm.eventually (ge_mem_nhds (show ‖(0:ℝ)‖<1 by norm_num))] with x h p; have hp:0<(radiusB x:ℝ):=by exact_mod_cast h
 unfold leash crest; rw [←one_div]; apply (le_div_iff₀ hp).mpr -- check statement
 rw [norm_mul,Real.norm_of_nonneg (pow_nonneg hp.le _),pow_succ] at p; nlinarith -- match `le_inv`. 
variable (v':ℕ→ℕ)(x':ℕ→ℝ)
structure Season (w:ℕ) (x:ℝ)(m:ℕ) where
 out:Month x a i p N0 V W
 ht: out.q ≤ ((seat_u V J x N0)*N).val
 F:ℕ→ℝ→ℝ
 G:ℕ→ℝ→ℝ
 Q:Valley V q J a h N0 p Ta w F G
 alive: leash x m (F 0)
 worth: leash x m (G 0)
 act:ℕ→ℝ
 X: Vestal (seat_u V J x N0*N) B R.L
 S:Cape (seat_u V J x N0*N) B R.L
 pay: Charted V a p i N0 w J q F G out _ ht act S X (h:=h)
variable (u:0<a)(zZ0:2 ≤ p)(zZ1:6 ≤ i)
include u zZ0 zZ1
lemma plan_A : ∃ x:ℕ→ℝ,(∀ i,x' i < x i) ∧ Tendsto x atTop atTop ∧ ∀ i',Nonempty (Season V a p i N0 q J h Ta (v' i') (x i') i'):=by
 have he(j:ℕ):∃ x:ℝ,max (x' j) (j:ℝ)<x ∧ Nonempty (Season V a p i N0 q J h Ta (v' j) x j):=by
    obtain ⟨F,G,Q⟩:= niceV V q J a h N0 p Ta (v' j); obtain ⟨a1,w⟩:= Q.size 0 (by omega)
    obtain ⟨r,H⟩:= eventually_atTop.mp ((leadL j _ _ a1).and (leadL j _ _ w)); obtain ⟨t,p,b,Y⟩:= seed_p V a p i N0 (v' j) J q Ta F G zZ1 zZ0 u Q (max r (max (x' j) (j:ℝ))) -- order q duplicate
    let S:= seat_u V J t N0; let y:= seat_size V a _ _ _ b J Y.z -- maybe order q
    obtain ⟨X,Z,U,C⟩:= Y.calendar S (by change J.h ≤ J.h+_+_; omega) y; obtain ⟨i,k⟩:= H t ((le_max_left ..).trans p.le); exact ⟨t,(le_max_right ..).trans_lt p,⟨⟨b,y,F,G,Q,i,k,X,U,Z,C⟩⟩⟩
 choose Vw H hη using he; exact ⟨Vw,fun i=>(le_max_left ..).trans_lt (H i),tendsto_atTop_mono (g:=Vw) (fun i=>le_trans (le_max_right ..) (H i).le) tendsto_natCast_atTop_atTop,hη⟩ -- tune
end YM.CF.Py
