import ForceSatin.Comet
import YM.SU5.Hiro.Fresh
import YM.SU5.FiniteGaugeData.Tower.Baggage
import ForceSatin.Wallet
import ForceSatin.Ramp
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
-- genuine Mark polynomial & cost. Keep support and masks explicit; period registration asserted separately
variable {N:Side}{cN:Side}{r:Lattice.Ratio cN (More N)} (T:Tiling cN N r)
variable (S:Support (More N)){H₁:Bed} {Z:PathData SU.group}  {q:Clip} {η CS W t x β y:ℝ}
variable (R:Rules SU.group)(B:Z.Bounds q η CS W) (P₁:Attached H₁ Z)(L:Side)
variable {v' τ:ℝ}(M0:Floor H₁ q (More N) τ v') (O:Bid.Sworn H₁ (More N) SU.group)
open ProbabilityTheory
open Lifted Afterglow Satin Cygnet Loaves Horizons InnerProductSpace
open _root_.YM.Regis.Head
-- tan. build covariant matter pair & color path. actual replica estimators, phase winds paid at both
open FoliageP Lifted Loaves Horizons Afterglow.Tower
namespace Moonlit
-- public builders for the tensor optics. NB use Work.PointB convention. Not the interactive Ward certificate.
namespace SwitchC
namespace Garland
open CF.SU
variable {K:Calibration}{o:Cover}{S:Finset Cover}{m:ℕ}{x t:ℝ}
open Tapestry
namespace Terrace
section
-- finite sum straps. uniformly packed.
variable {I:Type*}{J:Type*}[DecidableEq J][DecidableEq I]
abbrev packT (A:Finset I)(F:I→ Tab J): Tab (Σ _i:I,J):= ⟨fun ⟨i,j⟩=> (F i).w j,A.sigma fun i=>(F i).cover,fun ⟨i,j⟩=>(F i).tax j⟩
lemma packed_stock (A:Finset I)(F:I→ Tab J): (packT A F).cookP x K=∑ i∈A,(F i).cookP x K:=by unfold packT Tab.cookP drier; rw [sum_sigma]
lemma packed_price (A:Finset I)(F:I→ Tab J): (packT A F).terms=∑ i∈A,(F i).terms:=by unfold packT Tab.terms; rw [sum_sigma]
lemma packed_ticket (A:Finset I)(F:I→Tab J)(p:∀ i∈A,SwitchC.ticket S t x m (F i)): SwitchC.ticket S t x m (packT A F):= fun ⟨i,j⟩ a=> p i (mem_sigma.mp a).1 j (mem_sigma.mp a).2
lemma pack_holds (A:Finset I)(F:I→Tab J)(p:∀ i∈A,Tab.holds K x (F i)): Tab.holds K x (packT A F):=by
 unfold Tab.holds; rw [packed_stock]; induction A using Finset.induction_on with| empty=> rw [sum_empty]; intro i g U; exact (map_zero _).symm| insert i S e ih=> rw [sum_insert e]; intro k g U; simp only [Pi.add_apply,map_add]; exact congrArg₂ _ (p i (mem_insert_self ..) k g U) (ih (fun i a=> p i (mem_insert_of_mem a)) k g U)
end
variable {V M:MaskShape}(W:List MaskShape)(N:Side)(A B:CSocket o)(F G:SpinSocket o) {U:Pane N} {d:ℝ}
-- two gauge insertions. mark truly pure gauge.
abbrev Terra (V M:MaskShape)(A B:CSocket o) := packT univ (fun i:Sage=> mulT (lensBeam V A i) (lensBeam M B i))
def checkLen (V M:MaskShape)(N:Side) (B B':CSocket o) (x:ℝ) (U:Pane N):ℝ:= if blink N [V] U ∧ blink N [M] U then inner ℝ (cropT N B x U) (cropT N B' x U) else 0
lemma terrify (p:UseLens A V x t S)(q:UseLens B M x t S): SwitchC.ticket S t x 2 (Terra V M A B):= packed_ticket _ _ fun i _=> Tab.mul_ticket (use_price _ _ p i) (use_price _ _ q i)
lemma price_ter (V M:MaskShape): (Terra V M A B).terms=(Fintype.card Sage:ℝ)*((Fintype.card Sage:ℝ)*Fintype.card Sage):=by unfold Terra; rw [packed_price]; simp_rw [Tab.mul_cost,cost_lens,sum_const,card_univ,nsmul_eq_mul]
lemma terra_pay (n:Side)(U:Fields (K.c n)): (Terra V M A B).cookP x K n U = (checkLen V M (K.c n) A B x U.1:ℂ) • (1:FC (Single (K.c n))):=by
 unfold Terra checkLen; rw [packed_stock,Finset.sum_apply,Finset.sum_apply]; simp_rw [Tab.cook_mul,Pi.mul_apply,lens_view,Algebra.smul_mul_assoc,one_mul,smul_smul]; split
 next h =>
    unfold spotC; simp_rw [if_pos h.1,if_pos h.2, EuclideanSpace.inner_eq_star_dotProduct, dotProduct]; push_cast; rw [Finset.sum_smul]; apply sum_congr rfl fun i _=>?_ ; change _=((↑(cropT (K.c n) B x U.1 i):ℂ)* _) • 1; rw [mul_comm]; rfl
 next h=>
    push Not at h; unfold spotC; by_cases p:blink (K.c n) [V] U.1; swap; · simp_rw [if_neg p]; simp
    simp_rw [if_neg (h p)]; simp
lemma terra_neutral : Tab.holds K x (Terra V M A B):=by
 intro i g U
 have he(F:MaskShape): blink (K.c i) [F] ((simultaneous g U).1) ↔ blink (K.c i) [F] U.1:= blink_gauge ..
 rw [terra_pay,terra_pay,twist_scalar,map_one]; apply congrArg (fun x:ℝ=> (x:ℂ) • _)
 unfold checkLen; by_cases p:blink (K.c i) [V] U.1∧ blink (K.c i) [M] U.1; · rw [if_pos p,if_pos (show _∧_ from ⟨(he V).mpr p.1,(he M).mpr p.2⟩),show (simultaneous g U).1= gauge g U.1 from rfl,crop_cov,crop_cov]; exact StressFlux.inner_adjoint ..
 rw [if_neg p,if_neg ((and_congr (he V) (he M)).mp.mt p)]
-- mixed Ĉ. explicit representation convention. 
abbrev Cross := SU.group.Color →ₗ[ℝ] Op SU.Slot
def equivariant (C:Cross):Prop:= ∀ x (g:SU.E), C (SU.group.adjoint g x)= twist (SU.matter g) (C x)
abbrev unionBill (A:CSocket o)(M:MaskShape)(F G:SpinSocket o)(C:Cross):=packT univ (fun i:Sage=>mulT (lensBeam M A i) (spinBeam W F G (C (f0 i))))
lemma crossover (p:UseLens A V x t S)(u:UsePair F G S x)(r:∀ i∈W,UseMask i S x t)(C:Cross): SwitchC.ticket S t x 3 (unionBill W A V F G C):= packed_ticket _ _ fun i _=> Tab.mul_ticket (use_price V A p i) (spin_price W F G u r _)
abbrev crossTax (X:Cross):ℝ:= ∑ i:Sage, (Fintype.card Sage:ℝ)*(Fintype.card Teeth*‖X (f0 i)‖)
lemma cross_cost(X:Cross):(unionBill W A V F G X).terms≤crossTax X:=by unfold unionBill; rw [packed_price]; unfold crossTax; exact sum_le_sum (fun i _=>by rw [Tab.mul_cost,cost_lens]; exact mul_le_mul_of_nonneg_left (spin_cost ..) (by positivity))
noncomputable def checkBoth (V:MaskShape)(W:List MaskShape)(N:Side) (B:CSocket o) (F G:SpinSocket o) (x:ℝ)(C:Cross)(U:Pane N): FC (Single N):= if blink N [V] U ∧ blink N W U then PairBud N F G (bindN N U F G (C (cropT N B x U))) else 0
lemma tenderS (X:SU.group.Color): X=∑ i:Sage, X i • f0 i:=by apply PiLp.ext; intro i; simp only [WithLp.ofLp_sum,Finset.sum_apply,WithLp.ofLp_smul,Pi.smul_apply,smul_eq_mul, f0,PiLp.single_apply]; rw [sum_eq_single i]; simp; intro j _ x; simp [Ne.symm x]; simp
private lemma magistrate (X:SU.group.Color)(C:Cross)(U:Pane N): ∑ i:Sage,(X i:ℂ) • PairBud N F G (bindN N U F G (C (f0 i)))=PairBud N F G (bindN N U F G (C X)):=by
 let Y:Op SU.Slot→ₗ[ℂ] FC (Single N):= {
    toFun:= fun p=>PairBud N F G (bindN N U F G p)
    map_add' a b:= by unfold PairBud bindN; simp_rw [mul_add,add_mul,Matrix.add_apply,add_smul,sum_add_distrib]
    map_smul' a b:= by unfold PairBud bindN; simp_rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, Matrix.smul_apply, smul_eq_mul,RingHom.id_apply,Finset.smul_sum, mul_smul] }
 let Z:= (Y.restrictScalars ℝ).comp C; -- instead use Y.sum.Scalar.
 change ∑ i:Sage,(X i:ℂ) • Y (C (f0 i))= Z X; rw [show Z X= _ from congrArg Z (tenderS X),map_sum]; apply sum_congr rfl fun i _=>?_ ; rw [map_smul]; rfl -- coercion matrix.real smul not defeq L?
lemma cross_pay (n:Side)(U:Fields (K.c n))(C: Cross): (unionBill W A V F G C).cookP x K n U = checkBoth V W (K.c n) A F G x C U.1:=by
 unfold unionBill checkBoth; rw [packed_stock,Finset.sum_apply,Finset.sum_apply]; simp_rw [Tab.cook_mul,Pi.mul_apply,lens_view,spin_view,Algebra.smul_mul_assoc,one_mul]
 by_cases h: blink (K.c n) [V] U.1∧ blink (K.c n) W U.1; · unfold spotC; rw [if_pos h]; simp_rw [if_pos h.1,if_pos h.2]; exact magistrate ..
 · rw [if_neg h]
   push Not at h; unfold spotC; by_cases p:blink (K.c n) [V] U.1; swap; · simp_rw [if_neg p]; simp
   simp_rw [if_neg (h p)]; simp
lemma cross_neutral(C:Cross) (p: Terrace.equivariant C): Tab.holds K x (unionBill W A V F G C):=by
 intro i g U
 have he(F:List MaskShape): blink (K.c i) F ((simultaneous g U).1) ↔ blink (K.c i) F U.1:= blink_gauge ..
 rw [cross_pay,cross_pay]; unfold checkBoth; by_cases t:blink (K.c i) [V] U.1∧ blink (K.c i) W U.1; swap; · rw [if_neg t,if_neg ((and_congr (he [V]) (he W)).mp.mt t),map_zero]
 rw [if_pos t,if_pos (show _∧_ from ⟨(he _).mpr t.1,(he _).mpr t.2⟩),show (simultaneous g U).1= gauge g U.1 from rfl,crop_cov,p,bind_cov]; exact (PairBud_turn ..).symm
-- comparison tensor as PB.4. color ∑ALL families, grade5 target direct legal r c, Weyl matrix still requester. **NOT** N Force witness or Real perturbation charge. explicit dMatter-Schedule.
abbrev witnessGaugeKernel : Cross := (Complex.I:ℂ) • CF.Hiro.walkC
lemma witnessGenerator(x:SU.group.Color): witnessGaugeKernel x=SU.dMatter (SU.group.colorMat x):=by unfold witnessGaugeKernel; rw [LinearMap.smul_apply,CF.Hiro.walk_price,smul_smul]; simp
lemma witness_equiv : Terrace.equivariant witnessGaugeKernel:=fun x g=>by unfold witnessGaugeKernel; rw [LinearMap.smul_apply,LinearMap.smul_apply,CF.Hiro.walk_rotate,twist_scalar]
#print axioms terrify
#print axioms terra_pay
#print axioms cross_pay
#print axioms cross_neutral
end Terrace
end Garland
end SwitchC
end Moonlit
end Moon
end Papal
end LocalLimit
end Rate
end YM.CF.Py
