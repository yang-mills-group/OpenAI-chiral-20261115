import ForceSatin.Groove
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
-- sugar for joint WA.8 unscaled Wake.J.Any
open Tower Tapestry
namespace SwitchC
variable {t x:ℝ}{i j m m':ℕ} {A D:Horizon} {C C' : ℝ} {S S': Finset Cover}{N:Side}{K:Calibration}{J I:Type*}[DecidableEq J][DecidableEq I]
noncomputable abbrev coupler (A D:Horizon):Horizon:=⟨A.song ++ D.song,A.face++D.face,A.cabin++D.cabin,A.mask++D.mask⟩
omit [DecidableEq J] [DecidableEq I] in
private lemma boom (L R:List Bite):hex (L++R)=Bool.xor (hex L) (hex R):=by induction L with| nil=> cases q:hex R <;> simp [hex,q]| cons j L ih=> rw [List.cons_append,hex,ih,←Bool.xor_assoc,hex] -- assoc
lemma joined(h:LoPrice A t x S m)(p:LoPrice D t x S m'): LoPrice (coupler A D) t x S (m+m'):=by
 refine ⟨fun i a=> (List.mem_append.mp a).elim (h.plot i) (p.plot i), (by unfold coupler; simp [boom,h.even_,p.even_]), (by simp only [List.length_append]; exact Nat.add_le_add h.spin p.spin), (by simp only [List.length_append]; exact Nat.add_le_add h.face p.face), (by simp only [List.length_append]; exact Nat.add_le_add h.cabin p.cabin),(fun i a=>(List.mem_append.mp a).elim (h.on_lens i) (p.on_lens i)), (fun i a=>(List.mem_append.mp a).elim (h.stool i) (p.stool i)),(fun i a=>(List.mem_append.mp a).elim (h.mark i) (p.mark i)),fun i a=>?_⟩
 rcases List.mem_append.mp a with k|k
 · obtain ⟨z,v,t,u⟩:=h.eyes i k; exact ⟨z,List.mem_append_left _ v,t,u⟩
 obtain ⟨z,v,t,u⟩:=p.eyes i k; exact ⟨z,List.mem_append_right _ v,t,u⟩
lemma improve (p:LoPrice A t x S m)(a:S⊆S')(u:m≤ m'): LoPrice A t x S' m':= ⟨fun i v=> ⟨a (p.plot i v).1,(p.plot i v).2⟩,p.even_,p.spin.trans u,p.face.trans u,p.cabin.trans u,fun i v=> ⟨Finset.Subset.trans (p.on_lens i v).1 a,Finset.Subset.trans (p.on_lens i v).2 a⟩,fun i v=> ⟨Finset.Subset.trans (p.stool i v).1 a,(p.stool i v).2⟩,fun i v=> ⟨Finset.Subset.trans (p.mark i v).1 a,(p.mark i v).2.1,fun j h=> Finset.Subset.trans ((p.mark i v).2.2 j h) a⟩,p.eyes⟩
lemma bake_coupler (L:LinksC) : bakeFlag (coupler A D) L x=bakeFlag A L x * bakeFlag D L x:=by unfold bakeFlag coupler bakedC; simp only [List.map_append,List.prod_append,List.forall_mem_append]; split_ifs with h v t <;> first | tauto | (push_cast; ring)
lemma formed (A D:Horizon) : Frost x K (coupler A D)= Frost x K A*Frost x K D:=by
 funext m U; unfold Frost plotN; simp_rw [Pi.mul_apply]; unfold Buffered.scalar; rw [show softP x _ _=_ from bake_coupler _, show chartP _ _=_ from (?a)]; simp_rw [Algebra.smul_mul_assoc,one_mul,Algebra.mul_smul_comm,smul_smul]; -- arg order
 case a => show chartP (K.c m) (coupler A D).song=chartP (K.c m) A.song*chartP (K.c m) D.song; rw [coupler, chartP,List.map_append,List.prod_append]; rfl
 rfl
structure Tab (J:Type*) where
 w: J→ Horizon
 cover : Finset J
 tax : J→ℂ
abbrev ticket (s:Finset Cover) (t x:ℝ)(m:ℕ)(A:Tab J) := ∀ i∈A.cover, LoPrice (A.w i) t x s m
abbrev plusT (A:Tab J)(B:Tab I): Tab (J⊕ I):= ⟨Sum.elim A.w B.w,A.cover.disjSum B.cover,Sum.elim A.tax B.tax⟩
abbrev mulT (A:Tab J)(B:Tab I): Tab (J× I):= ⟨fun ⟨i,j⟩=>coupler (A.w i) (B.w j), A.cover×ˢ B.cover,fun ⟨i,j⟩=>A.tax i*B.tax j⟩
abbrev weightT(A:Tab J)(x:ℂ):Tab J:= {A with tax:= fun i=>x*A.tax i}
namespace Tab
variable {A:Tab J} {D:Tab I} -- overrides
local notation "pcm" => LoPrice
abbrev terms (A:Tab J):ℝ:=∑ i∈ A.cover,‖A.tax i‖
abbrev cookP (A:Tab J)(x:ℝ)(K:Calibration):= drier x K A.w A.cover A.tax
abbrev holds (K:Calibration)(x:ℝ)(A:Tab J):Prop:= CovCover K (cookP A x K)
theorem plus_ticket(p:SwitchC.ticket S t x m A)(h:SwitchC.ticket S t x m D): SwitchC.ticket S t x m (plusT A D):=by
 intro i a; cases i with
 | inl l=> exact p l (inl_mem_disjSum.mp a) -- positive
 | inr l=> exact h l (inr_mem_disjSum.mp a) -- indent
lemma mul_ticket(p:SwitchC.ticket S t x m A)(h:SwitchC.ticket S t x m' D): SwitchC.ticket S t x (m+m') (mulT A D):= fun ⟨i,j⟩ a=> joined (p i (mem_product.mp a).1) (h j (mem_product.mp a).2)
lemma weight_ticket(p:SwitchC.ticket S t x m A)(d:ℂ): SwitchC.ticket S t x m (weightT A d):= p
lemma plus_cost : (plusT A D).terms=A.terms+D.terms:=by unfold terms plusT; rw [sum_disjSum]; rfl
lemma mul_cost : (mulT A D).terms=A.terms*D.terms:=by unfold terms mulT; rw [sum_product]; simp_rw [norm_mul]; rw [sum_mul]; simp_rw [mul_sum]
lemma weight_cost (d:ℂ) : (weightT A d).terms= ‖d‖*A.terms:=by unfold terms weightT; simp_rw [norm_mul,←mul_sum]
lemma cook_plus : (plusT A D).cookP x K=A.cookP x K+D.cookP x K:=by unfold cookP plusT drier; rw [sum_disjSum]; rfl
lemma cook_mul : (mulT A D).cookP x K=A.cookP x K*D.cookP x K:=by
 unfold cookP mulT drier; rw [sum_product]; simp_rw [formed,mul_smul]; rw [sum_mul]; simp_rw [mul_sum]; apply sum_congr rfl fun i T=> sum_congr rfl fun j _=>?_ ; -- algebra.Algebra ℂ?
 rw [smul_mul_assoc,mul_smul_comm] -- check
lemma cook_weight (d:ℂ) : (weightT A d).cookP x K=d • A.cookP x K:=by unfold cookP weightT drier; simp_rw [smul_sum, mul_smul]
lemma thermal (A:Tab J)(p:SwitchC.ticket S t x m A)(y:ℝ): InTest K true S false (cookP A y K):= drier_word _ _ _ _ _ _ p
lemma holds_plus (p:holds K x A)(h:holds K x D): holds K x (plusT A D):=by unfold holds; rw [cook_plus]; intro i g U; simp only [Pi.add_apply,map_add]; rw [p i g U,h i g U]
lemma holds_mul (p:holds K x A)(h:holds K x D): holds K x (mulT A D):=by unfold holds; rw [cook_mul]; intro i g U; simp only [Pi.mul_apply,map_mul]; rw [p i g U,h i g U]
lemma holds_weight (p:holds K x A)(d:ℂ): holds K x (weightT A d):=by unfold holds; rw [cook_weight]; intro i g U; simp only [Pi.smul_apply,twist_scalar]; rw [p i g U]
-- reading on combination
abbrev issues (A:Tab J)(βm:ℝ) (w:HorizonLens→HorizonLens→ℝ)(y:ℝ):= ∑ i∈A.cover,A.tax i* Picker.colorWage w βm y (A.w i)
#print axioms cook_mul
#print axioms mul_ticket
end Tab
end SwitchC
end Moonlit
end Moon
end Papal
end LocalLimit
end Rate
end YM.CF.Py
