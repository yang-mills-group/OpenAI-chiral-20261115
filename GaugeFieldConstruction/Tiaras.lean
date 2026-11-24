import GaugeFieldConstruction.Pillars
import GaugeFieldConstruction.Gibber
set_option autoImplicit false
set_option maxHeartbeats 20000
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
open scoped ComplexOrder
variable {N:Side}{K : Teller SU.group}{R:Patch}{L:ChartRatio SU.group}
variable {P:Preparation}{l:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus l))
open YM.Gleam
open BProof.PricePort Gleam.clocks

namespace Papal
open Sour.SliceRoof Fock.Flux
-- Purchase preradius for P3board, same bias V, then *release* on history.
def Cash_T (V:Grace K R L)(d h:ℝ) :Prop:= ∃ a>0,∃ b>0,(∃ e>0,∃ c> (0:ℝ),1≤K.j ∧ ∀ (N:Side)(P:Aim N),P.toll V.f V.g V.F1 V.F2 → Reef.Cry P → ∃ F:Sour.Elm N Unit d e c,Sour.NearL F (fun _=> Moire.bloom P)∧ groupShape F) ∧ ∃ B:ℕ,(∀ N:Side,B≤ N.val → ∀ M:Male, ∃ Z:Sour.Elm N Unit d a b,Sour.NearL Z (fun _=>hemi_L N K.j M)∧groupShape Z ∧ pure_Rim Z) ∧ ∃ A D:ℝ,0<A∧0<D ∧ (1+(b+1/2))*D ≤ h ∧ ∀ {N:Side}, Kea.Pad K.j N→∀ (u:Seat N → SU.E)(M:Male)(c:ℝ),|c|≤1 → PurchB A D c (oneWarp (boardC N K.j M) (pinShift N K.j M) (tradew N u) c) ∧ PurchB A D c (star (onePeak (boardC N K.j M) (pinBack N K.j M) (tradew N u) c))
lemma order_T (V:Grace K R L)(p:1≤K.j):∃ e>(0:ℝ),∀ d:ℝ,0<d → d≤e→∀ᶠ h:ℝ in atTop,Cash_T V d h:=by
 obtain ⟨D,l,a,v,b,w,i,Q⟩:= hemi_q _ p
 obtain ⟨E,t,A,q,c,u,B⟩:= sides_T _ _ _ _ V.pos1.le V.pos2.le V.width1 V.width2
 obtain ⟨X,x,hX,hz,o⟩:= Excite_crown 1 _ p
 refine ⟨min D E,lt_min l t,fun d s f=>?_⟩; filter_upwards [eventually_ge_atTop ((1+(b+1/2))*x)] with h k
 exact ⟨a,v,b,w,⟨A,q,c,u,p,fun N=> B N _ s (f.trans (min_le_right ..))⟩,i,fun N i M=> (Q N i _ s (f.trans (min_le_left ..)) M).2.2,X,x,hX,hz,k,@fun N=> o⟩
local notation "Xq" s:max => Vale.hat P.R.L P.x s
lemma even_with (s i:ℕ) : Even (count Y s i).val:=by unfold count; let z:Side:= mesh (Y.ir i) P.R.L s; change Even (z.val*2 * P.block.val); exact Even.mul_right (even_two.mul_left _) _ -- tune
lemma mint_w (s i k:ℕ)(e:s≤ Y.uv k): let G:=gram Y s i k;let V:=G.J.P; V.toll P.V.f P.V.g P.V.F1 P.V.F2 ∧ Reef.Cry V:=by
 intro G V; let H:=(Y.voyage i).X (Y.uv k); have p:=H.pull.owns s e
 have t:InterestX P.W.C _ G.J:=p.taste ▸ ((P.W.arm ..).sound s)
 exact ⟨P.W.h1 ▸ P.W.h2 ▸ P.W.h3 ▸ P.W.h4 ▸ t.leanJ.1,t.ready⟩
lemma count_ages (B:ℕ): ∀ᶠ s in atTop,∀ i:ℕ, B≤ (count Y s i).val:=by
 let L:= P.R.L; have he: 1<L.val:= lt_of_lt_of_le (by decide) P.V.tallX
 filter_upwards [eventually_ge_atTop B] with s p i
 have hp : s ≤ L.val^s:=(Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_left (by omega) _)
 exact p.trans (hp.trans ((Nat.le_mul_of_pos_left _ (Y.ir i).property).trans (((Nat.le_mul_of_pos_right _ (by decide:0< (2:ℕ))).trans (Nat.le_mul_of_pos_right _ P.block.property)))))
lemma debit_eq (j i k:ℕ):
 let W:=gram Y j i k; let N:=count Y j i; let X:=Graph.past W; let u:=changeM P.U (1:Pane N) W.J.M
 ‖inner ℂ (mateK N) u‖ > 0 ∧ sod Y k j i = Fineness.gaugedBase P.L W.beta (More N) (P.V.L.H (Y.uv k-j))+ Real.log ‖inner ℂ (mateK N) u‖:=by
 intro G N X u; have he:P.U.roundZ ≤ N.val:=P.J.gran.trans ((Y.voyage i).ownership j).size; have hp:1 ≤ P.K.j:=by rw [P.kJ]; decide
 obtain ⟨hv,h,_⟩:= angle_pay G.J.M P.K.j P.U _ hp he P.dpos; exact ⟨norm_pos_iff.mpr hv,congrArg (Fineness.gaugedBase .. + ·) h⟩ -- increase text
abbrev offWall (j i k:ℕ)(U:Skye.Seat (count Y j i)→SU.E)(b:ℝ) := let N:= count Y j i; let M:=(gram Y j i k).J.M; wall (boardC N P.K.j M) (pinShift N P.K.j M) (tradew N U) b
abbrev offSeek (j i k:ℕ)(U:Skye.Seat (count Y j i)→SU.E)(b:ℝ) := let N:= count Y j i; let M:=(gram Y j i k).J.M; seek (boardC N P.K.j M) (pinBack N P.K.j M) (tradew N U) b
abbrev ØFlat (j i k:ℕ):= changeM P.U (1:Pane (count Y j i)) (gram Y j i k).J.M
abbrev ØCost (j i k:ℕ):ℝ:= ‖inner ℂ (mateK (count Y j i)) (ØFlat Y j i k)‖
lemma cosmos {j i k:ℕ}(t: Kea.Pad P.K.j (count Y j i)) (U:Skye.Seat (count Y j i) → SU.E): ∃ c:ℂ, ‖c‖ = ØCost Y j i k ∧ ∀ b:ℝ, acts (star (offSeek Y j i k U b)) (mateK (count Y j i)) = c • (ØFlat Y j i k):=by
 let M:=(gram Y j i k).J.M
 apply near_anchor (token_V t (by rw [P.kJ]; decide) M) (baseP t M) (Kea.cut_t _) (board_rank t M) (tradew _ U) (Cascade.tick_g U) _ _ _ (tickB _) -- tune
 exact sea_g (P.J.gran.trans ((Y.voyage i).ownership j).size) _ (guard0 P.dpos.le) _

lemma seasonal_m (p:Geometry P)(q:Spicing P): ∀ᶠ s in atTop,∀ i k:ℕ,(Y.voyage i).kick≤k → s≤Y.uv k → let D:= Fintype.card (Site (More (count Y s i))); receipt_P Y s i k * ØCost Y s i k ≤ Real.exp (2*saveZ (Xq s)*D) * ‖compensated P.U (gram Y s i k) (room Y s i)‖ :=by
 let X(s):=Xq s; filter_upwards [pressure_path Y p q,(stage_slope P.V P.x).eventually_gt_atTop 1] with s f t i k h v D; have ht:= f i k h v
 have g:X s^(-(1/10):ℝ) ≤ saveZ (X s):=by rw [saveZ,Rrp_out _ (X s) (zero_lt_one.trans t)]; exact Real.rpow_le_rpow_of_exponent_le t.le (by norm_num [gratuity])
 let K:= ØCost Y s i k; obtain ⟨u,S⟩:= debit_eq Y s i k; change 0<K at u; let R:=gram Y s i k; let F:=Fineness.gaugedBase P.L R.beta (More (count Y s i)) (P.V.L.H (Y.uv k-s)); let T:= Real.exp (2*saveZ (X s)*D); apply le_trans _ (mul_le_mul_of_nonneg_left (show Real.exp (sod Y k s i - X s^(-(1/10):ℝ)*sites (count Y s i)) ≤ _ from ht) (show 0≤ T from (Real.exp_pos _).le))
 change Real.exp (F+ _)* K≤ _; nth_rw 1 [←Real.exp_log u]; unfold T; rw [←Real.exp_add,←Real.exp_add,S]; apply Real.exp_monotone; have hx:sites (count Y s i)=(D:ℝ):=(sites_as_price ..).symm -- tune
 rw [hx]; change F+saveZ (X s)* D + Real.log K≤2*saveZ (X s)*D+(F+Real.log K-X s^_ * D);
 linarith only [mul_le_mul_of_nonneg_right g (Nat.cast_nonneg (α:=ℝ) D)]
end Papal
end LocalLimit
end Rate
end YM.CF.Py
end
