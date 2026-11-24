import YM.CF.BProof.Rest.Dog
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
open Lich.Muster Lor
open Jet Vol Rel
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Haro Nor Siete PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir
open Footprint Jade Py
open YM.CF.Floral Ione Haro Beau Oise Larch Lilt Vow
open scoped YM.CF.Mew
namespace Cupboard
variable {K:Teller SU.group}{R:Patch}{L:ChartRatio SU.group}{V:Grace K R L}{N B:Side}{d x:ℝ}{U:Grasp V.U B d}{W:GivenX V U}{q:Chi}{e a h γ w:ℝ}{order power:ℕ}
-- Bough spine geometry keeps Hue, lifts genuine fields. h rt fixed at hq; no size when comparing l0 theta step. Spans Estimate. Need access S.ρ uniforms.
open Bake PushA Episode Salt
variable {m:Side}{hx N0 n:ℕ}{T': Month x a order power N0 V W}
namespace Realm
variable {P:Realm V T' m n}
local notation "νγ"=>hat R.L x
local notation "Xκ"=> (cell m B R.L)
local notation "Lr"=>dleaf R.L
variable {J:Robes N V W}{Z:Cape m B R.L}{F R0 R1 ψ:ℝ→ℝ}{ρ:ℕ→ℝ}{η αP:ℝ}{Lm:ℕ}
namespace Shell
variable (Y:Shell P q Z J h F R0 R1 ψ ρ η αP Lm)
open FundingL Day
variable {Y} {v: StarPS n}{Θ:∀ j,Parcel (cell m B R.L j)}
namespace Tide
variable {V' Fp:ℝ→ℝ}{k:ℕ}
abbrev mu_e (η:ℝ)(F:ℝ→ℝ)(x:ℝ)(L:Side)(k i:ℕ) := η^(k-i)*(F (hat L x k)/4)
local notation "μd_" i:max => (mu_e η F x R.L k i)
include Y
lemma mu_c (k:ℕ){i:ℕ}(u:i≤ k) : let v:=mu_e η F x R.L k i; 0< v∧ v≤ F (νγ i)/4:=by
 let L:=F (νγ k); have hL:0< L/4:= (Y.leafP k).trans_le (Y.hotF k); have ht:= Y.hot.rat
 intro v; unfold v mu_e; refine ⟨mul_pos (pow_pos ht _) hL,?_⟩; exact (mul_le_of_le_one_left hL.le (pow_le_one₀ ht.le (Y.hot.disc.trans (by norm_num)))).trans (by linarith only [(Y.expense u).2])
lemma desc {i:ℕ}(p:i<k) : μd_ i=η* μd_ (i+1):=by unfold mu_e; rw [show k-i=k-(i+1)+1 from by omega,pow_succ']; ring
omit Y
variable (Q:Y.wish.Ship v Θ) (δ:∀ j:ℕ, Wheels (cell m B R.L j) Lm R)
local notation "ΩR"=> Journey.H Q
abbrev Peered (Q:Y.wish.Ship v Θ)(i k:ℕ)(b:Parcel (cell m B R.L i)) := Duel (T'.a i) (Θ i) b h (mu_e η F x R.L k i)∧ ∃ c:ℝ, Keel K.j (P.ref i) b h c c R
abbrev Link (k i:ℕ)(l:Parcel (cell m B R.L i))(u:Parcel (cell m B R.L (i+1))):Prop:=∃ A:SpaceM,∃ c:ℝ,(T'.a i).threshold^2*|c|≤ αP* mu_e η F x R.L k (i+1) ∧ dist A (Journey.H Q i)≤2* R1 (νγ i)*(4*mu_e η F x R.L k (i+1)/F (νγ i))∧ ‖A‖ ≤ R1 (νγ i) ∧ StepEq A u (P.ref (i+1)) U (Z i) (Z (i+1)) (P.A i) (P.S i) q J.d ((δ i).val.PiZ (T'.a i) c) (P.astr i l)
include Q Y
open Journey
variable {t c:ℝ}
lemma start {b:Parcel (cell m B R.L k)} (L:k≤n)(u:TopK P h k (Θ k))(p:Laurel (colour (P.ref k) b) K.j h c c R.L.val)(hB:(Θ k).βx=b.βx)(w: c+Lr (νγ k) ≤ F (νγ k)/4): Peered Q k k b:=by
 have he:= tollR (p0:=show Provides R.L K.j (P.astr k b) h c none from p) le_rfl; have hc:= tollR (q0:=none) u le_rfl; refine ⟨⟨hB,Books.mono (Books.sub he.reg hc.reg) ?_, Pressed.mono (Pressed.sub he.force hc.force) ?_⟩,c,laurel_k p⟩ <;> simpa [mu_e] using w
lemma toll{j:ℕ} {b:Parcel (cell m B R.L j)} (p:j≤n)(q:Peered Q j k b): ShiftQ (P.ref j).p h (μd_ j+ Lr (νγ j)) b:= budD (Y:=P.ref j) _ _ q.1 (tollR (q0:=none) (leaf Q j p) le_rfl)
lemma regain {i:ℕ}{u':Parcel (cell m B R.L (i+1))} (p:i<k)(v:k≤n)(q:Peered Q (i+1) k u'):∃ l, Peered Q i k l∧ Link Q δ k i l u':=by
 let Z:= Y.book i (lt_of_lt_of_le p v); let x':= P.ref (i+1); let Bv:=Journey.document Q (lt_of_lt_of_le p v)
 have hx:= (Y.expense (show i ≤ i+1 from by omega)); have hξ:= mu_c (Y:=Y) k (i:=i+1) (by omega)
 have he:(Θ (i+1)).βx=u'.βx:=q.1.common; obtain ⟨c,g⟩:= q.2
 have hg:x'.p=(T'.a (i+1)):=rfl
 let G:= P.A i; let u1:BF P F h i:= ⟨u',⟨?_,?_,g.IonicX⟩, FundingL.keel_y rfl g⟩
 case refine_1=> change u'.βx ∈ Year R (νγ i); rw [←he]; exact (P.narrow (lt_of_lt_of_le p v)).mp (Journey.matched Q (by omega : i+1≤n))
 case refine_2=> exact FundingL.ShiftQ.mono_b (toll Q (by omega) q) (by linarith only [hx.2,hx.1, Y.hotF (i+1),Y.leafP (i+1),hξ.2])
 let Tψ:= μd_ (i+1); have he2:Tψ ≤ F (νγ i)/4:=hξ.2.trans (by linarith only [hx.2])
 have h0:Bv.val= Θ (i+1):= document_1 ..; obtain ⟨w,Y0,a,l,D,LQ,tQ⟩:= Z.mutualP Bv u1 (δ i) Tψ (FundingL.ShiftQ.mono_b (price Q (lt_of_lt_of_le p v)) (by linarith only [Y.hotF i,Y.leafP i])) (show Duel x'.p Bv.val u' h Tψ from h0 ▸ q.1) hξ.1 he2
 refine ⟨Y0,⟨?_,LQ⟩, Z.rot u1,w,a,?_,Z.radius u1,tQ⟩
 · rw [document_2 Q (lt_of_lt_of_le p v),desc (Y:=Y) p]; exact D
 rw [real_θ Q (lt_of_lt_of_le p v)]; exact l
end Tide
end Shell
end Realm
end Cupboard
end YM.CF.Py
