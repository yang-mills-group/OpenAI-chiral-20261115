import YM.CF.BProof.Rest.Thaw
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
-- suffix scheduling.These at all n meeting.Buyer settlement.
open Chaff Gloss Maize Tye RP RP.Str
open Brace
-- auxiliary sunrise: Hoist input as existing. variant all n.
variable {P:Realm V T' m n}{F0:(m:Side)→ Scroll m B (Brace.northZ m B)}
variable (F0) {Fp:ℝ→ℝ}{J:Robes N V W}
namespace Realm
variable {Z:Cape m B R.L}{R0 :ℝ→ℝ} {F:RankX→ℝ→ℝ}{c:ℝ}{b k:ℕ}{F0} (A:Hot P Z F0 Fp h)
local notation "νγ"=>hat R.L x
local notation "Xκ"=> (cell m B R.L)
namespace Act
variable (Q:Act P J h Z q b k Fp R0 F) (Θ:∀ i:ℕ, Parcel (cell m B R.L i))
-- upper suffix state needed lower application
abbrev TreasuryR(P:Realm V T' m n)(θ:∀ j:ℕ,Parcel (cell m B R.L j))(j:ℕ)(f:RankX→ℝ→ℝ)(h:ℝ)(k:ℕ):Prop:= tagK k j (θ j) P h f
include Q
structure Tonic (Q:Act P J h Z q b k Fp R0 F)(c:ℝ) :Prop where
 hot: Θ n=A.rootD (Θ n).βx
 hc: (Θ k).βx=c
 rise(j:ℕ)(u:k ≤ j)(v:j ≤ n): tagK k j (Θ j) P h F∧ matchedX (hat R.L x j) (Θ j).βx
 fee(j:ℕ): k ≤ j→ j<n→ |((Θ (j+1)).βx - P.β (j+1)) - ((Θ j).βx - P.β j)|≤ grant_B R.L (hat R.L x j)
 bond(j:ℕ): k ≤ j→ j<n→ pLink (P:=P) (q:=q) (Z:=Z) (J:=J) (R0:=R0) (k:=k) j (Θ (j+1)) (Θ j)
-- ensure Q captured
include Q
lemma tonic (hp:|c-P.β k|≤νγ k/16) : ∃ Ξ,Tonic A Ξ Q c:=by
 obtain ⟨W,z,p⟩:= Quest.sail _ (stroll A Q hp); have h:=Q.fee
 let L:= Q.cliff c; have hb(j)(u:k ≤ j)(v:j ≤ n): (W j).βx= L.aim z j:= (p.fee j u v).2
 refine ⟨W,?_,?_,fun j u v=>⟨(p.fee j u v).1, hb j u v ▸ Q.eligible c hp z u v⟩,?_, fun j u v=>p.anchor j u v ⟩
 · rw [p.orbit]
 · change (W k).βx=_; rw [hb k le_rfl (by omega),Air.aim_z]; change P.β k+(c-P.β k)=_; abel
 intro i u v; have hv:= Air.aim_s L i u z; have hx: (W (i+1)).βx- P.β (i+1)- ((W i).βx-P.β i)= guess_Q n L.W z i:=by rw [hb _ (by omega) (by omega),hb i u v.le,hv]; change _+(P.β (i+1)-P.β i)+_-_-_= _; abel
 rw [hx]; exact credits_q _ _ (fun i=>(L.hp i).le) _ _
end Act
end Realm
end Cupboard
end YM.CF.Py
