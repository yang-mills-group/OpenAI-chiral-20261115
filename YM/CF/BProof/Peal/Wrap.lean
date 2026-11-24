import YM.CF.BProof.Peal.Woven
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
open Chaff Gloss Maize Tye RP RP.Str Brace
-- avoid macro in variable
variable {Lall:ℕ}{G:RankX→ℝ→ℝ}{F0:(m:Side)→Scroll m B (Brace.northZ m B)}
variable (Q:Y.wish.Ship v Θ)(δ:∀ j:ℕ,Wheels (cell m B R.L j) Lm R)(A:Hot P Z F0 Fp h)(H:Act P J h Z q Lall k Fp V' G)
local notation "μd_" i:max=> mu_e η F x R.L k i
-- Offset.Y.B not encoded in torus state masks.D.SO.
include Q
structure Cloth (Ξ:∀ i:ℕ, Parcel (cell m B R.L i))(l:ℕ) : Prop where
 top: Realm.Act.Tonic A Ξ H (Θ k).βx
 pay(j:ℕ):l ≤ j → j ≤  k → Peered Q j k (Ξ j)
 vent(j:ℕ): l ≤ j → j<k → Link Q δ k j (Ξ j) (Ξ (j+1))
variable (h0:dleaf R.L (hat R.L x k)+G none (hat R.L x k) ≤ F (hat R.L x k)/4) -- no local notation!
include h0 H
open Journey
lemma basis_e(l:ℕ)(p:l ≤ k) : ∃ Ξ,Cloth Q δ A H Ξ (k-l) :=by
 induction l with
 |zero=>
   have h:= H.fee; have hx: |(Θ k).βx-P.β k|≤ (νγ k)/16:=by rw [beta Q (by omega)]; exact βapprox _ v Y.hot.pos
   obtain ⟨Ξ,f⟩:= Act.tonic A H hx; refine ⟨Ξ,f,fun j l z=>?_,fun j l z=>by omega⟩
   rw [show j=k from by omega]
   have h1:= (f.rise k le_rfl (by omega)).1; unfold Act.tagK at h1; rw [H.low] at h1
   exact start Q (by omega) (leaf Q _ (by omega)) h1 f.hc.symm (by linarith)
 |succ l ih=>
   obtain ⟨Ξ,r⟩:= ih (by omega); have h:=H.fee; let i:= k-(l+1); have hi:i+1=k-l:=by unfold i; omega
   obtain ⟨X,u,mY⟩:=regain Q δ (i:=i) (by omega) (by omega) (r.pay (i+1) (by omega) (by omega)); let L:=update Ξ i X; have hl(j)(t:i< j):L j=Ξ j:= Function.update_of_ne t.ne' ..; have hx:L i=X:=Function.update_self ..; let C0:=r.top
   refine ⟨L,⟨?_,?_,?_,?_,?_⟩,fun j (l':i ≤ j) q=> ?_,fun j (h:i ≤ j) q=> ?_⟩
   · rw [hl n (by omega)]; exact C0.hot
   · rw [hl k (by omega)]; exact C0.hc
   · intro j u v; rw [hl j (by omega)]; exact C0.rise j u v
   · intro j u v; rw [hl j (by omega),hl (j+1) (by omega)]; exact C0.fee j u v
   · intro j u v; rw [hl j (by omega),hl (j+1) (by omega)]; exact C0.bond j u v
   · rcases eq_or_ne j i with p|p; subst j; rw [hx]; exact u
     rw [hl j (by omega)]; exact r.pay j (by omega) q
   rw [hl (j+1) (by omega)]; rcases eq_or_ne j i with p|p; subst j; rw [hx]; exact mY
   rw [hl j (by omega)]; exact r.vent j (by omega) q
theorem lace : ∃ Ξ, Cloth Q δ A H Ξ 0:=by simpa only [Nat.sub_self] using basis_e Q δ A H h0 k le_rfl
omit h0 Q H
variable {Q A H δ} {Ξ:∀ i:ℕ, Parcel (cell m B R.L i)}
namespace Cloth
variable (D:Cloth Q δ A H Ξ 0)
include A H Q D -- conflicts omitted h0 deps?
lemma affordable{j:ℕ}(u:j ≤  k): ShiftQ (T'.a j) h (mu_e η F x R.L k j+dleaf R.L (hat R.L x j)) (Ξ j):=toll Q (by have hp:= H.fee; omega) (D.pay j (Nat.zero_le _) u)
lemma common{j:ℕ}(u:j ≤ k): (Ξ j).βx=(Θ j).βx:=(D.pay j (Nat.zero_le _) u).1.common.symm
lemma matchedX{j:ℕ}(v:j ≤  n):matchedX (hat R.L x j) (Ξ j).βx:=by by_cases u:j ≤ k; rw [D.common u]; exact Journey.matched Q v; exact (D.top.rise j (by omega) v).2
lemma lot{j:ℕ}(v:j ≤ n):∃ t, ShiftQ (T'.a j) h t (Ξ j):=by by_cases u:j ≤ k; exact ⟨_, D.affordable u⟩; exact ⟨_, FundingL.tollR (D.top.rise j (by omega) v).1 le_rfl⟩
end Cloth
end Tide
end Shell
end Realm
end Cupboard
end YM.CF.Py
