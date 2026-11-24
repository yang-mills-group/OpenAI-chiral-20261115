import YM.SU5.Relativistic.SpringCourt
import YM.SU5.Relativistic.Harvest
/-!
# soft pressure matched with massless. Applies on this very history. Retains
 affordability before gauge. No handwaving leading eigenweight.
-/
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
open Oath Feu Feu.Corset Nor
open Chaff Gloss Maize Tye RP RP.Str
open Brace
namespace Rate
open Pitching Focus CF.Mint
namespace LocalLimit
open Preparation
open Pannier
variable {P:Preparation}{l:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus l))
namespace Papal
open CF.Pannier.Damask
open Buffered
open Papyrus.GaugeFlux
open CF.Papyrus.Granat CF.Pannier.Chancel
variable {a δ κ:ℝ}
-- grant all regulations. Choose C independent of preparation (needed for election).
-- cohort d enough after all requests. Earning's scope.
def Lesion (s i k:ℕ)(h η d v:ℝ)(F:Mark (count Y s i)):Prop:=
 let I:= gram Y s i k
 let Y' := tickA (count Y s i)
 let H:= room Y s i
 ∀ x: Orbit (count Y s i), Yep h (acts (star (F (x.1,H x))) (mateK _)) (changeM P.U (H x) I.J.M)
    (Real.exp (crater Y' (spar P.K.j I.J.M (H x)) (η^2)+d+v*flakes I.p.threshold x.1))
def WealthF (C:ℝ):Prop := ∀ (b:ℝ),0<b→ b ≤1→∀ (N:Side)(M:Tulip.Male),IsStarProjection (spar 4 M (1:Pane N))→crater (tickA N) (spar 4 M (1:Pane N)) (b^2) ≤ seaPrec 4 N M+C*b*(N.val:ℝ)^4
theorem endowed :∃ C:ℝ,0≤C ∧ WealthF C:=soft_flat (by decide :1≤4)
variable {E C H ζ η:ℝ}
open Buffered.Afterglow.Journey
lemma lease_h (g: FairRoute P.P P.J P.h P.N0 Chi.canonical)(t:0≤ζ)(h:ζ ≤ P.h)(q: Inflation E P)
    (u:P.d ≤ δ)(x:∃ N:ℕ,∀ ξ>(0:ℝ),∃ γ>(0:ℝ),∃ w:ℕ,∀ n:Side,N ≤ n.val→ Winter P.K.j δ n γ w ξ)
    (p:WealthF C)(hx:0≤ C)(e:0<η)(v:η≤1) (ε K:ℝ)(hp:0<ε)(hv:0≤K) :
    ∀ᶠ s in atTop,∀ᶠ i:ℕ in atTop,∀ k:ℕ,(Y.voyage i).kick ≤ k → s ≤ Y.uv k →∀ F:Mark (count Y s i),∀ d:ℝ,Envelope F→ Lesion Y s i k ζ η d K F→‖compass Y i k s F‖ ≤ Real.exp (d+(C*η+ ε)*sites (count Y s i)):=by
 let a:=ε/2; obtain ⟨b,h₀,P'⟩:= frosts Y (pow_pos e 2) (pow_le_one₀ e.le v) u x a (half_pos hp)
 filter_upwards [P',scales_h Y g t h q a (b+K) (half_pos hp) (add_nonneg h₀ hv)] with s hs ht
 filter_upwards [hs,ht] with i u₀ l₀ k H J F d G V'
 let M:= (gram Y s i k).J.M; let n:= count Y s i; let N:= (More n); let L:= sites n
 let z:= d+(C*η + a)*L; let D:= spar P.K.j M (1:Pane n); let B:= tickA n
 have he: crater B D (η^2) ≤ seaPrec P.K.j n M + C*η*(n.val:ℝ)^4:=by
    have hw:IsStarProjection D:= (P.U.broadness _ (P.J.gran.trans ((Y.voyage i).ownership s).size) _).projection _ (guard0 P.dpos.le)
    unfold D at *; rw [P.kJ] at hw ⊢; exact p η e v n M hw
 have hm : (n.val:ℝ)^4≤ L:=by
    change _≤ (((n.val*2:ℕ):ℝ)^4); exact_mod_cast (Nat.pow_le_pow_left (show n.val ≤ n.val*2 by omega) 4)
 apply (l₀ k H J F z G _).trans (Real.exp_le_exp.mpr (le_of_eq (by change z + a*L = _; unfold z a L n; ring))) -- tuner
 intro y; apply Yep.weigh (V' y) _ t; apply Real.exp_le_exp.mpr; let U:= flakes (gram Y s i k).p.threshold y.1
 let f:= spar P.K.j M (room Y s i y)
 let r:=crater B f (η^2)
 have hu : r ≤ crater B D (η^2) + a*L+b*U:= u₀ k J y
 change r+d+K*U≤ seaPrec P.K.j n M+z+(b+K)*U; unfold z; nlinarith only [hu,he,mul_le_mul_of_nonneg_left hm (show 0≤C*η by positivity)]
lemma folderShare {s i k:ℕ} {X:Mark (count Y s i)} (η ε a d G:ℝ)(e:0<η)(p:η≤1)(z:0<ε)(g:ε ≤ 1)(hx:0 < a) (w:∀ y: Orbit (count Y s i),
    let f:= count Y s i
    let x:Orbit f:=y
    let U:= room Y s i x
    ∃ n:ℕ,∃ A B B' F F': Fin n→ FC (Single f), ∃ b:Bool,∃ k':ℕ,∃ L: List (Fin n),∃ C:FC (Single f),
        CF.Pannier.Chancel.Folder A B B' F F' b a ε (mateK f) (changeM P.U U (gram Y s i k).J.M) C ∧ JumpCost k' C∧ L.Nodup ∧
        X (x.1,U)= CF.Pannier.Chancel.fo (fun i=>together (A i) (B' i)) L*C∧ (η^2)⁻¹^(2*L.length+k')*(ε*(a+3))^L.length *‖C‖ ≤Real.exp (d+G*flakes (gram Y s i k).p.threshold x.1)) :
    Lesion Y s i k ((η^2)⁻¹*ε⁻¹) η d G X:=by
 intro x; obtain ⟨n,A,B,B',F,F',b,D,L,C,V,p₁,p₂,h,c⟩:= w x
 obtain ⟨X',Y'⟩:= safety Y s i k x
 have hv:=V.harvest z hx g X' (plus_P _) (tickB _) (pow_pos e 2) (pow_le_one₀ e.le p) p₁ Y' L p₂
 -- beta
 rw [h]; apply hv.weigh _ (by positivity); rw [add_assoc,Real.exp_add, mul_assoc, mul_assoc]; exact mul_le_mul_of_nonneg_left (by rwa [mul_assoc] at c) (Real.exp_pos _).le
end Papal
end LocalLimit
end Rate
end YM.CF.Py
#print axioms YM.CF.Py.Rate.LocalLimit.Papal.lease_h
#print axioms YM.CF.Py.Rate.LocalLimit.Papal.folderShare
#print axioms YM.CF.Py.Rate.LocalLimit.Papal.endowed
