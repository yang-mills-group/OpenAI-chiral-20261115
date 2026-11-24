import YM.CF.Esti.Penn
import YM.CF.Vol.Celt
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Psalm.Baton
import YM.CF.Palot.End
import YM.CF.Appel.Sat
import YM.Next.FLUCTUATIONS.Grants
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Folio.Wind
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Esti
open Siete
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG PhysicalNext.JointLoad Heir Next.Foundations AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD
open Ac
variable {c f:Side}(S:StepData c f){r v:ℕ}
open CF.Jet
local notation "G"=> SU.group
variable {S}{n:ℕ}{θ a b m x t w K C d:ℝ}
variable {K': Teller G}{A B:Stores S}{T:Tube G S}{V:Config G c}{U:Config G f}{k:S.Choices}{q:Chi}{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][Nonempty E]{x':E}
open AnalyticBridge.Annulus1AD Push.SectorMeasure.Oriented Pressure.Tube
variable {O:Stores S}{F: Forest S.ratio}{Y:LinkArray G (Frozen A x F)}{z:LogArray G (Active A x F)}{β Q γ D L M s:ℝ}{J:ChartRatio G}{P:Patch}
theorem blaze (P:Teller G)(Q:Patch)(h:Q.Branches P.bind G) (n j l:ℕ)(hn:3 ≤ n)(hj:2 ≤ j)(hl:l ≤18)(W:Push.Uniform.Before G P.top.width P.top.paths P.j P.bind n)(W':Push.Uniform.Before G P.top.width P.top.paths P.j P.bind (n+2))(q:Chi)(R:ChartRatio G)(hp:LocalRatio R) (w:ℝ)(hw:0<w)(hγ:0<γ) :∃ N:ℝ,1≤N∧∀ width ≥ N,∃ A B s:ℝ,0<A ∧ 0<B ∧0 < s ∧ ∀ᶠ x:ℝ in atTop, SafeX P Q R w γ width 0 j n x ∧∀ (β:ℝ), β∈Set.Icc (y G Q.L x/2) (2*y G Q.L x) → let t:= fiery G x Q.L; let Y:=B*Scales.p G Q.L x; let d:= width*t; 0<t ∧ 0<β ∧0<Y ∧wireP G (coupling β) d (A*t) A ≤ Y∧∀{c f:Side}(S:StepData c f)(U:Tube G S), Cert Q P S U x→∀ (Z O:Stores S)(F:Forest S.ratio)(V:Config G c)(k:S.Choices), sizedP G Q P S U F → Z.flags=RG.flags (temp x) V → MossX n l x Z F U V k A d t q ∧(0<O.shares→Packet O Z ((j+5)*radiusB x)→PointCharge U x w γ → ∀ Y':LinkArray G (Frozen Z x F),∀ z:LogArray G (Active Z x F), ‖z‖ ≤ Y→∀ (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E][Nonempty E](i:E→L[ℝ] Directions G c), ‖i‖ ≤ 1 → (∀ u:E, axl Z.flags (temp x • i u)=temp x • i u) → Allows n (grandP U Z O F x k q d Y' l z β R j s w (Vmove x V ∘ i)) 0 (Real.exp (-γ/8*(Scales.p G Q.L x)^2*O.shares))) :=by
 obtain ⟨N,hN,H⟩:=help P Q h hp w γ hw hγ; refine ⟨N,hN,fun width hy=> ?_⟩
 obtain ⟨A,B,C,D,M,L,u,m,K,s,hA,hB,hC,hD,hM,hL,hu,hm,hK,hs,hp⟩:= mintS P Q h n j l hn hj hl W W' q R hp w width γ 0 hw (zero_lt_one.trans_le (hN.trans hy)); refine ⟨A,B,s,hA,hB,hs,?_⟩
 filter_upwards [hp,H width hy 0 j n,payer Q n j w width C D M L u m K s hγ hD hL] with x ht hx hv; refine ⟨hx,fun β h=>?_⟩
 obtain ⟨h1,h2,h3,h4,H⟩:= ht.wear β h; refine ⟨h1,h2,h3,h4,@fun c f S T p A' O F V k u he=>?_⟩; obtain ⟨p1,p2⟩:=H S T p O A' F V k u he
 refine ⟨p1, fun z w v Y' q h E _ _ _ i j' hp=>?_ ⟩; apply Allows.mono (p2 w v hx Y' q h E i j' hp (latticeFieldEstimates O j x) fun i=> ?_) -- tune
 · exact hv S p.got A' O z F β ‹_›
 exact_mod_cast vault (O:=O) j (x:=x) (s:=i)
end YM.CF.Esti
