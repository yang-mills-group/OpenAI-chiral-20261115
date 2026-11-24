import YM.CF.Cloak.Tally
import YM.CF.Rill.Oboe
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Cloak
open Siete
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG PhysicalNext.JointLoad Heir Next.Foundations AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree Esti
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
open Forge Reine Rill
open Rill
local notation "m₀"=> SU.group.colorScale
section ages
open Rill Cay
variable (M: Monk G S){v' L a:ℝ} {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E](U:Monk G S→E)(F:Directions G c× ℝ→ E)
abbrev starsW := (fun v:Directions G c=> U (M.atop v x)-U (rough (M.atop v x) 0)) -- include x? need include or use explicitly
lemma sculpt (ha:0<a)(h:0<L)(p:0<β)(hv:coupling β*L/a ≤1)(hq:∀ᶠ i in 𝓝 (0:Directions G c),∀ t:ℝ,t∈ Set.Icc (-1:ℝ) 1→ U (rough (M.atop i x) (t•M.z))= F (i,t*coupling β*L/a))(Ht:∀ t:ℝ,|t|≤coupling β*L/a → Allows (n+2) F (0,t) C): let t:=coupling β*L/a; let X:=starsW (x:=x) M U; let G':=starsW (x:=x) (violet M) U
 Allows n X 0 ((2^n*t)*composeCost n C 1)∧Allows n (X+G') 0 (2*((2^n*t)^2*composeCost n C 1)):=by -- notations token missing space
 intro t X V; have ht:0<t:=div_pos (mul_pos (coupling_pos p) h) ha; obtain ⟨he,hk⟩:= rushP F C t n (fun u v=> Ht _ (v.trans_eq (abs_of_nonneg ht.le))) (by rw [abs_of_nonneg ht.le]; exact hv); rw [abs_of_nonneg ht.le] at he hk
 have hK: X=ᶠ[𝓝 0] fun y=>F (y,t)-F (y,0):=by
    filter_upwards [hq] with y v; have hm:= v 1 ⟨by norm_num,le_rfl⟩; have he:=v 0 (by constructor <;> norm_num); simp only [one_smul,one_mul,zero_smul,zero_mul,zero_div] at hm he; change U (M.atop y x)- U _= _; rw [←he,←hm]; rfl
 refine ⟨he.germ hK.symm,hk.germ ?_⟩; filter_upwards [hK,hq] with y h' k; have hp:= k (-1) ⟨le_rfl,by norm_num⟩; have hg:= k 0 (by constructor <;> norm_num); simp only [neg_one_smul,one_mul,neg_mul,neg_div,zero_smul,zero_mul,zero_div] at hp hg; change _=X y+ V y; rw [←h']; unfold t; rw [←hp,←hg]; rfl
end ages
section payoff
open Cay Vol
-- actual short unmasked loop for far. scalar assembly.L
variable {M: Monk G S}{r l:ℕ}
def keyX (A:RG.Atom G r)(x:ℝ)(s:Signed)(i: Site f)(M:Monk G S)(T:Tube G S)(β:ℝ)(q:Chi)(d:ℝ)(l:ℕ):= A.unmasked (pull s 0 (M.sent x T q d l β)) i
lemma crop_l (n l j:ℕ)(σ:ℝ)(t:0<σ)(P:Patch)(K K':ℝ)(h:0<K)(hv:0<K'):∃ r C:ℝ,0<r ∧0≤C ∧∀ᶠ x in atTop,∀ β∈Set.Icc (y G P.L x/2) (2*y G P.L x),∀{c f:Side}(S:StepData c f)(T:Tube G S), S.patch=P →∀ (M:Monk G S)(O:ℝ),0<O → O≤ K'*Scales.p G P.L x→‖M.z‖ ≤ O →∀ (q:Chi)(d:ℝ)(A: RG.Atom G j)(s:Signed)(i:Site f), MossX (n+2) l x M.key M.park T M.V M.k K d (fiery G x P.L) q → let U(z:Monk G S):= keyX A x s i z T β q d l; let X:=starsW (x:=x) M U; let V:=starsW (x:=x) (violet M) U; let t:=coupling β*O/r
 Allows n X 0 ((2^n*t)*composeCost n (C*A.budget σ) 1)∧Allows n (X+V) 0 (2*((2^n*t)^2*composeCost n (C*A.budget σ) 1)):=by
 let a:=m₀; have ha:=SU.group.colorScale_pos; obtain ⟨r,hp,H⟩:= coze (n+2) l P a K K' ha h hv; obtain ⟨L,hℓ,H0⟩:= plain (n+2) j a σ t ha.le; refine ⟨r,L,hp,hℓ,?_⟩
 filter_upwards [H] with x h β hb c f S T he M O ho hO hm q d A s i hM U X V t
 let Y:= repine T x M d l q r O; obtain ⟨ht,hl,hq⟩:= h β hb O ho hO; let tB(y):=A.unmasked (pull s 0 (Y y)) i
 apply sculpt M U tB hp ho ht hl ?_ ?_ -- tune duplicate
 · refine Eventually.of_forall fun z u _=>?_ ; unfold tB Y; rw [belt T x M d l q r O β u z hp.ne' ho.ne']; rfl
 intro v' hz; have hp':= (hq S T he M v' q d hm hM (hz.trans hl)).1; have hm' : FuelG _ Y (0,v') (n+2) a:=fun i=> ((hp' i).paid (le_of_eq (show ‖SU.group.mat _‖ = m₀ from Gauge.unitary_frob (SU.group.mat_mul_star _)))).mono (max_self a).le
 exact H0 _ _ (fuel_s hm' s) _ _
end payoff
end YM.CF.Cloak
