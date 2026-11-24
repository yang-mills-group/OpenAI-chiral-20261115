import YM.CF.Lor.Fire
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Lor
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
open Stilo Palot Scion Function Levier Hake Urn Peaks Fock Laic Branch Drapes
open Rush Scroll Paige Vault Phase Acorn Spire Eire
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Jet Lich Corne
open Lich.Muster
attribute [local instance] opCStarAlgebra
local notation "G₅"=> SU.group
open Pressure.Tube
open Vol
variable{c f N B:Side}{d n m l:ℕ}{a b K v v' u D D' κ τ τ' :ℝ}{p:BudgetPoint}{q:Chi}
-- common allowance-target category.Across any Horizon.S.True.N.Anchor.g
variable{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
open Fief
-- sharp thermo through V.M $coupling gains
variable(Q:Patch)(p':Teller G₅)(n l:ℕ)
variable (Z:ChartRatio G₅) (q:Chi)
local notation "κ"=> Jet.composeCost
def rumP(L:Side)(X:ℝ)(n d:ℕ)(a v x:ℝ):= (2^n*(2*Scales.g SU.group L x*v/a))^d * κ n X 1
lemma rust_k(θ m:ℝ):sizeK Q.L 1 (fun x=>rumP Q.L a n 1 θ (m*Scales.p G₅ Q.L x) x):=by
 simp_rw [rumP,pow_one,div_eq_mul_inv]
 let V:=(sizeK.main Q.L).scale 2; let W:= (sizeK.height Q.L).scale m; exact ((((V.tint W).tint (sizeK.mild Q.L _)).scale _).tint (sizeK.mild Q.L _)) -- tune
lemma thawZ (c C D s K L:ℝ)(h:0<c)(hp:0≤D)(hx:0<s)(v:4*s< Z.radius)(hZ:LocalRatio Z)(hv:0<K)(hl:0<L): ∃ a W:ℝ,0<a∧0≤W∧∀ᶠ x:ℝ in atTop, ∀ {N P:Side}(S:StepData N P)(T:Tube G₅ S),Cert Q p' S T x→T.up.Bounds T.high c C D →∀ A: Monk SU.group S,∀β∈ Set.Icc (y G₅ Q.L x/2) (2*y G₅ Q.L x),∀ v:ℝ,0 < v → v ≤ L*Scales.p G₅ Q.L x→ ‖A.z‖≤ v→∀ α d:ℝ,MossX (n+2) l x A.key A.park T A.V A.k K d (fiery G₅ x Q.L) q→∀ i:Site N, let X(y):=A.atop y x; let F(U:Monk SU.group S):=zenA T x q d α l U β Z s i; let p(k):=rumP Q.L W n k a v x
 Allows n (fun y=> F (X y)) 0 (p 1)∧ Allows n (fun y=>F (X y)+ F ((violet A).atop y x)) 0 (2*p 2):=by -- maybe Expected precedence newline
 let v':= SU.group.colorScale; let D':=max 1 v'; have hv':1 ≤ D':=le_max_left ..; obtain ⟨a,u,ha⟩:= coze (n+2) l Q 1 K L zero_lt_one hv hl; obtain ⟨C0,hC,hU⟩:= plain (n+2) 2 D' c h (zero_le_one.trans hv'); obtain ⟨Y,hY,hK⟩:=rub q (n+2) Z s hZ hx v
 let W:ℝ:=moon Q*Y+(about Q.L 0:ℝ)*(C0*D); have hW:0 ≤ W:=by unfold W moon; positivity -- tune cast
 refine ⟨a,W,u,hW,?_ ⟩; filter_upwards [ha] with x ha N P S T e p A β b v hg hk hw α d hz i X F p0
 let L(y'):= coupling β*y'/a; let H:= psiG T q l x s β Z i d; let U:= papS T A q l x a s v Z i d; obtain ⟨ht,hx',hv'⟩:= ha _ b _ hg hk; have he :0<L v:=div_pos (mul_pos (coupling_pos ht) hg) u
 obtain ⟨g,y⟩:= sculpt A H U u hg ht hx' (Eventually.of_forall fun y t _=> sprit T A q l x a s β v Z i d u.ne' hg.ne' t y) (show ∀ t:ℝ,|t|≤L v→ Allows (n+2) U (0,t) W from by
    intro z pz; let V:= repine T x A d l q a v; obtain ⟨l',o',t'⟩:= hv' S T e.got A z q d hw hz (pz.trans hx')
    have hx :FuelG _ V (0,z) (n+2) D':=fun i=> (l' i).paid (le_of_eq (show ‖SU.group.mat _‖=_ from Gauge.unitary_frob (SU.group.mat_mul_star _)))
    refine palm_s Q T A q (n+2) l x a s v Z i d (dustM Q T A q (n+2) l x a s v Z i d e.got hY.le fun i=> hK _ _ (t' i)) e.got (mul_nonneg hC hp) (fun s i=>kilo T (n+2) x p (fun i'=> (fuel_s hx s i').smooth) (fun A' u=>hU _ _ (fuel_s hx s) _ _) i hC)) -- tune
 rw [turnY T A q l x s β α Z i d e.funds.1 hZ] at g y; rw [turnY T (violet A) q l x s β α Z i d e.funds.1 hZ] at y
 have hp:0 < Scales.y G₅ Q.L x:=(by have hu:= b.2; linarith) -- shadow
 let t:=2*Scales.g G₅ Q.L x*v/a; have hx : L v ≤ t := (div_le_div_iff_of_pos_right u).mpr (mul_le_mul_of_nonneg_right (compare_v G₅ Q.L x b hp).1 hg.le); have hU:0 ≤ κ n W 1:=by unfold Jet.composeCost; positivity
 constructor; refine g.mono ?_; unfold p0 rumP; rw [pow_one]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hx (by positivity)) hU
 refine y.mono (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (mul_nonneg (show 0≤(2:ℝ)^n by positivity) he.le) (mul_le_mul_of_nonneg_left hx (by positivity)) _) hU) (by norm_num))
-- near absolute kite at every $phase point
lemma heat_w(s K L:ℝ)(hx:0<s)(v:4*s<Z.radius)(hZ:LocalRatio Z)(hp:0<K)(hl:0<L):∃ C:ℝ,0≤C ∧∀ᶠ x:ℝ in atTop,∀ (β:ℝ),β∈Set.Icc (y G₅ Q.L x/2) (2*y G₅ Q.L x) →∀ {c f:Side}(S:StepData c f)(T:Tube G₅ S)(M: Monk SU.group S), S.patch=Q → ‖M.z‖ ≤ L*Scales.p SU.group Q.L x →∀(d:ℝ), MossX n l x M.key M.park T M.V M.k K d (fiery G₅ x Q.L) q→∀ i:Site c,Allows n (fun y=>kite T x q d l (M.atop y x) β Z s i) 0 C:=by
 obtain ⟨C,h,H⟩:=rub q n Z s hZ hx v; refine ⟨moon Q*C,(by unfold moon; positivity),?_⟩; filter_upwards [tamper n l Q K L hp hl] with x p β b c f S T M hS Y d he i; let L:=Tarn.gate x M i; let U(j:M.zoo x)(y: Directions G₅ c):= ansC (S:=S) i j.val.val*Corne.flare T x q d l β Z s (M.atop y x) j
 have hv(j:M.zoo x): Allows n (U j) 0 C:= ((H _ _ (p _ b S T M hS Y q d he j)).smul (ansC (S:=S) i j.val.val)).mono (mul_le_of_le_one_left h.le (plant_v (w:=fun _:Fin (0+2)=>j.val.val)))
 refine ((summed L U (fun i _=>hv i)).mono (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr ((bed_count x i M).trans_eq (by rw [hS]))) h.le)).germ ?_
 filter_upwards with y; exact sum_subset (subset_univ L) (fun j _ p=>by unfold U ansC; rw [if_neg (fun v=>p (mem_filter.mpr ⟨mem_univ _,v⟩)),zero_mul])
end YM.CF.Lor
