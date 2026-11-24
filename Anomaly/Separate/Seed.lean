import Anomaly.Separate.Roses
import Anomaly.Basis.Brush
import Anomaly.Signal
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Swell
open Function NormedSpace Filter Metric Finset Lattice MeasureTheory RG
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Classical Kronecker
open Cube Lat Tenant Tulip Spire Scroll Scree Jet Skye Pastry Dial Fock Branch Drapes Rill Sour
open Nacre Next.Rank.Spindle Sonar LampP Exterior Precision Wilson
open Pressure Vow Nor Hake Rue Salt TreasuryFog Vow.TreasuryFog
open scoped Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {N:Side}{j c:ℕ}{B:BudgetPoint}{Y:SOp N}{q:ℕ}{K:Scree.Loom N}{o:Site N}{v f α C M d a b w s:ℝ} {T:tableQ SU.group (More N) ℂ}
local notation "Q"=>tangD N
local notation "V_"=>node o
local notation "U_"=>traceMeter B K o Y
local notation "P_"=>halo q {node o}
local notation "H_"=>halo B.B {node o}
variable (R:Knit Y (node o) q d α M C w B.order T)(L:mintQ α C d B.order)(G':FlowPrice v f B.order)
variable (r:Rules SU.group) (c':2*(q+1)<(More N).val)(t:4*(q:ℝ)*B.threshold≤r.c)
local notation "s_"=> ((8*(q:ℝ)+1)*B.threshold)
local notation "S_"=> Jet.composeCost B.order (2*(2*C*M)*(f*s_)^2) 1
variable {j₀:ℕ} (J:Roof N s d j₀ K)(u:B.threshold ≤ s)(g:q+j₀+10≤ B.B)
variable (P:Trunk (node o) Y q a b d) (hv:0≤a)(ha:0<d)
include R L G' r c' t J u g P hv ha
abbrev traceB_cost (B:BudgetPoint)(f A:ℝ)(q:ℕ)(u:ℝ):ℝ:= let v:=(8*(q:ℝ)+1)*B.threshold; (B.order+1:ℝ)*(Jet.composeCost B.order (2*A*(f*v)^2) 1+u)
abbrev scalarPulse {p:Side}(B:BudgetPoint)(K:Scree.Loom p)(o:Site p)(Y:SOp p) (x:Orbit p): FC (Dwell p):= traceMeter B K o Y x.1 • 1
open Sault
attribute [local instance] loreM loreN
lemma traceHerb (h:s_≤v)(z:f*s_<α)(m:ℝ)(X:Aura N)(x:B.B+12 ≤ j*B.B) (wX:halo (j*B.B) {node o}⊆X.val): Herb B j₀ X m (scalarPulse B K o Y) (traceB_cost B f (2*C*M) q ‖rawQ Y 1‖):=by
 have hp:= G'.size; have ht:= B.threshold_pos; have hz:0 ≤2*C*M:= (R.circle (0:Q) (by rw [norm_zero]; exact L.1)).nonneg; have hf:0< s_:=by positivity
 have u₀: 0 ≤ traceB_cost B f (2*C*M) q ‖rawQ Y 1‖:=by unfold traceB_cost Jet.composeCost; dsimp only; positivity
 refine ⟨u₀,fun X' L' D hD vD=>?_,fun _ _ _ _ _=>rfl⟩
 have ht₁: Continuous (fun V:Op (Single N)=>Matrix.trace V):=by fun_prop
 refine ⟨⟨(Continuous.smul (f:=id) (g:=fun (_:ℂ)=> (1:FC (Dwell N))) continuous_id continuous_const).measurable.comp ((ht₁.measurable.comp (pinMatrix_env J ha P u g hv).1).comp measurable_fst),fun i=> Fock.Sector.one.scale _,fun Xx y xp q t e=>?_ , fun i t e=>?_⟩,?_⟩ -- tune
 · unfold scalarPulse traceMeter
   rw [(pinMatrix_local J ha P u g) _ _ (agrees_mono t (Finset.coe_subset.mpr ((inspect_fits ..).trans ((Corona.halo_mono x le_rfl).trans (Subset.trans wX L')))))]
 · unfold scalarPulse traceMeter; rw [sauce,singT,win_c,win_i,twist_scalar,map_one,show pinMatrix _ _ _ _ _= _ from pinMatrix_gauge J ha P u g i t,trace_twist]; rfl
 let Kz:= AuraOp.sat (P:=B) (X:=X') (D:=D) m (fun i:Orbit N=>traceMeter B K o Y i.1) (1:FC (Dwell N)) (Ark.one _) u₀ (fun i xp W L₁=> Rue.bare_p _ _ (hiresQ R L G' r c' t J u g h z i _ _ W ((Corona.halo_mono (by omega:B.B≤ j*B.B) le_rfl).trans (Subset.trans wX L')) xp))
 rw [mul_one] at Kz; exact Kz.pay
end YM.CF.Swell
