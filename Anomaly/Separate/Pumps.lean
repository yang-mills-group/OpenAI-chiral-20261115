import Anomaly.Separate.Seed
import Anomaly.Second.Strike
/-! Pump entries for the separate actors, based on Pose. Qualified on Hearth, extends Hold -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Swell
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre Vow
open RG Mew Rive Nor Hake MeasureTheory Bake Rue Salt
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Dial Paige Vault Rill
open Kennel
variable {C B L:Side}{X Y:SOp C}{o:Seat C}{a b c d v s t K' hτ qz:ℝ}{n l q j:ℕ}
variable {g:Odd L.val}{H:Pricing j L g (Thread j)}{e:ℝ}(P:Grasp H B e)
open Sault Leaf Vow.TreasuryFog
local notation "N"=> mid C B
variable (R:GramM (mid C B))(K:Scree.Loom (mid C B))
variable {k m:ℝ} {V:SOp (mid C B)} {i:ℕ}
local notation "zι"=> funde j R.J.M (mid C B)
local notation "zT"=> Moire.bloom R.J.P
variable {O: Site (mid C B)}{F':Bag (mid C B)}(f:Trunk (node O) V i a b e)
variable (u:Roof (mid C B) k e q K) (z:P.roundZ≤ (mid C B).val)
lemma downgrade (V:Soak o X a b d)(w:c≤a):Soak o X c b d:=by
 obtain ⟨F,W,T,v,h,u⟩:=V; refine ⟨F,W,T,v, le_trans ?_ h,u⟩; apply sum_le_sum; intro i _; apply mul_le_mul_of_nonneg_right _ (sum_nonneg fun j _=>sum_nonneg fun k _=> (T i).nonn j k); exact Real.exp_monotone (mul_le_mul_of_nonneg_right w (Nat.cast_nonneg _))
local notation "Rp"=> R.p
variable {c' ε μ a':ℝ}
abbrev spinPhys (K:Scree.Loom N)(B:BudgetPoint)(Y:SOp N)(o:Site N):phy N:= houseK B (offsetMask B.B o) (firePlate K Y)
local notation "SV"=> spinPhys K R.p V O
variable (p:DockPulse R.p K k e a' m c' 24 q)
-- rB threshold post cost no aperture yet.
include p f z
lemma spinHold (w:R.slip=0)(u:a' ≤ a)(v: Solo a' K' (funde j R.J.M N) e)(w':Solo a' K' (Moire.bloom R.J.P) e)
 (U:s+d+d≤c')(hs:0 ≤ s)(hd:0<d)(φ:Sectoral R.p q (scald R.p (Ione.head_L R.F)) m (s+d) c): let a:=treeEarnings 24 R.p c' m a' K' *b; let t:=2*(spanV R.p.B*d⁻¹*a*c); let Z:= t+(2:ℝ)⁻¹*(2*(spanV R.p.B*d⁻¹*t*c)); ∃ F:Bag (mid C B), Hold P R K q 24 (node O) m s (spinPhys K R.p V O) F (a+Z) (a+Z):=by
 have h:= (trimQ m p v w' (downgrade (o:=node O) (C:=N) f.pay u)).aft (Corona.halo_mono (show R.p.B ≤ 24*R.p.B from by omega) (le_refl _))
 rw [show spinPhys K R.p V O=houseK R.p _ _ from rfl]
 exact grab_hold P R K p.roof z w hs hd (Py.Rate.LocalLimit.Preparation.downFence (m:=0) h U) φ -- tune let
omit p f z
open Buffered StressExchange
include u f
lemma spinPoint (h:R.p.threshold≤ k)(q':i+q+10≤R.p.B)(ha:0≤a)(he:0<e): WindowTag (spinMark R.p K O V) O (R.p.B+12) (b+b)∧Contact K (offsetMask (R.p.B+12) O) (spinMark R.p K O V) (spinPhys K R.p V O):=by
 let T:=spinWindow O u he f h q' ha
 let Q:=pinMatrix R.p K (node O) V; have hu(i:Orbit N): spinPhys K R.p V O i=dg (Q i.1):=by
    unfold Q spinPhys; rw [pinMatrix_eval u he f h q' i,houseK]; by_cases g:i∈pingMask R.p (offsetMask R.p.B O)
    · rw [Set.indicator_of_mem g,Set.indicator_of_mem g]
    rw [Set.indicator_of_notMem g,Set.indicator_of_notMem g]; simp [dg,dyad]
 refine ⟨T,T.ticket,fun x=>?_,fun x=>?_⟩
 · rw [hu]; refine lift_v (pair_charge (pinMatrix_support u he f h q' x)) (modes_monotone (Corona.halo_mono (by omega) le_rfl))
 rw [hu]; exact (bra_eq _ (Cascade.plus_P N) (mateK N) (tickB N)).symm
omit u f
open Sonar Next.Rank.Spindle
variable {T: tableQ SU.group (More (mid C B)) ℂ}(t':Trunk (node O) V i a b e) (R':Knit V (node O) i e ε b μ qz R.p.order T)(L':mintQ ε μ e R.p.order)(G':FlowPrice v c R.p.order)
variable (r:Rules SU.group) (b':2*(i+1)<(More (mid C B)).val) (x:4*(i:ℝ)*R.p.threshold ≤ r.c)
local notation "s_"=> ((8*(i:ℝ)+1)*R.p.threshold)
abbrev tracePhys (K:Scree.Loom N)(B:BudgetPoint)(O:Site N)(V:SOp N):phy N:=fun x=> traceMeter B K O V x.1 • 1
include u t' R' L' G' r b' x
-- at s' (request sufficient offset). canopy trivial
lemma scalarHold (he:0 < e)(g:i+q+10 ≤ R.p.B) (p':R.p.threshold ≤ k)(y:s_≤v)(h:c*s_<ε) (g':0 ≤ s)(hv:0≤a): let U:=pozV (node O) R.p 24 (scalarPulse R.p K O V); let Q:= cashPoncho (traceB_cost R.p c (2*μ*b) i ‖rawQ V 1‖) s 24; Hold P R K q 24 (node O) m s (tracePhys K R.p O V) U Q Q:=by
 intro U Q
 refine ⟨⟨charm _ _ ?_ g',fun X h Y=> ?_⟩,fun i=>?_⟩
 · exact traceHerb R' L' G' r b' x u p' g t' hv he y h m (Porticus.temple 24 R.p _) (show R.p.B+12 ≤ 24*R.p.B from (by have hu:=R.p.B_pos; omega)) le_rfl
 · rw [← show giveB U X=_ from Finset.sum_apply ..,show giveB U=scalarPulse R.p K O V from offset_P ..]
   unfold scalarPulse tracePhys; rw [act_smul,act_smul,map_smul,act_one,act_one]
 rw [show giveB U=scalarPulse R.p K O V from offset_P ..]
 exact Leaf.ψX _ _ Leaf.ρX
omit u t' R' L' G' r b' x
lemma rise_hold {X:Bag N}{G:phy N}(T:Hold P R K q l (node O) m s G X a b)(p:a ≤ K')(t:b≤ v): Hold P R K q l (node O) m s G X K' v:= ⟨nestUp _ _ _ p t T.toNest,T.rank⟩
lemma scale_hold {X:Bag N}{G:phy N}(T:Hold P R K q l (node O) m s G X a b)(x:ℂ): Hold P R K q l (node O) m s (x • G) (x • X) (‖x‖*a) (‖x‖*b):= by
 refine ⟨nestScale _ _ _ x T.toNest,fun i=>?_⟩; unfold giveB; simp only [Pi.smul_apply, ← smul_sum] -- gives sum of firing, eval. tune
 exact Leaf.ψX _ _ (T.rank i)
end YM.CF.Swell
