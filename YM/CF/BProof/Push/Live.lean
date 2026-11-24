import YM.CF.BProof.Push.Beam
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Beau.PushA
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
open Jet Yaw Nor Prism Font Push.AbsoluteSums Wray
variable{n:Side} {P: BudgetPoint}{x y a b h c d:ℝ}{k' m:ℕ}
local notation "DN"=>tangD n
local notation "E'"=>SU.group
variable {X D Y Z:Support (More n)}{U:Pane n}
local notation "Ink" n=> Hake.Raid (Dwell n)
open Next.Foundations Push.Local AnalyticBridge.VerifiedReset Vow Rue
open Ione
local notation "N"=> P.order
local notation "Xo"=>Skye.Seat n
open Ione Larch
open Taxi Geo RG.PathData Next.Scheduling UVNext.PricedKernels Work.F03 WilsonStartup
local notation "Hz"=> Scree.Hub n
open Trees
open Iva Lilt Salt Palot Floral Sour Haro Tap Sour.BondL Mew
open scoped YM.CF.Mew
open Reef Taxi.Denn
structure Mint (P:BudgetPoint)(R:PathData SU.group)(q:Clip)(h σ C κ Γ:ℝ)(n: Side)(m L:ℕ) : Prop where
 day : Taxi.DayT P.order Γ
 ori : Taxi.OriK P.order κ
 p:∃ u,R.Bounds q σ C u
 nn: 1≤h
 ha:0≤Γ
 hc:0≤κ
 hw:Decent q P
 hp:Geo.Width P q σ
 hn:20*(m+10)< (More n).val
 hL:(P.supportExponent+1+1)/(P.B:ℝ)≤σ/8
 h6:m+6≤ P.B
 r: Rare R
 km:1<L
abbrev regC (P:BudgetPoint)(q:Clip)(σ C κ Γ:ℝ):=(tax_E P q σ C κ Γ+1)
abbrev actuator(P:BudgetPoint)(R: PathData SU.group)(q:Clip)(V:Ids n)(b:ℝ)(F:RegBudget n)(v:ℝ)(L:ℕ):Prop:=∀ x:Orbit n,FleetS P.threshold x.1→ let d:=aora P L F; exponentL P F x.1=(moldV n v+moldV n (R.inChannels q P b x.1-R.inChannels q P (b-d) x.1))+exponentL P (brol P R q L F) x.1+fuelV P (truce P R q L F V) x
variable {R:PathData SU.group}{q:Clip}{σ C Γ κ:ℝ}{L:ℕ}
namespace Mint
variable (g:Mint P R q h σ C κ Γ n m L)
variable (C0:Taxi.Denn.Cart n m)(a b:ℝ)(V:Ids n){u:ℝ}{F:RegBudget n}
include g
lemma grow (Q:Sweep n→Prop)(p:a=0∨∀ s,Q s→ C0.Turns s): let K:=CH P m Γ*(P.threshold^2*|a|); IncX Utrue (Er n a) P h K ∧ Ionic P L (C0.Sr a) ∧ IncX Q (C0.Sr a) P h K ∧ Heats P h (kδ P) (C0.Zr a) K ∧ aora P L (Er n a)=a :=by
 intro K; obtain ⟨t,w,z⟩:=usesCH P m Γ a g.ha; have h6:= g.h6; have hn:=g.hn; let b:=Er_full (n:=n) (h:=h) m P (by omega) a g.ha g.day
 refine ⟨?_, C0.S_spark P hn a h g.nn g.day _, ?_,Wallet.mono (C0.Z_paid P (by omega) a (kδ P) g.day g.ha (zero_le_one.trans g.nn) (by unfold kδ; linarith [P.exponent_pos])) z,alpha_δ P a (by omega) g.km (by omega)⟩
 · obtain ⟨u,v,h⟩:=b.weight; exact ⟨⟨u,v,fun i=> (h i).trans t⟩,b.face⟩
 have he:= C0.S_paid (h:=h) P (by omega) a g.ha g.day (fun _=>False) fun _ v=>v.elim; obtain ⟨u,v,Q_⟩:=he.weight; refine ⟨⟨u,v,fun i=>(Q_ i).trans w⟩,?_⟩; rcases p with rfl|p; · simp only [Cart.Sr_zero]; exact fun s t V l X W=> (map_zero _).symm
 exact (C0.S_paid (h:=h) P (by omega) a g.ha g.day Q p).face -- tune h metavars
lemma ready_A (p:IncX Utrue F P h u): Heats P h (kδ P) (truce P R q L F V) (glow_W P q σ C Γ u L) ∧ (ZealQ (truce P R q L F V)) ∧ IncX Utrue (brol P R q L F) P h (regC P q σ C κ Γ*u) ∧ Ionic P L (brol P R q L F) ∧ (∀ Y: Finset (Scree.Hub n),Haro.StackL (brol P R q L F) Y = Haro.StackL F Y) ∧ P.threshold^2 *|aora P L F| ≤ ‖Complex.reCLM‖*u ∧∃ v,actuator P R q V b F v L:=by
 obtain ⟨w,H⟩:= g.p; obtain ⟨W,t,u',k,x,i,f,hp,v,k0⟩:= α_ubK (b:=b) P R H κ Γ g.day g.ori g.ha g.hc g.hw g.hp (by have:=g.hn; omega) V g.nn g.hL (by have:=g.h6; omega) g.r F L p
 exact ⟨Heats.iff_anuk.mpr ⟨W,t,k⟩,u',x,i,f,(mul_comm ..).trans_le ((le_div_iff₀ (sq_pos_of_pos P.threshold_pos)).mp hp),v,k0⟩
-- offset: same gauge path, clip and support list. Real. It's important b_c not put into input; the subtraction works for all b.
end Mint
variable {F G:RegBudget n}{s t:ℝ}
lemma weaken (p:IncX Utrue F P h s):Books P F h s:=⟨p.weight,fun _ u=>u.elim⟩
lemma add_p{Q:Sweep n→Prop} (p:IncX Utrue F P h s)(v:IncX Q G P h t):IncX Q (F+G) P h (s+t):=⟨(Books.plus (weaken p) (show Books P G h t from ⟨v.weight,fun _ k=>k.elim⟩)).weight,fun i u V t X j=>(congrArg₂ (·+·) (p.face i trivial V t X j) (v.face i u V t X j)).trans (map_add ..).symm⟩
lemma congr_p {w:ℝ}(p:IncX Utrue F P h s)(v:IncX Utrue G P h t)(k:Books P (F-G) h w): IncX Utrue (F-G) P h w:= ⟨k.weight,fun i u V t X j=>(congrArg₂ (·-·) (p.face i trivial V t X j) (v.face i u V t X j)).trans (map_sub ..).symm⟩
lemma upE{w:ℝ}{Q:Sweep n→Prop}(v: IncX Q F P h s)(g:s≤w): IncX Q F P h w:=by obtain ⟨i,v',t⟩:=v.weight; exact ⟨⟨i,v',fun i=>(t i).trans g⟩,v.face⟩
lemma putZ(F G:RegBudget n)(p:∀ i,G i 1=0)(S:Finset (Scree.Hub n)): StackL (F+G) S= StackL F S:=by unfold StackL; simp_rw [Pi.add_apply,p,add_zero]
lemma aora_add (h1:1≤h)(p:IncX Utrue F P h s)(v: IncX Utrue G P h t)(L:ℕ): aora P L (F+G)=aora P L F+aora P L G:=by
 have ht:= aora_diff (addT P p v) v h1 L; rw [add_sub_cancel_right] at ht; rw [ht]; abel -- ht rw loops?
lemma regC_pos (P:BudgetPoint)(q:Clip)(σ C κ Γ:ℝ)(p:0≤κ): 0<regC P q σ C κ Γ:=by unfold regC tax_E fee_l cone_D; have ht:= Collection.turnFee_pos P; have hg:= mode_W P.order P.power; positivity
end YM.CF.Beau.PushA
