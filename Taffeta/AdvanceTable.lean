import Taffeta.Est
import YM.SU5.FiniteGaugeData.Tower.Linearity
import Taffeta.Linen
import Taffeta.Quote
import Sparkle.Curvature
import Sparkle.Seed
import YM.CF.Buffered.StepIdentity
set_option autoImplicit false
set_option maxHeartbeats 2200000
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
variable{N P B:Side}{S:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S}{K:Teller SU.group}{G:Ratio (mid N B) (mid P B)}{R:Patch}{L:ChartRatio SU.group}
variable {d e η t z g A B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L)
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
variable {x y0 β:ℝ}(pp:BudgetPoint){t₀ v v₁ p11 p22 p3 p4:ℝ}
local notation "SN"=> Site (Domain N B)
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
local notation "ζ"=> (radiusB x)
open Trees Footprint Iva Eire
open Jade
-- certify.WAGES off all granted tasks
variable {u Hh pK qK a γ vS dS kL w:ℝ}{r p i:ℕ}{X: GramM (mid N B)}{Y: GramM (mid P B)}{U:Grasp V.U B d}
open Oath Feu Feu.Corset Haro Nor Siete PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir
open Footprint Jade Py
-- earnings profiles quant issued b through \ell. Accept permit Rent
open Larch Vow Bake Mew Roots Rive Neon
local notation "BN"=> mid N B
local notation "Η"=> Scree.Hub (mid N B)
local notation "Θ"=> X.p.supportExponent
variable {J:Type}[LinearOrder J][Fintype J]
variable (σ:J→Site (mid N B))(K_ E0:Key J→ RegBudget (mid N B))(F_:Key J→ ForceBudget (mid N B))
variable (Xo Yo:Key J→ RegBudget (mid P B))(Zo:Key J→ ForceBudget (mid P B)) {G₀:Scree.Loom (mid N B)}{G₁:Scree.Loom (mid P B)} (Xi:Op SU.Slot){q:Chi}{h:ℝ}
local notation "Tz"=> Cube.node ∘ σ
local notation "P_"=> X.p
variable (Q:J→ℝ)(qE:J→ArcΦ)(qΨ:J→ ArcΦ)(s:J→ℂ)
variable {Vp Va Bk Cμ Wη Eμ Cx ZΨ QΦ ξQ:ℝ} -- remove
variable (Fκ:Cause_P V U G S G₀ G₁ X Y Xo Yo Zo Xi q kL h Vp Va σ Q qE K_ F_ qΨ s Bk Cμ Wη Eμ Cx ZΨ QΦ)
open Roots Mew Rive Oise
variable {α:Type}[DecidableEq α]
open scoped YM.CF.Mew
local notation "Ω"=> mid N B
local notation "qμ"=> (Cube.node ∘σ)
local notation "Ωk"=> MixT σ
open Drift Oise
attribute [-instance] instDecidableEqLex
open Compass
namespace Dyad
open Swell Compass Taxi Ione Tune Grain AnalyticBridge.VerifiedReset
open Buffered Larch
namespace Keeping
open Buffered.Advance Mew
open Stencil
open Buffered.Afterglow.Tower (liner_unit liner_scale liner_plus)
local notation "mH"=>mid N B
local notation "pH"=>mid P B
open Compass Mint
-- bandwidth in gauge count. uniform reserve cost
abbrev padding(D w J:ℕ):=2*Advance.gross D w J+20
abbrev sitepad(o:Site mH)(r:ℕ):Support (More mH):= Lattice.halo r {node o}
-- Opaque prototype ordinary true supports promotions
variable {I:Type}[LinearOrder I][Fintype I]
variable (o:I→Site (Scree.mid N B))(cΛ:ℕ)(f:I→Mark (Scree.mid N B))(hC:∀ i,AtSupport false (sitepad (o i) cΛ) (f i))
-- full products at all distinct with given supports
abbrev couple(F:I→Mark mH)(l:List I):=(l.map F).prod
abbrev skyline (l:List I):Support (More mH):= l.toFinset.biUnion fun i=> sitepad (o i) cΛ
include hC
lemma company(S:List I): AtSupport false (skyline o cΛ S) (couple f S):=by
 induction S with
 | nil=>exact AtSupport.oneM _
 | cons i l ih=>
    change AtSupport false _ (f i * couple f l); refine AtSupport.mulM (b:=false) (c:=false) ?x ?y
    exact (hC i).mono (fun x h=> mem_biUnion.mpr ⟨i,List.mem_toFinset.mpr (List.mem_cons_self),h⟩)
    exact ih.mono (fun x hx=>by obtain ⟨a,b,c⟩:= mem_biUnion.mp hx; exact mem_biUnion.mpr ⟨a,List.mem_toFinset.mpr (List.mem_cons_of_mem _ (List.mem_toFinset.mp b)),c⟩)
variable (Rk uK HK:ℕ)
structure Tickets (D w J:ℕ)(L0:Side)(V0:SiteLedger V U kL q)(low high:ℕ):Prop where
 side (i:ℕ): (V0.ratio i).count=L0
 ask : ∀ i:ℕ, low ≤ i → i<high → LoomLaw (V0.plant i) w ∧ (V0.job i).patch.J≤ J
#check Tickets
local notation "ℓ"=> G.count.val
local notation "S_"=> halo
variable (T':StepData (Domain N B) (Domain P B))(h_l:T'.ratio= ratio G){Uν:Haro.SpaceM}
variable(hG:Odd G.count.val)(hL:1<G.count.val)(Tℓ:LaurentRadius K.j G.count Rk)(pB:Girt.BaseL U G Y G₀ G₁ q kL)(hT:T'.patch.Branches T'.kernel SU.group)(m0L:LoomLaw G₀ uK)(yT:T'.patch.J≤ HK)(qC:∀ i j:I,i≠j→ 2*(cΛ + padding Rk uK HK)< separation (node (o i)) (node (o j))) -- m shadow
local notation "upX"=>pushMark G T' K.j Uν.val Y.J.M hG q kL Y.beta G₀
local notation "nH" i:max=> Hove.heel G (o i)
omit hC
lemma site_at(A:Site mH)(x:Site (More mH)):x∈ sitepad A cΛ ↔ separation (node A) x ≤ cΛ:=by rw [sitepad,halo_spec]; simp
lemma near_f :2*(nearZero Rk +uK) ≤2*padding Rk uK HK:=by 
    unfold nearZero padding Advance.gross beforePad
    omega
include hC
include qC hG hT Tℓ pB m0L
lemma productFilm (S: List I)(t:S.Nodup) : (upX) (couple f S)=couple (fun i=>(upX) (f i)) S:=by
 induction S with
 | nil=>exact liner_unit G T' K.j Uν.val Y.J.M hG q kL Y.beta G₀ hT
 | cons i L ih=>
    obtain ⟨e,p⟩:= List.nodup_cons.mp t
    obtain ⟨_,_,_,z,_⟩:=pB.cap
    simp only [couple,List.map_cons,List.prod_cons]
    rw [separated_mult G T' K.j Uν.val Y.J.M hG q kL Y.beta G₀ Tℓ z.bill hT pB.legal.1 pB.legal.2 _ _ (hC i) (company o cΛ f hC L) m0L ?sep]
    exact congrArg ((upX) (f i)*·) (ih p)
    case sep=>
     intro x t y g; obtain ⟨k,hb,v⟩:= mem_biUnion.mp g
     have hB:2*(cΛ+ padding Rk uK HK)<separation (node (o i)) (node (o k)):= qC i k (fun v'=> e (v' ▸ List.mem_toFinset.mp hb))
     have h':= separation_triangle (node (o i)) x (node (o k)); have hx:= separation_triangle x y (node (o k)); rw [separation_comm y (node (o k))] at hx; have t:= (site_at cΛ (o i) x).mp t; have v:= (site_at cΛ (o k) y).mp v; have u:=near_f Rk uK HK; omega
#check liner_unit
include hL h_l yT
local notation "pT"=> padding Rk uK HK
-- choose c' at every point. ≥ enough for gross. conserve reserve.Lens.L.
lemma afterBill: ∃ Q:ℕ,(∀ i j:I,i≠j→ 2*(Q+pT)<separation (node (nH i)) (node (nH j)))∧∀ i, AtSupport false (sitepad (nH i) Q) ((upX) (f i)):=by
 let g:= Advance.gross Rk uK HK; let Q:= G.count.val*(cΛ+g)
 have hy:2*(Q+pT)≤ G.count.val*(2*(cΛ+pT)):=by
    -- L≥2, g≤ (pT-20)/2. needed L*g+pT ≤ L*pT equiv pT ≤L(g+20), yes
    have he:2*g+20 = pT:=rfl; have hD:0≤cΛ:=Nat.zero_le _; have hh:0≤g:=Nat.zero_le _; unfold Q; nlinarith
 obtain ⟨_,_,_,z,_⟩:=pB.cap
 have hz(i:I):node (nH i)=(ratio G).embed (node (o i)):= Py.claw G hG _ -- Py? actually Py roles. open.
 refine ⟨Q,fun i j p=> hy.trans_lt ?_,fun i=>?_⟩
 · simp_rw [hz]; rw [Laic.emptio]; exact Nat.mul_lt_mul_of_pos_left (qC i j p) G.count.property
 · apply (surround G T' K.j _ Y.J.M hG q kL Y.beta G₀ Tℓ z.bill hT pB.legal.1 pB.legal.2 _ (hC i) m0L h_l).mono
   intro x h; obtain ⟨y,hb,e⟩:= halo_spec.mp h; obtain ⟨j,k,rfl⟩:= mem_image.mp hb
   apply (site_at Q (nH i) x).mpr; rw [hz]
   apply le_trans (separation_triangle _ _ _); rw [Laic.emptio]
   have hh:= (site_at cΛ _ j).mp k; have hg: Advance.gross Rk uK T'.patch.J ≤ g:= by unfold g Advance.gross; gcongr
   have he:= e.trans (Nat.mul_le_mul_left _ hg)
   exact ((Nat.add_le_add (Nat.mul_le_mul_left _ hh) he).trans_eq (Nat.left_distrib ..).symm)
#print axioms productFilm
#print axioms afterBill
end Keeping
end Dyad
end YM.CF.Py
end
