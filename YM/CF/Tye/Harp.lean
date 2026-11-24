import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Trails
import YM.CF.Tye.Pine
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Tye
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
open Stilo Palot Scion Function Levier Hake Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire Eire
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Corne Lich Lich.Muster Rink Jet Vol
variable{N P B:Side}{S:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S}{K:Teller SU.group}{G:Ratio (mid N B) (mid P B)}
variable {x e m:ℝ}(A:Muster G S x e T)(M:Monk SU.group S)(s:Signed)(b:Site (Domain N B))(g:Site (Domain N B)→ SU.group.El)
open AnalyticBridge.GaussianFieldAlignment Tensor Orthogonal PhysicalNext.OrderedAffine2B.SymRows Channels Locations
variable {d:ℕ}
local notation "Y"=> clue S s b M
local notation "V"=> shiftZ g M
local notation "F"=> cedar M
variable (h:K.Funds S T)(hp:FreeResolvent.Gap (baseX T x M.key M.park M.k M.V) m)(hv:120 ≤ radiusB x)(hz:0 < m)(hA: Reef.Rare T.up)(hB:Reef.Rare T.down)(ht: LocalRatio A.vita)(hi:0 < A.rota)(hm:4*A.rota < A.vita.radius)(hb:0 < A.beta)
local notation "d"=> Domain N B
local notation "d'"=> Domain P B
local notation "L"=> Stores.till x
local notation "Z"=> mid N B
local notation "j'"=> A.loft
local notation "q"=> A.trot
local notation "Q"=> A.LawQ
local notation "L'"=> A.post
local notation "J"=> A.vita
local notation "R"=> A.rota
local notation "v'"=> A.room
local notation "H"=> A.hot
local notation "β"=> A.beta
local notation "α"=> A.ang
local notation "γ"=> A.fee
local notation "X"=> kist M
variable (f:Sweep (mid N B))(W U': Rent0 G e)(i:Site (Domain N B))
variable (ph:S.ratio=ratio G)(t:tyke G A.LawQ)(xw:A.Beds.val=(1,1))
local notation "W'"=> male e G f W
local notation "N'"=> rot f M
local notation "A'"=> clue S f.s (Facet.pasta f) M
local notation "Λ"=> chart f
local notation "Ω"=> M.key.dome (j'*radiusB x)
open Rel Nacre Reef
-- Gauge of averaged terms unaffected. proof for arbitrary μ.
variable {U₁ U₂ U₃:ℝ}{k r n:ℕ} (o:Stores S)(P':Tab S)
local notation "l"=> A.post
-- GI due to Rotor path OST
abbrev Gi (f:Pane (mid N B)→ℂ) :Prop:=∀ U: Pane (mid N B),∀ g:Site (Domain N B)→SU.group.El, f (Lattice.gauge g U)=f U
lemma discharged(A:DirP (Domain N B)) (p:∀ i j, Gi (A i j)): Gi (dict A i) :=by intro Vw g; unfold dict; simp only [Pi.sub_apply, Finset.sum_apply,p]
lemma duty_p (f:Tab S→FileM d SU.group)(K:Tab S→DirP d)(p:∀ i j,Gi (K P' i j))(w:Gi (f P' i+dict (K P') i)): Gi (issued x k r f K o P' i):=by
 intro Vw g; let G':= cClip x r K o P'; have hh:Gi (f P' i):=by
    intro U g; have he:=w U g; rw [Pi.add_apply,Pi.add_apply,discharged i _ p] at he; exact add_right_cancel he
 have hx(j i):Gi (G' i j):=by unfold G' cClip; split; exact p _ _; exact fun _ _=>rfl
 unfold issued; rw [Pi.add_apply, Pi.add_apply,show dict _ _ _=_ from discharged i G' (fun i j=>hx j i) Vw g]; split; rfl; rw [hh]
abbrev Baton : Prop:=∀ (N_:Monk SU.group S) g i, marble A (shiftZ g N_) i=marble A N_ i
local notation "Π"=> Tarn.Coin T x A.hash q J R v' α L'
variable {U₄ U₅ U₆ U₇ U₈ U₉:ℝ}{bA c a r':ℕ}
lemma baton_p(w:Woven (fun t:Tab S=> Arena.fame T t A.trot x v' A.post) A.muK k a n U₁ U₂ U₃) (p: Wick (ηδ A) A.etaD bA r U₄ U₅ U₆)(hx:Wick (ξδ A) A.xiD c r' U₇ U₈ U₉): Baton A:=by
 intro U g i; let P:= (U.park,U.k); have he(Ζ:Tab _→FileM d SU.group)(F':Tab S→DirP d)(p:∀ i j, Gi (F' P i j))(w: Gi (Ζ P i + dict (F' P) i))(u:ℕ): issued x j' u Ζ F' U.key P i (Lattice.gauge g U.V)=issued x j' u Ζ F' U.key P i U.V:=duty_p i U.key P Ζ F' p w U.V g -- notation Z collision
 exact congrArg₂ (·-·) (congrArg Complex.ofReal (congrArg (fun u:ℂ=> -β*u.re) (he _ A.muK (fun i j=>(w.crew P i j).1.fixed) (w.power P i|>.1.fixed) A.mup))) (congrArg₂ (·+·) (he _ A.etaD (fun i j=>(p.vows P i j).1.fixed) ((p.better P i).1.fixed) _) (he _ A.xiD (fun i j=>(hx.vows P i j).1.fixed) ((hx.better P i).1.fixed) _)) -- tune other EtaD formula
lemma pole_k: rough (clue S s b (shiftZ g M)) 0= shiftZ (g∘ affine s b) (rough Y 0):=by -- b shadow natural fix
 let P0:=clue S s b (shiftZ g M); let g' := g ∘ affine s b; rw [←rough_g]; refine flank _ _ rfl rfl rfl (ProjectorNext.Equivariance.pull_gauge ..) ?_
 change Lattice.pull s _ (Lattice.gauge (constantGauge g _) M.U)= Lattice.gauge _ _; rw [ProjectorNext.Equivariance.pull_gauge]; refine congrArg (fun z=> Lattice.gauge z _) ?_; ext1 i; exact congrArg g (Locations.parent_map ..)
lemma he_g {m: Side}(g:Site m→SU.group.El)(U:Config SU.group m): Reef.echo (Lattice.gauge g U)=Lattice.gauge (Reef.echo g) (Reef.echo U):=by funext i; simp only [Reef.echo,Lattice.gauge,map_mul,map_inv]
lemma pend_e: rough (cedar V) 0=shiftZ (Reef.echo g) (rough F 0):= by rw [←rough_g]; refine flank _ _ rfl rfl rfl (he_g ..) ?_; exact he_g _ _
lemma gapG: ∃ k: Site (Domain N B)→SU.group.El, rough (rot f V) 0=shiftZ k (rough (rot f M) 0):=by
 let g':=g∘ affine f.s (Facet.pasta f); unfold rot dice; split
 next u=>
    refine ⟨Reef.echo g',?_⟩
    rw [rough_f,pole_k,rough_f]; have he:= pend_e (rough A' 0) g'; have hC(t:Monk SU.group S): rough (rough t 0) 0=rough t 0:=rfl
    rw [rough_f,rough_g,hC,rough_f,hC] at he; exact he
 exact ⟨g',pole_k ..⟩
end YM.CF.Tye
