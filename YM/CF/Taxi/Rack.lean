import YM.CF.Taxi.Lilt
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Taxi
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
variable{n:Side} {P: BudgetPoint}{x y a b h c d:ℝ}{k m:ℕ}
local notation "DN"=>tangD n
local notation "E'"=>SU.group
variable {X D Y Z:Support (More n)}{U:Pane n}
local notation "Ink" n=> Hake.Raid (Dwell n)
open Next.Foundations StressFlux AnalyticBridge.VerifiedReset Push.Local
open Vow
variable(T:RegBudget n)(F:InkD n)(X0: Scree.Hub n){U':Scree.Hub n→ℝ}
abbrev Pant (F:RegBudget n): Prop:=∀ i:Sweep n, ∃ S: UNI SpinIdx,∀ X:Scree.Hub n,∀ V:Pane n, F (moveHub i X) (flashA i V)= Vow.FrameR i S (F X V)
variable (p: Pant T)
def lifeH (F:InkD n)(U:Pane n):ℂ := Pastry.pane (F U)
abbrev realH (F:RegBudget n):RealP n:= fun i=> Complex.reCLM ∘ lifeH (F i)
abbrev magi (F: RegBudget n)(X:Scree.Hub n):Pane n→ℝ:= Complex.imCLM ∘ lifeH (F X)
local notation "Q"=> (T X0)
local notation "N"=> (Single n)
local notation "G"=> SU.group
private lemma auraT (f:Sweep n)(S:UNI SpinIdx)(x:Cipher n): Pastry.pane (Vow.FrameR f S x)=cSignX (f.charge.xor (detX f.s)) (Pastry.pane x):=by
 let r:= detX f.s; let b:= f.charge; let W:= prepU (castX f) S (xtra b) n; let V:= spice W r
 let L:Dough (LeanV (Single n)):= ⟨windX (b.xor r) x.val,Wtrans _ (fineShape x)⟩; change Pastry.pane (Pastry.fold V L)=_; rw [center_b]
 change crumb (windX (b.xor r) x.val) ∅=cSignX (b.xor r) (Pastry.pane x); cases b.xor r <;> rfl -- tune
include p
lemma era : βsP (realH T):=by
 intro X T' U u; obtain ⟨S,v⟩:=p T'; have ht: flashA T' U = pull T'.s ((assembly n).embed T'.b) U:=by rw [revoke,u]; rfl
 unfold realH lifeH; simp only [Function.comp_apply]; rw [←ht,v,auraT,u]; cases detX T'.s<;>rfl -- tune
lemma mirage : ∀ U, magi T X0 (Reef.echo U)= - magi T X0 U:=by
 intro U; let f:Sweep n:=⟨1,0,true⟩; obtain ⟨S,h⟩:=p f; have hp: flashA f U=Reef.echo U:=by rw [revoke]; change polarT true ∘ Lattice.pull 1 ((assembly n).root 0) U= _; rw [map_zero,pull_id]; rfl
 have he:moveHub f X0=X0:=by
    have ht:boxA f= Equiv.refl _:= Equiv.ext fun i=>by rw [sitA]; change affine 1 ((assembly n).root 0) i=i; rw [map_zero]; simp [affine]
    refine Subtype.ext (Prod.ext ?_ ?_); change (boxA f).symm _=_; rw [ht]; rfl; change Finset.map (boxA f).symm.toEmbedding _=_; rw [ht]; ext; simp
 rw [show magi T X0 (Reef.echo U)=(Pastry.pane (T (moveHub f X0) (flashA f U))).im by rw [he,hp]; rfl,h,auraT]; change (cSignX (true.xor (detX 1)) _).im=_
 rw [show detX 1=false from ?_]; rfl
 exact det_i -- tune
omit p
variable (hQ:PressB P X0 F h c)(hw:0≤h)
local notation "Xr"=> X0.val.2
local notation "o"=> X0.val.1
include hQ hw
lemma eraF(V:Pane n)(t:pingS P.threshold Xr V):Signs P o ((lifeH F) ∘ increment V) c:=by
 let Z:= F; obtain ⟨g,p,w,u⟩:=hQ.worth; let a:=(w V t ∅); apply Prism.high a; calc
    _ = Scree.tariff P o h ∅*g ∅:= by simp [Scree.tariff,endL]
    _ ≤ _ := (single_le_sum (fun i _=>mul_nonneg (show 0≤Scree.tariff P o h i by unfold Scree.tariff; positivity) (p i)) (mem_univ _)).trans u
lemma cashR (L:ℂ→L[ℝ]ℝ)(f:ℝ)(k:‖L‖ ≤ f): BandS P X0 (L ∘ lifeH F) (f*c) :=by
 let Z:= (L ∘ lifeH F)
 have hz(V: Pane n)(h:pingS P.threshold Xr V):Signs P o (Z ∘ increment V) (f*c):=Prism.skills ((Prism.skin (eraF _ X0 hQ hw V h)).linear L k)
 have ht (V: Pane n)(h:Healthy (pintK P).threshold Xr V):Chart P.order Z V:= (hz _ (ping_lo (half_lt_self P.threshold_pos) h)).paid
 refine ⟨⟨fun i j p=> by simp only [Function.comp_apply,lifeH,hQ.term i j p],L.continuous.measurable.comp (((show Continuous (Pastry.pane (n:=LeanV (Single n))) from mast_cont.comp (g:=mast (n:=LeanV (Single n))) continuous_subtype_val).measurable).comp hQ.measureV),fun v i=>?_ ,ht,fun U p a l g=>left_has a g (ht _ p)⟩,hz⟩
 unfold lifeH; rw [Function.comp_apply,hQ.gaugeV]; exact congrArg L (show Pastry.pane _= _ from Pastry.center_b ..)
omit hQ hw
variable(g: ∀ i, PressB P i (T i) h (U' i))
include p g hw
lemma pureK : fluxP X0 (magi T X0)=0:=by ext x y; exact pure_e X0 (cashR Q X0 (g _) hw _ _ le_rfl) (mirage T X0 p) x y
lemma gloryT (hn:60 < (More n).val)(i:Site (More n)) (V:Pane n): ∑ X:Scree.Hub n, fuelC X (realH T X) i V=lureC (realH T) *((∑ x:PlaqAxes,‖AnalyticBridge.VerifiedReset.petals V i x‖^2)/2):=by exact mergeT _ (era T p) (fun X=> cashR (T X) X (g X) hw Complex.reCLM ‖Complex.reCLM‖ le_rfl) hn i V -- froben norm Color/unrelated
end YM.CF.Taxi
