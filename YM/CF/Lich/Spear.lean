import YM.CF.Lich.Venus
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Lich
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
-- separate path ledger Φ.M.Target.S.P
variable {N P B:Side}(G:Ratio (mid N B) (mid P B))(S:StepData (Domain N B) (Domain P B))(x e:ℝ)(T:Tube SU.group S)
variable{r n j d:ℕ}
namespace Muster
variable{G S x e T}
variable(A:Muster G S x e T)
variable(U: Monk SU.group S)(V W:Rent0 G e) -- V true W at ζ=0
local notation "θ"=> A.room
local notation "j"=> A.loft
local notation "β"=> A.beta
local notation "q"=> A.trot
local notation "α"=> A.ang
local notation "γ"=> A.fee
local notation "l"=> A.post
local notation "F"=> U.sent x T q θ l β
local notation "Y"=> (U.park,U.k)
local notation "K"=> U.key.dome (j*radiusB x)
local notation "Q'"=> A.LawQ
local notation "YY"=> A.Beds
-- account per site
-- far components plus interior.Optional momentum.
open Corne
variable{r r' b k D R₁:ℕ}{a d' k' v v' z y:ℝ}{F₁: nomA N P B→ Op (Single (mid N B))}{Φ:nomA N P B→ℂ}
local notation "S₁"=> Words S
local notation "Zc"=> Site (Domain N B)
variable (R:GramM (mid P B))(Z:Eire.Dress G S e r D U R k (A.mapV b))(L t w:ℝ)
variable (c : A.Gard (n:=n) (a:=a) (a':=d') (C:=k') (D:=v) (c:=v') (v:=z) (Z:=y) (J:=F₁) (Φ:=Φ) (R₁:=R₁) r r' b k)
abbrev onK(Yw:Rill.Arch G e): Rent0 G e:=⟨Yw.val.1,Yw.property.1⟩
variable (H:Stores S→Rill.Arch G e)
abbrev pageX (P:Stores S):= onK (Z.blocks P)
abbrev pageY (P:Stores S):=onK (H P)
def ruin : Eire.Dress G S e r D U R k (A.mapV b):={Z with
   rare O:= hue A (Eire.trot S U O) (pageX A U R Z O) (pageY H O) r r' t w L
   coin O:= elk A (Eire.trot S U O) (pageX A U R Z O) (pageY H O) r' k t w
   rareP i j':= by exact nice_r A (Eire.trot S U i) (pageX A U R Z i) (pageY H i) r r' k b t w L c j' -- order!
   coinP i j':= by exact nice_v A (Eire.trot S U i) (pageX A U R Z i) (pageY H i) r r' k b t w c j'}
local notation "B2"=> A.mapV b
local notation "V₀"=> ruin A U R Z L t w c H
open Eire.Dress
lemma panelV (T' W':Rill.Arch G e)(Ω:Ride S)(p:CrownB G S e T' W' k Ω): Panel A (Stilo.bay Ω) k (onK T') (onK W'):= fun y v=>⟨(p.hears y v).1,(p.hears y v).2.1⟩
open Rel
variable (Q:Ids (mid N B))(Q1:Scree.Loom (mid N B))(Q2:Scree.Loom (mid P B)){f s u hv hv' v1 v2 g:ℝ}{κ δ:ℕ}(q':Chi)
variable (p: Eire.Dress.Visit Z Q Q1 Q2 s f hv u hv' v1 v2 x g A.post κ δ q')(hp:Z.pipe=T)(he:A.trot=Z.chi)(hb:A.room=Z.wage)(hk:R.beta=A.beta)(p0:∀ F': Stores S, let V:= Eire.trot S (rough U 0) F'; Eire.Clan G S (T:=Z.pipe) Z.axes Q Z.cloth V Q1 Q2 Z.chi q' A.post x Z.wage g R.beta (H F'))(h0:∀ F':Stores S,F'.flags=flags (temp x) U.V→ Bell S (Eire.trot S (rough U 0) F') x Z.pipe Z.chi Z.wage A.post R.beta f u)
-- operations don't depend on Z's other fields. residue FFT.
include p hp he hb hk p0 h0
local notation "bay"=>Stilo.bay
lemma vital : Eire.Dress.Infant V₀ x:=by
 constructor; intro i j' X P d' F' f u v; obtain ⟨wS,wC,wD⟩:= Eire.Dress.Ion Z x l p i F' u
 let M1:=penn S i; let H':= penn S (i∪ j'); let zeta(M:Stores S):= Eire.trot S U M; let Z' := rough U 0; let w'(M):= Eire.trot S Z' M
 have hv(W:Monk SU.group S):Duo SU.group S (Eire.trot S W M1) (Eire.trot S W H') (bay X):= by unfold H' M1; simp only [penn,toLeft_union]; exact burn_r S W i.toLeft j'.toLeft (bay X) _ d' (fun _ v=>litG S B2 f _ v)
 have hz:CrownB G S e (Z.blocks M1) (Z.blocks H') k X:=by let P:=Z.blocks M1; let V:=Z.blocks H'; change CrownB _ _ _ P V k _; have ht:= frosty G S Z.axes X Q Q Z.cloth Z.cloth (Z.blocks M1) (Z.blocks H') wC (skyC S X) i.toLeft wS rfl c.ages p.ceil (p.haul M1) (p.haul H') (hv U).toBeat p.pole p.heel p.toes p.horn (fun _ _=>rfl) (fun _ _=>rfl) (fun _ _=>rfl); exact (congrArg (fun k=>CrownB G S e P V k X) p.wear).mpr ht
 have hc:CrownB G S e (H M1) (H H') k X:=by
    have hV:= peal («l»:=A.post) S (rough U 0) i.toLeft X u.1 u.2.2 p.years wS p.legP p.mint p.tone p.pole h0; rw [p.wear]; exact frosty G S Z.axes X Q Q Z.cloth Z.cloth (H M1) (H H') hV (skyC S X) i.toLeft wS rfl c.ages p.ceil (p0 M1) (p0 H') (hv Z').toBeat p.pole p.heel p.toes p.horn (fun _ _=>rfl) (fun _ _=>rfl) (fun _ _=>rfl)
 have hx: Muster.Post A (Eire.trot S U M1) (Eire.trot S U H') (onK (Z.blocks M1)) (onK (H M1)) (onK (Z.blocks H')) (onK (H H')) k (bay X):= ⟨hv U, ⟨fun _ _=> rfl,fun _ _=>rfl,fun _ _=>rfl,fun _ _=>rfl⟩,panelV A _ _ _ hz, panelV A _ _ _ hc⟩
 constructor
 · intro i' z; obtain ⟨j',f,h⟩:=mem_image.mp z; subst i'; exact (roofH A _ _ _ r r' k b t w L c hx _ (litG S _ F' _ f)).symm
 intro i' t'; exact (roofX A _ _ _ r r' k b t w c hx i' (lodX S B2 F' _ (mem_toRight.mp (mem_toRight.mp t')))).symm
end Muster
end YM.CF.Lich
