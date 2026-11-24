import YM.CF.Eire.Vote
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Eire
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
variable {N P B:Side}(G:Ratio (mid N B) (mid P B))(S:StepData (Domain N B) (Domain P B))(x:ℝ)(e_:ℝ)(r l k D:ℕ)
local notation "bay"=> Stilo.bay
variable {ι:Type}[Fintype ι][DecidableEq ι](X:ι→ Palot.leaf (Site (Domain N B)))
open Rush Scroll Paige Vault Phase Acorn Spire
namespace Dress
variable {S G D k r l x}
variable (M:Monk SU.group S)(R:GramM (mid P B))
variable {M R X e_}
variable (U:Dress (r:=r) G S e_ D M R k X) -- order inferred?
variable (x:ℝ)(l:ℕ)
local notation "B₀"=> BranchX S X k
local notation "Fh"=> flags (temp x) M.V
local notation "O'"=> capG S Fh (chillB M) R.p.threshold
-- charged SCALAR Heir split.R.Phase law.JM.
variable {i j:Troupe S r ι} {H L T:Ride S}
-- local stencil clients
variable {g:ℝ}{q:Chi}{W:Scree.Loom (mid N B)}{W': Scree.Loom (mid P B)}{C: Ids (mid N B)}{s t b a c v w:ℝ}{k' k1:ℕ}
variable (X': Visit U C W W' s t b a c v w x g l k' k1 q) (K: Infant U x)
variable {A:Side}{κ n:ℕ}{o:Odd A.val}{Y:Pricing n A o (Thread n)}{q':Grasp Y B e_}{μ h v₁ v₂ d L₁ L₂ B₁:ℝ}
include X' K
set_option maxHeartbeats 800000 in
lemma breeze(d': Disjoint (bay H) (bay L))(p:Palot.fits B₀ i H)(t: Palot.fits B₀ j L)(u:Dyes μ e_ R.J.I κ U.dyes d B₁)(z: Hive.Vista q' R.J.M R.J.P U.pens κ h ((Fintype.card Play:ℝ)*L₁) v₁ v₂)(ξ:∀ i:Kite S r,ShiftD κ L₂ h e_ (danceL S i.1.val r) U.cloth (Hive.chip (danceL S i.1.val r) U.cloth))(f:O' i H)(Gv:O' j L) : U.songP (i∪j)=U.songP i*U.songP j:=by
 have he:=earn_s S X p t d' R.p.threshold (chillB M) (flags (temp x) M.V)
 have h₀:Palot.fits B₀ (i∪j) (H⊔L):=fun w k=> (mem_union.mp k).elim (fun h=>(p w h).trans le_sup_left) (fun g=>(t w g).trans le_sup_right)
 have hp':=he.mpr ⟨f,Gv⟩; have hg:=U.Alps x l X' K p t d' f Gv; have hc:=U.Alps x l X' K t p d'.symm Gv f
 obtain ⟨hh,x',ure⟩:= U.Ion x l X' (i∪j) h₀ hp'; obtain ⟨hi,x',ui⟩:=U.Ion x l X' i p f; obtain ⟨hj,y',vj⟩:=U.Ion x l X' j t Gv
 have hQ: ∀ k∈j.toLeft,Agrees ((k.2.1∪k.2.2):Support (Domain P B)) (U.coats (i∪j)).val.1.1 (U.coats j).val.1.1 ∧ Agrees ((k.2.1∪k.2.2):Support (Domain P B)) (U.coats (i∪j)).val.2 (U.coats j).val.2 := by rw [union_comm i]; exact chomp_s G S L (U.coats (j∪i)) _ _ hj (X'.wear ▸ hc.pose) -- tune
 unfold songP; dsimp only; rw [toLeft_union]; exact amble S D H L U.pens U.dyes _ _ _ _ U.cloth _ _ d' (moon p) (moon t) _ u z _ ξ (by rw [←show (i∪j).toLeft=i.toLeft∪j.toLeft from toLeft_union]; exact ure) ui vj (chomp_s G S H (U.coats (i∪j)) _ _ hi (X'.wear ▸ hg.pose)) hQ
lemma glad_l(d': Disjoint (bay H) (bay L))(p:Palot.fits B₀ i H)(t: Palot.fits B₀ j L)(u:Dyes μ e_ R.J.I κ U.dyes d B₁)(z: Hive.Vista q' R.J.M R.J.P U.pens κ h ((Fintype.card Play:ℝ)*L₁) v₁ v₂)(ξ:∀ i:Kite S r,ShiftD κ L₂ h e_ (danceL S i.1.val r) U.cloth (Hive.chip (danceL S i.1.val r) U.cloth)) : U.blazon x l (i∪j) (H⊔ L)= U.blazon x l i H*U.blazon x l j L:=by
 have he:=earn_s S X p t d' R.p.threshold (chillB M) (flags (temp x) M.V)
 unfold blazon; by_cases f:capG S (flags (temp x) M.V) (chillB M) R.p.threshold i H; swap; · rw [if_neg f, if_neg (fun p=>f (he.mp p).1),zero_mul]
 by_cases Gv:O' j L; swap; · rw [if_neg Gv, if_neg (fun p=>Gv (he.mp p).2),mul_zero]
 have hp':=he.mpr ⟨f,Gv⟩; rw [if_pos f, if_pos Gv, if_pos hp']; have hg:=U.Alps x l X' K p t d' f Gv; have hc:=U.Alps x l X' K t p d'.symm Gv f
 exact vote U x l d' p t hg hc (U.breeze x l X' K d' p t u z ξ f Gv) X'.wear X'.years X'.pole
omit X' K
lemma loom (L:List (Hos S r))(Y Z:Pane (mid P B)): paint S D U.pens U.dyes Y Z U.cloth ∅ L=1:=by induction L with| nil=> rfl| cons i w ih=> rw [paint, rankG, if_neg,ih,one_mul]; simp [liftK]
@[local simp] lemma TL (A B:Type*):(∅:Finset (A⊕B)).toLeft=∅:=rfl
@[local simp] lemma TR(A B:Type*):(∅:Finset (A⊕B)).toRight=∅:=rfl
lemma standard : U.blazon x l (∅:Troupe S r ι) ⊥=1:=by
 unfold blazon; let Y:Troupe S r ι:=∅; rw [if_pos]; swap
 · simp [capG, earn,pureK,penn,cook,vase,Pear,liftK,rendL,brushK,TL,TR,bayB]
 let t:=U.stageT x l Y
 let H:Ride S:=⊥; have hu:Scion.cluster B₀ Y=H:= by rw [Scion.cluster,show Y=∅ from rfl, Finset.sup_empty]
 apply Subtype.ext; change (vigor t H).val=(1:Cipher (mid N B)).val; rw [vigor,←show view H (reconL.symm (vig t))=(reconL.symm (vig t)) H from ?_,recon]; swap
 · change ∑ i∈deckX H,_=_; rw [show deckX H={H} from Finset.ext fun i=> by rw [deckH,mem_singleton]; exact le_bot_iff,sum_singleton]
 change Scion.tempo t H=1; unfold Scion.tempo; rw [if_pos hu.le]; change issue (U.heatT Y H) (U.bodyL x l Y).val (U.songP Y)*(U.brew Y).val=1
 rw [show U.brew Y=1 from ?_]; swap; · unfold brew; simp [Y,liftK]
 rw [show (1:Cipher (mid N B)).val=1 from rfl,mul_one]; have hp: U.bodyL x l Y=1:=by unfold bodyL; simp [Y,lure]; -- tune
 rw [hp,show U.songP Y=1 from ?_]; swap; · unfold songP; rw [show Y.toLeft=∅ from rfl]; exact loom ..
 exact Eq.trans (ring_u (U.heatT Y H) [] []) rfl
include X' K
lemma cogent (u:Dyes μ e_ R.J.I κ U.dyes d B₁)(z:Hive.Vista q' R.J.M R.J.P U.pens κ h ((Fintype.card Play:ℝ)*L₁) v₁ v₂)(ξ:∀ i:Kite S r,ShiftD κ L₂ h e_ (danceL S i.1.val r) U.cloth (Hive.chip (danceL S i.1.val r) U.cloth)) : Org (BranchX S X k) (U.blazon x l) :=by
 refine ⟨fun i H p=>?_,standard U x l,fun H L i j d p h=>glad_l U x l X' K d p h u z ξ⟩; unfold blazon at p; split at p; exact fuelFit _ H p; contradiction
end Dress
end YM.CF.Eire
