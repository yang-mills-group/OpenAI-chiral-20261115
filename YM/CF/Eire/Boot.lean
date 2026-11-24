import YM.CF.Eire.Root
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
variable {N P B:Side}(G:Ratio (mid N B) (mid P B))(S:StepData (Domain N B) (Domain P B))(u:S.ratio=Rush.ratio G) (z:Odd G.count.val)(e:ℝ)(g:0<e)(X: Meter TailB G e)(V: Meter Grave G e)
local notation "bay"=> Stilo.bay
variable (T U:Rill.Arch G e) (k:ℕ) (f:ReefT G e X V)
local notation "α"=> tinOre (switchG G).symm
abbrev stretchF (H:Ride S)(Y:Support (Domain P B)):= halo k (hatY S Y) ⊆ bay H
structure CrownB (H:Ride S) :Prop where
 hears Y: stretchF S k H Y → Agrees Y T.val.1.1 U.val.1.1 ∧ Agrees (cloudG G Y) T.val.1.2 U.val.1.2 ∧ Agrees Y T.val.2 U.val.2
variable {H L W:Ride S}
lemma collects (w:H≤L): gleans S k H ⊆ gleans S k L:=fun i v=> mem_filter.mpr ⟨mem_univ _,((mem_filter.mp v).2).trans w⟩
lemma reaches (w:H≤L){Y}(p:Y∈gleans S k H):stretchF S k L Y:= (show halo k (hatY S Y)≤ _ from (bay_beam _).symm.le).trans (bay_m (((mem_filter.mp p).2).trans w))
local notation "τ"=> cala G S z e g X V
variable (d:Disjoint (bay L) (bay W))(w:H ≤ L ⊔ W)(p:CrownB G S e T U k L)
include d w
private lemma catchB {Y:Support (Domain P B)}(a:Y∈gleans S k H)(i)(g: i∈ hatY S Y)(h: i∈bay L): Y∈ gleans S k (H⊓ L):=by
 obtain ⟨x,y⟩:= mem_filter.mp a; refine mem_filter.mpr ⟨mem_univ _,le_inf y (((beam_choice d _ (y.trans w))).resolve_right fun u=>?_)⟩
 exact disjoint_left.mp d h (bay_m u (by rw [bay_beam]; exact halo_subset _ _ g))
include p g f
private lemma brandL(i:TailB)(v t: Iota G)(h:S.ratio.parent (lookM G v)∈bay L): (∑ Y∈gleans S k H,X i Y (bring g T) v t)=(∑ Y∈gleans S k (H ⊓ L), X i Y (bring g U) v t):=by
 let F(Y):=X i Y (bring g T) v t; rw [show (∑ _∈_,_) = _ from (sum_subset (f:=F) (collects S k (show H⊓L ≤ H from inf_le_left)) ?_).symm]; swap
 · intro Y a u; obtain ⟨C,p⟩:=f.sail i Y; by_contra e'; exact u (catchB S k d w a _ (mem_image_of_mem _ (till G e p _ _ _ e').1) h)
 refine sum_congr rfl fun Y a=>?_ ; obtain ⟨C,l⟩:=f.sail i Y; obtain ⟨p,t,v⟩:=p.hears Y (reaches S k inf_le_right a); unfold F; rw [brick g Y (X i Y) _ _ C l T U p t v] -- tune
private lemma brandR(i:Grave)(v t:Iota G)(h:S.ratio.parent (lookM G v)∈bay L): (∑ Y∈gleans S k H,heal G e V i Y (bring g T) v t)=(∑ Y∈gleans S k (H⊓ L), heal G e V i Y (bring g U) v t):=by
 let F(Y):=heal G e V i Y (bring g T) v t; rw [show (∑ _∈_,_)=_ from (sum_subset (f:=F) (collects S k (show H⊓ L ≤ H from inf_le_left)) ?_).symm]; swap -- notation wrong double
 · intro Y a u; obtain ⟨C,p⟩:= f.flow i Y; by_contra e'; exact u (catchB S k d w a _ (mem_image_of_mem _ (till G e p _ _ _ e').1) h)
 refine sum_congr rfl fun Y a=>?_ ; obtain ⟨C,l⟩:= f.flow i Y; obtain ⟨p,t,v⟩:=p.hears Y (reaches S k inf_le_right a); unfold F; rw [brick g Y _ _ _ C l T U p t v]
include z
lemma drift_l (i:Twig (Single (mid P B)))(hp:i∈ mintK S L): (τ T k H).seats i=(τ U k (H⊓ L)).seats i:=by
 funext j; change Urn.mount _ _ _= Urn.mount _ _ _; dsimp only [Urn.mount,LenT, Radix,marge,Matrix.submatrix_apply,id]; change mint S (twigS i).2∈bay L at hp; rw [melt G] at hp
 simp only [Matrix.sum_apply]; rw [brandL G S e g X V T U k f d w p _ _ _ hp]
lemma drift_r (i j:Twig (Single (mid P B)))(hp:i∈ mintK S L): (τ T k H).pals i j=(τ U k (H⊓ L)).pals i j:=by
 change Urn.soar _ _ _=Urn.soar _ _ _; dsimp only [Urn.soar,KinG,oakN]; change mint S _∈bay L at hp; rw [melt G] at hp; simp only [Matrix.add_apply,Matrix.sum_apply]; rw [brandR G S e g X V T U k f d w p _ _ _ hp]
omit p
lemma drift_z(i j: Twig (Single (mid P B)))(h:i∈mintK S L)(u:j∈ mintK S W): (τ T k H).pals i j=0:=by
 change mint S (twigS i).2∈ bay L at h; change mint S (twigS j).2∈ bay W at u; rw [melt G] at h; rw [melt G] at u; generalize ha:(α i)=x at *; -- tune goal
 change Urn.soar (KinG G e V (bring g T) _) _ (α j)=_; rw [ha]; dsimp only [Urn.soar,KinG,oakN]; split; rfl
 let v:=(twigS x).2; let t:=(twigS (α j)).2; let R: Grave:= (tallC x,tallC (α j), (twigS x).1,(twigS (α j)).1)
 have ht:v≠t:=fun k=> disjoint_left.mp d h (show S.ratio.parent (lookM G v)∈bay W from k.symm ▸ u); have hx:feeX G R v t=0:=by unfold feeX; split<;> simp [Matrix.smul_apply,Matrix.one_apply_ne,ht] -- tune
 have he:∑ i∈gleans S k H,heal G e V R i (bring g T) v t=0:=by
    apply sum_eq_zero; intro i l; by_contra p; obtain ⟨C,g⟩:= f.flow R i; obtain ⟨a,b⟩:= till G e g _ _ _ p; have hu:= catchB S k d w l _ (mem_image_of_mem S.ratio.parent a) h; exact disjoint_left.mp d ((reaches S k (show H⊓L≤ L from inf_le_right) hu) (halo_subset k _ (mem_image_of_mem _ b))) u
 simp only [Matrix.add_apply, Matrix.sum_apply]; change Scroll.cSignX _ ((∑ i∈_,heal G e V R i (bring g T) v t)+feeX G R v t)=_; rw [hx,he,add_zero]; simp [Scroll.cSignX]
end YM.CF.Eire
