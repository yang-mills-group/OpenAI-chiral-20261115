import YM.CF.Eire.Prig
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
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
variable {N P B:Side}(S:StepData (Domain N B) (Domain P B)){r D:ℕ}
variable (L L':Ride S)
local notation "bay"=> Stilo.bay
open Rush Scroll Paige Vault Phase Acorn Spire
variable {A:Side}{j k:ℕ}{o:Odd A.val}{Y:Pricing j A o (Thread j)}{e:ℝ}{q:Grasp Y B e}{I:Aim (mid P B)}{M:Male}{α K K' t a d C H:ℝ}
variable (V: ∀ A:Support (Domain P B),Lend P B e A)(X:Tints P B e)
variable(T T' U U':Pane (mid P B))(G:Ids (mid P B))(D)
-- unconditional guard caps on seams derived once around every core; no per-subview flag re-tests in inversion
structure HullK(Z:Finset (Kite S r))(X:Pane (mid P B))(Y:Pane (mid P B))(e:ℝ) : Prop where
 raft:D+1≤ r
 actsB K:K ⊆ liftK S Z → Guard (valve S X Y K D) e
lemma pays_l (Z:Finset (Kite S r))(p: HullK S D Z T U e)(F:Finset (Hos S r))(u:F⊆ liftK S Z)(i:Hos S r)(h:i∈ liftK S Z) : printG S D T U F i ∈ MonoX P B e (danceL S i.val r):=by
 refine ⟨fun j=>?_,port_nest S F i T U D p.raft⟩; cases j; exact p.actsB _ u; exact p.actsB _ (insert_subset h u)
section
variable (P' Q': Finset (Kite S r))(p:Disjoint (bay L) (bay L'))(f:∀ i∈P',frameP S i⊆bay L)(v:∀ i∈Q',frameP S i⊆bay L')
omit f v
lemma port_l {f:Side}{Y X:Support f}(h:Y⊆X):∀ W:Support f,Y∩W⊆ X∩W:=fun W=> inter_subset_inter h (Subset.refl _)
lemma clip_union (w:List (Hos S r)): clipM S (P'∪Q') w=clipM S P' w ∪ clipM S Q' w:=by unfold clipM liftK; rw [image_union]; ext; simp only [mem_union,mem_inter]; tauto -- tune
include p f v
lemma quietK: Disjoint (liftK S P') (liftK S Q'):=by
 apply Finset.disjoint_left.mpr; intro i k u; obtain ⟨j,x,rfl⟩:=mem_image.mp k; obtain ⟨y,l,k⟩:=mem_image.mp u; obtain ⟨i',h⟩:=stem_p S j.1; exact Finset.disjoint_left.mp p (f j x (frame_s S j h)) (v y l (frame_s S y ((congrArg (stem S) k).symm ▸ h)))
-- from equality on EACH LABEL for Arch.L
lemma bill_l(w:List (Hos S r))(i:Kite S r)(l:i∈P')(u:Agrees ((i.2.1∪i.2.2):Support (Domain P B)) T T')(a: Agrees ((i.2.1∪i.2.2):Support (Domain P B)) U U')(h: D+1≤ r) : ∀ b: Bool, Agrees ((i.2.1∪i.2.2):Support (Domain P B)) (printG S D T U (clipM S (P'∪Q') w) i.1 b) (printG S D T' U' (clipM S P' w) i.1 b):=by
 let H:=clipM S Q' w; have hp (W:Finset (Hos S r)):Agrees ((i.2.1∪i.2.2):Support (Domain P B)) (valve S T U (W∪H) D) (valve S T' U' W D):=by
    intro j t z; have ht:S.ratio.parent j.1∈bay L:= f i l (mem_union_right _ (mem_image_of_mem S.ratio.parent (by rw [union_assoc]; exact mem_union_right _ t)))
    have he(a)(x:a∈H) : ¬ tastes S j (a.val.dome D):=by obtain ⟨a',y,b⟩:=mem_image.mp ((mem_inter.mp x).1); subst a; exact fun g=>disjoint_left.mp p ht (v a' y (frame_s S a' ((Corona.halo_mono h (Subset.refl _)) (driftK S j g)))) -- tune
    unfold valve; by_cases k:∃ i∈W,tastes S j (i.val.dome D); · rw [if_pos k,if_pos (by obtain ⟨i,x,z⟩:=k; exact ⟨i,mem_union_left _ x,z⟩)]; exact a j t z
    rw [if_neg k,if_neg]; exact u j t z; rintro ⟨i,x,v⟩; exact k ⟨i,(mem_union.mp x).resolve_right fun y=>he i y v,v⟩
 intro b; unfold printG; rw [clip_union]; cases b; exact hp _; simp only [ite_true, ← insert_union]; exact hp _ -- tune orientation
variable (ξ:HullK S D (P'∪Q') T U e)(ϕ: HullK S D P' T' U' e)(A:∀ i∈P', Agrees ((i.2.1∪i.2.2):Support (Domain P B)) T T' ∧ Agrees ((i.2.1∪i.2.2):Support (Domain P B)) U U')
lemma boston_l (R:Pec.Pride (mid P B))(ψ:Dyes α e R k X C H)(η:Vista q M I V k K t a d)(w:List (Hos S r))(i:Hos S r)(t:i∈liftK S P')(αX: HullK S D (P'∪Q') T U e)(βX: HullK S D P' T' U' e)(A:∀ i∈P',Agrees ((i.2.1∪i.2.2):Support (Domain P B)) T T' ∧ Agrees ((i.2.1∪i.2.2):Support (Domain P B)) U U') : rankG S D V X T U G (P'∪Q') w i=rankG S D V X T' U' G P' w i:=by
 unfold rankG; have he: liftK S (P'∪Q')=liftK S P'∪ liftK S Q':=image_union ..; have hz:i∉ liftK S Q':=Finset.disjoint_left.mp (quietK S L L' P' Q' p f v) t; have hu:i∈ liftK S (P'∪Q'):=he.symm ▸ mem_union_left _ t; rw [if_pos hu, if_pos t]; refine sum_congr ?_ fun j x=> ?_ -- x in P'??
 · ext j; simp only [legend,mem_filter]; apply and_congr_left; intro y; rw [mem_union,or_iff_left]; exact fun a=>hz (y ▸ mem_image_of_mem Prod.fst a)
 obtain ⟨hx,hh⟩:=mem_filter.mp x; unfold postM; rw [dif_pos (pays_l S D T U _ αX _ inter_subset_left _ (hh.symm ▸ hu)),dif_pos (pays_l S D T' U' _ βX _ inter_subset_left _ (hh.symm ▸ t))]; exact lit_i S V X j η R ψ _ _ G G (fun _ _=>rfl) (bill_l S D L L' T T' U U' P' Q' p f v w j hx (A j hx).1 (A j hx).2 αX.raft) -- tune order D args hx
end
end YM.CF.Eire
