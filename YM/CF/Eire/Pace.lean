import YM.CF.Eire.Tall
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
variable {P' Q': Finset (Kite S r)}
lemma amble(T'' U'': Pane (mid P B))(p:Disjoint (bay L) (bay L'))(f:∀ i∈P',frameP S i⊆bay L)(v:∀ i∈Q',frameP S i⊆bay L')(R:Pec.Pride (mid P B))(ψ:Dyes α e R k X C H)(η:Vista q M I V k K ((Fintype.card Play:ℝ)*t) a d)(w:List (Hos S r))(u:∀ i:Kite S r,ShiftD k K' K e (danceL S i.1.val r) G (Hive.chip (danceL S i.1.val r) G))(αX:HullK S D (P'∪Q') T U e)(βX:HullK S D P' T' U' e)(γ:HullK S D Q' T'' U'' e)(h:∀ i∈P',Agrees ((i.2.1∪i.2.2):Support (Domain P B)) T T'∧ Agrees ((i.2.1∪i.2.2):Support (Domain P B)) U U')(g:∀ i∈Q',Agrees ((i.2.1∪i.2.2):Support (Domain P B)) T T''∧Agrees ((i.2.1∪i.2.2):Support (Domain P B)) U U'') : paint S D V X T U G (P'∪Q') w=paint S D V X T' U' G P' w*paint S D V X T'' U'' G Q' w:=by
 have hu:=quietK S L L' P' Q' p f v; induction w with
 | nil=>rw [paint,paint,paint,one_mul]
 | cons i w ih=>
    rw [paint,paint,paint,ih]; by_cases e:i∈ liftK S P'
    · rw [boston_l S D L L' V X T T' U U' G P' Q' p f v R ψ η w i e αX βX h, show rankG S D V X T'' U'' G Q' w i= 1 from if_neg (Finset.disjoint_left.mp hu e), one_mul,mul_assoc]
    rw [show rankG S D V X T' U' G P' w i=1 from if_neg e,one_mul]; by_cases k:i∈ liftK S Q'
    · have hK:= boston_l S D L' L V X T T'' U U'' G Q' P' p.symm v f R ψ η w i k (by rw [union_comm]; exact αX) γ g; rw [union_comm Q' P'] at hK; have hx:= priced S L' L p.symm _ _ (ink_p S D L' V X T'' U'' G Q' v η (fun i _=>u i) w i) (paint_p S D L V X T' U' G P' f η (fun i _=>u i) w); rw [hK,←mul_assoc,hx.eq,mul_assoc]
    have hk: i∉ liftK S (P'∪Q'):=by rw [show liftK S (P'∪Q')=liftK S P'∪liftK S Q' from image_union ..,mem_union]; tauto
    rw [show rankG S D V X T U G (P'∪Q') w i=1 from if_neg hk,show rankG S D V X T'' U'' G Q' w i=1 from if_neg k,one_mul, one_mul]
lemma sit_m (p:Finset (Kite S r))(l:List (Hos S r)): clipM S p (l.filter (fun i=>i∈liftK S p))=clipM S p l:=by
 ext i; simp [clipM]; tauto
lemma jug (p:Finset (Kite S r))(l:List (Hos S r)): paint S D V X T U G p (l.filter (fun i=> i∈ liftK S p))=paint S D V X T U G p l:=by
 induction l with
 | nil=> rfl
 | cons i l ih=>
    by_cases h:i∈ liftK S p
    · rw [List.filter_cons_of_pos (by simpa using h),paint,paint,rankG,sit_m,ih]; rfl
    rw [List.filter_cons_of_neg (by simpa using h),paint,rankG, if_neg h,one_mul,ih]
open scoped Classical
-- exact choice sum under all label packs. expand with recursion carrying l as background selector. add new port does not affect products evaluated for current FULL monk, but shift cones only for l-toFinset.
lemma capPure(X:Finset (Kite S r))(u:Set.PairwiseDisjoint ((liftK S X):Set (Hos S r)) (stem S))(p:Set.InjOn Prod.fst (X:Set (Kite S r))): pureK S X:=by
 intro i k j v g; exact u (mem_image_of_mem Prod.fst (show i∈ X from k)) (mem_image_of_mem Prod.fst (show j∈ X from v)) (fun e=>g (p k v e))
lemma pray (i: Kite S r)(p: Finset (Kite S r))(l:List (Hos S r))(h:i.1∉ l): paint S D V X T U G (insert i p) l=paint S D V X T U G p l:=by
 induction l with
 | nil=> rfl
 | cons j l ih=>
    rw [List.mem_cons,not_or] at h; rw [paint, paint, ih h.2]; congr 1; have hs: liftK S (insert i p) = insert i.1 (liftK S p):= image_insert ..; have hx: i.1∉ l.toFinset:=by simpa using h.2
    unfold rankG; simp only [legend,clipM,hs,filter_insert,if_neg h.1,mem_insert, or_iff_right (Ne.symm h.1)] -- tune hx; remove inter
    rw [show insert i.1 (liftK S p)∩l.toFinset= liftK S p ∩ l.toFinset from Finset.ext fun j=>by simp only [mem_insert,mem_inter]; constructor; intro ⟨g,u⟩; exact ⟨g.resolve_left (fun p'=> hx (p' ▸ u)),u⟩; exact fun k=>⟨Or.inr k.1,k.2⟩]
lemma solo (p:Finset (Kite S r))(i:Hos S r)(h:pureK S p)(y)(g:(i,y)∈ p): legend S p i={(i,y)}:= Finset.ext fun a=>by rw [mem_singleton]; constructor; intro t; exact proud_p S p h (mem_filter.mp t).1 g (mem_filter.mp t).2; exact fun l=> l.symm ▸ (mem_filter.mpr ⟨g,rfl⟩)
end YM.CF.Eire
