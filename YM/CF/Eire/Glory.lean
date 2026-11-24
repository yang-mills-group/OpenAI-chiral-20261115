import YM.CF.Eire.Gown
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
-- proof-carrying split. no extra Path option dependence allowed per H. Dress open.
def blazon (i:Troupe S r ι)(H:Ride S): Cipher (mid N B):= if capG S (flags (temp x) M.V) (chillB M) R.p.threshold i H then Scion.vigor (U.stageT x l i) H else 0
variable {i j:Troupe S r ι} {H L T:Ride S}
local notation "B₀"=> BranchX S X k
lemma source_p(d:Disjoint (bay H) (bay L))(p:Palot.fits (BranchX S X k) i H)(h:Palot.fits (BranchX S X k) j L)(v: k=(l+90)*radiusB x)(t:1000 ≤ radiusB x)(z:Ready U.pipe x): U.bodyL x l (i∪j)= U.bodyL x l i* U.bodyL x l j:=by
 have ht(Y Z:Troupe S r ι)(H L:Ride S)(d:Disjoint (bay H) (bay L))(p:Palot.fits B₀ Y H)(h:Palot.fits B₀ Z L)(w:Rust (mid P B))(u:w∈ Y.toRight.toLeft): OpK S x R (trot S M (penn S (Y∪Z))) U.cloth U.pipe U.chi U.wage l w= OpK S x R (trot S M (penn S Y)) U.cloth U.pipe U.chi U.wage l w:=by
    unfold penn; rw [toLeft_union]; symm; apply earnR _ x _ _ _ _ _ _ _ _ _ (burn_r S M _ _ _ _ d (fun i v=> litG S X h i v)) z t U.copies w _ (fun _ _=>rfl); have hp: Lattice.halo k (Eire.port S w) ⊆ bay H:=lodX S X p _ (mem_toRight.mp (mem_toLeft.mp u)); exact (chilling (by rw [v]; simp_rw [Nat.add_mul]; omega : (l+75)*radiusB x≤k) (Subset.refl _)).trans hp
 have he: Disjoint i j:= pli S X p h d; have hv: Disjoint i.toRight.toLeft j.toRight.toLeft:=Finset.disjoint_left.mpr fun y w t=> Finset.disjoint_left.mp he (mem_toRight.mp (mem_toLeft.mp w)) (mem_toRight.mp (mem_toLeft.mp t))
 unfold bodyL lure
 rw [show (i∪j).toRight.toLeft=i.toRight.toLeft ∪ j.toRight.toLeft from by simp only [toRight_union,toLeft_union],prod_union hv]; exact congrArg₂ (·*·) (prod_congr rfl fun k v=> ht i j H L d p h k v) (prod_congr rfl fun z t=> by rw [union_comm i, ht j i L H d.symm h p z t])
structure Risen (i j:Troupe S r ι)(H L:Ride S): Prop where
 pose: CrownB G S e_ (U.coats (i∪j)) (U.coats i) k H
 tendB p:p∈ liftK S i.toLeft→ U.rare (penn S (i∪j)) p=U.rare (penn S i) p
 tendC p:p∈i.toRight.toRight→ U.coin (penn S (i∪j)) p=U.coin (penn S i) p
lemma brew_t (d:Disjoint (bay H) (bay L))(p:Palot.fits B₀ i H)(h: Palot.fits B₀ j L)(g: U.Risen i j H L)(h':U.Risen j i L H) : U.brew (i∪j) = U.brew i*U.brew j:=by
 unfold brew; dsimp only; have hp:= quietK S H L _ _ d (moon p) (moon h); have ht:liftK S (i∪j).toLeft=liftK S i.toLeft∪ liftK S j.toLeft:=by simp only [liftK,toLeft_union, image_union] -- tune
 have he:Disjoint i.toRight.toRight j.toRight.toRight:=by apply Finset.disjoint_left.mpr; intro u v w; exact disjoint_left.mp (pli S X p h d) (mem_toRight.mp (mem_toRight.mp v)) (mem_toRight.mp (mem_toRight.mp w))
 rw [ht,prod_union hp,toRight_union, toRight_union,prod_union he]
 rw [prod_congr (Eq.refl (liftK S i.toLeft)) (fun y t=>g.tendB y t), prod_congr (Eq.refl i.toRight.toRight) (fun y t=>g.tendC y t), union_comm i,prod_congr (Eq.refl (liftK S j.toLeft)) (fun y t=>h'.tendB y t),prod_congr (Eq.refl j.toRight.toRight) (fun y t=>h'.tendC y t)]; ring
lemma vote (d:Disjoint (bay H) (bay L))(p:Palot.fits B₀ i H)(h: Palot.fits B₀ j L)(g: U.Risen i j H L)(h':U.Risen j i L H)(c: U.songP (i∪j)=U.songP i*U.songP j)(v:k=(l+90)*radiusB x)(t:1000≤ radiusB x)(z:Ready U.pipe x) : Scion.vigor (U.stageT x l (i∪j)) (H⊔L)= Scion.vigor (U.stageT x l i) H* Scion.vigor (U.stageT x l j) L:=by
 have he(Q L H:Ride S)(q:i=i)(p:S.ratio=ratio G)(Q':Troupe S r ι)(q':Troupe S r ι)(v:U.Risen Q' q' H L) (w:Q≤H⊔L)(d:Disjoint (bay H) (bay L))(x:Twig (Single (mid P B)))(u:x∈mintK S (Q⊓H)): (U.heatT (Q'∪q') Q).seats x= (U.heatT Q' (Q⊓H)).seats x ∧ ∀ i,(U.heatT (Q'∪q') Q).pals x i=(U.heatT Q' (Q⊓H)).pals x i := ⟨drift_l G S U.odds _ U.yawB _ _ _ _ _ U.guardP d w v.pose x (bay_m inf_le_right u),fun i=> drift_r G S U.odds _ U.yawB _ _ _ _ _ U.guardP d w v.pose x i (bay_m inf_le_right u)⟩ -- tune signatures
 apply engine H L _ _ _ d (Finset.sup_le p) (Finset.sup_le h); intro T t' w; have hh:T≤L⊔H:=by rw [sup_comm]; exact t'
 let Y:=U.stageT x l (i∪j); constructor
 · exact congrArg Subtype.val (U.source_p x l d p h v t z)
 · exact c
 · exact congrArg Subtype.val (U.brew_t d p h g h')
 · exact fun j u=>(he T L H rfl U.axes _ _ g t' d j u).1
 · intro X hp; change (U.heatT (i∪j) T).seats X=_; rw [union_comm]; exact (he T H L rfl U.axes _ _ h' hh d.symm _ hp).1
 · exact fun j u y _ => (he T L H rfl U.axes _ _ g t' d _ u).2 y
 · intro X hp y p'; change (U.heatT (i∪j) T).pals X y=_; rw [union_comm]; exact (he T H L rfl U.axes _ _ h' hh d.symm X hp).2 y
 intro u x v p; exact ⟨drift_z G S U.odds _ U.yawB _ _ _ _ U.guardP d t' _ _ (bay_m inf_le_right x) (bay_m inf_le_right p),drift_z G S U.odds _ U.yawB _ _ _ _ U.guardP d.symm hh _ _ (bay_m inf_le_right p) (bay_m inf_le_right x)⟩
end Dress
end YM.CF.Eire
