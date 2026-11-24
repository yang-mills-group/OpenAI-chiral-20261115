import YM.CF.Lich.Wart
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
-- symmetric independent susceptibility stencils
local notation "m"=> Domain N B
local notation "m'"=> Domain P B
variable (t w:ℝ){M:Monk SU.group S}
variable {X:Support (Domain N B)}(H:Duo SU.group S U M X)(p:Ready T x)(hv:1000≤radiusB x)(h:shovel S.patch+10≤radiusB x)
private def home(i:Sat S):Support (Domain N B):= match i with
| .inl i=> startPos S i
| .inr (.inl i)=> pinPos i
| .inr (.inr i)=> Tarn.grove S i
private def parentX(i:Sat S):Site (Domain N B):=match i with
| .inl i=> S.ratio.parent i.1
| .inr (.inl i)=> i.1
| .inr (.inr i)=> S.ratio.parent i.1
lemma hold_s(i:Sat S): parentX i∈home i:=by rcases i with i|i|i; exact mem_image_of_mem _ (Work.E01.base_touched i); exact mem_insert_self ..; exact mem_image_of_mem _ (mem_insert_self ..)
def domeQ(k:ℕ)(i:Sat S): Palot.leaf (Site (Domain N B)):= ⟨halo k (home i),_,halo_subset _ _ (hold_s i)⟩
local notation "b'"=> (j+l+200)*radiusB x
local notation "b₀"=> radiusB x
include H p hv
lemma borne(i:Bond m')(g: (domeQ b' (S:=S) (.inr (.inr i))).val ⊆ X): boon A i U=boon A i M:=by
 let C:= Tarn.grove S i; have ht(o: Site (Domain N B))(v:o∈C):Beat.shadows (o:=o) X b':= (Corona.halo_mono le_rfl (singleton_subset_iff.mpr v)).trans g
 let O:=S.ratio.parent i.1; have hx:= ht O (mem_image_of_mem _ (mem_insert_self ..)); let p':=(j+104)*radiusB x
 let D(N:Monk SU.group S):Prop :=∃ j'∈(locals N.key N.key x N.park p')ᶜ,j'.val.val=i
 have hy(Fw Vw:Monk SU.group S)(u:Beat Fw Vw X)(g:D Fw):D Vw:=by
    obtain ⟨j',r,J⟩:=g; obtain ⟨k,l'⟩:= (u.scope (r:=0) (x:=x) (o:=O) (by simp only [Nat.add_mul]; omega) hx).switch j' (by rw [J]; simp [O]); have hk:= l'.symm.trans J
    refine ⟨k,mem_compl.mpr (fun z=> mem_compl.mp r (mem_filter.mpr ⟨mem_univ _,?_⟩)),hk ⟩ -- loses z relevance prove
    change _∨_; rw [J]; rcases (mem_filter.mp z).2 with t|t
    · exact Or.inl (u.sym.same hx (show O∈Vw.key.dome p' from (by unfold O; rw [←hk]; exact t)) (by change separation O O+p'≤_; rw [separation_self]; unfold p'; simp only [Nat.add_mul]; omega))
    have he: S.ratio.parent (i.1+step i.2)∈Vw.key.dome p':=by rw [← hk]; exact t
    exact Or.inr (u.sym.same hx he (by unfold O p'; simp only [Nat.add_mul]; have ht:= Work.E03.parent_step S i.1 i.2; omega))
 unfold boon; by_cases he:D U
 · let hz:=hy _ _ H.toBeat he; unfold D at he hz; rw [dif_pos he,dif_pos hz]; apply congrArg (broad q θ); exact H.toBeat.reflected p hv (he.choose_spec.2.trans hz.choose_spec.2.symm) (by rw [he.choose_spec.2]; exact (Corona.halo_mono (Nat.mul_le_mul_right _ (by omega)) (Subset.refl _)).trans hx)
 rw [dif_neg he,dif_neg (mt (hy _ _ H.toBeat.sym) he)]
include h
lemma payT(i:Cell m')(v:(domeQ (S:=S) b' (.inl i)).val⊆ X): portF A U t w (.inl i)=portF A M t w (.inl i):=by
 have he(u: Site m)(hx:u∈home (S:=S) (.inl i)):Beat.shadows (o:=u) X b':= (Corona.halo_mono le_rfl (singleton_subset_iff.mpr hx)).trans v
 have ht:= he _ (hold_s (S:=S) (.inl i))
 have hp(r)(p:r≤ b'):Disjoint (home (S:=S) (.inl i)) (U.key.dome r) ↔ Disjoint (home (S:=S) (.inl i)) (M.key.dome r):=by
    have hp(u)(v:u∈home (S:=S) (.inl i)):u∈U.key.dome r ↔ u∈M.key.dome r:=⟨fun t=>H.toBeat.same (he _ v) t (by rw [separation_self]; omega),fun t=>H.toBeat.sym.same (he _ v) t (by rw [separation_self]; omega)⟩
    exact ⟨fun h=>Finset.disjoint_left.mpr fun u v t=>disjoint_left.mp h v ((hp _ v).2 t),fun h=>Finset.disjoint_left.mpr fun u v t=>disjoint_left.mp h v ((hp _ v).1 t)⟩
 unfold portF; specialize hp ((j+110)*b₀) (by simp only [Nat.add_mul]; omega); dsimp only [home] at hp; dsimp only [parentX] at ht; simp only [nearFace, mem_compl,mem_filter,mem_univ,true_and, Sum.elim_inl,hp]; have he:Beat.shadows (o:=S.ratio.parent i.1) X ((l+63)*b₀):= (Corona.halo_mono (Nat.mul_le_mul_right _ (by omega)) (Subset.refl _)).trans ht; split_ifs; rfl; exact H.biri p hv i he -- note neg-neg splits
lemma payC(i:Bond m)(v:(domeQ (S:=S) b' (.inr (.inl i))).val⊆ X): portF A U t w (.inr (.inl i))=portF A M t w (.inr (.inl i)):=by
 have he(u: Site m)(hx:u∈home (S:=S) (.inr (.inl i))):Beat.shadows (o:=u) X b':= (Corona.halo_mono le_rfl (singleton_subset_iff.mpr hx)).trans v
 have ht:= he _ (hold_s (S:=S) (.inr (.inl i)))
 have hp(r)(p:r≤ b'):Disjoint (home (S:=S) (.inr (.inl i))) (U.key.dome r) ↔ Disjoint (home (S:=S) (.inr (.inl i))) (M.key.dome r):=by
    have hp(u)(v:u∈home (S:=S) (.inr (.inl i))):u∈U.key.dome r ↔ u∈M.key.dome r:=⟨fun t=>H.toBeat.same (he _ v) t (by rw [separation_self]; omega),fun t=>H.toBeat.sym.same (he _ v) t (by rw [separation_self]; omega)⟩
    exact ⟨fun h=>Finset.disjoint_left.mpr fun u v t=>disjoint_left.mp h v ((hp _ v).2 t),fun h=>Finset.disjoint_left.mpr fun u v t=>disjoint_left.mp h v ((hp _ v).1 t)⟩
 unfold portF; specialize hp ((j+100)*b₀) (by simp only [Nat.add_mul]; omega); dsimp only [home] at hp; dsimp only [parentX] at ht; simp only [nearNoise, mem_compl,mem_filter,mem_univ,true_and, Sum.elim_inl, Sum.elim_inr,hp]; have he:Beat.shadows (o:=i.1) X ((l+68)*b₀):= (Corona.halo_mono (Nat.mul_le_mul_right _ (by omega)) (Subset.refl _)).trans ht; split_ifs; rfl; exact H.ebb_p p hv h i he w
omit h in
lemma payB (i:Bond m')(v:(domeQ (S:=S) b' (.inr (.inr i))).val⊆ X): portF A U t w (.inr (.inr i))=portF A M t w (.inr (.inr i)):=by
 dsimp only [portF, Sum.elim_inr]; exact borne A U H p hv i v
omit H h p hv
lemma sat_i{L:Sat S→ Prop}(a:∀ i,L (.inl i))(b:∀ i,L (.inr (.inl i)))(c:∀ i,L (.inr (.inr i))) :∀ j':Sat S,L j':=by rintro (i|i|i); exact a i; exact b i; exact c i -- not dependent elim!
include H h p hv
lemma payF(i:Sat S)(v:(domeQ (S:=S) b' i).val⊆ X): portF A U t w i=portF A M t w i:= sat_i (L:=fun i=>(domeQ (S:=S) b' i).val ⊆ X→portF A U t w i=portF A M t w i) (payT A U t w H p hv h) (payC A U t w H p hv h) (payB A U t w H p hv) i v
end Muster
end YM.CF.Lich
