import YM.CF.Atala.Wills
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Atala
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD Ac Esti
variable {G:Gauge}{c f:Side}{S:StepData c f}{r v l:ℕ}{w x β d:ℝ}{q:Chi}{T:Tube G S}
open CF.Forge
open Branch Tenant
section
variable {ι:Type*}
lemma grove_bars{P:ι→Support c}{p:Finset ι}(h:Spark P p)(A:ι→Support f)(g:∀ i∈p,Grove (terr _) (A i))(t:∀ i∈p,∀ j∈p, meets P i (P j) → meets A i (A j)): Grove (terr _) (p.biUnion A):=by
 obtain ⟨z,v⟩:= h.1; have hp(v:Grove (terr _) (A z)):(A z).Nonempty:=by generalize ha:A z =X at *; cases v<;> simp
 obtain ⟨x,e⟩:=hp (g z v); let X:= p.biUnion A
 have hz: ∀ i, chain P p z i → i∈ p → ∀ y∈ A i,Origin (terr _) X x y:=by
    intro i k; induction k with
    | refl=>intro _ y he; exact orig_sub (rooted (g z v) x e _ he) fun i h=> Finset.mem_biUnion.mpr ⟨z,v,h⟩
    | @tail a b j k ih=>
       obtain ⟨y,p,l⟩:= t b k.2.1 a k.1 k.2.2
       intro hb w e; exact Relation.ReflTransGen.trans (ih k.1 _ p) (orig_sub (rooted (g b hb) y l w e) fun _ h=> Finset.mem_biUnion.mpr ⟨b,hb,h⟩)
 apply Branch.trunk (B:=terr _) (mem_biUnion.mpr ⟨z,v,e⟩); intro y g; obtain ⟨i,p,h'⟩:=mem_biUnion.mp g; exact hz i (h.2 z v i p) p y h'
lemma spot_p(S:StepData c f)(i:Mark S): (spotting S i).Nonempty:=by
 cases i with
 | inl i=>cases i with| inl i=>exact ⟨_,mem_image_of_mem S.ratio.parent (YM.Work.E01.base_touched i)⟩ | inr i=>exact ⟨_,mem_insert_self ..⟩
 | inr i=>exact singleton_nonempty _
lemma spot_t(S:StepData c f)(i:Mark S){x y:Site c}(p:x∈spotting S i)(k:y∈spotting S i): separation x y ≤ 20:=by
 rcases i with (i|i)|i
 · obtain ⟨u,w,rfl⟩:=mem_image.mp p; obtain ⟨v,h,rfl⟩:=mem_image.mp k; have he:=Work.E04.parent_separation S.ratio u v; have hp:=Work.E01.sep_touched i _ w; have hh:=Work.E01.sep_touched i _ h; have hx:=separation_triangle u i.1 v; rw [separation_comm u i.1] at hx; omega
 · change x∈pinPos i at p; change y∈pinPos i at k; have hz:=Work.E01.sep_step_le (n:=c) i.1 i.2; simp only [pinPos,mem_insert,mem_singleton] at p k; rcases p with p|p<;>rcases k with k|k<;>subst x y<;> first|solve|simp|exact hz.trans (by decide)|exact (separation_comm ..).trans_le (hz.trans (by decide)) -- tune
 rw [mem_singleton.mp p,mem_singleton.mp k]; simp
lemma spark_t(S:StepData c f)(i:Mark S)(D:Site c→ Support f)(h:∀ x∈ spotting S i,Grove (terr _) (D x))(p:∀ x∈spotting S i,∀ y∈spotting S i,meets D x (D y)): Grove (terr _) ((spotting S i).biUnion D):=by
 let X:=spotting S i; apply grove_bars (P:=fun _=>({0}:Support c)) ⟨spot_p ..,fun x l y v=>?_⟩ D h (fun i w j g _=>p i w j g); -- syntax tune
 exact Relation.ReflTransGen.single ⟨l,v,0,mem_singleton_self _,mem_singleton_self _⟩
end
variable (S)
abbrev twinkle (y:Site c):ℕ→Support f:= fun r=> halo (S.ratio.count.val*(r+20)) {S.ratio.embed y}
def danceL(A:Stores S)(r:ℕ):= A.place.biUnion fun y=> twinkle S y r
lemma glen_x {i:Site f}{A:Stores S}{u:Site c}(p:separation u (S.ratio.parent i) ≤ r):i∈ twinkle S u r:=by
 apply halo_spec.mpr; let L:=S.ratio.count.val; have hx:= Corona.near S.ratio i; have hk:=Laic.emptio (S.ratio) u (S.ratio.parent i); refine ⟨_,mem_singleton_self _,(separation_triangle _ (S.ratio.embed (S.ratio.parent i)) i).trans ?_⟩ -- check names
 rw [separation_comm i] at hx; rw [hk,Nat.mul_add]; exact Nat.add_le_add (Nat.mul_le_mul_left _ p) (by omega)
lemma dance_cover (A:Stores S){i:Site f}(p: S.ratio.parent i ∈ A.dome r): i∈ danceL S A r:=by obtain ⟨t,h,v⟩:=halo_spec.mp p; exact mem_biUnion.mpr ⟨t,h,glen_x (A:=A) _ v⟩
lemma dance_g (O:Hos S r): Grove (terr _) (danceL S O.val r):=by
 let F(i):= (spotting S i).biUnion fun y=>twinkle S y r
 have ht(i:Mark S): Grove (terr _) (F i):=by
    apply spark_t S; intro i y; unfold twinkle; rw [←tract]; exact Tenant.glen .. -- tune
    intro x p y k; let K:=S.ratio.embed x; refine ⟨K,halo_spec.mpr ⟨_,mem_singleton_self _,?_⟩, halo_subset _ _ (mem_singleton_self K)⟩
    rw [show K=_ from rfl,Laic.emptio]; exact Nat.mul_le_mul_left _ ((spot_t _ i k p).trans (by omega))
 have hv(i:Mark S){x:Site c}(p:x∈Palm S r i): S.ratio.embed x∈F i:=by
    obtain ⟨y,p,v⟩:=halo_spec.mp p; exact mem_biUnion.mpr ⟨y,p,glen_x (A:=O.val) _ (Ratio.embed_parent .. |>.symm ▸ v)⟩ -- tune
 have he:Grove (terr _) ((plots O.val).biUnion F):= grove_bars O.property F (fun i _=>ht i) (fun i _ j _ ⟨x,k,q⟩=>⟨S.ratio.embed x,hv j k,hv i q⟩)
 rwa [danceL, place_plots,biUnion_biUnion] -- tune reverse
lemma floorX(A:Stores S): (danceL S A r).card ≤ A.shares *4 * (2*S.patch.L.val*(r+20)+1)^4:=by
 let F(y):=twinkle S y r
 apply Finset.card_biUnion_le.trans
 apply le_trans (sum_le_sum (g:=fun _=> (2*S.patch.L.val*(r+20)+1)^4) fun i _=> ?_)
 · rw [sum_const,nsmul_eq_mul]; apply Nat.mul_le_mul_right; rw [mul_comm A.shares]; exact Work.E01.place_card _ -- tune order
 exact (Corona.halo_size _ _).trans_eq (by change ({S.ratio.embed i}:Support f).card*_=_; simp [Nat.add_mul, StepData.ratio]; ring)
end YM.CF.Atala
