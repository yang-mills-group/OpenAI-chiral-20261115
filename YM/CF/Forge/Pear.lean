import YM.CF.Esti.Song
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Forge
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD Ac Esti
variable {G:Gauge}{c f:Side}{S:StepData c f}{r v l:ℕ}{w x β d:ℝ}{q:Chi}{T:Tube G S}
-- carry unrestricted product variables
structure Monk (G:Gauge)(S:StepData c f) where
 key:Stores S
 park:Forest S.ratio
 k:S.Choices
 V:Config G c
 U:Config G f
 z: Directions G f
namespace Monk
variable (M:Monk G S) (x:ℝ)
abbrev zoo := Active M.key x M.park
abbrev loc:= Frozen M.key x M.park
def bush : LinkArray G (M.loc x):=fun i=> M.U i.val.val
def bell : LogArray G (M.zoo x):= fun i=> M.z i.val.val
variable (T:Tube G S)(q:Chi)(d:ℝ)(l:ℕ)(β:ℝ)
def fuel:=realP β T M.park M.key M.V M.k x l q d (M.bush x) (M.bell x)
def rich:=putU β T M.park M.key M.V M.k x l q d (M.bush x) (M.bell x)
def sent:=fieldU β T M.park M.key M.V M.k x l q d (M.bush x) (M.bell x)
end Monk
structure Beat (M N:Monk G S)(X:Support c):Prop where
 road(i): i∈X→(i∈M.key.place↔i∈N.key.place)
 fr (i):i∈X→ M.k.1 i=N.k.1 i
 fe(i):pinPos i ⊆ X→ M.k.2 i=N.k.2 i
 trunks(i):(S.ratio.parent i.1)∈X→(i∈M.park.trunks↔i∈N.park.trunks)
 view: Agrees X M.V N.V
 data(i):Next.SectorChange.points S i ⊆ X→ M.U i=N.U i
 color(i):Next.SectorChange.points S i ⊆ X→ M.z i=N.z i
abbrev Beat.shadows{o:Site c}(X:Support c)(r:ℕ):Prop:= halo r {o} ⊆ X
variable {M N:Monk G S}{X:Support c}
namespace Beat
lemma mono (h:Beat M N X){Y:Support c}(u:Y ⊆ X):Beat M N Y:= ⟨fun i p=>h.road _ (u p),fun i p=>h.fr _ (u p),fun _ p=>h.fe _ (Subset.trans p u),fun _ p=>h.trunks _ (u p),fun i p l=>h.view _ (u p) (u l), fun i p=>h.data _ (p.trans (Finset.coe_subset.mpr u)),fun _ p=>h.color _ (p.trans (Finset.coe_subset.mpr u))⟩
variable (h:Beat M N X) {o z: Site c} {b:ℕ}
include h
lemma sees (u:shadows (o:=o) X b) {i:Site c}(p:separation o i≤b):i∈X:= u (halo_spec.mpr ⟨_,mem_singleton_self _,p⟩) -- h not needed
lemma same (u:shadows (o:=o) X b)(p:z∈ M.key.dome r)(t:separation o z +r ≤ b): z∈ N.key.dome r:=by
 obtain ⟨i,p,e⟩:= halo_spec.mp p; exact halo_spec.mpr ⟨i,(h.road i (h.sees u ((separation_triangle o z i).trans (by rw [separation_comm z i]; omega)))).mp p,e⟩
lemma sym:Beat N M X:=⟨fun i l=> (h.road i l).symm,fun i l=>(h.fr i l).symm,fun i l=>(h.fe i l).symm,fun i l=>(h.trunks i l).symm,fun i w p=>(h.view _ w p).symm,fun i l=> (h.data i l).symm,fun i l=>(h.color i l).symm⟩
lemma outC (u:shadows (o:=o) X b)(p:r+1≤b){i:Bond f}(w:separation o (S.ratio.parent i.1)≤r):Next.SectorChange.points S i⊆ X:=by
 intro j t; rcases Set.mem_insert_iff.mp t with g|g; rw [g]; apply h.sees u (by omega); rw [Set.mem_singleton_iff.mp g]; apply h.sees u; refine (separation_triangle o (S.ratio.parent i.1) _).trans ?_; have h:=Work.E03.parent_step S i.1 i.2; omega
lemma scope (hx:r+1+10*radiusB x+1 ≤ b)(u:shadows (o:=o) X b): Scan S x o r M.key N.key M.park N.park M.k N.k M.V N.V (M.bush x) (N.bush x):=by
 have he{e:Bond c}(g:separation o e.1 ≤ r):separation o (e.1+step e.2) ≤ r+1:=(separation_triangle o e.1 (e.1+step e.2)).trans (Nat.add_le_add g (Work.E01.sep_step_le ..))
 refine ⟨fun i p=> h.road i (h.sees u (by omega)),fun i p=>h.fr i (h.sees u (by omega)),fun i p=> ?_,fun i p=>h.trunks i (h.sees u (by omega)),fun i (p:separation o i.1≤r)=>h.view i (h.sees u (by omega)) (h.sees u ((he p).trans (by omega))),fun i j p l=> ?_⟩ -- annoy needs Set val
 · exact h.fe i (insert_subset (h.sees u (by omega)) (singleton_subset_iff.mpr (h.sees u ((he p).trans (by omega)))))
 unfold Monk.bush; exact (h.data _ (h.outC u (by omega : r+1≤b) p)).trans (congrArg N.U l)
lemma reaction(hr:Ready T x)(p:1000≤radiusB x){i:Rows.In x M.key M.park (G:=G)}{i':Rows.In x N.key N.park (G:=G)}(hp:PatchReads.lift i=PatchReads.lift i')(u:shadows (o:=front M.key M.park i) X ((l+62)*radiusB x)): Monk.fuel M x T q d l β i= Monk.fuel N x T q d l β i':=by
 let a:=coupling β; let T' :=front M.key M.park i; let R:=radiusB x
 let U:=credW T M.key M.park M.k q d x (M.bush x) l M.V; let U':=credW T N.key N.park N.k q d x (N.bush x) l N.V
 have hh:=h.scope (x:=x) (r:=(l+50)*radiusB x) (by simp_rw [Nat.add_mul]; omega) u -- implicit x
 change liftN T x M.V M.k M.key M.park q d (M.bush _) l i+a*(U *ᵥ tape.symm (M.bell x)) i= liftN T x N.V N.k N.key N.park q d (N.bush _) l i'+ a*(U' *ᵥ tape.symm (N.bell x)) i'
 rw [liftN_read hr (hh.lower (Nat.mul_le_mul_right _ (by omega))) hp]; congr 2 -- tune
 simp only [Matrix.mulVec,dotProduct]; refine PatchReads.sum_eq (hh.lower (r':=R) (by unfold R; simp_rw [Nat.add_mul]; omega)) (fun j hj=>?_ ) (fun j hj=>?_) fun j j' hj hj'=> ?_
 · rw [show U i j=0 from (supportH hr p l).rank _ _ hj,zero_mul]
 · rw [show U' i' j=0 from (supportH hr p l).rank _ _ ((faces hp).symm ▸ hj),zero_mul] -- tune
 rw [show U i j=U' i' j' from layPt (q:=q) (D:=d) (Y:=M.bush x) (Y':=N.bush x) (l:=l) hr p i i' j j' (hh.lower (Nat.mul_le_mul_right _ (by omega))) hp hj'] -- abbreviations
 apply congrArg (U' i' j' * ·); change M.z j.1.val.val j.2 = N.z j'.1.val.val j'.2
 have hg: j.1.val.val=j'.1.val.val:=congrArg Prod.fst hj'; rw [h.color _ (h.outC u (by simp_rw [Nat.add_mul]; unfold R; omega) hj),hg, show j.2=j'.2 from congrArg Prod.snd hj']
lemma reflected(hr:Ready T x)(p:1000≤radiusB x){i:Active M.key x M.park}{j:Active N.key x N.park}(hp:i.val.val=j.val.val)(u:shadows (o:=S.ratio.parent i.val.val.1) X ((l+62)*radiusB x)):Monk.rich M x T q d l β i=Monk.rich N x T q d l β j:=by ext z; exact h.reaction (i:=(i,z)) (i':=(j,z)) hr p (congrArg (fun e:Bond f=>(e,z)) hp) u
lemma backF(hr:Ready T x)(p:1000≤radiusB x)(i:Bond f)(u:shadows (o:=S.ratio.parent i.1) X ((l+62)*radiusB x)): Monk.sent M x T q d l β i= Monk.sent N x T q d l β i:=by
 let o:=S.ratio.parent i.1; have hh: Scan S x o 0 M.key N.key M.park N.park M.k N.k M.V N.V (M.bush x) (N.bush x):= h.scope (by simp_rw [Nat.add_mul]; omega) u; have hx:separation o (S.ratio.parent i.1) ≤ 0:=by unfold o; simp
 by_cases he:i∈M.park.trunks; · exact (M.park.on_tree _ ⟨i,he⟩).trans (N.park.on_tree _ ⟨i,(hh.trunks _ hx).1 he⟩).symm -- tune
 let a:M.park.Free:=⟨i,he⟩; let b:N.park.Free:=⟨i,mt (hh.trunks i hx).2 he⟩; have hp:=hh.freeze_same (i:=a) (j:=b) hx rfl
 unfold Monk.sent fieldU Next.SectorChange.physical; rw [show i=a.val from rfl,M.park.off_tree, show a.val=b.val from rfl,N.park.off_tree]; unfold returned thaw
 by_cases hv:chill M.key x M.park a
 · let I:Frozen M.key x M.park:=⟨a,hv⟩; let J:Frozen N.key x N.park:=⟨b,hp.mp hv⟩; rw [show a=I.val from rfl, show b=J.val from rfl, freeze_held,freeze_held]; exact hh.held I J hx rfl
 let I:Active M.key x M.park:=⟨a,hv⟩; let J:Active N.key x N.park:=⟨b,mt hp.mpr hv⟩; rw [show a=I.val from rfl, show b=J.val from rfl,freeze_regular,freeze_regular]; unfold release putU; -- try
 exact congrArg₂ (·*·) (congrArg G.lieExp (h.reflected (i:=I) (j:=J) (β:=β) (d:=d) (q:=q) hr p rfl u)) (rep_share (S:=S) hh.outer i hx)
end Beat
end YM.CF.Forge
