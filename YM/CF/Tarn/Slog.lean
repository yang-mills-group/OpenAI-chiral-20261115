import YM.Primitives.HAAR_LOG_JETS.Guard
import YM.CF.Tarn.Haar
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Tarn
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch MeasureTheory NormedSpace Nacre Braid Font
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace Matrix Kronecker
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Push.Uniform (curve Slope tint partSpace meetVar)
open AnalyticBridge.Annulus1AD AnalyticBridge.SectorAffine Oriented Esti Vol Bloch Exterior Jet
open RG Forge Cay Slate Rel
open Arena
local notation "G"=> SU.group
variable {c f:Side}{S:StepData c f}{T:Tube SU.group S}{F:Forest S.ratio}{q:Chi}{s:Signed}{l n:ℕ}{x d β C D σ m:ℝ}{P:Tab S}{V:Config SU.group c}
open Cube
variable {r:ℕ}{u v W a b w s':ℝ}{i:Site c}{F:Tab S}{K:Teller G}{P': Tab S}
section
variable (T:Tube G S)(x:ℝ)
variable(q:Chi)(d:ℝ)(l:ℕ)(R:ChartRatio G)(t:ℝ)
open AnalyticBridge.GaussianFieldAlignment Orthogonal Gauges Locations PhysicalNext.OrderedAffine2B.SymRows Tensor Channels Primitives.HaarLogJets.Guard
open Souk
variable {M N: Monk G S}{H: Support c}{P P':Tab S}
def evoke(P:Tab S): Active (bareStores S) x P.1≃ P.1.Free:= { toFun:=fun i=>i.val, invFun:=fun i=>⟨i,notChilled S P.1 x i⟩,left_inv:=fun _=>rfl,right_inv:=fun _=>rfl}
lemma orchard(U:Config G c)(P:Tab S)(o:Site c): let M:= bunk S P U; HWork T x q d l R t M o= (∑ i:P.1.Free, ansC (S:=S) o i.val*logGuard q R t (M.rich x T q d l 0 ((evoke x P).symm i)):ℝ):=by intro M; unfold HWork; rw [← Equiv.sum_comp (evoke x P)]; simp_rw [Equiv.symm_apply_apply]; rfl
-- all H reads general also
abbrev gate(M:Monk G S)(o:Site c):= univ.filter fun i:M.zoo x=> o∈grove S i.val.val
def seat (M:Monk G S)(i:M.zoo x)(o:Site c):= ansC (S:=S) o i.val.val*logGuard q R t (M.rich x T q d l 0 i)
lemma city_x(M: Monk G S)(o:Site c): HWork T x q d l R t M o=((∑ i∈gate x M o, seat T x q d l R t M i o):ℝ):=by
 unfold HWork; apply congrArg Complex.ofReal; apply Eq.symm (Finset.sum_subset (f:= fun i=>seat T x q d l R t M i o) (subset_univ _) ?_); intro i p h; unfold seat ansC; rw [if_neg (fun u=>h (mem_filter.mpr ⟨p,u⟩)),zero_mul]
lemma innZ(y: Site c)(i:Bond f)(h:y∈grove S i): separation y (S.ratio.parent i.1)≤1:=by
 rw [←mem_coe,grove_x] at h; rcases Set.mem_insert_iff.mp h with t|t; · rw [t]; simp
 rw [Set.mem_singleton_iff.mp t,separation_comm]; exact Work.E03.parent_step S i.1 i.2
lemma cit_p (i:Site c)(h:Ready T x)(ht:1000 ≤ radiusB x)(p:Beat.shadows (o:=i) H (horn x l)): Virt S (fun M=>HWork T x q d l R t M i) H:=by
 intro A B u; dsimp only; rw [city_x,city_x]; refine congrArg Complex.ofReal ?_
 have he(U V:Monk G S)(h: Beat U V H)(j)(p':j∈gate x U i):∃ v∈gate x V i,j.val.val=v.val.val :=by -- tune
    have hz:= (mem_filter.mp p').2; let s:= S.ratio.parent j.val.val.1; have hv:= innZ _ _ hz; have hh:= h.scope (x:=x) (r:=1) (by unfold Cay.horn; simp_rw [Nat.add_mul]; omega) p; obtain ⟨V,hV⟩:= hh.switch j hv; exact ⟨V,mem_filter.mpr ⟨mem_univ _,hV ▸ hz⟩,hV⟩
 choose f H' hp using he A B u -- not inhabited active. remove !
 refine Finset.sum_bij (fun i p=> f i p) H' (fun i hi j hj h=> Subtype.ext (Subtype.ext (hp i hi|>.trans ((congrArg (fun z:B.zoo x=>z.val.val) h).trans (hp j hj).symm)))) ?_ (fun i' hv=> ?_) -- tune
 · intro i p; obtain ⟨j,h,hp'⟩:=he _ _ u.sym _ p; exact ⟨j,h,Subtype.ext (Subtype.ext ((hp j h).symm.trans hp'.symm))⟩
 unfold seat; rw [hp i' hv]; apply congrArg (ansC (S:=S) _ _ * ·); apply congrArg (logGuard q R t); exact u.reflected h ht (hp i' hv) (aroundBk H p (by have he:=innZ _ _ ((mem_filter.mp hv).2); unfold Cay.horn; simp_rw [Nat.add_mul]; omega)) -- tune hp shadows
lemma paidz(i:Site c)(h:Kind S P P' (pavilion (horn x l) i))(U V:Config G c)(hv:drift G i (horn x l) U V)(p:Ready T x)(hp:1000 ≤radiusB x): MossZ T x q d l R t P i U=MossZ T x q d l R t P' i V:=by
 have he(U V:Config G c)(hr:drift G i (horn x l) U V): HWork T x q d l R t (bunk S P U) i=HWork T x q d l R t (bunk S P' V) i:=cit_p T x q d l R t i p hp (Subset.refl _) ⟨fun _ _=>Iff.rfl,h.site,fun i w=>h.edge i (w (mem_insert_self ..)),KinT h,fun i p _=>hr _ ((theatre ..).mp p),fun _ _=>rfl,fun _ _=>rfl⟩
 exact congrArg₂ (·-·) (he _ _ hv) (he _ _ (fun _ _=> rfl))
lemma izan(P:Tab S)(v:Mast G c)(ht:Fire T x P.1 P.2 l w n C v)(i:P.1.Free): let y:=w •v; let V:= satU G w v; (bunk S P V).rich x T q d l 0 ((evoke x P).symm i)= Eman P.1 i (flute P.1 (sol S T P.2 x P.1 l) 1 y):=by
 intro y V; let M:= bunk S P V; let A:= sol S T P.2 x P.1 l y
 have he:M.fuel x T q d l 0=leaveX P.1 x A:=by
    rw [oasisN T q x d l (M:=M) rfl, show M.bush x=1 from rfl, ←(ht.shine q d).2]; funext i; unfold liftN; rw [if_pos]; unfold green; simp [M,bunk,bareStores,Stores.dome,Stores.place,halo_spec] -- tune
 let u:=flute P.1 (sol S T P.2 x P.1 l) 1 y; change tape (M.fuel x T q d l 0) _= (Push.Uniform.paint _ _ u).2 _; rw [he,show u=meetVar y A from ?_, Push.Uniform.paint_meet]
 · rfl
 unfold u flute; rw [one_smul]; rfl
end
end YM.CF.Tarn
