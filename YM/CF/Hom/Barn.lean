import YM.CF.Reef.Bice
import YM.Next.STATIONARY.FullPlanned
import YM.Next.FREE_KERNELS.Rack
import YM.Next.FLUCTUATIONS.Grants
import YM.Extra.WILSON_STARTUP.Match
set_option autoImplicit false
noncomputable section
namespace YM.CF.Hom
open Function Filter NormedSpace Lattice Laurent Bloch Wilson Precision RG Work Exterior Next.Free Work.F08 Craft Pressure Finset
open scoped Topology BigOperators Matrix
variable {G:Gauge}{j:ℕ}{K:KernelChoices}{p q:Clip}{η C a σ:ℝ}
-- rank-one initial special
lemma metric0 {T:Bed}(p:Defined K.penalty 0 (Train.top j) T)(v:∀ n,T.diagonal.acts n=1)(h:4≤j) (n:Side): T.metric.acts n=1:=by
 have he: (pink K.penalty (Train.top j)).acts n=1:=by rw [←p.diag,v]
 let X:=Train.top j; let A:= K.penalty; let G:= (amend A 0 X).acts n; let W:=(blue A X).acts n; obtain ⟨hx,hy,hV⟩:=obligations A 0 K.penalty_pos le_rfl h X n; change (pink K.penalty (Train.top j)).acts n * W=1 at hx; rw [he,one_mul] at hx; rw [p.metric]; change G=1
 have hu: G*W=1:=by have hh:(pledge A 0 X).acts n=W:= (hy.2).trans (by rw [zero_smul, add_zero]); rw [← hh]; exact hy.1
 rwa [hx,mul_one] at hu
open WilsonStartup
private def roster(T:Bed)(p:Clip):Bed:={T with roots:=(Design.bed p).roots}
def MainIn (G:Gauge)(p:Clip) (H:Bed)(μ a M: ℝ) := H.covered a M∧(∀ n,Floor H p n μ M)∧ ∀ n, Bid.Sworn H n G
lemma worship (hp:p.direct≤1)(j:ℕ)(h:4≤j) (C:ℝ) (hv:1≤C)(A:ℝ) (H:BottomQuote K j 0 A σ η C)(hb:p.direct≤ A) : ∃ Z:Bed,Defined K.penalty 0 (Train.top j) Z ∧ Attached Z (Design.top G p)∧MainIn G p Z η σ C:=by
 obtain ⟨M,x,y,f,g,t⟩:=H p hb (Train.top j)
 let U:= roster M p; have ht(n): M.metric.acts n=1:= metric0 x (t rfl) h n
 refine ⟨U,{x with }, ⟨(Design.attached p (G:=G)).layout⟩,?_,fun n=> ?_,fun n=> g n _⟩ -- tune
 · exact ⟨y.1, y.2.1,y.2.2.1, (Design.covered p hp hv).2.2.2.1, y.2.2.2.2⟩
 let v:= f n; refine {v with roots:=?_}; rw [show U.full p n=(Design.bed p).full p n from rfl, Design.full_root p hp]; exact (ht n).symm
lemma p_coin(k:ℝ)(p:0<k):∃ s:Clip, s.direct ≤ 1 ∧ s.direct≤ k:=by
 let x:=min 1 k; have he:0<x:=lt_min zero_lt_one p; exact ⟨⟨x,x/17,1,he,by positivity,by linarith,one_pos⟩,min_le_left ..,min_le_right ..⟩
structure Trail (j:ℕ)(K:KernelChoices)(m:ℝ)(N:ℕ)(p:Clip)(a η D:ℝ):Prop where
 sturdy:0≤m
 standard:∀ q:Clip,q.direct=p.direct→BottomQuote K j m q.direct a η D
 initial:∀ q:Clip,q.direct=p.direct→BottomQuote K j 0 q.direct a η D
 hopT:HopQuote K j j m m a η D N
 hopI: HopQuote K j j 0 m a η D N
 tight:p.direct ≤1
lemma trailV(j:ℕ)(k:4≤j)(K:KernelChoices):∃ n:ℕ,∃ m η a C:ℝ, 0 < η ∧ 0<a∧ 1≤C∧∃ p:Clip, Trail j K m n p a η C:=by
 obtain ⟨l,hb,H⟩:=Next.Free.buys K j j
 obtain ⟨σ,c,M,V,u,hA,f⟩:= H l l hb.le le_rfl; obtain ⟨σ',d,Y,v,hU,hD,F⟩:= H 0 l le_rfl le_rfl
 obtain ⟨w,x,y,C,h,hP,hx,hC,U⟩:= bid_bed K.penalty l K.penalty_pos hb.le k
 obtain ⟨W,X,z,D,hW,hX,hz,hR,Q⟩:= bid_bed K.penalty 0 K.penalty_pos le_rfl k
 obtain ⟨p,hp,hr⟩:= p_coin _ (lt_min h hW); have hh:Mag j j:= ⟨k,k,Or.inl rfl⟩
 let a:=min (min x σ) (min σ' X); let r:=min (min y z) (min c d); let C':= max 1 (max (max C D) (max M Y)); refine ⟨max V v,l,r,a,C', lt_min (lt_min hx hz) (lt_min hA hD),lt_min (lt_min hP u) (lt_min hU hX),le_max_left ..,p,hb.le,fun q e=> ?_,fun q e=> ?_,?_,?_,hp⟩
 · rw [e]; exact BottomQuote.revise (fun R v=> U R (v.trans (hr.trans (min_le_left ..)))) (by unfold a; grind) (by unfold r; grind) (by unfold C'; grind)
 · rw [e]; exact BottomQuote.revise (fun R v=> Q R (v.trans (hr.trans (min_le_right ..)))) (by unfold a; grind) (by unfold r; grind) (by unfold C'; grind)
 · exact HopQuote.revise (f hh) (by unfold a; grind) (by unfold r; grind) (by unfold C'; grind) (le_max_left ..)
 exact HopQuote.revise (F hh) (by unfold a; grind) (by unfold r; grind) (by unfold C'; grind) (le_max_right ..)
end YM.CF.Hom
