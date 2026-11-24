import YM.CF.Rel.Saint
set_option autoImplicit false
noncomputable section
namespace YM.CF.Rel
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch MeasureTheory NormedSpace Nacre Braid Font
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable{G:Gauge}{n:Side}{m l r:ℕ}{A C σ:ℝ}
open Stationary Push.Loops
abbrev ShowM(G:Gauge)(m:ℕ):= SpotG G (m+1)→ OutM m
abbrev Qind(n:Side)(G: Gauge)(m:ℕ):=SpotG G (m+1)× DialT n m × CurRun (m+1)
def hue(Q:SpotG G (m+1)→ noteG G m)(q: Qind n G m):ℂ:= Ca (Q q.1 q.2.2) q.2.1
def ValueQ(Q:SpotG G (m+1)→ noteG G m)(q:Qind n G m): SpaceX G n:=hue Q q • fans 0 (diskP 0 q.2.1 q.2.2) (rope (silica q.1))
def DabQ(Q:SpotG G (m+1)→ noteG G m)(q:Qind n G m): Salt n G:= fun x=> hue Q q*oct q.2.2 x q.1 q.2.1 0
abbrev Dent(n:Side)(G:Gauge)(m:ℕ):=SpotG G (m+1)× Fin (m+1) × DialT n m× TypeFace 3 × CurRun (m+1) × Axis
section legs
variable (F: ShowM G m)(Q:SpotG G (m+1)→noteG G m)(k:Site n)(D:Dent n G m)(i:Fin (m+1))(d:DialT n m)(s:SpotG G (m+1))(g:G.El)
def cape (k:Site n)(u:Dent n G m):Site n:= palm k u.2.1 u.2.2.2.2.2
def rub (u:Dent n G m):ℂ:= match u with| ⟨s,i,d,b,p,a⟩=> left ℂ 2 a b (p i)*sting k i a * B (F s i) p d b
def seedsV(u:Dent n G m):Disk n (m+1):= match u with | ⟨_,i,d,_,p,a⟩=>diskP 0 (d+reedU i a) p
def potsC:=rub F k D • fans 0 (seedsV D) (rope (silica D.1))
def trot :Salt n G:=fun x=> match D with | ⟨s,i,d,b,p,a⟩=> pailH (F s) k i x s d p b a
lemma trot_p : prism (m+1) (potsC F k D) (saltP (trot F k D)):=by
 obtain ⟨s,i,d,b,p,a⟩:=D
 let c:= left ℂ 2 a b (p i)*sting k i a * B (F s i) p d b
 let D' : DialT n m := d+reedU i a
 let W:= diskP 0 D' p
 have he : trot F k (s,i,d,b,p,a)=c • (fun x=> oct p x s D' 0):= rfl
 unfold potsC; rw [he, saltP_mul,show saltP _=vat W (rope (silica s)) from ?_]; exact prism.mul c (fans_p 0 W (rope (silica s))) -- tune
 exact funext fun i=> (oct_u s p i D').symm
lemma trot_c : serene (trot F k D):=by obtain ⟨s,i,d,b,p,a⟩:=D; intro x; exact (oct_v s p x (d+reedU i a)).const_mul (rub F k ⟨s,i,d,b,p,a⟩)
lemma dab_c(q:Qind n G m): serene (DabQ Q q):=fun i=> (oct_v q.1 q.2.2 i _).const_mul _
lemma dab_p(q:Qind n G m): prism (m+1) (ValueQ Q q) (saltP (DabQ Q q)):=by
 rcases q with ⟨s,d,a⟩; let b:= hue Q (s,d,a); have he(x:InputZ G n):saltP (DabQ Q (s,d,a)) x=b*vat (diskP 0 d a) (rope (silica s)) x:=by rw [oct_u]; unfold saltP DabQ; rw [integral_const_mul]
 unfold ValueQ; rw [funext he]; exact prism.mul b (fans_p 0 (diskP 0 d a) (rope (silica s)))
abbrev intoY :=∑ i:Dent n G m,(stroll k (cape k i) (potsC F k i)-potsC F k i)
abbrev intoQ:=∑ i:Qind n G m, ValueQ Q i
lemma dent_x(W:KitM G n (m+1)) (v:Axis→ℝ)(h: Push.Loops.Matches (axes v) k) (f:SpaceX G n)(hp: prism (m+1) f (fun x=> ∑ p,engages W p (fun _=> x))) (hz:∀ i,Trade (W i))(he:∀ s i,Paddle i (F s i))(hX:∀ s p x,(breathL W k s-Q s) x (axes p)=∑ i,nullL (cardR v (axes p)) i (F s i (axes p)) x) : prism (m+1) (f+ (intoX W k + intoY F k)-intoQ Q) 0:=by -- implicit n
 let H:Dent n G m→Salt n G:=trot F k; let C (i:Dent n G m):=courseC k (cape k i) (H i)-H i; let T':= intoX W k; let v':=intoY F k; let G':=∑ i:Qind n G m, ValueQ Q i; let e:=∑ i: Disk n (m+1), courseC k (-(i 0).1) (vat i (W i))
 have hm : e+∑ i,C i -∑ i:Qind n G m,DabQ Q i=0:=by
    ext1 x; unfold e; simp only [Pi.sub_apply,Pi.add_apply]; change _+_-_=0; rw [capi,Finset.sum_apply,Finset.sum_apply]; let B (s:SpotG G (m+1)):= trimU (breathL W k s-Q s) s x
    have hl: (∑ i:Qind n G m, DabQ Q i x)=∑ s:SpotG G (m+1),trimU (Q s) s x:=by unfold Qind trimU; rw [Fintype.sum_prod_type]; simp_rw [Fintype.sum_prod_type]; rfl
    rw [hl,show ∑ i,C i x= -(∑ s:SpotG G (m+1), B s) from ?_]; swap
    · unfold B; simp_rw [show ∀ i, trimU (breathL W k i-Q i) i x=_ from fun i=> fairy k v (F i) h (breathL W k i-Q i) (he i) (hX i) i x]; unfold Dent; simp_rw [Fintype.sum_prod_type,← Finset.sum_neg_distrib, neg_sub]; rfl
    unfold B; have h(s:SpotG G (m+1)): trimU (breathL W k s-Q s) s x=trimU (breathL W k s) s x-trimU (Q s) s x:=trim_s x s; simp_rw [h,sum_sub_distrib]; abel
 have hχ(i:Dent n G m): prism (m+1) (stroll k (cape k i) (potsC F k i)-potsC F k i) (saltP (C i)):=by
    have he':= trot_p F k i; unfold C; rw [saltP_sub (serene.shift k _ (trot_c F k i)) (trot_c F k i),salt_shift]; exact prism.sub (prizeC k (cape k i) he') he'
 have he : e+∑ i,saltP (C i)-∑ i:Qind n G m,saltP (DabQ Q i)=0:=by
    have hT:∀ i,serene (H i):=trot_c F k
    have hL:serene e:=serene.total univ fun i _=> serene.shift k _ (fun x=> ((W i).contDiff (n:=ω)|>.continuous.comp (f:=fun g:G.El=> fun j=>sumH G (atU G g x) (i j)) (continuous_pi fun a=>by simp_rw [←sumH_p]; exact ad_j _)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    have hf(i:Dent n G m):serene (C i):=(serene.shift k _ (hT _)).sub (hT i)
    rw [← show saltP e=e from sailC W k hz]; -- tune
    rw [← saltP_sum univ _ fun i _=>hf i, ← saltP_sum univ (DabQ Q) fun i _=>dab_c Q i]; have he : saltP (e+∑ i,C i)=saltP e+saltP (∑ i,C i):= funext fun i=> integral_add (hL i) (serene.total univ (fun i _=>hf i) i); rw [← he,← saltP_sub (hL.add (serene.total univ fun i _=>hf i)) (serene.total univ (fun i _=> dab_c Q (n:=n) i)),hm]; ext1; simp [saltP]
 rw [← add_assoc,←he]; exact prism.sub ((prism.add (geode hp k) (prism.sumZ univ (fun i=>stroll k (cape k i) (potsC F k i)-potsC F k i) _ fun i _=>hχ i))) (prism.sumZ univ (ValueQ Q) _ fun i _=>dab_p Q _)
end legs
end YM.CF.Rel
