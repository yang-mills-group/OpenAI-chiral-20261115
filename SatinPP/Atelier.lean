import SatinPP.Radiance
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Silk
open Quays
open Function Filter Metric Set OS OS.Semigroup Hierarchy.Seld Complex MeasureTheory
open Spectral Boundary Probe
open scoped Topology BigOperators NNReal InnerProductSpace

variable {H:Hilbert}{a:Axis}(S:OS.Semigroup H a)(g:Test4)
-- ℓ variable at z

def fetter(t c:ℝ):ℂ:= t+sideways c
lemma fetter_mem{t:ℝ}(e:0<t)(c:ℝ):fetter t c∈ inside:=by change 0 < (_ :ℂ).re; simpa [fetter,sideways] using e
lemma fE {t:ℝ}(e:0<t)(c:ℝ):
  S.F (fetter t c)=S.E t.toNNReal * tide S (sideways c) ∧
  S.F (fetter t c)=tide S (sideways c)* S.E t.toNNReal:=by
 rw [← tide_heat S _ (fetter_mem e _),tide_edge]
 have h:(fetter t c).re=t∧-(fetter t c).im=c:=by simp [fetter,sideways]
 rw [tide,h.1,h.2]; refine ⟨?_,rfl⟩
 rw [← S.roots_heat (Real.toNNReal_pos.mpr e)]
 have v:=dur.mpr (Real.toNNReal_pos.mpr e)
 exact (S.along v _).trans (S.either v _).symm

#check Semigroup.either

variable {l u c:ℝ}{d m:ℕ}{A:Stamp H}{B:H.Op}{r:ℝ}
variable (l u A c) in
def clip (p:E4) : H.Op := paint S A (fetter (c-l) (p a - c)) (fetter (u-c) (c-p a))

variable {S}(h:c∈Ioo l u)(R:Role S d A B)(K:Paid S m r A)
include h R K
local notation "E" t:max=> S.E (Real.toNNReal t)
local notation "κ"=>Cache S d
lemma gem (p:E4):
 κ * lit S (clip S l u c A) p * κ =
 E (c-l)* entry S c c B (sideways 1) p * E (u-c) := by
 let y:=fetter (c-l) (p a - c)
 let w:=fetter (u-c) (c-p a)
 have hy:y∈inside:=fetter_mem (sub_pos.mpr h.1) _
 have hw:w∈inside:=fetter_mem (sub_pos.mpr h.2) _
 have k (s:E4) :κ*Q S s=Q S s *κ:=((cupU S _).pow_left _).eq
 have b(n:ℂ)(m:n∈inside)(s:E4):S.F n * Q S s=Q S s * S.F n:= S.stays m _

 unfold lit
 change κ*(Q S p * paint S A y w * Q S (-p))*κ=_
 rw [←mul_assoc,←mul_assoc,k,mul_assoc,←k (-p),
     R.suited K y w hy hw]
 simp_rw [mul_assoc]
 rw [←mul_assoc (κ) (parabola S d y),←mul_assoc (parabola S d w) κ,recover _ _ _ hy,change_m _ _ _ hw]
 rw [←mul_assoc, ←b _ hy]
 rw [b w hw]
 dsimp only [w,y]
 rw [(fE S (sub_pos.mpr h.1) _).1,(fE S (sub_pos.mpr h.2) _).2]
 unfold entry fore aft;rw[infer_side,infer_side,mul_one,mul_one]
 simp_rw [mul_assoc]

omit R
lemma clipC:Continuous (clip S l u c A):=by
 apply continuous_iff_continuousAt.mpr; intro p
 unfold clip
 apply continuousAt_paint K
 · exact fetter_mem (sub_pos.mpr h.1) _
 · exact fetter_mem (sub_pos.mpr h.2) _
 all_goals unfold fetter sideways; fun_prop

variable (S B l u c) in
def velvet:= coat S c c B g (sideways 1)
include R
lemma gemmed (v:HasCompactSupport g): κ * salon S g (clip S l u c A) * κ =
  E (c-l) * velvet S g c B * E (u-c):=by
 have t:Held g (clip S l u c A):=⟨v, fun _ _=>(clipC h K).continuousAt⟩
 unfold velvet
 ext1 x
 change κ (salon S g _ (κ x))=S.E _ (coat _ _ _ _ _ _ (S.E _ x))
 rw [salon_val S t _,coat_val, ← (κ).integral_comp_comm (litI S t (κ x)),← ContinuousLinearMap.integral_comp_comm _ (coatI ..)]
 congr 1 with p
 rw [map_smul,map_smul]
 exact congrArg _ (DFunLike.congr_fun (gem h R K p) x)
#print axioms gemmed

omit R h
variable {g}
lemma verror (b:Band a l u g){f:E4→H.Op}(t:Held g f){δ:ℝ}
 (q:∀ p∈tsupport g, ‖f p-sail S A l u 1 p‖≤δ)(y:0≤δ):
 ‖salon S g f - voyage S A l u 1 g‖ ≤ vial g*δ:=by
 have hg : 0 ≤ vial g:=by rw[vmeets]; exact integral_nonneg fun _=>norm_nonneg _
 apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hg y)
 intro x
 rw [ContinuousLinearMap.sub_apply,salon_val S t _,voyage_val K b eu _,←integral_sub (litI S t x) (litI S (held_sail K b eu) x),
  mul_assoc,vmeets,←integral_mul_const]
 refine norm_integral_le_of_norm_le (g.integrable.norm.mul_const _) (Eventually.of_forall (fun p=>?_))
 simp only [←smul_sub,norm_smul]
 by_cases v:p∈tsupport g
 · have d (k r:E4→H.Op): lit S k p x - lit S r p x= lit S (k-r) p x:=by unfold lit;rw [Pi.sub_apply,mul_sub,sub_mul,ContinuousLinearMap.sub_apply]
   rw [d]
   exact mul_le_mul_of_nonneg_left
     ((litP S p x).trans (mul_le_mul_of_nonneg_right (q p v) (norm_nonneg _))) (norm_nonneg _)
 simp [image_eq_zero_of_notMem_tsupport v]




omit K in
lemma slice4 {p:E4}(v:ContDiffBump p)
 (w:HasCompactSupport g):
 ∃ f t:Test4,
  (tsupport f ⊆ tsupport g ∩ closedBall p v.rOut)∧
  tsupport t ⊆ tsupport g \ ball p v.rIn ∧
  (∀y, f y+t y=g y)∧ vial f+vial t=vial g:=by
 let F:= fun y=>v y • g y
 let T:= fun y=>(1-v y) • g y
 have f:tsupport F ⊆ tsupport g := by
    apply closure_mono;intro q h; contrapose! h;rw [notMem_support] at *;simp [F,h]
 have t:tsupport T ⊆ tsupport g :=by
    apply closure_mono;intro q h; contrapose! h;rw [notMem_support] at *;simp [T,h]
 let f':Test4:= HasCompactSupport.toSchwartzMap (w.of_isClosed_subset (isClosed_tsupport _) f) (v.contDiff.smul (g.smooth _))
 let t':Test4:= HasCompactSupport.toSchwartzMap (w.of_isClosed_subset (isClosed_tsupport _) t) ((contDiff_const.sub v.contDiff).smul (g.smooth _))
 refine ⟨f',t',subset_inter f ?_,subset_diff.mpr ⟨t,?_⟩,fun y=>?_,?_⟩
 · change tsupport F⊆closedBall _ _
   rw [← v.tsupport_eq]
   apply closure_mono;intro q h; contrapose! h;rw [notMem_support] at *;simp [F,h]
 · have h:tsupport T ⊆ (ball p v.rIn)ᶜ:=closure_minimal (fun q h e=> h (show T q=0 by unfold T;rw[v.one_of_mem_closedBall (ball_subset_closedBall e),sub_self,zero_smul])) isOpen_ball.isClosed_compl
   exact Set.disjoint_left.mpr fun _ a=>h a
 · change v y • g y+(1-v y)•g y=g y
   rw[←add_smul];simp
 rw [vmeets,vmeets,vmeets,←integral_add (f'.integrable.norm) (t'.integrable.norm)]
 congr 1 with p
 change ‖v p • g p‖+‖((1:ℝ)-v p) • g p‖=‖g p‖
 rw [norm_smul,norm_smul,Real.norm_of_nonneg v.nonneg, Real.norm_of_nonneg (sub_nonneg.mpr v.le_one)];ring

/-- Inductive scripts. -/
inductive Dress (Bnd:Set E4)(δ l u:ℝ)(B:H.Op)(d:ℕ): ℝ→Test4→H.Op→Prop
 | nil {g:Test4}(h:∀p,g p=0) (e:ℝ)(h₁:0≤e): Dress Bnd δ l u B d e g 0
 | stitch {y:ℝ}{g:Test4}{D:H.Op}:Dress Bnd δ l u B d y g D→
   ∀ {g₀ f:Test4},tsupport f ⊆ Bnd → ∀ c∈Ioo l u,(∀ p∈tsupport f,|p a-c|<δ)→
   ∀(e:ℝ),‖velvet S f c B‖ ≤ e→ (∀p,f p+g p=g₀ p)→
    ∀ M:H.Op,Cache S d*M*Cache S d=
          S.E (c-l).toNNReal*velvet S f c B*S.E (u-c).toNNReal →
   Dress Bnd δ l u B d (e+y) g₀ (M+D)

include R
lemma dressable (b:Band a l u g){δ:ℝ}(e:0<δ):
 ∃ M:H.Op,Dress (S:=S) (tsupport g) δ l u B d (vial g*‖B‖) g M ∧
    ‖M-voyage S A l u 1 g‖≤ vial g * δ:=by
 classical
 let Y:=tsupport g
 have L (y:Y):
     ∃ f:ContDiffBump y.val,∀p∈Y,p ∈ closedBall y.val f.rOut→ |p a-y.val a|<δ∧
        ‖clip S l u (y.val a) A p-sail S A l u 1 p‖ ≤ δ:= by
    have h:y.val a ∈ Ioo l u:=b.snug y.val y.property
    have i:clip S l u (y.val a) A y.val=sail S A l u 1 y.val:=by simp [clip,sail,fetter,sideways,infer,aft,fore]
    have e': ∀ᶠ p in 𝓝 y.val, |p a-y.val a|<δ∧
         ‖clip S l u (y.val a) A p-sail S A l u 1 p‖ <δ := by
        refine Eventually.and (ContinuousAt.eventually_lt (by fun_prop) continuousAt_const (by simpa using e))
           (ContinuousAt.eventually_lt (((clipC (S:=S) h K).continuousAt.sub
              ((held_sail K b eu).2 y.val y.property)).norm) continuousAt_const (by simpa only [i,sub_self,norm_zero] using e))
    obtain ⟨v,r,t⟩:=Metric.nhds_basis_closedBall.mem_iff.mp e'
    exact ⟨⟨v/2,v,by linarith,by linarith⟩,fun p _ z=>⟨(t z).1,(t z).2.le⟩⟩
 choose f t using L
 let U(y:Y):=ball y.val (f y).rIn
 obtain ⟨s,h⟩:= b.wide.elim_finite_subcover U (fun _=>isOpen_ball)
    (fun y p=>mem_iUnion.mpr ⟨(⟨y,p⟩:Y),mem_ball_self (f ⟨y,p⟩).rIn_pos⟩)
 suffices V:∀s:Finset Y,∀w:Test4,Band a l u w→ tsupport w ⊆ Y→ tsupport w ⊆ ⋃ y∈s,U y →
     ∃ M:H.Op,Dress (S:=S) Y δ l u B d (vial w*‖B‖) w M ∧
       ‖M-voyage S A l u 1 w‖ ≤ vial w * δ from V s g b (by rfl) h
 intro s'
 induction s' using Finset.induction_on with
 | empty =>
    intro w urg' x p
    have z(y:E4):w y=0:=image_eq_zero_of_notMem_tsupport (fun q=>by simpa using p q)
    refine ⟨0,.nil z _ (by simp [vmeets,z]),?_⟩
    have v:voyage S A l u 1 w=0:=by ext1 y; rw[voyage_val K urg' eu y]; simp[z]
    simp [v,vmeets,z]
 | @insert y s q ih =>
    intro w urg' x p
    obtain ⟨k,n,v,z,j,h'⟩:=slice4 (f y) urg'.wide
    have urg (i:Test4)(a':tsupport i ⊆ tsupport w):Band a l u i:=⟨urg'.wide.of_isClosed_subset (isClosed_tsupport _) a', fun p r=>urg'.snug _ (a' r)⟩ -- u shadows

    have p':tsupport n ⊆ ⋃ y'∈s,U y':=by
       intro a d;obtain ⟨r,q⟩:=z d
       have m:=p r
       rw[Finset.set_biUnion_insert] at m
       exact m.resolve_left q
    have k':=urg k (fun i b=>(v b).1)
    have n':=urg n (fun i b=>(z b).1)
    obtain ⟨M,Q,W⟩:= ih n n' (fun _ e'=> x (z e').1) p'
    let D:=salon S k (clip S l u (y.val a) A)
    have i:= b.snug y.val y.property
    have band(p)(r:p∈tsupport k):= t y p (x (v r).1) (v r).2
    refine ⟨D+M,?_ ,?_⟩
    · rw [←h',add_mul]
      exact Dress.stitch Q (f:=k) (fun _ z=>x (v z).1) (y.val a) i (fun p h=>(band p h).1) _
        (coat_norm ..) j D (gemmed k i R K k'.wide)

    have J:voyage S A l u 1 w=voyage S A l u 1 k+voyage S A l u 1 n:=by
      ext1 y'; rw[ContinuousLinearMap.add_apply,voyage_val K urg' eu y',voyage_val K k' eu y',voyage_val K n' eu y',
             ←integral_add (litI S (held_sail K k' eu) _) (litI S (held_sail K n' eu) _)]
      congr 1 with p; rw [←j,add_smul]
    rw [J,add_sub_add_comm,←h',add_mul]
    exact (norm_add_le ..).trans <| add_le_add (verror (S:=S) K k' ⟨k'.wide,fun _ _=>
          (clipC (c:=y.val a) i K).continuousAt⟩ (fun p h=>(band p h).2) e.le) W

#check coat_edge
#print Dress
#print axioms dressable

