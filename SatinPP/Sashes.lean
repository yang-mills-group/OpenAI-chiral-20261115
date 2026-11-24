import SatinPP.Domes
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Silk

open Function Filter Set MeasureTheory
open OS OS.Semigroup Spectral Boundary Probe Hierarchy.Seld
open YM.Quays YM.SatinJets
open scoped Topology Matrix BigOperators InnerProductSpace NNReal ContDiff
variable {H:Hilbert}{j:Axis}{S:OS.Semigroup H j}
local notation "R"=>saucer S
local notation "K"=>Cache S


variable (S)
lemma shingle (g:Test4)(B:H.Op)(d r:ℕ):
  valise S (K d * B * K r) g=K d * valise S B g * K r := by
  apply ContinuousLinearMap.ext; intro y;apply ext_inner_left ℂ; intro x
  have e(p:E4):optx S (K d * B * K r) p=K d * optx S B p * K r:=by
     have u:M S p*K d=K d*M S p:= ((tread S p).pow_left d).eq.symm
     have v:K r*M S (-p)=M S (-p)*K r:= ((tread S _).pow_left r).eq
     unfold optx;rw [←mul_assoc,←mul_assoc,u];simp_rw [mul_assoc,v]
  rw [← sell_in, ← waterQ S x y B g]
  simp only [lucent,e]
lemma anoint {P Y:H.Op}(g h:Test4){d:ℕ}
   (a:valise S P g=R*valise S Y h*R):
   ℑ S P g (d+1)=ℑ S Y h d:=by
  ext1 x;apply Subtype.ext;apply cache_I S (d+1)
  rw [Hierarchy.Seld.native,a]
  let z:=ℑ S Y h d x
  have u: R (hall S (d+1) x)=hall S d x:=by simpa [Cache] using downstairs S 1 d x
  change R (valise S Y h (R (hall S (d+1) x)))= _ 
  rw [u,←Hierarchy.Seld.native,Cache,Cache,pow_succ']
  rfl

lemma tire (g:Test4)(B:H.Op):valise S (R*B*R) g= R*valise S B g*R :=by
 simpa [Cache] using shingle S g B 1 1
namespace Role
variable {S}{A:Stamp H}{P:H.Op}{d:ℕ}(u:Role S d A P)
include u
lemma up_one : Role S (d+1) A (R * P * R):=by
 constructor;intro v w p q
 generalize z:A v w=Z
 have a:= u.wear _ _ p q
 rw [z] at a
 simp only [Wrap,Cache] at a ⊢
 calc
   _= R * (R^d * Z * R^d) * R:=by
      rw [pow_succ'];simp only [mul_assoc];rw [show R*R^d=R^d*R from (Commute.refl R).pow_right d];
      -- change RHS?
   _=jacket S v w (R*P*R) :=by
      rw [a]
      change R*(S.E _*_ * S.E _) * R=S.E _* (_*_ *_)*S.E _
      rw [←mul_assoc,←mul_assoc,(cupE S _).eq]
      simp_rw [mul_assoc]
      rw [(cupE S _).eq] -- goal


lemma increase {n:ℕ}(t:d≤n):
    ∃Q,Role S n A Q ∧ ∀ g, ℑ S Q g n=ℑ S P g d:=by
 induction n,t using Nat.le_induction with
 | base => exact ⟨P,u,fun _=>rfl⟩
 | succ i ti h =>
    obtain ⟨Q,e,f⟩:=h
    exact ⟨_,e.up_one,fun g=>(anoint S g g (tire S g Q)).trans (f g)⟩
lemma mismatch {Q:H.Op}(m:Role S d A Q):Q=P:=by
 let f(n:ℕ):ℝ:=1/(n+1)
 let a:Tendsto f atTop (𝓝 0):= tendsto_const_nhds.div_atTop
    (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
 have p(n):0<f n:=by unfold f;positivity
 apply ContinuousLinearMap.ext;intro y;apply ext_inner_left ℂ;intro x
 exact tendsto_nhds_unique ((Spine.return_Wire m a p).funds x y) ((Spine.return_Wire u a p).funds x y)
lemma compatible {Q:H.Op}{n:ℕ}(m:Role S n A Q)(g:Test4):
   ℑ S Q g n=ℑ S P g d:=by
 obtain ⟨Q',c,k⟩:=u.increase (le_max_left d n)
 obtain ⟨P',a,t⟩:=m.increase (le_max_right d n)
 rw [←k g,←t g,c.mismatch a]

lemma plus {Y:H.Op}{D:Stamp H}
    (p:Role S d D Y): Role S d (A+D) (P+Y):=by
  constructor;intro v t a b
  rw [map_add,←u.wear _ _ a b,←p.wear _ _ a b]
  simp only [Wrap,Pi.add_apply,mul_add,add_mul]
lemma times (z:ℂ):Role S d (z • A) (z • P):=by
  constructor;intro v t a b
  rw [map_smul,←u.wear _ _ a b]
  simp only [Wrap,Pi.smul_apply,mul_smul_comm,smul_mul_assoc]
end Role
-- canonical ℑ assignment
def latent (S:OS.Semigroup H j) (A:Stamp H):Spool H:=by
 classical
 exact if h:∃P:Spool H, Role S P.d A P.cell then h.choose else ⟨0,0⟩
def feature(S:OS.Semigroup H j)(A:Stamp H):
    Test4→ₗ[ℂ] (Bench S→ₗ[ℂ]Bench S):=
  σV S (latent S A).cell (latent S A).d

lemma serve {A:Stamp H}(p:Sold S A):
   (latent S A).Token S A:=by
 obtain ⟨_,_,c⟩:=p
 obtain ⟨B,d⟩:=role_exists S c
 have h:∃P:Spool H,Role S P.d A P.cell:=⟨⟨_,B⟩,d⟩
 unfold latent; rw [dif_pos h]; exact h.choose_spec
#print Spool.Token

variable {S}{A D:Stamp H}(u:Sold S A)(p:Sold S D)

lemma feature_eq {A:Stamp H}{d:ℕ}{B:H.Op}(k:Role S d A B)(g:Test4):
   feature S A g=ℑ S B g d:=by
 have h:∃P:Spool H,Role S P.d A P.cell:=⟨⟨_,B⟩,k⟩
 unfold feature latent;rw [dif_pos h];exact k.compatible h.choose_spec _
variable (S)
lemma feature_zero(g:Test4):feature S 0 g=0:=by
 have q:Role S 0 (0:Stamp H) 0:=⟨fun _ _ _ _=>by simp [Wrap]⟩
 rw [feature_eq q]
 exact add_eq_left.mp ((anyB S 0 0 g 0).symm.trans (by rw [add_zero]))
variable {S}
include u
lemma feature_smul(g:Test4)(z:ℂ):
    feature S (z • A) g=z • feature S A g:=by
 rw [feature_eq (Role.times (serve S u) z)]
 exact anyC ..
include p
lemma feature_add(g:Test4):
    feature S (A+D) g=feature S A g+feature S D g:=by
 let n:=(latent S A).d;let d:=(latent S D).d
 obtain ⟨B,q,_⟩:=Role.increase (serve S u) (le_max_left n d)
 obtain ⟨Y,h,_⟩:=Role.increase (serve S p) (le_max_right n d)
 rw [feature_eq (q.plus h),anyB,feature_eq q,feature_eq h]


omit p u in
lemma feature_sum {ι:Type}(I:Finset ι)(J:ι→Stamp H)(z:∀i,Sold S (J i))(g:Test4):
    feature S (∑i∈I,J i) g=∑ i∈I,feature S (J i) g:=by
 classical
 induction I using Finset.induction_on with
 | empty=>simp [feature_zero]
 | @insert i I d k=>
     rw [Finset.sum_insert d,feature_add (z _) (Sold.sum _ _ z),k,Finset.sum_insert d]
omit p in
lemma feature_turn(g:Test4)(X Y:Bench S):
    inner ℂ (feature S A g X).val Y.val=
    inner ℂ X.val (feature S (Turn A) (bar g) Y).val:=by
 rw [feature_eq (Role.turn (serve S u))]
 exact sees_κ ..

#print axioms feature_add
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Silk
