import GaugeFieldConstruction.Bruise
/-!
# 87-92 Contour calculus. Fixed test, signed angular derivative costs, no request for order six membership. 
-/
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction.Fathom
open Function Filter Set TopologicalSpace YM Analysis MeasureTheory Points Bulb Payroll Finset
open scoped Topology BigOperators ContDiff
variable {n : ℕ} {k : Fin n}
local instance rnTs : SMul ℝ (Test n):=inferInstance
-- real smul through cost
lemma dollar (f : Bond n) (r :ℝ) (u : Test n): f (r • u)=r • f u:= (f.restrictScalars ℝ).map_smul r u

variable {p : Test n} {h : Bulb}
-- packs angular derivative terms. (101) and (91) signs
lemma sword (v:∀ i : Axis, Quiet p (h.LED i)) (a : Axis) (Ω : Ortho.Skew) (A : Variation n) :
    ∑ i : Axis,∑ j : Axis, A i j ((Ω.val j a:ℝ) • lace p (h.LED i) (v i))=
    ∑ j : Axis,(Ω.val j a:ℝ) • delta (ticket j) p h v A := by  -- binder
  simp_rw [dollar, deconstant,Finset.smul_sum]; rw [Finset.sum_comm]

-- derivative price notation deliberately distribution sign. no differentiation of cutoff with moved x
lemma Delta_x (k : Fin n) (f : Test n) (J : Bulb) (p:∀ i : Axis, Quiet f (J.LED i)) (A : Variation n) (b a):
    delta (ticket a) f J p (fun i j=>paid k.succ b (A i j))=
      - delta (ticket a) (tilt (direction k b) f) J (fun i=> (p i).down _ (dband ..)) A:= by
  simp_rw [deconstant,pays,tilt_side,Finset.sum_neg_distrib]
lemma Delta_x' (k : Fin n) (f : Test n) (J : Bulb) (p:∀ i : Axis, Quiet f (J.LED i)) (A : Variation n) (b:Axis) (Ω) :
    delta (desk k Ω) f J p (fun i j=>paid k.succ b (A i j))=
      - delta (desk k Ω) (tilt (direction k b) f) J (fun i=>(p i).down _ (dband ..)) A+
        ∑ j :Axis,(Ω.val j b:ℝ) • delta (ticket j) f J p A := by
  let u:=tilt (direction k b) f; let v i: Quiet u (J.LED i) := (p i).down _ (dband ..)
  have E (i j : Axis): tilt (direction k.succ b) (testcut (desk k Ω) f J p i j)= testcut (desk k Ω) u J v i j- (Ω.val j b:ℝ) • lace f (J.LED i) (p i) :=by
    rw [sub_eq_add_neg,add_comm (testcut _ u _ _ _ _),testcut,weight_deriv,tilt_side]; congr 1; ext1 x
    let t:=lace f (J.LED i) (p i); change D (direction k.succ b) (lab k Ω j) x • t x= - ((Ω.val j b:ℝ) • t x); rw [Dtag,tenant,neg_smul]
  rw [← sword p b Ω A]; unfold delta; rw [← sum_neg_distrib,← sum_add_distrib]; refine sum_congr rfl fun i _=> ?_
  rw [← sum_neg_distrib,← sum_add_distrib]; refine sum_congr rfl fun j _=> ?_; rw [pays,E,map_sub]; abel

lemma Delta_z (v : Works h p k) (A : Variation n) (a b : Axis) (q:Conserves A): delta (ticket a) p h v.cared (fun i j=>paid 0 b (A i j))=0:= by
  have B (i : Axis) : tilt (direction 0 b) (lace p (h.LED i) (v.cared i))=tilt (direction 0 i) (lace p (h.LED b) (v.cared b)) := by
    rw [tilt_lace,tilt_lace]; ext1 x; let y:= helm (n:=n) x; change D _ (D _ h.f) y • p (riders x)= D _ (D _ h.f) y • p _
    rw [commuteD ((h.d.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt (x:=y))]
  rw [deconstant]; simp_rw [pays,B,sum_neg_distrib,q.withdraw,neg_zero]
lemma Delta_z' (v : Works h p k) (A : Variation n) (b : Axis) (Ω) (q:Conserves A): delta (desk k Ω) p h v.cared (fun i j=>paid 0 b (A i j))=
    -∑ j :Axis,(Ω.val j b:ℝ) • delta (ticket j) p h v.cared A:= by
  let B :=h.LED b; let U :Quiet p B:=v.cared b; let L := desk k Ω
  let s (i j : Axis):= testcut L p h v.cared i j
  have E (i j : Axis): tilt (direction 0 b) (s i j)= (Ω.val j b:ℝ) • lace p (h.LED i) (v.cared i) + testcut L p B (cares U) i j:= by
    unfold s testcut; rw [weight_deriv,tilt_lace]; congr 1
    · ext1 x; change D (direction (n:=n+1) 0 b) (lab k Ω j) x • (_:ℂ)= (Ω.val j b:ℝ) • (_:ℂ); rw [Dtag,primary]
    congr 1; ext1 x; change D _ (D _ h.f) (helm x) • p (riders x)=D _ (D _ h.f) (helm x) • p _; rw [commuteD ((h.d.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt (x:=helm x))]
  change (∑ i:Axis,∑ j:Axis,paid 0 b (A i j) (s i j))=_; simp_rw [pays,sum_neg_distrib,E,map_add,sum_add_distrib]; rw [sword _ b Ω A, show (∑ i:Axis,∑ j:Axis,A i j (testcut L p B (cares U) i j))=0 from plume _ _ _ U A q,add_zero]

-- Nest slack: inner support entirely in outer lit zone
structure Before (b a : Bulb) : Prop where
  burns : ∀ x∈b.run,a.lit x
lemma Before.nested {a b} (h : Before b a) (x) (p:x∈ a.shore): x ∉ b.run := fun k=> centre (h.burns x k) p
namespace Works_Nest
variable {a b :Bulb}

lemma resident (K : Payroll n) (v : Works b p k) (w : Works a p k) (q:Before b a) (i j): Works b (testcut K p a w.cared i j) k.succ where
  bulb x g:= (v.bulb _ (testcut_L K p a w.cared i j g).2)
  direct x g m:= by
    have ht:= testcut_L K p a w.cared i j g; refine Fin.cases ?_ ?_ m
    · intro _; exact q.nested _ ht.1
    intro s he; exact v.direct _ ht.2 s (fun x=>he (congr_arg Fin.succ x))

lemma district (K : Payroll n) (v : Works b p k) (w : Works a p k) (q:Before b a) (i j m): Quiet (testcut K p b v.cared i j) (a.LED m):= by
  intro x h; have t:=testcut_L K p b v.cared i j h; intro s; refine Fin.cases ?_ ?_ s
  · intro e; exact centre (q.burns _ (strands (b:=b) t.1)) (cone a m (a:=helm x) e) -- check
  intro s; exact w.cared m _ t.2 s

/-- making ψ on ring of b with slack, directly a−c. Then use decomposition
    on ∆ with J,T. -/
def fades (a c : Bulb): Bulb:= ⟨a.f-c.f,a.d.sub c.d,a.c.sub c.c⟩
lemma rent {c : Bulb} (K : Payroll n) (v : Works b p k) (w : Works a p k) (u : Works c p k) (q:Before b a) (r:Before c b) (i j):Works (fades a c) (testcut K p b v.cared i j) 0 where
  bulb x g:= by
    have t:= testcut_L K p b v.cared i j g; let z:=helm x; have hz : z∈ b.shore:= t.1
    have ha:= q.burns z (strands hz); have hc:= notMem_tsupport_iff_eventuallyEq.mp (show z ∉ c.run from r.nested _ hz)
    have h:= ha.sub hc; change fades a c |>.lit z; exact h.trans (Eventually.of_forall fun _=> sub_zero _)
  direct x g m:= by
    have t:= testcut_L K p b v.cared i j g; refine Fin.cases ?_ ?_ m
    · simp
    intro s _; let y:=riders x s; have hy :riders x∈ tsupport p:= t.2; change y∉ _
    by_cases p' : s=k
    · subst s; have hc:=u.bulb _ hy; have ha:=w.bulb _ hy
      exact notMem_tsupport_iff_eventuallyEq.mpr ((ha.sub hc).trans (Eventually.of_forall fun _=>sub_self _))
    have hc : y ∉ c.run:= u.direct _ hy _ p'; have ha : y ∉ a.run:=w.direct _ hy _ p'
    exact fun H=> (tsupport_sub a.f c.f H).elim ha hc

lemma parted {K : Payroll n} (h:∀ i, Quiet p (a.LED i)) (v : ∀ i, Quiet p (b.LED i)) (u : ∀ i, Quiet p ((fades a b).LED i)) (A: Variation n):
    delta K p a h A=delta K p b v A+delta K p (fades a b) u A:=by
  have E (i j : Axis): testcut K p a h i j = testcut K p b v i j + testcut K p (fades a b) u i j:= by
    ext1 x; change _ = testcut _ p b v i j x + testcut _ p (fades a b) u i j x; simp_rw [testcut_v]; unfold fades D; rw [fderiv_sub (a.d.differentiable (by simp) (helm x)) (b.d.differentiable (by simp) (helm x))]; simp only [ContinuousLinearMap.sub_apply, sub_mul, sub_smul, add_sub_cancel]
  unfold delta; simp_rw [E,map_add,Finset.sum_add_distrib]
end Works_Nest
end YM.GaugeFieldConstruction.Fathom
