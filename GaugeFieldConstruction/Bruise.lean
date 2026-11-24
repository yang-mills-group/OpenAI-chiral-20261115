import GaugeFieldConstruction.Cable

/-!
# q2 formula with fixed, separated contour

 Includes centered-angular inputs. Compare nested, holding one contour fixed even when address x varies. Bulb is 1 in nhds of addressed slot/test and 0 around other positions. actual operation ranges from external proof. Costs distribution identities, not assuming commuting operations etc.
-/
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction.Fathom
open Function Filter Set TopologicalSpace YM Analysis MeasureTheory Points
open scoped Topology BigOperators ContDiff
variable {n : ℕ}
structure Bulb where
  f : E4→ℝ
  d : ContDiff ℝ ∞ f
  c : HasCompactSupport f
namespace Bulb
instance : CoeFun Bulb fun _=> E4→ℝ:= ⟨Bulb.f⟩
def LED (b : Bulb) (a:Axis) : Bulb := ⟨D (basis a) b.f,b_sm _ b.d _,b_co _ b.c _⟩
/-- Contour qualifications -/
def lit (b : Bulb) (x : E4) := b.f =ᶠ[𝓝 x] fun _=>1
def run (b : Bulb):=tsupport b.f
def shore (b : Bulb) := tsupport (fderiv ℝ b.f)
lemma surrounded {b : Bulb} {x} (h:lit b x): x∈ b.run:= subset_closure (by change _ ≠ 0; exact Ne.symm (ne_of_lt (show 0 < b.f x from (h.eq_of_nhds.symm ▸ zero_lt_one))))
lemma centre {b : Bulb} {x} (h:lit b x): x ∉ b.shore := by
  apply notMem_tsupport_iff_eventuallyEq.mpr
  change fderiv ℝ _ =ᶠ[𝓝 x] _; exact (h.fderiv (𝕜:=ℝ)).trans (Eventually.of_forall fun x=>fderiv_const_apply _) -- check
lemma strands {b : Bulb}: b.shore⊆b.run:= tsupport_fderiv_subset _
lemma cone (b : Bulb) (i): (b.LED i).run⊆b.shore := by apply closure_mono; intro x hx p; exact hx (by change fderiv ℝ b.f x _=0; change fderiv ℝ b.f x=0 at p; rw [p]; rfl)

structure Works (b : Bulb) (p : Test n) (k : Fin n) : Prop where
  bulb (x : Points n): x∈tsupport p→lit b (x k)
  direct (x : Points n): x∈tsupport p→∀ j,j≠k→ x j ∉ b.run
lemma Works.via {b : Bulb} {p : Test n} {k} (h:Works b p k) (f : Test n) (v : tsupport f ⊆ tsupport p) : Works b f k := ⟨fun i v'=>h.bulb _ (v v'),fun i v'=>h.direct _ (v v')⟩
lemma Works.cared {b : Bulb} {p : Test n} {k} (h : Works b p k) (i : Axis): Quiet p (b.LED i) := by
  intro x hx j hv
  have v : x j∈ b.shore:= cone b i hv -- hmm
  by_cases p : j=k
  · exact centre (p.symm ▸ h.bulb x hx) v
  exact h.direct x hx j p (strands v)
-- arbitrary run
lemma cares {b : Bulb} {p : Test n} (h:Quiet p b) (i): Quiet p (b.LED i) := h.refines _ (Subset.trans (cone b i) strands)
lemma shining {p q : Bulb} {x} (h:x ∉ p.run) (v : p =ᶠ[𝓝 x] q): x∉ q.run := notMem_tsupport_iff_eventuallyEq.mpr (v.symm.trans (notMem_tsupport_iff_eventuallyEq.mp h))

def lace (p : Test n) (b : Bulb) (v:Quiet p b) : Test (n+1) := punched p b v b.d b.c
lemma trail_s (p : Test n) (b : Bulb) (v:Quiet p b) : tsupport (lace p b v)⊆ fuse ⁻¹' (b.run ×ˢ tsupport p):=hits_off p b
end Bulb
open Bulb

structure Payroll (n : ℕ) where
  K : Axis→ Points (n+1)→ ℝ
  sm (a) : ContDiff ℝ ∞ (K a)
  skew a b x : D (direction 0 a) (K b) x= - D (direction 0 b) (K a) x
namespace Payroll
variable (K : Payroll n)
open M4
-- versions constant or angular
def proj (b : Axis) : E4→L[ℝ] ℝ:= PiLp.proj _ _ b -- check
lemma views (b) (x:E4) : proj b x=x b:=rfl
def loc (k : Fin n) : Points n→L[ℝ] E4 := PiLp.proj _ _ k
lemma address (k : Fin n) (x : Points n) : loc k x=x k:=rfl
def turn (Ω:Ortho.Skew): E4→L[ℝ] E4:= LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin Ω.val)
def ticket (i : Axis) : Payroll n where
  K j _:=basis i j
  sm j:=contDiff_const
  skew a b x:= by simp [D]
-- x displacement shift

def lab (k : Fin n) (Ω : Ortho.Skew) (i : Axis) : Points (n+1)→L[ℝ] ℝ := proj i ∘L turn Ω ∘L (helm-loc k ∘L riders)
lemma primary (k : Fin n) (Ω i) (a): lab k Ω i (direction 0 a)=Ω.val i a:=by
  simp only [lab,ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply, head_on,on_left,map_zero, sub_zero]; exact M4.move_basis .. -- check
lemma tenant (k : Fin n) (Ω i) (a) : lab k Ω i (direction k.succ a) = - Ω.val i a:=by
  simp only [lab, ContinuousLinearMap.comp_apply,ContinuousLinearMap.sub_apply,nope,on_rail,zero_sub,map_neg]; congr 1; rw [address]; simp only [direction,PiLp.single_eq_same]; exact M4.move_basis .. -- check
lemma Dtag (k : Fin n) (Ω i) (j a) (x : Points (n+1)): D (direction j a) (lab k Ω i) x=lab k Ω i (direction j a):= by unfold D; rw [ContinuousLinearMap.fderiv]

def desk (k : Fin n) (Ω : Ortho.Skew) : Payroll n where
  K i:=lab k Ω i
  sm i:=(lab k Ω i).contDiff
  skew a b x:=by rw [Dtag,Dtag,primary,primary]; exact congr_fun (congr_fun Ω.property a) b
lemma angle (k : Fin n) (Ω : Ortho.Skew) (a) (x : Points (n+1)) : (desk k Ω).K a x=M4.move Ω.val (x 0-riders x k) a :=rfl
end Payroll
open Payroll
abbrev Variation (n : ℕ) := Axis →Axis → Bond (n+1)
def testcut (K : Payroll n) (f : Test n) (h : Bulb) (p:∀ i : Axis, Quiet f (h.LED i)) (i j : Axis): Test (n+1):= weigh (K.K j) (K.sm j) (lace f (h.LED i) (p i))
lemma testcut_v (K : Payroll n) (f : Test n) (h : Bulb) (p:∀ i : Axis, Quiet f (h.LED i)) (i j : Axis) (x : Points (n+1)): testcut K f h p i j x = (D (basis i) h.f (helm x)*K.K j x) • f (riders x) := by rw [mul_comm,mul_smul]; rfl
lemma testcut_L (K : Payroll n) (f : Test n) (h : Bulb) (p:∀ i : Axis, Quiet f (h.LED i)) (i j : Axis): tsupport (testcut K f h p i j) ⊆ fuse ⁻¹' (h.shore ×ˢ tsupport f):= Subset.trans (taxed ..) (Subset.trans (trail_s ..) (preimage_mono (prod_mono (cone ..) (Subset.refl _))))
def delta (K : Payroll n) (f : Test n) (h : Bulb) (p:∀ i : Axis, Quiet f (h.LED i)) (A : Variation n) : ℂ:=∑ i:Axis,∑ j:Axis,A i j (testcut K f h p i j)
lemma deconstant (f : Test n) (h : Bulb) (p:∀ i : Axis, Quiet f (h.LED i)) (A : Variation n) (a) : delta (ticket a) f h p A=∑ i :Axis,A i a (lace f (h.LED i) (p i)):= by
  unfold delta; apply Finset.sum_congr rfl; intro i _; rw [Finset.sum_eq_single a]; congr 1; ext1 x; simp only [testcut_v,ticket,basis_eq, ↓reduceIte,mul_one]; rfl
  · intro b _ g; have he :testcut (ticket a) f h p i b=0:= by ext1 x; rw [testcut_v,show (ticket a).K b x (n:=n)=0 by simp [ticket,g]]; simp
    rw [he,map_zero]
  simp
lemma tilt_lace (p : Test n) (w : Bulb) (i) (v:Quiet p w) : tilt (direction 0 i) (lace p w v)=lace p (w.LED i) (cares v i) := punch_front ..
lemma tilt_side (p : Test n) (w : Bulb) (k : Fin n) (a) (q:Quiet p w) : tilt (direction k.succ a) (lace p w q)=lace (tilt (direction k a) p) w (q.down _ (dband ..)):= punch_back ..

/-- Inward orientation. Empty contour. -/
structure Conserves (A : Variation n) : Prop where
  maps (i j : Axis) : A i j=A j i
  levy j : ∑ i : Axis, paid 0 i (A i j) = 0
lemma Conserves.withdraw {A : Variation n} (h:Conserves A) (u : Test (n+1)) (j): ∑ i : Axis, A i j (tilt (direction 0 i) u)=0:=by
  have v:=LinearMap.congr_fun (h.levy j) u; simp only [LinearMap.sum_apply,LinearMap.zero_apply,pays,Finset.sum_neg_distrib,neg_eq_zero] at v; exact v
lemma opposite (F : Axis→Axis→ℂ) (p:∀ i j,F j i = - F i j): ∑ i : Axis,∑ j :Axis,F j i=0 := by
  let x:= ∑ i:Axis,∑ j:Axis,F i j
  have h : ∑ i :Axis,∑ j :Axis,F j i= -x:= by
    unfold x; rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun i _=>by rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun j _=>p _ _
  rw [Finset.sum_comm] at h; rw [Finset.sum_comm]; change x=0; change x= -x at h; linear_combination h / 2
lemma plume (K : Payroll n) (f : Test n) (J : Bulb) (p:Quiet f J) (A : Variation n) (H:Conserves A) : delta K f J (cares p) A=0 := by
  let u:= lace f J p
  let t (i j : Axis):= weigh _ (DG (K.K j) (K.sm j) (direction 0 i)) u
  have h (i j:Axis): tilt (direction 0 i) (weigh _ (K.sm j) u) = t i j+testcut K f J (cares p) i j:= by
    unfold u; rw [weight_deriv, tilt_lace]; rfl
  let s (i j : Axis):= A i j (t i j)
  have T (a b : Axis) : t a b= - t b a:= by ext1 x; change D (direction 0 a) (K.K b) x • (u x:ℂ)= -(D (direction 0 b) (K.K a) x • (u x:ℂ)); rw [K.skew a b x,neg_smul] -- stuck
  have U (a b : Axis) : s b a = - s a b:= by unfold s; rw [H.maps,T,map_neg]
  unfold delta
  rw [Finset.sum_comm]; refine Eq.trans (Finset.sum_congr (g:=fun j=> -(∑ i:Axis,s i j)) rfl fun j _=> ?_) ?_
  · exact eq_neg_of_add_eq_zero_left (show (∑ i :Axis,A i j (testcut K f J (cares p) i j)) + (∑ i :Axis,s i j) = 0 from by rw [← Finset.sum_add_distrib,← H.withdraw (weigh _ (K.sm j) u) j]; apply Finset.sum_congr rfl; intro i _; rw [h,map_add]; exact add_comm ..)
  rw [Finset.sum_neg_distrib,opposite s U,neg_zero]
end YM.GaugeFieldConstruction.Fathom
