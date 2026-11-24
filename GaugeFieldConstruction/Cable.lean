import YM.Euclid.Differential
import YM.Euclid.Test
/-!
# Distributional Q2 & U2 contour calculus on smooth Conf tests. Coupons.

 Operate one arbitrary addressed slot; stress insert always first. Can purchase cuts varying smoothly in all test slots later. For this local result hold χ *fixed*. Never need test touching collisions. Permutation law as needed for nested products. No assumption here about S itself.
-/
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction.Fathom
open Function Filter Set TopologicalSpace YM Analysis MeasureTheory Points
open scoped Topology BigOperators ContDiff
variable {n : ℕ} (v : Points n)
def tilt (v : Points n) : Module.End ℂ (Test n) := (TestFunction.lineDerivCLM ℂ v).toLinearMap
lemma tilt_pays (u : Test n) : (↑(tilt v u) : Points n → ℂ)=D v u:=funext fun x=> by
  change TestFunction.lineDerivCLM ℂ v u x=_
  rw [TestFunction.lineDerivCLM_eq_fderivCLM,TestFunction.fderivCLM_apply_of_le u (k:=⊤) (by simp)]; rfl
-- omit variant hidden.
lemma dband (v : Points n) (f : Test n) : tsupport (tilt v f)⊆ tsupport f:= by
  apply Subset.trans _ (tsupport_fderiv_subset (f:= (f : Points n→ℂ)) ℝ); apply closure_mono; rw [tilt_pays]; intro x hx w
  exact hx (by change fderiv ℝ (f : Points n→ℂ) x v=0; change fderiv ℝ (f : Points n→ℂ) x=0 at w; rw [w]; rfl)
lemma tilts (v w : Points n) (u : Test n) : tilt v (tilt w u)=tilt w (tilt v u):= by
  apply TestFunction.ext; intro x; simp_rw [tilt_pays]; exact commuteD ((u.contDiff.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt) _ _
lemma diffT (u : Test n) : Differentiable ℝ u := u.contDiff.differentiable (by simp)

def loop (p : Equiv.Perm (Fin n)) : Points n ≃L[ℝ] Points n where
  toFun := arrangeL p
  invFun:= arrangeL p.symm
  left_inv x:= PiLp.ext (fun i=> by simp)
  right_inv x:= PiLp.ext (fun i=> by simp)
  map_add':=(arrangeL p).map_add
  map_smul':=(arrangeL p).map_smul

lemma ts_pull {n m :ℕ} (c : Points n ≃L[ℝ] Points m) (u : Points m→ℂ) : tsupport (u ∘ c)=c ⁻¹' tsupport u := by
  have he : support (u ∘ c)= c ⁻¹' support u:=rfl
  unfold tsupport; rw [he]; exact (c.toHomeomorph.preimage_closure _).symm

def pullLinear {m : ℕ} (c:Points n≃L[ℝ] Points m) (q:c ⁻¹' conf m ⊆ conf n) : Test m →ₗ[ℂ] Test n where
  toFun u:=⟨u ∘ c,u.contDiff.comp c.contDiff,by rw [HasCompactSupport, ts_pull]; exact c.toHomeomorph.isCompact_preimage.mpr u.hasCompactSupport,
    by rw [ts_pull]; exact Subset.trans (preimage_mono u.tsupport_subset) q⟩
  map_add' _ _:= TestFunction.ext (fun _=> rfl)
  map_smul' _ _:= TestFunction.ext (fun _=>rfl)

lemma pull_val {m :ℕ} (c:Points n ≃L[ℝ] Points m) (q:c ⁻¹' conf m ⊆ conf n) (u : Test m) (x): pullLinear c q u x=u (c x) :=rfl

def perm (p:Equiv.Perm (Fin n)) : Module.End ℂ (Test n) := pullLinear (loop p) fun x hx=> by
  rw [← (loop p).symm_apply_apply x]; exact Points.rearrange_in p.symm (show loop p x∈ conf n from hx)
lemma perm_app (p:Equiv.Perm (Fin n)) (u : Test n) (x) : perm p u x = u (rearrange p x):=rfl
lemma voyages (p:Equiv.Perm (Fin n)) (u : Test n) (i) (a) : tilt (direction (p i) a) (perm p u)=perm p (tilt (direction i a) u) := by
  ext1 x; rw [perm_app,tilt_pays,tilt_pays]; exact placement p i a _ _ (diffT u).differentiableAt

-- Derivative in the slot on a distribution. Precomposition with minus tilt.
abbrev Bond (n : ℕ) := Test n→ₗ[ℂ] ℂ
def paid (i : Fin n) (a : Axis) : Module.End ℂ (Bond n) := (LinearMap.llcomp ℂ (Test n) (Test n) ℂ).flip (-tilt (direction i a))
lemma pays (i : Fin n) (a) (x : Bond n) (u : Test n) : paid i a x u=- x (tilt (direction i a) u) := x.map_neg _
lemma both (i j : Fin n) (a b : Axis) (x : Bond n): paid i a (paid j b x)=paid j b (paid i a x) := by ext1 v; simp only [pays]; rw [tilts]

section Weights
variable {v : Test n} (g : Points n → ℝ) (p : ContDiff ℝ ∞ g)

def weigh : Module.End ℂ (Test n) where
  toFun x:= ⟨fun w=> g w • (x w : ℂ),p.smul x.contDiff,HasCompactSupport.smul_left (f:=g) x.hasCompactSupport,Subset.trans (tsupport_smul_subset_right g x) x.tsupport_subset⟩
  map_add' _ _:= TestFunction.ext fun z=> smul_add ..
  map_smul' r x:= TestFunction.ext fun z=> smul_comm (g z) (r:ℂ) (x z)
lemma scalar (u : Test n) (x): weigh g p u x=g x • (u x:ℂ) := rfl
lemma taxed (u : Test n) : tsupport (weigh g p u)⊆ tsupport u := tsupport_smul_subset_right g u
include p
lemma DG (u : Points n) : ContDiff ℝ ∞ (D u g) := contDiff_iff_contDiffAt.mpr fun x=> dSmooth p.contDiffAt u (by simp)
lemma weight_deriv (v : Test n) (w : Points n): tilt w (weigh g p v)=weigh (D w g) (DG _ p w) v+weigh g p (tilt w v) := by
  ext1 x; change tilt w _ x=(weigh (D w g) (DG _ p w) v) x+(weigh g p (tilt w v)) x; rw [scalar,scalar,tilt_pays,tilt_pays]; rw [show (⇑(weigh g p v) : Points n→ℂ)=fun x=>g x • v x from rfl]
  unfold D; rw [fderiv_fun_smul (p.differentiable (by simp) x) (diffT v x)]; simp [add_comm]
end Weights

section
-- Nickels for an external field inserted first

def fuse : Points (n+1)≃L[ℝ] E4 × Points n:= Points.peel.toContinuousLinearEquiv.trans (WithLp.prodContinuousLinearEquiv _ _ _ _) -- check
lemma fuse_p (q : Points (n+1)): fuse q=(head q,tail q):=rfl
lemma fuse_m (q : E4 ×Points n) : fuse.symm q=cons q.1 q.2:=rfl
def helm : Points (n+1)→L[ℝ] E4:= (ContinuousLinearMap.fst ..).comp fuse.toContinuousLinearMap
def riders : Points (n+1)→L[ℝ] Points n:=(ContinuousLinearMap.snd ..).comp fuse.toContinuousLinearMap
lemma helm_head (q :Points (n+1)): helm q=q 0:=rfl
lemma riders_tail (q : Points (n+1)): riders q=tail q:=rfl
lemma head_on (a) : helm (direction (n:=n+1) 0 a)=basis a:=by rw [helm_head]; simp [direction]
lemma on_left (a) : riders (direction (n:=n+1) 0 a)=0:= by ext1 i; rw [riders_tail]; simp [tail,direction,PiLp.single_apply]
lemma nope (i : Fin n) (a) : helm (direction i.succ a)=0:=by rw [helm_head]; simp [direction,PiLp.single_apply]
lemma on_rail (i : Fin n) (a): riders (direction i.succ a)=direction i a := by ext1 k; rw [riders_tail]; simp [direction,Points.tail,PiLp.single_apply]

lemma first_conf (x : Points (n+1)) (p:riders x∈conf n) (u:∀ i : Fin n,riders x i ≠ helm x) : x∈conf _:= by
  intro i; refine Fin.cases ?_ ?_ i
  · intro j; refine Fin.cases ?_ ?_ j
    · simp
    intro k H; exact ((u k) H.symm).elim
  intro k j; refine Fin.cases ?_ ?_ j
  · intro z; exact ((u k) z).elim
  intro m z; exact congr_arg _ (p (a₁:=k) (a₂:=m) z) -- check binder

/-- t bulb in stress coordinate, keeping tsupport(t) away from all old positions -/
def Quiet (f : Test n) (t : E4→ℝ) := ∀ x : Points n,x ∈ tsupport f → ∀ i : Fin n,x i ∉ tsupport t
lemma Quiet.down {f : Test n} {t} (h:Quiet f t) (q : Test n) (p : tsupport q⊆tsupport f) : Quiet q t := fun i v=> h i (p v)
lemma Quiet.refines {f : Test n} {t} (h:Quiet f t) (l) (p : tsupport l⊆tsupport t) : Quiet f l:=fun i v k a=> h i v k (p a)

def hits (x : Points (n+1)) (u : Test n) (t : E4→ℝ): ℂ:= t (helm x) • u (riders x)
lemma hits_off (u : Test n) (t : E4→ℝ) : tsupport (fun x=>hits x u t) ⊆ fuse (n:=n) ⁻¹' (tsupport t ×ˢ tsupport u) := by
  apply closure_minimal _ (((isClosed_tsupport _).prod (isClosed_tsupport _)).preimage fuse.continuous); intro x hx
  constructor
  · change helm x∈_; apply subset_closure; intro p; exact hx (by change t _ • _=0; rw [show t (helm x)=0 from p]; simp)
  change riders x ∈ _; apply subset_closure; intro p; exact hx (by change _ • u _=0; rw [show u (riders x)=0 from p]; simp)

def punched (u : Test n) (t : E4→ℝ) (p : Quiet u t) (tS : ContDiff ℝ ∞ t) (tC : HasCompactSupport t) : Test (n+1) :=
  ⟨fun x=> hits x u t,(tS.comp helm.contDiff).smul (u.contDiff.comp riders.contDiff),
    (fuse.toHomeomorph.isCompact_preimage.mpr (tC.prod u.hasCompactSupport)).of_isClosed_subset
      (isClosed_tsupport _) (hits_off u t),
    fun x hx=> first_conf x (u.tsupport_subset (hits_off u t hx).2) fun i j=> p _ (hits_off u t hx).2 i (j.symm ▸ (show helm x ∈ tsupport t from (hits_off u t hx).1))⟩
variable (u : Test n) (t : E4→ℝ) (p : Quiet u t) (tS : ContDiff ℝ ∞ t) (tC : HasCompactSupport t)
lemma punch (x) : punched u t p tS tC x = t (helm x) • u (riders x):=rfl
lemma badgeD (v : E4) : tsupport (D v t)⊆tsupport t := by
  apply Subset.trans _ (tsupport_fderiv_subset (f:=t) ℝ); apply closure_mono; intro x hx q; apply hx; unfold D; rw [show fderiv ℝ t x=0 from q]; rfl
lemma b_sm (t : E4→ℝ) (tS : ContDiff ℝ ∞ t) (v : E4) : ContDiff ℝ ∞ (D v t):= contDiff_iff_contDiffAt.mpr fun x=> dSmooth tS.contDiffAt _ (by simp)
lemma b_co (t : E4→ℝ) (tC : HasCompactSupport t) (v : E4) : HasCompactSupport (D v t):=(show IsCompact (tsupport t) from tC).of_isClosed_subset (isClosed_tsupport _) (badgeD t v)
lemma punch_front (a : Axis) : tilt (direction 0 a) (punched u t p tS tC)=
    punched u (D (basis a) t) (p.refines _ (badgeD ..)) (b_sm _ tS _) (b_co _ tC _):= by
  ext1 x; rw [tilt_pays,punch]; change fderiv ℝ ((t ∘ helm (n:=n)) • (u ∘ riders)) x _= _
  rw [fderiv_smul ((tS.differentiable (by simp)).differentiableAt.comp _ helm.differentiableAt) ((diffT u).differentiableAt.comp _ riders.differentiableAt)]
  rw [fderiv_comp _ (tS.differentiable (by simp) _) helm.differentiableAt, fderiv_comp _ (diffT u _) riders.differentiableAt]; simp only [ContinuousLinearMap.fderiv, ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.comp_apply,on_left,head_on,map_zero, smul_zero,zero_add]; rfl
lemma punch_back (k : Fin n) (a : Axis) : tilt (direction k.succ a) (punched u t p tS tC)=
    punched (tilt (direction k a) u) t (p.down _ (dband ..)) tS tC:=by
  ext1 x; rw [tilt_pays,punch,tilt_pays]; change fderiv ℝ ((t ∘ helm (n:=n)) • (u ∘ riders)) x _= _
  rw [fderiv_smul ((tS.differentiable (by simp)).differentiableAt.comp _ helm.differentiableAt) ((diffT u).differentiableAt.comp _ riders.differentiableAt)]
  rw [fderiv_comp _ (tS.differentiable (by simp) _) helm.differentiableAt, fderiv_comp _ (diffT u _) riders.differentiableAt]; simp only [ContinuousLinearMap.fderiv,ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.comp_apply,nope,on_rail,map_zero,zero_smul,add_zero]; rfl
end
end YM.GaugeFieldConstruction.Fathom
