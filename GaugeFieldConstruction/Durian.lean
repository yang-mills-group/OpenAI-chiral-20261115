import GaugeFieldConstruction.Meters
/-!
# Regard (87) on three positions. Annular budget uses one-axis-separated, not every coordinate.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 5600
noncomputable section
namespace YM.GaugeFieldConstruction.Ember
open Calibration Raw Cauchy LabelAction Empire Fathom Payroll Function Filter Set TopologicalSpace Analysis MeasureTheory Points Bulb Palace
open scoped Topology BigOperators ContDiff
open Floor Wick Invoice Gap Sailing Module
attribute [local instance] iG iF iX iU iT2 iW2 iV iS
variable {n : ℕ} {X : Type*} {ℱ : Filter X} {S : City} {q:X→Carat}
local notation "l4" => Calibration.lift Floor.four
local notation "l5" => Calibration.lift Floor.five
-- prove conditional pair mirror from Views, no extra covariance assumption.
lemma roll_perm (i:Equiv.Perm (Fin n)) (v : Rim) (p : Test n): Fathom.perm i (v.roll p)=v.roll (Fathom.perm i p):= by ext1 x; rw [perm_app,Rim.value,Rim.value,perm_app]; rfl

def tie (x y : UV five) := Function.update (other x) front y
lemma io (x y): tie x y= (![x,y] : Fin 2→UV five) := by funext i; fin_cases i <;> simp [tie,other,front]
lemma roll_tie (S:City) (x y f): S.spot (other x) front y f=S.fee 2 (tie x y) f :=rfl
lemma dsails (H : Views S ℱ q) [ℱ.NeBot] (x y : UV five) (p : Test 2): silky x y p = silky y x (Fathom.perm rotor p):= by
  refine tendsto_nhds_unique_of_eventuallyEq (H.pair _ _ _) (H.pair _ _ _) (Eventually.of_forall fun k=> ?_)
  let Q:= q k; let v:= (Q.G five).c x; let w:= (Q.G five).c y
  change S.spot _ front w (Q.u.roll p)=S.spot (other w) front v (Q.u.roll _); rw [roll_tie,roll_tie, ← S.rearr rotor (tie v w), rotor_inv]
  rw [roll_perm,show tie v w ∘ rotor=tie w v by rw [io,io]; ext1 i; fin_cases i <;> rfl] -- adjust

lemma perMap (p : Equiv.Perm (Fin n)) : MeasurePreserving (arrangeL p) := by
  let A : Points n≃ₗᵢ[ℝ] Points n:=
    { toLinearEquiv := (loop p).toLinearEquiv
      norm_map' x:=by
        rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
        simp_rw [PiLp.norm_sq_eq_of_L2]; exact Equiv.sum_comp p (fun i=> ∑ j:Axis, ‖x i j‖^2) }
  exact A.measurePreserving

lemma cost_mirror (s : Equiv.Perm (Fin n)) (v : Test n) (K : Points n→ℂ): (Fathom.perm s v).applyTo K=v.applyTo (K ∘ arrangeL s.symm) := by
  rw [Test.applyTo,Test.applyTo]; nth_rw 2 [← (perMap s).integral_comp ((loop s).toHomeomorph.toMeasurableEquiv.measurableEmbedding)]
  apply integral_congr_ae; refine Eventually.of_forall (fun x=>?_)
  change v (arrangeL s x) * K x=v (arrangeL s x) * K ((loop s).symm (loop s x)); rw [ContinuousLinearEquiv.symm_apply_apply]

lemma aspect (x : Points 2): pr (arrangeL rotor x)= -pr x:= by
  rw [pr_val]; change x (rotor front)- x (rotor 0)=_
  rw [head', show rotor front=0 from true']; rw [pr_val,neg_sub]; rfl
lemma mirror_is (H : Views S ℱ q) [ℱ.NeBot] (x y : UV five) (p :Test 2) : silky x y p=p.applyTo (fun v=>eye (v 0-v front) (couples (shells _ y) (shells _ x))) := by
  rw [dsails H x y]
  change shown _ _= _
  rw [posts,cost_mirror]; congr 1

-- now the position orders of 3-price

def axisRange (n : ℕ) := {x : Points n| ∃ i : Axis, Function.Injective fun j => x j i}
lemma towards (p : Equiv.Perm (Fin n)) (x : Points n) (h:x ∈ axisRange n) : Points.rearrange p x∈axisRange n := by
  obtain ⟨i,hi⟩:=h; exact ⟨i,hi.comp p.injective⟩
def flip_last : Equiv.Perm (Fin 3) := Equiv.swap (1 : Fin 3) 2
lemma over_flip (f : Points 3) : helm (rearrange flip_last f)=helm f:= by change f _=_; rw [show flip_last 0=0 by decide]; rfl
lemma flap (j): flip_last (Fin.succ (n:=2) j)=(rotor j).succ:=by fin_cases j <;> rfl -- swap decidable rfl?
lemma rotorT (v : Points 3): riders (arrangeL flip_last v)=arrangeL rotor (riders v):= PiLp.ext (fun i=>by change v (flip_last i.succ) = v ((rotor i).succ); rw [flap])
lemma capd (v : Foil) (i j) (K : Payroll 2) : tsupport (testcut K v.p v.a v.u.cared i j) ⊆ axisRange 3 := by
  intro x hx
  obtain ⟨H,q⟩:= testcut_L K v.p v.a v.u.cared i j hx -- check
  let p:=riders x; have hv: p∈ tsupport v.p:=q; let z:=helm x; have hz : z∈ v.a.shore:= H
  have hY : ∀ i:Axis, p 0 i ≠ p 1 i:=fun i u=> (by decide : (0: Fin 2)≠1) ((v.plen hv i) u)
  have ht : ∀ i:Axis,p 0 i≠z i:=v.luck p hv z (strands hz)
  have he:p front≠z := fun e=>centre (b:=v.a) (e ▸ v.u.bulb _ hv) hz
  have uu :∃ k:Axis,p front k≠z k:= by by_contra! a; exact he (PiLp.ext a)
  obtain ⟨k,K⟩:=uu
  refine ⟨k,?_⟩; intro i j h; fin_cases i <;> fin_cases j <;> first|rfl| exact (ht k h).elim|exact (ht k h.symm).elim|exact (K h).elim|exact (K h.symm).elim|exact (hY k h).elim|exact (hY k h.symm).elim

lemma counter (S:City) (t x y p) : S.tagged (tie x y) t p=S.tagged (tie y x) t (Fathom.perm flip_last p):= by
  simp_rw [tagged_cost]; rw [← S.rearr flip_last, show flip_last.symm=flip_last from Equiv.symm_swap ..]; congr 2; ext1 i; rw [io,io]; fin_cases i <;> rfl
lemma into_patch (K:Payroll 2) (v:Foil) (i j): tsupport (Fathom.perm flip_last (testcut K v.p v.a v.u.cared i j)) ⊆ axisRange 3 := by
  let p:=testcut K v.p v.a v.u.cared i j; change tsupport ((p : Points 3→ℂ) ∘ loop flip_last) ⊆ _
  rw [ts_pull]; intro x h
  rw [← (loop flip_last).symm_apply_apply x]
  exact towards flip_last.symm _ (capd v i j K h)
end YM.GaugeFieldConstruction.Ember
