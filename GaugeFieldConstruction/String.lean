import GaugeFieldConstruction.Sensors
/-!
# Passive slots of section pricing. Work over complex (I preserving c).
-/
set_option autoImplicit false
set_option synthInstance.maxSize 5000
noncomputable section
namespace YM.GaugeFieldConstruction.Stage.Count
open Calibration Calibration.RawBank Floor Cauchy Row Record Phys Function Set Filter Raw Cell Angles
open U1 hiding VV -- avoid VS
open scoped Topology BigOperators
local instance iB : AddCommGroup XX:= @Submodule.addCommGroup ℂ (J Row.x) _ _ _ _
local instance iG : AddCommGroup (UG five):= @Submodule.addCommGroup ℂ (J Row.g) _ _ _ _
local instance iF : AddCommGroup (UF five):= @Submodule.addCommGroup ℂ (J Row.f) _ _ _ _

lemma shaved (x : XX) (h : ∀ Ω : Rotors,YX five false true Ω x=0):x=0 := by
  have hp: rhoX five false true (signMot allf all_yes) x=x:= disabled _ _ (pressure _ _ (leavesX five false true) _) h _
  apply paid_ext; rintro ⟨u,v⟩; apply negate
  have ht:= fee Once allf (leadf allf all_yes) x (u,v); rw [hp] at ht; exact ht
lemma whet (x : XX) (h : ∀ Ω : Rotors,YX five true false Ω x=0): x=0 := by
  apply paid_ext; rintro ⟨u,v⟩
  let a:=v.toBlade.val.1; let b:=v.toBlade.val.2
  obtain ⟨l,p,q⟩:= third a b; let m:=M a l
  have ht:= fee Double m (leadG m (M_pos a l)) x (u,v)
  have H: rhoX five true false (signMot m (M_pos a l)) x=x:= disabled _ _ (pressure _ _ (leavesX five true false) _) h _
  have he: Double.cost m (u,v)=true:=by
    have hv: wedAct.cost m v=true := by
      change ((Raw.v.exterior).cost m v.toBlade)=_; rw [Labels.wed_fee]; change (Labels.reverseBit (m.perm a) (m.perm b)).xor ((m.flip a).xor (m.flip b)) = _
      rw [M_on _ _  (Ne.symm p), M_no _ _ _ (v.toBlade.property.ne) q,M_perm,M_perm,show Labels.reverseBit a b=false from by simp [Labels.reverseBit,show ¬ b<a from not_lt.mpr v.toBlade.property.le]]; rfl -- p.symm wrong (.ne)?
    change (false.xor (wedAct.cost m v))=_; rw [hv]; rfl
  have hv:Double.move m (u,v)=(u,v) := by
    have hh:wedAct.move m v=v:= blade_same v.toBlade v.toBlade.property.ne
    exact Prod.ext rfl hh
  rw [he,hv,H] at ht; exact negate ht

-- projections from W
variable (D : District)
lemma w_g (x:OneW) (p:∀ Ω i,enlarged D five Ω (x.val i)=0) (h:D.g=true) : ∀ i : Axis,Gv (x.val i)=0:=by
  intro i; have H:= congr_arg Gv (x.property.2 i allf)
  let Y:= Gv (x.val i)
  change (gauge five).moves allf Y= -Y at H
  have hw: rhoG five (signMot allf all_yes) Y=Y:= disabled _ _ (pressure _ _ (leavesG five) _) (show ∀ u,YG five u Y=0 from fun Ω=>by
    have he : (enlarged _ five Ω (x.val i)).2.1=0 := congr_arg (fun a:UV five=> a.2.1) (p Ω i)
    rw [ruleG,h] at he; simp only [activates,if_true,one_smul] at he; exact he) _
  rw [properG,H] at hw; exact negate hw.symm
lemma w_h (x:OneW) (p:∀ Ω i,enlarged D five Ω (x.val i)=0) (u) (h:D.f u=true) : ∀ i,Fv u (x.val i)=0:= by
  intro i; have H : mH allf (Fv u (x.val i)) = -Fv u (x.val i) := by rw [← fundF, x.property.2]; exact map_neg ..
  have hw : ∀ Ω,YF five Ω (Fv u (x.val i))=0:= fun Ω=>by
    have he : (enlarged _ five Ω _).2.2.1 (Calibration.first u)=0:= congr_arg (fun a : UV five=> a.2.2.1 (Calibration.first u)) (p Ω i)
    rw [ruleF,EF,show (Calibration.first u).1=u from rfl,h] at he; simp only [activates,if_true,one_smul] at he; exact he
  have ht:= disabled (rhoF five) _ (pressure _ _ (leavesF five) _) hw (signMot allf all_yes)
  rw [properF,H] at ht; exact negate ht.symm
lemma w_m (x: OneW) (p:∀ Ω i,enlarged D five Ω (x.val i)=0) (u) (h:D.g=true ∨ D.f u=true) : ∀ i,Xv u (x.val i)=0:= by
  intro i; have hw Ω : YX five D.g (D.f u) Ω (Xv u (x.val i))=0:= by
    have H : (enlarged _ five Ω (x.val i)).2.2.2 (Calibration.first u)=0:=congr_arg (fun a:UV five=>a.2.2.2 (Calibration.first u)) (p Ω i)
    rw [ruleX] at H; exact H
  cases g:D.g <;> cases q:D.f u
  · rw [g,q] at h; simp at h -- tweak
  · simp_rw [g,q] at hw; apply shaved _ hw
  · simp_rw [g,q] at hw; apply whet _ hw
  simp_rw [g,q] at hw
  have he := disabled (rhoX five true true) _ (pressure _ _ (leavesX five true true) _) hw (signMot allf all_yes)
  rw [properX,← fundX,x.property.2] at he -- rw target
  have hp: -(Xv u (x.val i))= Xv u (x.val i):= by rw [← map_neg]; exact he
  exact negate hp.symm
end YM.GaugeFieldConstruction.Stage.Count
