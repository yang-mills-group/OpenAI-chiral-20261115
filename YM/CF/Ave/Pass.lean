import YM.CF.Ave.Racket
import YM.CF.Pastry.Bliss

/-! Effective measures, visibly the same cut and unit wedge, including exceptional sectors. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Ave
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology
open Fock SU Lat Cube Phase Phase.Sample Mir RP MeasureTheory NormedSpace Branch Lattice Tenant Function Pastry Petal Manifest Filter Finset
attribute [local instance] opCStarAlgebra
variable {m B : Side} {c : Foot m B} {W : Scroll m B c} {a d e v H k b t : ℝ} {p : 1≤H} {K : Seal (Index m)→ Briar m B e→ Ewe m B} {w : Seal (Index m)→ℝ}
def pigment {c : Foot m B} (W : Scroll m B c) (b : ℝ) (U:Skin m B) := ∫ x, law m B U x • Complex.exp (chargeS W b (U,x)) ∂rains m
def cloudD (K : Seal (Index m) → Briar m B e→Ewe m B) (x : Briar m B e) := ∑ S, cloudless (n:=Hearth m B) (K S x)
def scalarD (K : Seal (Index m)→ Briar m B e→ Ewe m B) (x : Briar m B e) := ∑ S,pane (n:=Hearth m B) (K S x)
def zeroOf (x : Briar m B e) (c : Foot m B) (h : Room B e) := nursery (n:=Elf m B) (lens m B c x.val) (lensP c h x.property)
-- moment identity
section
variable (Y : FormR W H p e k K w t b) (P : Room B e)
include Y
lemma duty (x : Briar m B e) : Integrable (fun z=> law m B x.val z • exp (chili W b t (x,z))) (rains m) := by
  by_contra v
  apply rise_ne (n:=Hearth m B) (∑ S,K S x); exact (Y.paid x).symm.trans (integral_undef v)
lemma pitchF (x : Briar m B e) : pigment W b x.val=Complex.exp (scalarD K x) := by
  let t₁ := fun z:Cue m => chili W b t ((x,z):Train m B e)
  let P : Ewe m B →L[ℝ] ℂ := ⟨(panHom _).toLinearMap,(panHom (Hearth m B)).toLinearMap.continuous_of_finiteDimensional⟩
  have he i : P i=pane i := rfl
  let F z:= law m B x.val z • exp (t₁ z)
  have hA z : P (F z)=law m B x.val z • Complex.exp (chargeS W b (x.val,z)) := by
    unfold F; rw [map_smul,he,paneExp]; unfold t₁ chili carry retire silt; rw [hull_sum,hullB,Quilt.mast,add_zero]; rfl
  have hM : Integrable F (rains m):= duty Y x
  have ht : ∫ z,P (F z) ∂rains m=P (exp (∑ S,K S x)) := (show (∫ z,P (F z) ∂rains m)=P (∫ z,F z ∂rains m) from (hinge (n:=Hearth m B) P hM)).trans (congrArg (fun x:Ewe m B=> P x) (Y.paid x))
  unfold pigment; simp_rw [hA] at ht; rw [he,paneExp,pane_f] at ht; exact ht
lemma pigmented (x : Briar m B e) : pigment W b x.val≠0 := by rw [pitchF Y]; exact Complex.exp_ne_zero _
omit Y
lemma decked (x : Briar m B e) : (∑ S,K S x)= hollow (scalarD K x)+cloudD K x := by
  unfold scalarD cloudD; rw [← hollow_sum]; simp only [cloudless,sum_sub_distrib]; abel
lemma darn (x : Briar m B e) (z : Cue m) (b t:ℝ) : (zeroOf x c P).cook (exp (chili W b t (x,z)))=Complex.exp (chargeS W b (x.val,z)) • exp (sheet m B c t x.val z) := by
  change _=Complex.exp _ • _; unfold chili carry; rw [expReal]; exact congrArg _ (congrArg NormedSpace.exp (show (zeroOf x c P).cook _= _ from diect m B t (x,z) c P))
include Y
lemma finale (x : Briar m B e) : (zeroOf x c P).cook (motor (travel m B e H p) (fun z=>exp (chili W b t z)) x)=pigment W b x.val • exp ((zeroOf x c P).cook (cloudD K x)) := by rw [Y.paid,pitchF Y,decked,expReal] -- issue decked binder implicits
-- hand moment link to integral; gross scalar Flight trace unchanged
abbrev Readers (m B : Side) := Skin m B→FC (Elf m B)
def leafR (K : Seal (Index m)→ Briar m B e→Ewe m B) (x : Briar m B e) (c : Foot m B) (P : Room B e) := acts (exp ((zeroOf x c P).cook (cloudD K x))) (sound m B c x.val)
def stroll (x : Briar m B e) {c : Foot m B} (W : Scroll m B c) (P : Room B e) (b t β : ℝ) (K : Seal (Index m)→ Briar m B e→Ewe m B) (f : Readers m B) := (↑(Wilson.bare (G:=SU.group) β x.val) : ℂ)*pigment W b x.val*Complex.exp ((t:ℂ)*energ m B c x.val)*inner ℂ (linearB (CSide m B)) (acts (f x.val) (leafR K x c P))
lemma mileage (x:Briar m B e) (f : Readers m B) (β) : ∫ z, ratioR W e β t b c (fun x=> f x.1) (x.val,z) ∂rains m = stroll x W P b t β K f := by
  let s := (zeroOf x c P).cook; let u := linearB (CSide m B); let A := sound m B c x.val
  let R (p:Ewe m B) := inner ℂ u (acts (f x.val) (acts (s p) A))
  let V : Ewe m B→L[ℝ] ℂ :=
    { toFun:=R
      map_add' p q:= by unfold R; rw [map_add s,act_add,map_add,inner_add_right]
      map_smul' p q:= by unfold R; change _= p • inner ℂ _ _; rw [map_smul s,actReal,eyeReal]
      cont := continuous_const.inner ((show Continuous (acts (f x.val)) from (acts _).continuous).comp ((acts_cont.comp (zeroOf x c P).cookC).clm_apply continuous_const))  -- tune
    }
  let G := energ m B c x.val
  let Y' := Wilson.bare (G:=SU.group) β x.val
  let M z:= law m B x.val z • exp (chili W b t (x,z))
  have he z : ratioR W e β t b c (fun x=>f x.1) (x.val,z)= (Y':ℂ)*Complex.exp ((t:ℂ)*G) * V (M z) := by
    by_cases q: law m B x.val z=0
    · rw [show M z=0 by simp [M,q],map_zero,mul_zero]; exact Set.indicator_of_notMem (by
        intro l; apply (show net m B β (x.val,z)≠0 from (show (x.val,z)∈TallyR m B e β from l).2); unfold net massR; simp [q]) _
    have hK := law_rich m B x.val z q
    have hg := produced c P x.property hK t
    rw [ratioR, Set.indicator_of_mem (show (x.val,z)∈ TallyR m B e β from ⟨x.property,mul_ne_zero q (Wilson.bare_pos (G:=SU.group) β x.val).ne'⟩)]
    change ↑(law m B x.val z*Y')*Complex.exp _*inner ℂ _ (acts _ _)=_
    unfold M; rw [act_mul,hg,map_smul,inner_smul_right, map_smul]; change _= (Y':ℂ)*Complex.exp ((t:ℂ)*G)*(law m B _ _ • inner ℂ _ (acts _ (acts ((zeroOf _ _ _).cook _) _)))
    rw [darn P x,act_smul,map_smul,inner_smul_right]; simp only [Complex.real_smul, Complex.ofReal_mul]; unfold chargeS; dsimp only; simp only [Complex.real_smul]; change (↑(law m B x.val z) * (Y':ℂ))*Complex.exp (-(b:ℂ)*cabin W (x.val,z))* (Complex.exp _*_)= _
    have hp : Complex.exp (-(b:ℂ)*cabin W (x.val,z))*Complex.exp ((t:ℂ)*G+fund m B c x.val z) = Complex.exp ((t:ℂ)*G)*Complex.exp (fund m B c x.val z-(b:ℂ)*cabin W (x.val,z)) := by rw [←Complex.exp_add,←Complex.exp_add]; congr 1; ring
    dsimp only [G] at hp ⊢; linear_combination (law m B x.val z:ℂ)*(Y':ℂ)*inner ℂ u (acts (f x.val) (acts (exp (sheet m B c t x.val z)) A))*hp -- tune u
  simp_rw [he]; rw [integral_const_mul,hinge (n:=Hearth m B) V (show Integrable M _ from duty Y x)]
  unfold stroll leafR; let D := ∫ z,M z ∂ rains m
  change (Y':ℂ) * Complex.exp ((t:ℂ)*G)*inner ℂ u (acts (f x.val) (acts (s D) A))= _; rw [show s D= _ from finale Y P x, act_smul,map_smul,inner_smul_right]; unfold G Y' u A; ring
end
end YM.CF.Ave
