import GaugeFieldConstruction.Permission

/-!
# U5 Dimension shortage theorem. Conditional on a single coherent frame of
 all the actual point-fields and on the angular relations. No lift
 conclusion included in the assumptions as to proper H at *all-active*
 (need to prove that conclusion via exclusion).
-/
set_option autoImplicit false
set_option synthInstance.maxSize 6000
noncomputable section
namespace YM.GaugeFieldConstruction.Empire
open Calibration RawBank Floor Cauchy Row Record Phys Function Filter Stage Count Submodule Module Raw
open scoped BigOperators
local instance ownG (d:Floor):AddCommGroup (UG d):= @Submodule.addCommGroup ℂ (J g) _ _ _ _
local instance ownF (d:Floor):AddCommGroup (UF d):= @Submodule.addCommGroup ℂ (J f) _ _ _ _
local instance ownX (d:Floor):AddCommGroup (UX d):= @Submodule.addCommGroup ℂ (J Row.x) _ _ _ _
local instance ownU (d: Floor):AddCommGroup (UV d):= inferInstanceAs (AddCommGroup (Prod _ _))
local instance iT2:AddCommGroup ↥SymT:= @Submodule.addCommGroup ℂ (Raw.Sym→UV four) _ _ _ _
local instance iW2:AddCommGroup ↥OneW:= @Submodule.addCommGroup ℂ (Axis→UV five) _ _ _ _

abbrev Across := UV four →ₗ[ℂ] UV five

/-- Poria: the single gradient allocation; build any divergence vector. Define
 externally for actual P. V charges land centered even on general `Θ` applications here
 to T due -I. (Don't assume Θ centers on general inputs.) -/
structure Bend (P : Axis → Across): Prop where
  tax s i x : spinFrame _ s (P i x)=pay (s.flip i) (P (s.perm i) (spinFrame _ s x))
  stripe g i x: flavors _ g (P i x)=P i (flavors _ g x)
namespace Bend

def wheel (P : Axis→Across) : SymT →ₗ[ℂ] VS→ UV five:= LinearMap.pi fun i=> P i.1 ∘ₗ LinearMap.proj i.2 ∘ₗ SymT.subtype
lemma turn {P : Axis→Across} (h:Bend P) (x:SymT): Bend.wheel P x∈BothV := by
  let f:= wheel P x
  have he i (s : Signed): spinFrame _ s (f i)= pay (vsAct.cost s i) (f (vsAct.move s i)):=by
    change spinFrame _ s (P i.1 (x.val i.2))=pay ((s.flip i.1).xor (symAct.cost s _)) _; rw [h.tax,x.property.2,← pay_comp]; cases symAct.cost s i.2
    · rfl
    exact congr_arg (pay _) (map_neg ..)
  constructor
  · rintro ⟨i,j⟩; constructor
    · have ht:= congr_arg (readOne five) (he (i,j) Count.allf); rw [sends_2,show vsAct.move Count.allf (i,j)=(i,j) from Prod.ext rfl (ordered_same _), show vsAct.cost Count.allf (i,j)=true from rfl,pay_true,map_neg] at ht; exact negate ht
    intro t; change flavors _ t (P i (x.val j))=P i _; rw [h.stripe,(x.property.1 j).2 t]; rfl
  exact fun i s=> he i s

def cents (P) (h:Bend P) : SymT→ₗ[ℂ] BothV := (wheel P).codRestrict _ (h.turn)
def sum (P) (h:Bend P) : SymT→ₗ[ℂ] OneW := rowSum.codRestrict _ may_row ∘ₗ cents P h
lemma payV {P} (h:Bend P) (t): (cents P h t).val= fun k=> P k.1 (t.val k.2):= rfl
lemma payW {P} (h:Bend P) (t i) : (Bend.sum P h t).val i= ∑ j:Axis, P j (t.val (ordered j i)) := rowAt ..
end Bend

/- Hints for U5. `Y`,`Z` are section π on the two spaces. Actual
 representation via I, including the unit (not a centering statement).
 Use Θ exactly on the four budget.
-/
variable (D:District)
structure Summit (D : District) where
  i : FreeName four
  j : FreeName five
  P : Axis→Across
  T : Axis→Across
  piP : Rotors→ Module.End ℂ (UV four)
  piQ : Rotors→ Module.End ℂ (UV five)
  trans (Ω x): piP Ω (i.c x)=i.c (enlarged D four Ω x)
  trans' (Ω x): piQ Ω (j.c x)=j.c (enlarged D five Ω x)
  heat : Bend P
  hues : Bend T
  /- Use actual hypotheses [equation through all tests] only in transfer proofs. -/
  complete (t:SymT) (h : Bend.sum P heat t=0) (i j): T i (t.val j)= P i (t.val j)
  wake (t:SymT): (∀ i b,P i (t.val b)=0) →t=0
  -- exact domains of (104) 
  bracket (i Ω x) : piQ Ω (T i x)- T i (piP Ω x)=∑ j:Axis, (Ω.val j i:ℂ) • T j x
  bracket' (i Ω) : piQ Ω ∘ₗ (P i-T i)=(P i-T i) ∘ₗ piP Ω
namespace Summit
variable {D} (B: Summit D)

lemma lethal (Ω) : B.piP Ω (one _)=0:= by rw [← B.i.unit, B.trans,alone,map_zero]
lemma nullify (x:SymT) (h:x∈ passiveBank D) (q) (Ω): B.piP Ω ((B.i.total symAct x).val q)=0 := by
  rw [FreeName.total_value]
  change B.piP Ω (centre _ _) =_
  rw [centre_at,map_sub,map_smul,B.lethal, smul_zero,sub_zero]
  change B.piP Ω (B.i.c _)=_; rw [B.trans, Count.sleepy D x h q Ω,map_zero]
lemma douse (x:SymT) (p:x∈ passiveBank D) (i j) : B.T i ((B.i.total symAct x).val j)=0 := by
  let C:= B.i.total symAct x
  let A:= Bend.cents _ B.hues C
  let q:=B.j.swapped.total vsAct A
  have H k l:B.j.c (q.val (k,l))=B.T k (C.val l):=by
    unfold q
    rw [FreeName.Xcost]; change B.j.c (B.j.c.symm _)=_; rw [LinearEquiv.apply_symm_apply]; rfl
  suffices Q: q=0 by
    change B.T i (C.val j)=_; rw [← H, Q]; exact map_zero _
  apply Count.passive_cover
  · intro k Ω i
    apply B.j.c.injective; rw [← B.trans', H];
    have h:= B.bracket i Ω (C.val k); rw [B.nullify x p k Ω,map_zero,sub_zero] at h
    rw [h,map_sum]; simp_rw [map_smul,H]
  intro g i; apply B.j.c.injective
  rw [map_zero,map_sum]; simp_rw [H]; rw [← map_sum]
  dsimp only [C]; simp_rw [FreeName.total_value,← map_sum, pure_tr D x g p, map_zero]

lemma dries (x : SymT) (p:x∈ passiveBank D): B.j.swapped.total Raw.v (Bend.sum _ B.heat (B.i.total symAct x))∈ Count.through D := by
  let V:=B.i.total symAct x; let Q:= B.j.swapped.total Raw.v (Bend.sum _ B.heat V)
  apply Count.subsidy; intro Ω i
  apply B.j.c.injective; rw [← B.trans',map_zero]
  change B.piQ Ω (B.j.c (Q.val i))=0; unfold Q
  rw [FreeName.Vcost]; change B.piQ Ω (B.j.c (B.j.c.symm _))=_; rw [LinearEquiv.apply_symm_apply,Bend.payW,map_sum]
  apply Finset.sum_eq_zero; intro j _
  let k:=ordered j i
  have u:=B.bracket' j Ω
  have hv:=LinearMap.congr_fun u (V.val k)
  have ht:= B.nullify x p k Ω; have hs:= B.douse x p j k
  change B.piQ Ω (B.P j (V.val k)-B.T j (V.val k))=B.P j (B.piP Ω (V.val k))- B.T j (B.piP Ω (V.val k)) at hv
  change B.T j (V.val k)=0 at hs; change B.piP Ω (V.val k)=0 at ht
  rw [ht,hs,map_zero,map_zero,sub_zero,sub_zero] at hv; exact hv

include B
lemma buys_all : D=All := by
  let H:= passiveBank D; let p : H →ₗ[ℂ] (Count.through D) := LinearMap.codRestrict _ ((B.j.swapped.total Raw.v).toLinearMap ∘ₗ ((Bend.sum _ B.heat) ∘ₗ (B.i.total symAct).toLinearMap ∘ₗ H.subtype)) (fun v=> B.dries v.val v.property)
  by_contra fake
  have h:= brittle D fake; apply Nat.not_le_of_lt h
  haveI : Module.Finite ℂ ↥OneW:= finiteInvariant Floor.five _
  letI : AddCommGroup ↥H:= @Submodule.addCommGroup ℂ _ _ _ _ _
  letI : AddCommGroup ↥(Count.through D) := @Submodule.addCommGroup ℂ _ _ _ _ _
  haveI : Module.Finite ℂ ↥(Count.through D):= @FiniteDimensional.finiteDimensional_submodule ℂ ↥OneW _ _ _ _ _
  apply LinearMap.finrank_le_finrank_of_injective (f:=p)
  apply (LinearMap.ker_eq_bot (f:=p)).mp
  apply LinearMap.ker_eq_bot'.mpr
  intro a h
  have he: Bend.sum _ B.heat (B.i.total symAct a.val)=0:= by
    apply (B.j.swapped.total Raw.v).injective; rw [map_zero]
    exact congr_arg Subtype.val h
  apply Subtype.ext; apply (B.i.total symAct).injective; change _ = B.i.total symAct 0; rw [map_zero]; apply B.wake; intro i b
  rw [← B.complete _ he]; exact B.douse a.val a.property i b

-- integrated sections (defined abstractly, without Lie object). Proper Signed agrees precisely only after buys_all.
def castP : SO→* Module.End ℂ (UV four) where
  toFun s:= B.i.c.toLinearMap ∘ₗ ledger D four s ∘ₗ B.i.c.symm.toLinearMap
  map_one':= by apply LinearMap.ext; intro i; simp
  map_mul' x y:= by apply LinearMap.ext; intro i; simp

def castQ : SO→* Module.End ℂ (UV five) where
  toFun s:= B.j.c.toLinearMap ∘ₗ ledger D five s ∘ₗ B.j.c.symm.toLinearMap
  map_one':= by apply LinearMap.ext; intro i; simp
  map_mul' x y:= by apply LinearMap.ext; intro i; simp

lemma map_spH (u x t) : Sends (fun t=>castP B (Angles.rise u t) x) t (B.piP u (castP B (Angles.rise u t) x)) := by
  let R s:= ledger D four s (B.i.c.symm x)
  change Sends (fun t=> B.i.c.toLinearMap (R (Angles.rise u t))) t (B.piP u (B.i.c (R _)))
  rw [B.trans]; exact posts (Stage.cost D u (B.i.c.symm x) t) B.i.c.toLinearMap
lemma map_spQ (u x t): Sends (fun t=>castQ B (Angles.rise u t) x) t (B.piQ u (castQ B (Angles.rise u t) x)) := by
  let R s:= ledger D five s (B.j.c.symm x)
  change Sends (fun t=> B.j.c.toLinearMap (R (Angles.rise u t))) t (B.piQ u (B.j.c (R _)))
  rw [B.trans']; exact posts (Stage.cost D u (B.j.c.symm x) t) B.j.c.toLinearMap
lemma enough : B.T=B.P := by
  ext1 i
  suffices H : B.P i-B.T i=0 by exact (sub_eq_zero.mp H).symm
  apply LinearMap.ext; intro x
  let p:= B.P i-B.T i
  have he := @Stage.follows (UV four) (UV five) _ _ _ _ _ (castP B) B.piP (castQ B) B.piQ (B.map_spH) (B.map_spQ) p (fun u=>(B.bracket' i u).symm) (signMot allf all_yes)
  have Hu : castP B (signMot allf all_yes)=spinFrame four allf := by
    apply LinearMap.ext; intro x; change B.i.c (ledger D four (signMot allf all_yes) (B.i.c.symm _))= _
    -- congr on name B-dependent D
    rw [show ∀ x, ledger D four (signMot allf all_yes) x= spinFrame _ allf x from fun x=> by rw [B.buys_all]; exact (Stage.mirror ..).symm,B.i.h,LinearEquiv.apply_symm_apply]
  have Hv : castQ B (signMot allf all_yes)=spinFrame five allf := by apply LinearMap.ext; intro x; change B.j.c (ledger D five _ _)=_; rw [show ∀ x, ledger D five (signMot allf all_yes) x=spinFrame five allf x from fun x=>by rw [B.buys_all]; exact (Stage.mirror ..).symm]; simp only [LinearMap.comp_apply,LinearEquiv.coe_coe, B.j.h,LinearEquiv.apply_symm_apply]
  rw [Hu,Hv] at he; change p x=0
  have T: p (spinFrame four allf x)=spinFrame five allf (p x):= LinearMap.congr_fun he x
  have h: spinFrame five allf (p x) = - p (spinFrame four allf x):= by
    dsimp only [p,LinearMap.sub_apply]; rw [map_sub,B.heat.tax,B.hues.tax]; change -_ - -_ = - (_-_); abel
  have H:= negate (T.trans h)
  have hp := (spinFrame five).map_one
  have f (v) :spinFrame five allf (spinFrame five allf v)=v:= by rw [← Module.End.mul_apply,← map_mul,show allf*allf=1 by ext <;> simp [allf,diagonalFlip],hp,Module.End.one_apply]
  rw [← f (p x),←T,H,map_zero]
end Summit
end YM.GaugeFieldConstruction.Empire
