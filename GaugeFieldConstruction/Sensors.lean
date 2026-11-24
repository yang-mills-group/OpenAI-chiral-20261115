import GaugeFieldConstruction.Blake
/-!
# No map from V × Sym for constraints of U5. Direct component evaluation
-/
set_option autoImplicit false
set_option synthInstance.maxSize 5000
noncomputable section
namespace YM.GaugeFieldConstruction.Stage.Count
open Calibration Calibration.RawBank Floor Cauchy Row Record Phys Function Set Filter Raw -- tweak
open Raw
open scoped Topology BigOperators

local instance XA : AddCommGroup XX:=@Submodule.addCommGroup ℂ (J Row.x) _ _ _ _
local instance GA : AddCommGroup (UG five):=@Submodule.addCommGroup ℂ (J Row.g) _ _ _ _
local instance FA : AddCommGroup (UF five):=@Submodule.addCommGroup ℂ (J Row.f) _ _ _ _

lemma no_spin0 (s : VS→XX) (p:∀ i, rotates (YX five true false) fun j=> s (j,i)) : s=0 := by -- unused X
  ext1 ⟨j,i⟩
  have he:= survives (rhoX five true false) (YX five true false) (Angles.pressure _ _ (leavesX five true false) _) (p i) allf all_yes j
  have H (v : XX) : rhoX five true false (signMot allf all_yes) v=v:= by
    have y :∀ i : X5,Double.move allf i=i ∧ Double.cost allf i=false := by decide +kernel
    obtain ⟨w,rfl⟩:= paid_sources v
    suffices g: rhoX five true false (signMot allf all_yes) ∘ₗ jet source= jet source by exact LinearMap.congr_fun g w
    apply ket_ext; intro i; rw [LinearMap.comp_apply,on_ket,leadG allf all_yes,(y i).1,(y i).2]; rfl
  rw [H] at he; exact negate he
lemma no_spinF (v : VS→ UF five) (u: passes mH v) (h:∀ i, rotates (YF five) fun j=> v (j,i)): v=0 := by
  have hp i :rotPay mH (fun j=>v (j,i)):= by
    intro s g j; rw [← show rhoF five (signMot s g) _ = _ from properF s g (v (j,i))]; exact survives (rhoF five) (YF five) (Angles.pressure _ _ (leavesF five) _) (h i) s g j
  let d:=ordered (0:Axis) 0; let V (i:Axis):= v (i,d)
  have H s j: mH s (V j)=pay (s.flip j) (V (s.perm j)):= by
    have hw:= u s (j,d)
    unfold V
    rw [hw]; change pay ((s.flip j).xor (symAct.cost s d)) (v (s.perm j,symAct.move s d)) = _
    rw [show symAct.cost s d=false from by unfold d; rw [fee_turn,Bool.xor_self]]; unfold d; rw [sym_turn, isotrope u hp _ (s.perm 0)]; simp only [if_true,Bool.xor_false]
  have hv : V=0:= fred V H (h d)
  ext1 ⟨i,k⟩; rw [← ordered_same k,isotrope u hp]; split_ifs <;> first|exact congr_fun hv i|rfl
lemma justG (x : VS→ UG five) (p : passes (gauge five).moves x)
    (h:∀ i,rotates (YG five) fun j=>x (j,i)) (w:∀ j : Axis,∑ i : Axis,x (j,ordered i i)=0) : x=0 := by
  refine trace_deletes p ?_ w; intro i s g j; exact Eq.trans (properG s g (x (j,i))).symm (survives (rhoG five) (YG five) (Angles.pressure _ _ (leavesG five) _) (h i) s g j)
lemma justX (x : VS→XX) (p:passes BH x) (h:∀ i,rotates (YX five true true) fun j=>x (j,i)) (w :∀ j:Axis, ∑ i:Axis,x (j,ordered i i)=0) : x=0 := by
  refine trace_deletes p ?_ w; intro i s g j; exact Eq.trans (properX s g (x (j,i))).symm (survives (rhoX five true true) (YX five true true) (Angles.pressure _ _ (leavesX five true true) _) (h i) s g j)
lemma vac {A:Type*} [AddCommGroup A] [Module ℂ A] (x: VS→A) (p:∀ i,rotates (fun _=> (0:Module.End ℂ A)) fun j=>x (j,i)):x=0 := by
  ext1 ⟨s,k⟩; obtain ⟨i,e,-⟩:= third s s
  have he:=p k (Ortho.plane s i) i
  change 0= ∑ j : Axis, _ at he; rw [Finset.sum_eq_single s] at he
  · simp [Ortho.plane,e,Ne.symm e] at he; exact he.symm
  · intro b _ v; simp [Ortho.plane,v,e, Ne.symm v, Ne.symm e]
  simp
variable (D : District)
abbrev Gv : UV five →ₗ[ℂ] UG five := LinearMap.fst .. ∘ₗ LinearMap.snd ..
abbrev Fv (i : Bool): UV five→ₗ[ℂ] UF five := LinearMap.proj (Calibration.first i) ∘ₗ LinearMap.fst .. ∘ₗ LinearMap.snd .. ∘ₗ LinearMap.snd ..
abbrev Xv (i : Bool): UV five →ₗ[ℂ] UX five := LinearMap.proj (Calibration.first i) ∘ₗ LinearMap.snd .. ∘ₗ LinearMap.snd .. ∘ₗ LinearMap.snd ..
-- If H over orientation includes generation-reversing, first tag amends spinFrame with rev_first.
lemma fundF (p : UV five) (s : Signed) (j) : Fv j (spinFrame _ s p)=mH s (Fv j p):= by change _= mH s (p.2.2.1 _); change mH s (p.2.2.1 (Calibration.rev s (Calibration.first j)))=_; rw [rev_first]
lemma fundX (p : UV five) (s : Signed) (j) : Xv j (spinFrame _ s p)=BH s (Xv j p):= by change _=BH s (p.2.2.2 _); change BH s (p.2.2.2 (Calibration.rev s (Calibration.first j)))=_; rw [rev_first]
lemma reserves {O:Type*} (f : VS → UV five) [AddCommGroup O] [Module ℂ O] {X : UV five→ₗ[ℂ] O} {H : Signed →* Module.End ℂ O} (w:f∈ BothV) (h :∀ p s,X (spinFrame _ s p)=H s (X p)) : passes H (X ∘ f) := by
  intro s i; dsimp; rw [← h, w.2 i s]; cases vsAct.cost s i; rfl
  exact map_neg X _
lemma stroll {O:Type*} (f : Axis → UV five) [AddCommGroup O] [Module ℂ O] {X : UV five→ₗ[ℂ] O} {H : Rotors →Module.End ℂ O}
    (h : rotates (enlarged D five) f) (p :∀ u s,H s (X u)=X (enlarged D five s u)) : rotates H (X ∘ f):= by
  intro s i; dsimp only [Function.comp_apply]; rw [p,h,map_sum]; simp only [map_smul]

lemma passive_cover (T : BothV) (p : ∀ i,rotates (enlarged D five) fun j:Axis=>T.val (j,i)) (h : D.g=true → ∀ j:Axis, ∑ i:Axis, T.val (j,ordered i i) = 0) : T=0 := by
  let A:= T.val
  have hf (i) : Fv i ∘ A=0 := by
    have ht j := stroll (O:=UF five) D (fun k=>T.val (k,j)) (X:=Fv i) (H:=fun B=> EF D B i) (p j) (fun p s=> Eq.symm (ruleF D s p (Calibration.first i)))
    cases g:D.f i
    · apply vac; intro j; have H:=ht j; simp only [EF,g,activates,Bool.false_eq_true, ↓reduceIte,zero_smul] at H; exact H
    apply no_spinF
    · exact reserves _ T.property (fun p s=>fundF p s i)
    intro j; have H:=ht j; simp only [EF,g,activates,if_true,one_smul] at H; exact H
  have w {O : Type} [AddCommGroup O] [Module ℂ O] (X: UV five→ₗ[ℂ] O) (p:D.g=true) (i) : ∑ j:Axis, X (T.val (i,ordered j j))=0 := by rw [← map_sum,h p,map_zero]
  have hx (i) : Xv i ∘ A=0 := by
    have ht j := stroll (O:=UX five) D (fun k=>T.val (k,j)) (X:=Xv i) (H:=fun B=> EX D B i) (p j) (fun p s=>Eq.symm (ruleX D s p (Calibration.first i)))
    have he: passes BH (Xv i ∘ A):= reserves _ T.property (fun p s=>fundX p s i)
    cases e:D.g <;> cases v:D.f i
    · apply vac; intro j; have H:=ht j; unfold EX at H; rw [v,e] at H
      intro s k; have hv:=H s k; rw [noneX] at hv; exact hv
    · apply vanish _ he; intro j; have H:=ht j; unfold EX at H; rw [v,e] at H; exact H
    · apply no_spin0 _; intro j; have H:=ht j; unfold EX at H; rw [v,e] at H; exact H
    apply justX _ he _ (w _ e); intro j; have H:=ht j; unfold EX at H; rw [v,e] at H; exact H
  have hg : Gv ∘ A=0:=by
    cases v:D.g
    · apply vac; intro i; apply stroll D (fun j=>T.val (j,i)) (p i); intro x s; apply Eq.symm; change (enlarged _ _ _ _).2.1=_; rw [ruleG,v]; exact zero_smul ..
    apply justG _ (reserves _ T.property (fun p g=>rfl)) ?_ (w _ v)
    intro i; exact stroll D _ (p i) fun p s=>Eq.symm (show Gv (enlarged D five s p)= YG five s (Gv p) from by change (enlarged _ _ _ _).2.1=_; rw [ruleG,v]; exact one_smul ..)
  apply (package five vsAct).injective; rw [map_zero]; apply Prod.ext
  · exact Subtype.ext (funext fun i=> congr_arg (fun p : UG five=>p.val) (congr_fun hg i)) -- tweak
  refine Prod.ext (funext fun i=>Subtype.ext (funext fun j=>?_)) (funext fun i=>Subtype.ext (funext fun j=>?_))
  · exact congr_arg (fun x : UF five=>x.val) (congr_fun (hf i) j)
  exact congr_arg (fun x : UX five=>x.val) (congr_fun (hx i) j)
end YM.GaugeFieldConstruction.Stage.Count
