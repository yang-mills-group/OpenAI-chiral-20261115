import GaugeFieldConstruction.String

/-!
# Dimensional shortage for any passive combination, join conditions
-/
set_option autoImplicit false
set_option synthInstance.maxSize 7000
noncomputable section
namespace YM.GaugeFieldConstruction.Stage.Count
open Calibration Calibration.RawBank Floor Cauchy Row Record Function Set Filter Complex Submodule Module
open Raw U1
open scoped Topology BigOperators

variable (D : District)
-- package OneW etc submodule
section Sector
variable {X Y : Type*} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
def whenCold (w : Bool) (A:Submodule ℂ X): Submodule ℂ A:= if w then ⊥ else ⊤
def ice (u : Bool→Bool) (A:Submodule ℂ X): Submodule ℂ (Bool→A) := Submodule.pi Set.univ (fun b=> whenCold (u b) A)
lemma held {u : Bool→Bool} (A : Submodule ℂ X) {p : Bool → A} (h : ∀ b,u b=true→p b=0) : p∈ice u A := by
  intro b _; change p b∈ whenCold (u b) A; cases v:u b; exact Submodule.mem_top
  exact (Submodule.mem_bot _).mpr (h b v)
def snow (u : Bool) : ℕ := if u=true then 0 else 1
lemma fr (w : Bool) (A:Submodule ℂ X) (h : Module.Finite ℂ A): finrank ℂ (whenCold w A)=snow w*finrank ℂ A := by
  cases w
  · change finrank ℂ (⊤:Submodule ℂ A)=1*finrank ℂ A; rw [finrank_top,one_mul]
  change finrank ℂ (⊥:Submodule ℂ A)=0 * _; simp
lemma frost (b : Bool→Bool) (A : Submodule ℂ X) (h : Module.Finite ℂ A): finrank ℂ (ice b A)= (snow (b false)+snow (b true))*finrank ℂ A:= by
  let V := fun i=> whenCold (b i) A
  let W : (ice b A) ≃ₗ[ℂ] ((V false)×(V true)) := {
    toFun f:=(⟨_,f.property false (Set.mem_univ _)⟩,⟨_, f.property true (Set.mem_univ _)⟩)
    invFun p:=⟨fun i=> if i then p.2.val else p.1.val,by
      intro b _; cases b <;> first|exact p.1.property|exact p.2.property⟩ -- layout
    left_inv v:= Subtype.ext (funext fun i=>by cases i <;> rfl)
    right_inv p:=Prod.ext rfl rfl
    map_add' x y:=rfl
    map_smul' z x:=rfl }
  rw [W.finrank_eq, Module.finrank_prod]; dsimp only [V]; rw [fr _ A h,fr _ A h,add_mul]
end Sector

local instance iT : AddCommGroup ↥SymT:=@Submodule.addCommGroup ℂ (Raw.Sym→UV four) _ _ _ _
local instance iW : AddCommGroup ↥OneW:=@Submodule.addCommGroup ℂ (Axis → UV five) _ _ _ _
-- issues recurring instance
local instance cT : AddCommGroup ↥(recG.allowed symAct (SG four)) := @Submodule.addCommGroup ℂ _ _ _ _ _
local instance aT : AddCommGroup ↥(ph.allowed symAct (SF four)) := @Submodule.addCommGroup ℂ _ _ _ _ _
local instance bT : AddCommGroup ↥(recX.allowed symAct (SX four)) := @Submodule.addCommGroup ℂ _ _ _ _ _
local instance cW : AddCommGroup ↥(recG.allowed Raw.v (SG five)) := @Submodule.addCommGroup ℂ _ _ _ _ _
local instance aW : AddCommGroup ↥(ph.allowed Raw.v (SF five)) := @Submodule.addCommGroup ℂ _ _ _ _ _
local instance bW : AddCommGroup ↥(recX.allowed Raw.v (SX five)) := @Submodule.addCommGroup ℂ _ _ _ _ _

def pond (D : District): Submodule ℂ (Trio four symAct):= (whenCold D.g (recG.allowed symAct (SG four))).prod ((ice D.f (ph.allowed symAct (SF four))).prod ⊥)
def starve (D: District):Submodule ℂ (Trio five Raw.v):= (whenCold D.g (recG.allowed Raw.v (SG five))).prod ((ice D.f (ph.allowed Raw.v (SF five))).prod (ice (fun i=> D.g || D.f i) (recX.allowed Raw.v (SX five))))

def passiveBank : Submodule ℂ SymT:= (pond D).map (package four symAct).symm.toLinearMap
def through : Submodule ℂ OneW:= (starve D).map (package five Raw.v).symm.toLinearMap
abbrev U := U1.ph
local instance fca : Module.Finite ℂ (recG.allowed symAct (SG four)) := Module.finite_of_finrank_pos (R:=ℂ) (by rw [show finrank ℂ (recG.allowed symAct (SG four))=3 from g_ranks.1]; decide)
local instance fcb : Module.Finite ℂ (ph.allowed symAct (SF four)) := Module.finite_of_finrank_pos (R:=ℂ) (by rw [show finrank ℂ (ph.allowed symAct (SF four))=2 from f_ranks.1]; decide)
local instance fG : Module.Finite ℂ (recG.allowed Raw.v (SG five)) := Module.finite_of_finrank_pos (R:=ℂ) (by rw [show finrank ℂ (recG.allowed Raw.v (SG five))=2 from g_ranks.2.2.1]; decide)
local instance fF : Module.Finite ℂ (ph.allowed Raw.v (SF five)) := Module.finite_of_finrank_pos (R:=ℂ) (by rw [show finrank ℂ (ph.allowed Raw.v (SF five))=1 from f_ranks.2.2.1]; decide)
local instance fX : Module.Finite ℂ (recX.allowed Raw.v (SX five)) := Module.finite_of_finrank_pos (R:=ℂ) (by rw [show finrank ℂ (recX.allowed Raw.v (SX five))=1 from x_ranks.2.2.1]; decide)

private def biform {X Y : Type*} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] (T : Submodule ℂ X) (S : Submodule ℂ Y) : T.prod S ≃ₗ[ℂ] ((T) × S) where
  toFun x:=(⟨x.val.1,x.property.1⟩,⟨x.val.2,x.property.2⟩)
  invFun x:=⟨(x.1.val,x.2.val),x.1.property,x.2.property⟩
  left_inv _:=rfl; right_inv _:=rfl; map_add' _ _:=rfl; map_smul' _ _:=rfl
private lemma coat {X Y : Type*} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] (T : Submodule ℂ X) (S : Submodule ℂ Y) [Module.Finite ℂ T] [Module.Finite ℂ S]: Module.Finite ℂ (T.prod S):= Module.Finite.equiv (biform T S).symm
private lemma pack_prod {X Y : Type*} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] (T : Submodule ℂ X) (S : Submodule ℂ Y) (h : Module.Finite ℂ T) (g : Module.Finite ℂ S) : finrank ℂ (T.prod S)= finrank ℂ T+finrank ℂ S:= by rw [(biform T S).finrank_eq, Module.finrank_prod]
lemma pays_T : finrank ℂ (passiveBank D)= snow D.g * 3 + (snow (D.f false)+snow (D.f true))*2 := by
  unfold passiveBank
  rw [LinearEquiv.finrank_map_eq (package four symAct).symm,pond] -- lemma?
  rw [pack_prod _ _ inferInstance (coat _ _), pack_prod _ _ inferInstance inferInstance, finrank_bot, add_zero, fr _ _ fca, frost _ _ fcb,show finrank ℂ (recG.allowed symAct (SG four))=3 from g_ranks.1,show finrank ℂ (ph.allowed symAct (SF four))=2 from f_ranks.1]
lemma pays_W : finrank ℂ (through D)= snow D.g*2 + ((snow (D.f false)+snow (D.f true))+ (snow (D.g || D.f false)+snow (D.g || D.f true))) := by
  rw [through,LinearEquiv.finrank_map_eq (package five Raw.v).symm,starve,pack_prod _ _ inferInstance inferInstance,pack_prod _ _ inferInstance inferInstance,fr _ _ fG, frost _ _ fF, frost _ _ fX,show finrank ℂ (recG.allowed Raw.v (SG five))=2 from g_ranks.2.2.1,show finrank ℂ (ph.allowed Raw.v (SF five))=1 from f_ranks.2.2.1,show finrank ℂ (recX.allowed Raw.v (SX five))=1 from x_ranks.2.2.1]; rw [mul_one,mul_one]
end YM.GaugeFieldConstruction.Stage.Count
namespace YM.GaugeFieldConstruction.Stage.Count
open Calibration Calibration.RawBank Floor Cauchy Row Record Function Set Filter Submodule Module Raw U1
open Matter (FlavorIndex)
open scoped Topology BigOperators
variable (D:District)
lemma brittle (p : D≠All) : finrank ℂ (through D) < finrank ℂ (passiveBank D):= by
  rw [pays_T,pays_W]
  cases D with
  | mk a b=>
  have h (p : Bool) : p=false∨p=true := by cases p <;> decide
  dsimp only
  cases a <;> cases y:b false <;> cases z:b true <;> try decide
  exfalso; apply p; unfold All; congr; ext i; cases i <;> first|exact z|exact y
lemma subsidy (v: OneW) (p :∀ Ω i,enlarged D five Ω (v.val i)=0) : v∈ through D := by
  refine ⟨package five Raw.v v,?_,(package ..).symm_apply_apply _⟩
  change _∈ whenCold _ _ ∧ (_,_) ∈ _
  constructor
  · cases e:D.g; exact Submodule.mem_top
    apply (Submodule.mem_bot _).mpr; apply Subtype.ext; funext i
    change (Gv (v.val i)).val=0; rw [w_g D v p e i]; rfl
  constructor
  · apply held; intro i h; apply Subtype.ext; funext j; change (Fv i (v.val j)).val=0; rw [w_h D v p i h j]; rfl
  apply held; intro i h; apply Subtype.ext; funext j; change (Xv i (v.val j)).val=0
  rw [w_m D v p i (Bool.or_eq_true_iff.mp h) j]; rfl
lemma snoozes (x: SymT) (q:x∈ passiveBank D): package four symAct x ∈ pond D := by
  obtain ⟨v,h,rfl⟩:=q; rw [LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply]; exact h
lemma dig {x : SymT} (q:x∈passiveBank D) (t) (h:D.g=true): (x.val t).2.1=0:=by
  have he: (package four symAct x).1∈ whenCold D.g _:= (snoozes D x q).1
  rw [h] at he; have hv := (Submodule.mem_bot ℂ).mp he; exact Subtype.ext (congr_fun (congr_arg Subtype.val hv) t)
lemma price_f {A : Type} (B : Labels A) (d x) (p : x∈ invariant B d) (i k): (x i).2.2.1 k=Flavor.bundle_ (fun j=>(x i).2.2.1 (Calibration.first j)) k := by
  have he (g : Flavor) := congr_arg (fun z:UV d=>z.2.2.1) ((p.1 i).2 g)
  exact congr_fun (faded (V:=UF d) (x i).2.2.1 (fun v=>he v)) k
lemma fiT {x : SymT} (p:x∈passiveBank D) (i : FlavorIndex) (h:D.f i.1=true) (t): (x.val t).2.2.1 i=0 := by
  have ht := (snoozes D x p)
  let F:= (package four symAct x).2.1
  have he:F i.1∈ whenCold (D.f i.1) _ := ht.2.1 i.1 (Set.mem_univ _)
  rw [h] at he; have hp:= (Submodule.mem_bot ℂ).mp he
  have hv : (x.val t).2.2.1 (Calibration.first i.1)=0 := Subtype.ext (congr_fun (congr_arg Subtype.val hp) t)
  rw [price_f symAct four _ x.property]; unfold Flavor.bundle_; split_ifs <;> first|exact hv|rfl
lemma noneV (x:UV four) (i) : x.2.2.2 i=0 := Subtype.ext ((Submodule.mem_bot ℂ).mp (x.2.2.2 i).property)

local instance iG3 : AddCommGroup (UG four):=@Submodule.addCommGroup ℂ (J Row.g) _ _ _ _
local instance iF3 : AddCommGroup (UF four):=@Submodule.addCommGroup ℂ (J Row.f) _ _ _ _
local instance iX3 : AddCommGroup (UX four):=@Submodule.addCommGroup ℂ (J Row.x) _ _ _ _

lemma sleepy (v: SymT) (p:v∈ passiveBank D) (t : Raw.Sym):∀ Ω,enlarged D four Ω (v.val t)=0 := by
  intro Ω; apply Prod.ext; rfl; apply Prod.ext
  · rw [ruleG]; cases h:D.g
    · change (0:ℂ) • _=(0:UG four); exact zero_smul ..
    rw [dig D p t h]; simp
  apply Prod.ext
  · ext1 i; rw [ruleF]; unfold EF; cases h:D.f i.1
    · simp [activates]
    rw [fiT D p i h]; simp
  ext1 i; rw [ruleX,noneV]; exact map_zero (EX D Ω i.1 (d:=four))
lemma pure_tr (v : SymT) (u : D.g=true) (p : v ∈ passiveBank D) : ∑ i : Axis,v.val (ordered i i)=0:= by
  have ht b : ∑ j:Axis, ((v.val (ordered j j)).2.2.1 (Calibration.first b))=0 := by
    let x:= (package four symAct v).2.1 b
    apply Subtype.ext
    have h: trace x.val=0 := (Submodule.mem_bot ℂ).mp (f_ranks.2.2.2.2.2.le (show _∈Submodule.map trace (TT ph fFour) from ⟨_,x.property,rfl⟩))
    have hp : trace x.val ()=0:=congr_fun h ()
    rw [trace_value] at hp
    rw [show ∀ g:Axis→UF four, (∑ i,g i).val=∑ i,(g i).val from fun g=> map_sum (SF four).subtype g Finset.univ]; exact hp
  refine Prod.ext ?_ ?_
  · rw [Prod.fst_sum]; exact Finset.sum_eq_zero fun i _=> (v.property.1 _).1
  rw [Prod.snd_sum]; apply Prod.ext
  · simp [Prod.fst_sum,dig D p _ u]
  rw [Prod.snd_sum]; apply Prod.ext
  · ext1 i; rw [Prod.fst_sum,Finset.sum_apply]
    have he (j : Raw.Sym) := price_f symAct four _ v.property j i; by_cases h:i.2.1=i.2.2
    · conv_lhs=> rw [Finset.sum_congr rfl (fun j _=> he (ordered j j))]
      simp only [Flavor.bundle_, h,↓reduceIte]; exact ht i.1
    simp only [Flavor.bundle_,if_neg h] at he; simp [he]
  ext1 i; rw [Prod.snd_sum,Finset.sum_apply]; simp [noneV]
end YM.GaugeFieldConstruction.Stage.Count
