import GaugeFieldConstruction.Ream
import GaugeFieldConstruction.Snip

/-!
# 81 point-statuses. transfer through actual (93) and stress identification. Use only qualitative distributions, in fact here only the pair subsystem.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 6600
noncomputable section
namespace YM.GaugeFieldConstruction.Ember
open Calibration Raw Cauchy LabelAction Empire Fathom Payroll Function Filter Set TopologicalSpace Analysis MeasureTheory Points Bulb Palace
open scoped Topology BigOperators ContDiff
open Floor Wick Invoice Gap Sailing Module
attribute [local instance] iG iF iX iU iT2 iW2 iV iS
variable {n :ℕ}
local notation "l4"=> Calibration.lift Floor.four
local notation "l5"=> Calibration.lift Floor.five

-- 81 plenum two-tests additionally x ≠ y
structure Carat where
  G (d : Floor): FreeName d
  u : Rim
  include_ (d x) : (G five).c (Calibration.lift d x)=Calibration.lift d ((G d).c x)
  center_ d x: Calibration.centered x→Calibration.centered ((G d).c x)
namespace Carat
variable (Q : Carat)
abbrev t : SymT ≃ₗ[ℂ] SymT := (Q.G four).total symAct
abbrev v : BothV ≃ₗ[ℂ] BothV:= (Q.G five).total vsAct
abbrev w : OneW ≃ₗ[ℂ] OneW:= (Q.G five).total Raw.v
lemma t_pay (x : SymT) (i) : (Q.t x).val i=(Q.G four).c (x.val i):= mark _ (Q.center_ four _ (x.property.1 i).1)
lemma v_pay (x : BothV) (i): (Q.v x).val i=(Q.G five).c (x.val i):= FreeName.Xcost ..
lemma w_pay (x : OneW) (i) :(Q.w x).val i=(Q.G five).c (x.val i):=FreeName.Vcost ..
lemma t_print (x : SymT) : prints (Q.t x)= fun i j=> (Q.G five).c (prints x i j) := by funext i j; simp [prints,pens,Q.include_,t_pay]
lemma tbar_c (x : SymT): tbar (Q.t x)=Q.t (tbar x):= Subtype.ext (funext fun i=>by change shade four _= _; rw [t_pay,t_pay, ←(Q.G four).charge]; rfl)
abbrev κ : ℂ:=Q.u.r
lemma nζ : Q.κ ≠0:= by unfold κ; exact_mod_cast Q.u.ne
def backₛ (S : City) (v : Bond n): Bond n:=v ∘ₗ Q.u.roll -- beta use remove S
end Carat
open Carat
variable {X : Type*} {ℱ : Filter X} {S : City} {P : Axis→Across} {q : X→Carat} (L:Sheds S P)
structure Views (S : City) (ℱ : Filter X) (q : X→Carat) : Prop where
  /- weak comparisons retain all tests & use **both** frames, unit and uncentered labels too. -/
  pair (f : Test 2) (b v) : Tendsto (fun k=>S.spot (other ((q k).G five |>.c b)) front ((q k).G five |>.c v) ((q k).u.roll f)) ℱ (𝓝 (silky b v f))
  weak : Tendsto (fun k=>(q k).u.r) ℱ (𝓝 0)
variable (Y : Views S ℱ q)

def lunar (S : City) (Q:Carat) (b : UV five): UV five→ₗ[ℂ] Bond 2:= ((LinearMap.llcomp ℂ (Test 2) (Test 2) ℂ).flip Q.u.roll) ∘ₗ S.spot (other ((Q.G five).c b)) front ∘ₗ (Q.G five).c.toLinearMap
lemma lucid (Q S b v f): lunar S Q b v f = S.spot (other ((Q.G five).c b)) front ((Q.G five).c v) (Q.u.roll f):=rfl

def levelP (P : Axis→ Across) (Q:Carat) (i : Axis): Across:= (Q.κ • (Q.G five).c.symm.toLinearMap) ∘ₗ ((P i:Across) ∘ₗ (Q.G four).c.toLinearMap)
lemma vert (Q:Carat) (i v): (Q.G five).c (levelP P Q i v)=Q.κ • P i ((Q.G four).c v) := by change (Q.G five).c (Q.κ • (Q.G five).c.symm _) = _; rw [map_smul, LinearEquiv.apply_symm_apply]; rfl
include L in
lemma surveyed (Q v i b): lunar S Q b (levelP P Q i v)=paid front i (lunar S Q b (l4 v)):= by
  apply LinearMap.ext; intro f
  let u:=Q.u; let g:=(Q.G five).c b
  change S.spot (other g) front ((Q.G five).c _) (u.roll f)=_; rw [vert,map_smul,L.money,LinearMap.smul_apply]
  rw [pays front i (lunar S Q b (l4 v)) f]; change _ = -(S.spot (other g) front ((Q.G five).c _) (u.roll _)); rw [Q.include_]
  have H:= u.roll_fee (S.spot (other g) front (l4 ((Q.G four).c v))) f front i; rw [pays] at H; rw [Complex.real_smul] at H
  exact H.symm

def alpha (S : City) (Q:Carat): UV five→ₗ[ℂ] Probe→ℂ := LinearMap.pi fun i=> survey i.1 ∘ₗ lunar S Q i.2
def etaF : UV five→ₗ[ℂ] Probe→ℂ := LinearMap.pi fun i=> survey i.1 ∘ₗ silky i.2
lemma etaF₀ : Injective etaF:= (detect _).mpr (fun x h=>dollarB (fun v f=> h (f,v)))
include Y in
lemma send : Scores ℂ ℱ etaF (fun k=> alpha S (q k)) :=fun i v=> Y.pair i.1.p i.2 v -- include Y
include Y L in
lemma dept (i): ∀ v,Dips ℂ ℱ (fun k=>levelP P (q k) i v) (Calibration.deriv i v):= by
  intro v
  refine (insight etaF₀ (send Y)).2 _ _ (fun x=> ?_); let f:=x.1.p; let b:=x.2
  change Tendsto (fun k=> lunar S (q k) b _ f) ℱ (𝓝 (silky b _ f))
  simp_rw [surveyed L, ← clear_point v b i] -- clear_point arguments
  simp_rw [pays]; exact (Y.pair _ b _).neg

-- Two costs on rank (93)
variable (S) in
def blade (Q : Carat) : (OneW × BothV) →ₗ[ℂ] (Probe × (Axis×Axis))→ℂ:= LinearMap.pi fun k =>
  let v:=k.2; let f:=Q.u.rolled k.1.1; let b:= (Q.G five).c k.1.2
  Q.κ • (survey f ∘ₗ LinearMap.proj v ∘ₗ check S (other b) front) ∘ₗ (Q.w.prodCongr Q.v).toLinearMap
lemma est (S:City) (Q:Carat) (b: OneW × BothV) (f:Probe) (a i): blade S Q b (f,(a,i))=
    ((∑ j:Axis, paid front j (lunar S Q f.2 (b.2.val (a,ordered j i))))-paid front a (lunar S Q f.2 (b.1.val i))) f.1.p:=by
  let s:=f.1.p; let u:=(Q.G five).c f.2; let m:=Q.u.roll s
  change Q.κ • (check S (other u) front (Q.w b.1,Q.v b.2) (a,i) m)=_
  rw [audit, LinearMap.sub_apply,LinearMap.sub_apply,smul_sub,LinearMap.sum_apply,LinearMap.sum_apply,Finset.smul_sum]
  have he (l : UV five) k : (Q.κ) • (paid front k (S.spot (other u) front ((Q.G five).c l)) m) = paid front k (lunar S Q f.2 l) s := LinearMap.congr_fun (Q.u.roll_price (S.spot (other u) front ((Q.G five).c l)) _ _) s
  simp_rw [v_pay,w_pay]; rw [he]; congr 1; exact Finset.sum_congr rfl (fun i _=> he _ _)

def mine : (OneW ×BothV)→ₗ[ℂ] (Probe × (Axis×Axis))→ℂ:= LinearMap.pi fun k=> survey k.1.1 ∘ₗ script k.1.2 ∘ₗ LinearMap.proj k.2 ∘ₗ combMap
lemma cue (v : Probe) (i a) (x : OneW × BothV): mine x (v,(i,a))=((∑ j:Axis, paid front j (silky v.2 (x.2.val (i, ordered j a))))-paid front i (silky v.2 (x.1.val a))) v.1.p:=by
  change script v.2 (combMap _ _) _=_; rw [combo,map_sub,map_sum]; simp_rw [← clear_l]; rfl
private instance : Module.Finite ℂ ↥BothV:=finiteInvariant ..
private instance : Module.Finite ℂ ↥OneW:=finiteInvariant ..
private instance : Module.Finite ℂ ↥SymT:=finiteInvariant ..
lemma moon : LinearMap.ker mine=LinearMap.ker combMap:=by
  ext1 x
  simp only [LinearMap.mem_ker]; refine ⟨?_,?_⟩
  · intro h; ext1 ⟨a,b⟩; apply (point_ker x a b).mp; apply nullB; intro v f; exact congr_fun h ((f,v),(a,b))
  intro h; ext1 ⟨v,a,b⟩; change script _ _ _=0; change script v.2 (combMap x (a,b)) _=0; rw [h]; exact congr_arg (fun (u:Bond 2)=>u v.1.p) (map_zero _)
lemma own : finrank ℂ (LinearMap.range mine)=59:= by
  rw [← r93]; apply Nat.add_right_cancel
  exact ((by rw [← moon]; exact LinearMap.finrank_range_add_finrank_ker _) : finrank ℂ (LinearMap.range mine)+finrank ℂ (LinearMap.ker combMap)=finrank ℂ (OneW × BothV)).trans (LinearMap.finrank_range_add_finrank_ker combMap).symm
include Y in
lemma watch : Scores ℂ ℱ mine (fun k=> blade S (q k)):= by
  intro p x; obtain ⟨v,a,b⟩:=p; simp_rw [est,cue,LinearMap.sub_apply,LinearMap.sum_apply,pays]
  exact (tendsto_finsetSum _ fun j _=> (Y.pair _ v.2 _).neg).sub (Y.pair _ v.2 _).neg
-- postcomp analytic rank lower transfer
lemma news (Q:Carat) : finrank ℂ (LinearMap.range (blade S Q)) ≤ finrank ℂ (LinearMap.range (readTest S)):= by -- ℱ remove
  obtain ⟨V,H⟩:=venture (blade S Q)
  refine LinearMap.finrank_le_finrank_of_injective (f:=(readTest S).rangeRestrict ∘ₗ (Q.w.prodCongr Q.v).toLinearMap ∘ₗ V) (fun a b h=> ?_)
  have h: readTest S (Q.w.prodCongr Q.v (V a))=readTest S (Q.w.prodCongr Q.v (V b)) := congr_arg Subtype.val h
  apply Subtype.ext; change (LinearMap.range _).subtype a=(LinearMap.range _).subtype b; rw [← H]; ext1 ⟨v,j⟩
  exact congr_arg (fun z:ℂ=>Q.κ • z) (congr_fun (congr_fun h (Q.u.rolled v.1,(Q.G five).c v.2)) j)

-- movement P on maps and D

def left₃ (Q:Carat) : SymT→ₗ[ℂ] OneW:= Q.κ • Q.w.symm.toLinearMap ∘ₗ (Bend.sum _ L.toBend ∘ₗ Q.t.toLinearMap)
lemma sv (t : SymT) (Q) (j): (left₃ L Q t).val j= ∑ i:Axis,levelP P Q i (pens t i j):=by
  apply (Q.G five).c.injective; rw [map_sum]; simp_rw [vert]; rw [← Finset.smul_sum]; change (Q.G five).c (Q.κ • ((Q.w.symm (Bend.sum P L.toBend (Q.t t))).val j))=_
  rw [map_smul, ← Q.w_pay,Q.w.apply_symm_apply,Bend.payW]; congr 1; exact Finset.sum_congr rfl fun i _=>by rw [t_pay]
include Y in
lemma downstairs (x: SymT): Dips ℂ ℱ (fun k=>left₃ L (q k) x) (divergence x) := by
  let P1: OneW→ₗ[ℂ] (Axis × (UV five→ₗ[ℂ] ℂ))→ℂ:= LinearMap.pi fun i=>i.2 ∘ₗ LinearMap.proj i.1 ∘ₗ OneW.subtype
  have he : Injective P1 := by
    let G:=Module.finBasis ℂ (UV five); intro a b h; apply Subtype.ext; ext1 i; apply G.equivFun.injective; ext1 j; exact congr_fun h (i,G.coord j)
  refine truth P1 he (fun i=>?_)
  change Tendsto (fun k=>i.2 ((left₃ L (q k) x).val i.1)) _ (𝓝 (i.2 ((divergence x).val i.1)))
  simp_rw [sv,map_sum,component_div,map_sum]
  exact tendsto_finsetSum _ (fun j _=> dept L Y j (pens x j i.1) i.2) -- arg
lemma acquiredQ (Q) : finrank ℂ (LinearMap.range (left₃ L Q)) ≤ finrank ℂ (LinearMap.range (Bend.sum P L.toBend)) := by
  obtain ⟨V,H⟩:=venture (left₃ L Q)
  let T:=Bend.sum P L.toBend
  refine LinearMap.finrank_le_finrank_of_injective (f:=T.rangeRestrict ∘ₗ Q.t.toLinearMap ∘ₗ V) (fun a b h=> ?_)
  apply Subtype.ext; have he:T (Q.t (V a))=T (Q.t (V b)):=congr_arg Subtype.val h
  exact ((LinearMap.congr_fun H a).symm.trans ((congr_arg (fun x:OneW=> Q.κ • Q.w.symm x) he).trans (LinearMap.congr_fun H b)))
include Y in
lemma acquired [ℱ.NeBot] : 4 ≤ Module.finrank ℂ (LinearMap.range (Bend.sum _ L.toBend)):= by
  obtain ⟨k,h⟩:=(sampled (downstairs L Y)).exists
  rw [div_dimension] at h; exact h.trans (acquiredQ L _)
end YM.GaugeFieldConstruction.Ember
