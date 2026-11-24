import YM.CF.Phase.Cove

/-! Grid translations and axis flips for the positivity step. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Mir
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Topology
open Function Fock Filter NormedSpace SU Lat Lattice Branch Cube Tenant MeasureTheory Phase
open Finset
attribute [local instance] opCStarAlgebra
variable {m B : Side}

def glazed (p : Axis→Bool) : Signed := ⟨Equiv.refl _,p⟩
@[simp] lemma glaz {R : Type*} [AddGroup R] (p) (x : Four R) (i) : (glazed p).act x i=if p i then -x i else x i := Signed.act_at (glazed p) x i
@[simp] lemma glaze_one : glazed (fun _=>false)=1 := rfl
@[simp] lemma glaze_mul (a c : Axis→Bool) : glazed a*glazed c=glazed fun i=> (a i).xor (c i) := rfl
@[simp] lemma glaze_inv (a : Axis→Bool) : (glazed a)⁻¹=glazed a := rfl

abbrev Craft (m : Side) := (Axis→Bool) × Site (More m)
-- potential issue existing group instance. use def wrapper instead
structure Trip (m : Side) where
  glare : Axis→Bool
  move : Site (More m)
instance (m : Side) : Fintype (Trip m) := Fintype.ofEquiv (Craft m) {toFun x:=⟨x.1,x.2⟩,invFun x:=(x.glare,x.move),left_inv x := rfl,right_inv x:=rfl}
@[ext] lemma Trip.ext {a b : Trip m} (h : a.glare=b.glare) (e:a.move=b.move) : a=b := by cases a; cases b; congr
namespace Trip
instance (m) : One (Trip m) := ⟨⟨fun _=>false,0⟩⟩
instance (m) : Mul (Trip m) := ⟨fun a b=>⟨fun i=> (a.glare i).xor (b.glare i),(glazed a.glare).act b.move+a.move⟩⟩
instance (m) : Inv (Trip m) := ⟨fun a=>⟨a.glare, -(glazed a.glare).act a.move⟩⟩
@[simp] lemma move1 (m) : (1 : Trip m).move=0 := rfl
@[simp] lemma glare1 (m) : (1 : Trip m).glare=(fun _=>false) := rfl
@[simp] lemma movep (a b : Trip m) : (a*b).move= (glazed a.glare).act b.move+a.move := rfl
lemma glarep (a b : Trip m) : glazed ((a*b).glare)=(glazed a.glare)*(glazed b.glare) := rfl
@[simp] lemma glarex (a b : Trip m) i : (a*b).glare i=(a.glare i).xor (b.glare i) := rfl
@[simp] lemma glarei (a : Trip m) : a⁻¹.glare=a.glare := rfl
@[simp] lemma movei (a : Trip m) : a⁻¹.move= -(glazed a.glare).act a.move := rfl
instance (m) : Group (Trip m) where
  one_mul x := ext (by funext; simp) (by simp)
  mul_one x := ext (by funext; simp) (by simp)
  inv_mul_cancel x := ext (by funext; simp) (by rw [movep,glarei,movei]; simp)
  mul_assoc x y z := ext (by funext i; simp [Bool.xor_assoc]) (by rw [movep,movep x,movep x,movep y z,glarep, Signed.act_mul]; simp [add_assoc])
instance (m : Side) : DecidableEq (Trip m) := Classical.decEq _
variable (B) (a : Trip m)
abbrev paneShift := (assembly (More m)).root a.move
abbrev torShift (a : Trip m) := (scaleR m B).root a.paneShift
def adv (x : Index m) := affine (glazed a.glare) a.paneShift x
def run (x : Site (Domain m B)) := affine (glazed a.glare) (torShift B a) x
lemma pane_mul (c : Trip m) : paneShift (a*c)=(glazed a.glare).act c.paneShift+a.paneShift := by unfold paneShift; rw [movep,map_add]; congr 1; exact (assembly (More m)).signed ..
lemma tor_mul (c : Trip m) : torShift B (a*c)= (glazed a.glare).act (torShift B c)+torShift B a := by unfold torShift; rw [pane_mul,map_add]; congr 1; exact (scaleR m B).signed ..
lemma adv_comp (b : Trip m) x : a.adv (b.adv x)=(a*b).adv x := by rw [adv,adv,adv,pane_mul,glarep]; simp only [affine,Signed.act_add, Signed.act_mul, add_assoc]
lemma run_comp (b : Trip m) x : run B a (run B b x) = run B (a*b) x := by rw [run,run,run,tor_mul,glarep]; simp only [affine,Signed.act_add,Signed.act_mul, add_assoc]
@[simp] lemma pane_o (m : Side) : paneShift (1:Trip m)=0 := by unfold paneShift; rw [move1,map_zero]
@[simp] lemma tor_o (m : Side) : torShift B (1:Trip m)=0 := by unfold torShift; rw [pane_o,map_zero]
@[simp] lemma main_o (x) : adv (1:Trip m) x=x := by rw [adv,affine,pane_o,glare1,glaze_one,Signed.act_one,add_zero]
@[simp] lemma run_o x : run B (1:Trip m) x=x := by rw [run,affine,tor_o,glare1,glaze_one,Signed.act_one,add_zero]
@[simp] lemma adv_back x : a⁻¹.adv (a.adv x)=x := by rw [adv_comp,inv_mul_cancel,main_o]
@[simp] lemma adv_last x : a.adv (a⁻¹.adv x)=x := by rw [adv_comp, mul_inv_cancel,main_o]
@[simp] lemma run_back x : run B a⁻¹ (run B a x)=x := by rw [run_comp,inv_mul_cancel,run_o]
@[simp] lemma run_last x : run B a (run B a⁻¹ x)=x := by rw [run_comp, mul_inv_cancel,run_o]
def facesA : Equiv.Perm (Index m) := ⟨adv a,adv a⁻¹,adv_back a,adv_last a⟩
def sites : Equiv.Perm (Site (Domain m B)) := ⟨run B a,run B a⁻¹,run_back B a,run_last B a⟩
def flips (x : Complex) := if Odd ((univ.filter (fun i=>a.glare i=true)).card) then star x else x
lemma flips1 (x : ℂ) : (1:Trip m).flips x=x := by simp [flips]
private lemma sheetp (s : Finset Axis) (p q : Trip m) (x : ℂ) :
    let f := fun k:Trip m => fun x:ℂ=> if Odd ((s.filter (fun i=>k.glare i=true)).card) then star x else x
    f p (f q x)=f (q*p) x := by
  intro f
  induction s using Finset.induction_on generalizing x with
  | empty => simp [f]
  | @insert i s h ih =>
    let g k (x:ℂ) := if Odd ((s.filter (fun i=>(k:Trip m).glare i=true)).card) then star x else x
    have he k x : g k (star x)=star (g k x) := by unfold g; split <;> simp
    have hx k x : f k x=if k.glare i then star (g k x) else g k x := by
      cases l:k.glare i <;> simp only [f, g,l,Bool.false_eq_true,ite_false, filter_insert,ite_true]
      have h' : i∉s.filter (fun i=> k.glare i=true) := fun e=> h (mem_filter.mp e).1
      rw [card_insert_of_notMem h']; by_cases e:Odd ((s.filter (fun i=> k.glare i=true)).card) <;> simp [Nat.odd_add_one, ←Nat.not_odd_iff_even,e]
    have hq : ∀ x, g p (g q x)=g (q*p) x := ih
    rw [hx,hx,hx, glarex]; cases p.glare i <;> cases q.glare i <;> simp only [ite_true,ite_false,Bool.false_eq_true, Bool.false_xor, Bool.true_xor,Bool.not_true,Bool.not_false,he,hq,star_star]
lemma flips_comp (b : Trip m) x : b.flips (a.flips x)=(a*b).flips x := sheetp Finset.univ b a x
lemma flips_norm (x) : ‖a.flips x‖=‖x‖ := by unfold flips; split <;> simp
lemma flips_add (x y) : a.flips (x+y)=a.flips x+a.flips y := by unfold flips; split <;> simp
lemma flips_sub (x y) : a.flips (x-y)=a.flips x-a.flips y := by unfold flips; split <;> simp
lemma flips_inv (x): a⁻¹.flips (a.flips x)=x := by rw [flips_comp,mul_inv_cancel,flips1]
lemma flips_real (x : ℝ) (v) : a.flips (x • v)=x • a.flips v := by unfold flips; split <;> simp
lemma flip_sum {I : Type*} (S : Finset I) (f : I→ℂ) : a.flips (∑ i∈S,f i)=∑ i∈S,a.flips (f i) := by unfold flips; split <;> simp
lemma flip_conj (x : ℂ) : a.flips (star x) = star (a.flips x) := by unfold flips; split <;> simp
lemma flip_inv_eq : a⁻¹.flips=a.flips := by funext x; rw [flips,glarei]; rfl
def through (U : Skin m B) := Lattice.pull (glazed a.glare) (torShift B a) U
def oncue (x : Cue m) := x ∘ a.adv
def onPack (t : Pack m B) := (through B a t.1,oncue a t.2) -- Pack not imported
lemma through_comp (b : Trip m) U : through B b (through B a U)=through B (a*b) U := by rw [through,through,Lattice.pull_pull,through,glarep]; simp only [affine,tor_mul]
lemma cue_comp (b : Trip m) x : b.oncue (a.oncue x)=(a*b).oncue x := by unfold oncue; funext i; simp only [Function.comp_apply,adv_comp]
lemma trip_comp (b : Trip m) t : onPack B b (onPack B a t)=onPack B (a*b) t := Prod.ext (through_comp ..) (cue_comp ..)
@[simp] lemma through_o (U) : through B (1:Trip m) U=U := by rw [through,glare1,glaze_one,tor_o,pull_id]
@[simp] lemma cue_o (x) : oncue (1:Trip m) x=x := by unfold oncue; ext; simp
lemma pack_id (x) : onPack B (1:Trip m) x=x := Prod.ext (through_o ..) (cue_o ..)
lemma addressAdv x : address m B (a.adv x) = run B a (address m B x) := by
  rw [adv,run,affine,affine]; unfold address torShift
  rw [map_add]; congr 1; exact (scaleR m B).signed ..
end Trip
end YM.CF.Mir
