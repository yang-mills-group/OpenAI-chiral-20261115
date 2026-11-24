import YM.CF.Delta.Invoice

/-! Marked overlap invoice before expansion to tiles. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Delta
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology
open Fock SU Lat Cube Phase NormedSpace Branch Tour Tour.Enters Function Finset Tenant MeasureTheory Filter Lattice
attribute [local instance] opCStarAlgebra
abbrev binder (z:IndexK) := Own z.1 × Own z.1
def NearP (z:IndexK) (p : binder z) := ‖Pmat z p.1-Pmat z p.2‖≤1/16 ∧ ‖pairF false z p.1-pairF false z p.2‖≤1/16
abbrev TwinK (z : IndexK) := Subtype (NearP z)
def tub (z : IndexK) (g : Geometry z.1) (v : binder z) : binder z := (toss g v.1,toss g v.2)
lemma conduct (z:IndexK) (v : binder z) (g : Geometry z.1) (h : NearP z v) : NearP z (tub z g v) := by
  let s := g ∘ node (N:=z.1); let U := conjG matter s
  have he (x) : Pmat z (toss g x)=twist U (Pmat z x) := by
    change projector (frame matter (links (Lattice.gauge g x.val.1)) z.2).H= _; rw [links_g]; exact twist_projection matter _ _ z.2 x.property.paid
  have hx x : pairF false z (toss g x)=congrC U (pairF false z x) := C_gauge ..
  change ‖Pmat z (toss g v.1) - Pmat z (toss g v.2)‖≤ _ ∧ ‖pairF false z (toss g v.1)-pairF false z (toss g v.2)‖ ≤ _; rw [he,he,hx,hx]
  refine ⟨?_,?_⟩
  · have hb (A B : Op (Model z.1)) : ‖twist U A-twist U B‖=‖A-B‖ := by rw [← map_sub, twist_norm];
    exact (show ‖twist U _-twist U _‖ ≤ _ from Eq.trans_le (hb _ _) h.1)
  have ht (A B : Op (Model z.1)): ‖congrC U A-congrC U B‖=‖A-B‖ := by rw [show congrC U A-congrC U B=congrC U (A-B) by unfold congrC; rw [mul_sub,sub_mul],congr_norm]
  exact le_trans (ht _ _|>.le) h.2

def bog (z:IndexK) (g : Geometry z.1) (v:TwinK z): TwinK z := ⟨tub z g v.val,conduct z v.val g v.property⟩
def binS (z:IndexK) : Stage (Site (More z.1)) (Model z.1) (TwinK z) (Geometry z.1) :=
  let A := slotK z.1
  ⟨A.F,A.home,bog z,fun S x y=> A.eval S x.val.1 y.val.1 + A.eval S x.val.2 y.val.2,fun S x y=>add_nonneg (A.pos ..) (A.pos ..), fun p x y=>add_le_add (A.includeV p _ _) (A.includeV p _ _)⟩
def gust (z:IndexK): Tag (binS z) := ⟨(sigK z.1).run,(sigK z.1).keeps⟩
def costS : Tour IndexK := { systemK with
  D:=TwinK
  dt z:= inferInstanceAs (TopologicalSpace (TwinK z))
  stageK:= fun z=>binS z }
lemma ampleR : ample costS:= ⟨quota,(show (0:ℝ)≤16 by norm_num).trans quota_bound,fun z=> norm_care (Y:=Unit) (binS z) rfl rfl⟩
abbrev keyP : ChartW costS:= gust
namespace View
variable (F : MapW systemK)
abbrev fc : MapW costS := fun z (x:TwinK z)=>F z x.val.1
abbrev sc : MapW costS := fun z (x:TwinK z)=> F z x.val.2
section clone
variable {Y I D D' G : Type*} [Fintype Y] [DecidableEq Y] [Fintype I] [DecidableEq I] [TopologicalSpace D] [TopologicalSpace D']
lemma revise (A : Stage Y I D G) (B : Stage Y I D' G) (s t : Tag A) (u v : Tag B) (e : B.F=A.F) (p : B.home=A.home) (g : u.run=s.run) (l:v.run=t.run) (f : D'→D) (k : Continuous f) (q : ∀ h d, f (B.drive h d)=A.drive h (f d)) (E : ∀ S x y, A.eval S (f x) (f y)≤B.eval S x y) {C a} {F : Raw D I} (h : RootedK s t a C F) : RootedK u v a C (F ∘ f) := by
  obtain ⟨X,Y,Z,w,V⟩:=h; refine ⟨fun S=>X S ∘ f,Y,fun S=>⟨fun g d=>?_,fun i j=>?_⟩,w,fun x=> V _⟩
  · simp only [Function.comp_apply,q]; rw [show u.run=_ from ‹_›, show v.run=_ from l]; exact (Z S).frame ..
  have he := (Z S).expo i j; exact ⟨he.positive,fun c=>by rw [e,p]; exact he.triggered c,fun x=>he.bounded _,fun x y=>(he.variation ..).trans (mul_le_mul_of_nonneg_left (E S x y) he.positive), he.connected.comp k⟩
end clone
lemma flow (s : ChartW systemK) (t : ChartW costS) (g : ∀ z, (t z).run=(s z).run) (h : Enters systemK weave s F) : Enters costS keyP t (fc F) ∧ Enters costS keyP t (sc F) := by -- tune
  obtain ⟨a,C,h,p,H⟩:=h; refine ⟨⟨a,C,h,p,fun z=>?_⟩,⟨a,C,h,p,fun z=>?_⟩⟩
  · let N:=z.1; exact revise (slotK z.1) (binS z) _ _ (gust z) _ rfl rfl rfl (g z) (fun x:TwinK z=>x.val.1) (continuous_fst.comp continuous_subtype_val) (fun _ _=>rfl) (fun _ _ _=> le_add_of_nonneg_right (vacancy_pos ..)) (H z)
  exact revise (slotK z.1) (binS z) _ _ (gust z) _ rfl rfl rfl (g z) (fun x:TwinK z=>x.val.2) (continuous_snd.comp continuous_subtype_val) (fun _ _=>rfl) (fun _ _ _=> le_add_of_nonneg_left (vacancy_pos ..)) (H z)
end View
open View
abbrev riseW : costS.MapW:= fun z x=> relay (fc Pmat z x) (fc (pairF false) z x) (body (sc Pmat z x) (sc (pairF false) z x))
abbrev hopK : costS.MapW:= fun z x=> pencil (riseW z x-1)
lemma riseR (z) (x:TwinK z) : ‖riseW z x-1‖≤1/2 := dovecote ⟨_,unit_each false z x.val.1⟩ ⟨_,unit_each false z x.val.2⟩ (attends _ x.val.1).projection (attends _ x.val.2).projection (tight false z x.val.1) x.property.1 x.property.2
lemma rising : Enters costS keyP keyP hopK := by
  obtain ⟨A,B⟩:= flow Pmat _ keyP (fun _=>rfl) (site amp launchH attends); obtain ⟨C,D⟩:= flow (pairF false) _ (Tour.partner keyP) (fun _=>rfl) (launchC _)
  apply A.relayLn C (B.bodyV D) (fun z (x:TwinK z)=> tight false z x.val.1) (fun z (x:TwinK z)=>unit_each _ z x.val.1) riseR ampleR
lemma diagonalP (z : IndexK) (x : Own z.1) : NearP z (x,x) := by unfold NearP; simp only [sub_self,norm_zero,and_self]; norm_num
def againK (z:IndexK) (x:TwinK z):TwinK z:= ⟨(x.val.1,x.val.1),diagonalP z x.val.1⟩
lemma cashR (z:IndexK) (x:TwinK z) : (hopK z (againK z x)).trace=0 := by
  rw [show (hopK z _).trace= invoice _ from (tally_log (lt_of_le_of_lt (riseR z (againK z x)) (by norm_num))).symm]
  let A:=x.val.1; have hp := (attends z A).projection; have H := (inv_close_le (⟨_,unit_each false z A⟩:UNI (VR z)) (tight false z A)).1
  have he := same_spark (P:=Pmat z A) (A:=pairF false z A) (n:=VR z) hp H; unfold spark at he; exact (div_eq_zero_iff.mp he).resolve_right (by norm_num)
end YM.CF.Delta
