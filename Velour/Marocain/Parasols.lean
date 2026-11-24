
import Velour.Marocain.Garland
set_option autoImplicit false
set_option quotPrecheck false
set_option maxRecDepth 1100
noncomputable section
namespace YM.OS.Semigroup
open Function Set Filter Complex Analysis MeasureTheory
open scoped NNReal ENNReal Topology BigOperators ContDiff InnerProductSpace ComplexOrder
variable {H : Hilbert} {a : Axis} (S:Semigroup H a)

open Boundary Probe

variable {n:ℕ}

local notation "U" => S.unit.translation
local notation "R" => S.gauze
local notation "D" => S.muslin
local notation "B" => S.weight
local notation "𝓧" => Fin n → H.Op
local notation "𝒦" => Fin n → ℕ
local notation "𝓕" => Fin n → Test4
local notation "𝓑" => Module.End ℂ D
local notation "𝓗" => H.space

local notation "G!" => S.heatL
local notation "E!" => S.E
local notation "𝓛" => Fin n → ℝ≥0
local notation "𝓣" => Fin n → S.Detector
local notation "𝓠" => Fin n → ℝ≥0 → H.Op

def invPts: Points n ≃ₗ[ℝ] Points n:=
 { toFun:=fun p=> points fun i=> p i.rev
   invFun:=fun p=> points fun i=> p i.rev
   left_inv:=by intro p; ext;simp
   right_inv:=by intro p; ext;simp
   map_add':=by intros;rfl
   map_smul':=by intros;rfl }

def invertPts : Points n ≃L[ℝ] Points n:={
 invPts with
 continuous_toFun:= (PiLp.continuous_toLp _ _).comp (continuous_pi fun i=> by fun_prop)
 continuous_invFun:= (PiLp.continuous_toLp _ _).comp (continuous_pi fun i=> by fun_prop)
}


def tip : Joint n →L[ℝ] Joint n:= bar.comp ((Probe.along invertPts).restrictScalars ℝ)
lemma tip_at(x:Joint n)(v:Points n): tip x v=star (x (invertPts v)):=rfl

lemma tip_smul(x:Joint n)(c:ℂ): tip (c • x)=star c • tip x:=by ext1;simp [tip_at]

lemma tip_pure (f:𝓕):
 tip (Joint.materialize n f)= Joint.materialize n fun i=>bar (f i.rev):=by
 ext1 x
 rw [tip_at,Joint.material_at, Joint.material_at]
 change starRingEnd ℂ _=_
 rw [map_prod]


 symm
 rw [← Equiv.prod_comp Fin.revPerm]
 change (∏i:Fin n, bar (f i.rev.rev) (x i.rev))=_
 simp_rw [Fin.rev_rev,bar_at];rfl


variable {S}

lemma filepast_last {α:Type} [Monoid α] (v:Fin (n+1)→α):
 filepast v=filepast (fun i:Fin n=>v i.castSucc) * v (Fin.last _):=by
 rw [filepast, List.ofFn_succ',List.prod_concat]

lemma faces_reverse (z y:Fin n→𝓑)(h:∀i,S.Faces (z i) (y i)):
  S.Faces (filepast z) (filepast fun i=>y i.rev):=by
 induction n with
 | zero=> simp [filepast];exact fun _ _=>rfl
 | succ n ih=>
   rw [filepast_cons,filepast_last _,Fin.rev_last]
   simp_rw [Fin.rev_castSucc]
   exact (h 0).mul (ih (Fin.tail z) (Fin.tail y) fun j=>h _)




open Work.C25
variable {t u:Fin n→S.Detector} {w v:S.Invitation n}

lemma everywhere_joint (p:Joint n→Prop)
 (H0:p 0)(Ha:∀x y,p x→p y→p (x+y))(Hs:∀(c:ℂ) x,p x→p (c•x))
 (Hp:∀f,p (Joint.materialize n f))(Hc:IsClosed {x | p x}):
 ∀x,p x:=by
   have e:Dense (span n:Set (Joint n)):=fun x=> 
       show x∈(span n).topologicalClosure from by
          rw [show (span n).topologicalClosure=⊤ from answer n]; exact Submodule.mem_top
   intro x
   have k: (span n:Set (Joint n)) ⊆ {x| p x}:=fun _ q=> Submodule.span_induction (p:=fun x _=>p x)
      (forall_mem_range.mpr Hp) H0 (fun x y _ _=>Ha x y) (fun c x _=>Hs c x) q
   exact closure_minimal k Hc (e x)


lemma Invites.facing (h:S.Invites t w)(g:S.Invites (fun i=>u i.rev) v)
   (z:∀i f,S.Faces (t i f) (u i (bar f))):
 ∀F,S.Faces (w F) (v (tip F)):=by
 apply everywhere_joint
 · simp;exact fun _ _=>by simp
 · intro F X e p; rw [map_add,map_add,map_add]; exact e.add p
 · intro c F e x y
   simp only [map_smul,tip_smul, LinearMap.smul_apply, Submodule.coe_smul_of_tower, inner_smul_left,
     inner_smul_right,e x y];rfl


 · intro f
   rw [tip_pure,h.extends_to,g.extends_to]
   exact faces_reverse (fun i=>t i (f i)) (fun i=>u i (bar (f i))) fun i=>z _ _
 · simp only [Faces, setOf_forall]
   refine isClosed_iInter fun x=>isClosed_iInter fun y=>isClosed_eq ?_ ?_
   · have e:(fun F=> inner ℂ (w F x).val y.val)=fun F=>inner ℂ (h.here x F) y.val:=
         funext fun F=> (congrArg (inner ℂ · y.val) (h.here_at x F)).symm 
     rw [e]; exact (h.here x).continuous.inner continuous_const
   · have e:(fun F=> inner ℂ x.val (v (tip F) y).val)=fun F=>inner ℂ x.val (g.here y (tip F)):=
         funext fun F=> (congrArg _ (g.here_at y (tip F))).symm 
     rw [e]; exact continuous_const.inner ((g.here y).continuous.comp tip.continuous)
#check closure_minimal
#print axioms Invites.facing

