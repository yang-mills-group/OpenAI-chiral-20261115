
import Velour.Marocain.Parasols
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


lemma filepast_thread (K:𝓑)(X Y:Fin n→𝓑)(p:∀i,K*X i = Y i * K):
  K * filepast X=filepast Y*K :=by
 induction n with
 | zero=> simp [filepast]
 | succ n ih=>
   rw [filepast_cons X,filepast_cons Y,←mul_assoc,p,mul_assoc,
       ih (Fin.tail X) (Fin.tail Y) (fun j=>p j.succ), mul_assoc]

variable {S} {t u:Fin n→S.Detector} {w v:S.Invitation n}

lemma Invites.thread (h:S.Invites t w)(g:S.Invites u v)
   (L:H.Op)(m:S.Sealed L)(joint:Joint n →L[ℂ] Joint n)(single:Fin n→ Test4→Test4)
   (js:∀f,joint (Joint.materialize n f)=Joint.materialize n fun i=> single i (f i))
   (through:∀i f,S.label L m * t i f =u i (single i f) *S.label L m)
   (F:Joint n): S.label L m * w F=v (joint F)*S.label L m:=by
 ext1 x
 apply Subtype.ext
 suffices e : L.comp (h.here x)=(g.here (S.label L m x)).comp joint by
    have c:=DFunLike.congr_fun e F
    rw [ContinuousLinearMap.comp_apply,ContinuousLinearMap.comp_apply,h.here_at,g.here_at] at c
    exact c
 refine ext_spring _ _ fun f=>?_
 rw [ContinuousLinearMap.comp_apply,ContinuousLinearMap.comp_apply,h.here_at,g.here_at,js,h.extends_to,g.extends_to]


 exact congrArg (fun z:𝓑 => (z x).val)
    (S.filepast_thread _ (fun i=>t i (f i)) (fun i=>u i (single i (f i))) (fun i=>through ..))

lemma Invites.sways (h:S.Invites t w)
   (through:∀(b:E4) i f,S.liftL b * t i f =t i (ahead b f) *S.liftL b)
   (b:E4)(F:Joint n):
 S.liftL b * w F=w (ahead (points fun _=>b) F)*S.liftL b:=by
 refine h.thread h (U b) _ _ (fun _=>ahead b) ?_ (through b) F
 intro f; ext1; simp

lemma Invites.keeps (h:S.Invites t w)
  (N:Submodule ℂ H.space)(closed:IsClosed (N:Set H.space))
  (a':∀i, Keeps N (t i)):
 ∀F,∀x:D,x.val∈N→(w F x).val∈N:=by
 intro F x e
 revert F
 apply everywhere_joint
 · simp
 · intro F G p q; rw [map_add];exact N.add_mem p q
 · intro c F p; rw [map_smul];exact N.smul_mem c p
 · intro f; rw [h.extends_to]
   have z: filepast (fun i=>t i (f i)) ∈ S.grove t univ:=by
     refine list_prod_mem ?_
     intro W p
     obtain ⟨i,rfl⟩:=List.mem_ofFn.mp p
     exact grove_seed i (show f i∈Set.univ from Set.mem_univ _)
   exact grove_keep a' z x e
 · simp_rw [←h.here_at]
   exact closed.preimage (h.here x).continuous

#check list_prod_mem
#print axioms Invites.thread
#print axioms Invites.keeps
