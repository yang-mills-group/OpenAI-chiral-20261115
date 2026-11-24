
import Velour.Marocain.Greet
import Velour.Organza.Cocoon
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

abbrev Invitation (n:ℕ):Type:= Joint n →ₗ[ℂ] 𝓑

/-- Precisely the ordered word, even jointly, on all graphs. -/
structure Invites (t:Fin n→S.Detector) (w:S.Invitation n):Prop where
 bought : ∃k, ∀ m, ∃ y:Joint n →L[ℂ] H.Op,∀F,S.Refines (w F) k m (y F)
 extends_to (f:𝓕): w (Joint.materialize n f)= filepast fun i=>t i (f i)

variable {S}
variable {t:Fin n→S.Detector} {w:S.Invitation n}

lemma Invites.firm (h:S.Invites t w)(F:Joint n): S.Firm (w F):=by
 obtain ⟨k,e⟩:= h.bought
 exact ⟨k,fun m=>⟨_, (e m).choose_spec F⟩⟩

def graphR (w:S.Invitation n)(v:D)(m:ℕ): Joint n →ₗ[ℂ] H.space where
 toFun F:= (B m (w F v)).val
 map_add' _ _:= by rw [map_add,LinearMap.add_apply,map_add]; rfl
 map_smul' _ _:= by rw [map_smul,LinearMap.smul_apply,map_smul]; rfl


def Invites.graph (h:S.Invites t w)(v:D)(m:ℕ):Joint n →L[ℂ] H.space where
 toLinearMap:=graphR w v m
 cont:=by
   obtain ⟨k,e⟩:=h.bought
   obtain ⟨y,b⟩:=e m
   change Continuous (fun F=> (B m (w F v)).val)
   simp_rw [fun F=>b F v]
   exact y.continuous.clm_apply continuous_const

def Invites.here (h:S.Invites t w)(v:D):=h.graph v 0
lemma Invites.here_at (h:S.Invites t w)(v:D)(F:Joint n):
 h.here v F=(w F v).val:=by
 change (B _ _).val=_; rw [S.weight0]

lemma Invites.unique (h:S.Invites t w){w':S.Invitation n}(e:S.Invites t w'):w=w':=by
 ext1 F
 ext1 v
 apply Subtype.ext
 suffices h.here v=e.here v by rw [←h.here_at,←e.here_at,this]
 refine ext_spring _ _ fun f=>?_ 
 rw [h.here_at,e.here_at,h.extends_to,e.extends_to]

abbrev toasted (t:Fin n→S.Detector) := ∀i,∃k X, t i=S.hatch X k
lemma inviting (k:𝒦)(X:𝓧){t:Fin n→S.Detector}
 (h:∀i,t i=S.hatch (X i) (k i)): S.Invites t (S.coaches k X):=
  ⟨⟨sheaf k, fun m=>⟨_,fun F=>S.coach_refines k X F m⟩⟩,
     fun f=>by simp_rw [h]; exact S.coach_pure k X f⟩


theorem invitational (h:toasted t):∃w,S.Invites t w:=by
 choose k X n' using h
 exact ⟨_, inviting k X n'⟩

def garland (h:toasted t): S.Invitation n:= (invitational h).choose
lemma garland_on (h:toasted t): S.Invites t (garland h):=(invitational h).choose_spec

variable (S)
lemma hatch_nil (X:H.Op)(f:Test4) : S.hatch X 0 f=S.labelled X f:=by
  ext1 v
  change B 0 (S.labelled X f (B 0 v))=_
  rw [S.weight0,S.weight0]
def banners (X:𝓧):S.Invitation n:= S.coaches (fun _=>0) X

lemma banner_invites (X:𝓧): S.Invites (fun i=>S.labelled (X i)) (S.banners X):=
 inviting _ X fun _=> LinearMap.ext fun f=>(S.hatch_nil _ f).symm

lemma banner_raised (X:𝓧)(F:Joint n)(v:D):
   (S.banners X F v).val= S.procession X F v.val:=by
 let h:= S.banner_invites X
 rw [←h.here_at v F]
 suffices h.here v=(ContinuousLinearMap.apply ℂ H.space v.val).comp (S.procession X) by rw [this];rfl
 refine ext_spring _ _ fun f=>?_
 rw [h.here_at,h.extends_to, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,S.procession_pure]
 -- use helper simp
 


 clear h F
 induction n with
 | zero=>simp [filepast]
 | succ n ih=>
    rw [filepast_cons,filepast_cons (fun i=> S.rasp (X i) (f i))]
    have t:= ih (Fin.tail X) (Fin.tail f)
    change _=S.rasp _ _ ((filepast fun i=> S.rasp (Fin.tail X i) (Fin.tail f i)) v.val)
    rw [←t]
    rfl

lemma banner_surge {p:ℕ→Fin n→H.Op}{q:𝓧}(e:∀j,Velour.Gleams H (fun i=>p i j) (q j))
    {V:ℕ→Joint n}{F:Joint n}(h:Tendsto V atTop (𝓝 F)):
    S.Surges atTop (fun i=> S.banners (p i) (V i)) (S.banners q F):=
  S.coaches_surge e _ h
#print axioms banner_raised
#print axioms invitational

