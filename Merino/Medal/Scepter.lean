import Merino.Medal.Gem
import Merino.Lace.Check
set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Merino.Medal
open Filter Topology Lattice Lat Tulip Branch Cube Tenant Vale RG
open scoped Matrix Matrix.Norms.L2Operator Classical InnerProductSpace
attribute [local instance] opCStarAlgebra
open Py.Rate Py.Rate.LocalLimit Preparation
open Skye Scree Buffered Afterglow MeasureTheory
open Yoke Papal Garter Gleam
variable {P:Preparation}{ℓ:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus ℓ))


open Finset Cuff Hem Fock StepIn Lamour.Bridge.Celeste.Clock.Fabric Py.Rate.Pannier
open Lamour.Bridge.Celeste.Clock
open Journey
variable {n:Side}
open CF.Pannier.Chancel
open Reed
open Diadem Lace
variable {m t l:ℕ}
lemma night (z:Cover){x:Seat n}
 (h:x∈baseball m (wrap (More n) z)) (i:Axis):
  ∃ a:ℤ, z i-m ≤ a∧ a≤ z i+m ∧ (a:Per (More n)) =x i:=by
 let y:=x-wrap (More n) z
 have d:pdist y≤ m:=by
    change separation x (wrap (More n) z)≤ m; rw [separation_comm]
    simpa only [baseball,halo_spec,mem_singleton,exists_eq_left] using h
 have p:(lift y i).natAbs ≤ m:= (Finset.le_sup (f:=fun a=> (lift y a).natAbs) (mem_univ i)).trans d
 have u:wrap (More n) (z+lift y)=x:=by rw [map_add,wrap_lift]; exact add_sub_cancel ..
 refine ⟨(z+lift y) i,?_,?_,?_⟩
 · rw [Pi.add_apply];omega
 · rw [Pi.add_apply];omega
 exact congrArg (fun v=>v i) u
lemma noon_le (t:ℕ)(i:Axis):0≤noon t i ∧ noon t i ≤t:=by
 by_cases p:pole=i
 · subst i; simp [Lace.noon,step]
 simp [Lace.noon,step,Ne.symm p]
#check band_spec


lemma noon_cows(B:ℕ) (p:2*(t+m)≤ B)
 (i:Axis): cows i (Lattice.halo 0 (duet m (showtime (More n) t))) B:=by
 refine ⟨-↑(t+m),fun x v=>?_⟩
 have h₀:=noon_le t i
 obtain ⟨y,b,j⟩:=halo_spec.mp v
 have h:x=y:=by
    have e:lift (y-x)=0:=by
       funext a; have p:(lift (y-x) a).natAbs≤ 0:= (le_sup (f:=fun i=>(lift (y-x) i).natAbs) (mem_univ a)).trans j
       rw [Pi.zero_apply]; omega
    exact (sub_eq_zero.mp (show _=0 by rw [← wrap_lift (y-x),e,map_zero])).symm
 rw [h]
 rcases Finset.mem_union.mp b with c|c
 · obtain ⟨a,e,h,u⟩:=night (m:=m) (Lace.noon t) c i
   exact ⟨a,by omega,by omega,u⟩
 change y∈baseball m (-wrap (More n) _) at c
 rw [←map_neg] at c
 obtain ⟨a,e,h,u⟩:=night (m:=m) (-(Lace.noon t)) c i
 rw [Pi.neg_apply] at e h
 exact ⟨a,by omega,by omega,u⟩


lemma matinee_up (p:m+l≤ t)(q:t+m+l≤n.val):
 baseball m (matinee (More n) t).there ⊆ Buffered.band n pole 0 l:=by
 intro x v
 obtain ⟨a,e,h,u⟩:=night (m:=m) (Lace.noon t) v pole
 rw [band_spec,Int.cast_zero,sub_zero,←u,show (a:Per (More n))=(a.toNat:ℕ) from ?_,
   ZMod.val_natCast_of_lt]
 all_goals simp [Lace.noon,step] at e h
 · omega
 · have v':0<n.val:=n.property; change a.toNat<n.val*2;omega
 rw [← Int.cast_natCast,Int.toNat_of_nonneg (by omega)]


abbrev now (t:ℕ)(f:Pane n→ℂ) :=fun V=>f ((matinee (More n) t).cabin V)
abbrev staged (t:ℕ)(c:ℝ)(f:Pane n→ℂ):Mark n:=
 (c:ℂ) • icon (now t f)

lemma staged_job (f:Pane n→ℂ)(c:ℝ)
 (v:Envelope f)(h:LocalOn (Yardlet (More n) m) f):
 AtSupport false (baseball m (matinee (More n) t).there) (staged t c f):=by
 apply AtSupport.smulM
 refine icon_job _ ⟨v.meas.comp (Wilson.continuous_pull ..).measurable,
        _,fun _=>v.cost.choose_spec _⟩ fun x y w=> h _ _ ((matinee _ t).agrees ?_)
 rw [apply_zero]; exact w

def photo {n:Side}(q:Mark n):=reflMark pole 0 q*q
lemma pose_line (f:Pane n→ℂ)(c:ℝ)(t:ℕ):
 photo (staged t c f)=
  ((c:ℂ)^2)• icon (polka 1 (showtime _ t) (false,true) f):=by
 let j:StepIn (More n):=⟨Signed.mirror pole,wrap (More n) (2 • ((0:ℤ) • step pole))⟩


 have y:j*(matinee _ t)=soiree _ t:=by
   change StepIn.mk (Signed.mirror pole*1)
      (affine (Signed.mirror pole) _ _) =soiree _ t
   simp only [soiree,mul_one,affine,Lace.noon]
   congr
   ext i
   by_cases p:i=pole <;> simp [j,Signed.act,Signed.mirror, step,wrap_here,p]
 funext x
 have u:f ((matinee _ t).cabin (reflFields pole 0 x).1)=f ((soiree _ t).cabin x.1):=by
   rw [←y,j.cabin_mul]; rfl
 rw [photo,Pi.mul_apply]
 unfold staged reflMark
 simp only [Pi.smul_apply,icon,now,theta_smul,theta_one,u,Matrix.smul_mul,one_mul,
    smul_smul]
 simp [polka,dart]
 ring_nf


lemma polka_pose (f:Pane n→ℂ)(β:ℝ)(t:ℕ):
 icon (polka β (showtime _ t) (false,true) f)=photo (staged t β f):=by
 rw [pose_line]
 funext x; simp [Pi.smul_apply,icon,smul_smul,polka,dart]
 ring_nf

end YM.CF.Merino.Medal

