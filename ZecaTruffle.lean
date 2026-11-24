import ZecaChartreuse
set_option autoImplicit false
set_option maxHeartbeats 440000
noncomputable section

namespace YM.ZecaSky
open Function Metric Filter Asymptotics Set
open scoped ComplexOrder InnerProductSpace BigOperators Topology

open Lattice Regis.Head.Brecht Regis.Circuit Stationary


open CF
open CF.Py.Rate.LocalLimit.Preparation.Yoke CF.QuadClock
namespace Gin

lemma full(c:Axis)(e:c≠3){t:ℝ}(p:0<t):
  spectrumℓ witnessZ SU.group (V c t)=codex c*pri t:=by
 have h:‖V c t‖^2=2*t^2:=by
   have a(i:Axis):(V c t i)^2=(if i=c then t^2 else 0)+(if i=3 then t^2 else 0):=by
     by_cases r:i=c
     · simp [V,r,v,e]
     simp [V,v,r]
   rw [EuclideanSpace.real_norm_sq_eq]
   simp_rw [a]; rw [Finset.sum_add_distrib]; simp; ring
 have q:V c t≠0:=by
    intro w; rw [w,norm_zero,sq] at h
    nlinarith only [h,sq_pos_of_pos p]
 rw [satire_in _ _ _ q,h,Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_ofNat,←price _ p]
 have a:(fun i=>(V c t i:ℂ))=plug (t:ℂ) c:=by
    funext i; simp [plug,V]
 rw [a]
lemma fresh(t:ℝ)(p:0<t):pri t ≠0:=by
 have h1:(Fintype.card SU.group.ColorIndex:ℂ)≠0:=by exact_mod_cast yAlive.ne'
 have h2:(t:ℂ) ≠0:= by exact_mod_cast p.ne'
 have h3:(Maxwell.normal:ℂ)≠0:=by exact_mod_cast Maxwell.normal_pos.ne'
 unfold pri amber; repeat' first|exact h3|apply inv_ne_zero|apply pow_ne_zero|apply mul_ne_zero|apply div_ne_zero|assumption|norm_num

lemma disc (t:ℝ)(p:0<t) :
 spectrumℓ witnessZ SU.group (V 0 t)≠
 spectrumℓ witnessZ SU.group (V 2 t):=by
 rw [full 0 (by decide) p,full 2 (by decide) p,codex_2,codex_0]
 intro i
 have e:=mul_right_cancel₀ (fresh _ p) i
 norm_num at e
#print axioms disc
