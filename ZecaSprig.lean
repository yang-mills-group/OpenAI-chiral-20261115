import ZecaMantle
import ZecaMist
set_option autoImplicit false
set_option maxHeartbeats 440000
noncomputable section

namespace YM.ZecaSky
open Function Metric Filter Asymptotics Set
open scoped ComplexOrder InnerProductSpace BigOperators Topology

open Lattice Regis.Head.Brecht Regis.Circuit Stationary

def rotor (b:Axis) (t:ℝ) (z:ℂ)(i:Axis):ℂ:=
 if i=b then z else if i=3 then ↑(2*t) else 0
def sqa (t:ℝ)(z:ℂ):ℂ:=z^2+(2*t:ℂ)^2
def rotary(b:Axis) (t z:ℝ):Gaia:=
 WithLp.toLp 2 fun i:Axis=> if i=b then z else if i=3 then 2*t else 0
lemma rotary_nz(b:Axis)(v:b≠3){t z:ℝ}(p:0<t):rotary b t z ≠0:=by
 intro e; have r:rotary b t z 3=(0:Gaia) 3:=congrArg (fun y:Gaia=>y 3) e
 change (if 3=b then z else if 3=3 then 2*t else 0)=(0:ℝ) at r
 rw [if_neg v.symm,if_pos rfl] at r; exact (mul_pos (by norm_num) p).ne' r
lemma rotary_fee(b:Axis)(v:b≠3){t z:ℝ}:
    (↑(‖rotary b t z‖^2):ℂ)=sqa t z:=by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [rotary,WithLp.ofLp_toLp, apply_ite (· ^ (2:ℕ)),zero_pow
        (by decide:(2:ℕ)≠0)]

    have h(i:Axis):
      (if i=b then z^2 else if i=3 then (2*t)^2 else 0)=(if i=b then z^2 else 0)+(if i=3 then (2*t)^2 else 0):=by
        by_cases a:i=b <;> [skip; simp [a]]
        simp [a,v]
    simp_rw [h]; simp [Finset.sum_add_distrib,sqa]
variable (colA:PlaqAxes→ℝ)(G:Gauge)(b:Axis) (t β:ℝ)
open Complex (I)
def faun (z:ℂ) :=
 Complex.exp (I*(β:ℂ)*z) *
 satire colA G (rotor b t z) (sqa t z)

/-- phases at displacement d positive, translation by -d; character factor exp(-βd i). -/
lemma faun_song (v:b≠3)(p:0<t)(z:ℝ):
 Complex.exp (I*(β:ℂ)*(z:ℂ)) * spectrumℓ colA G (rotary b t z) =
    faun colA G b t β z:=by
 have y:(fun i:Axis=>(↑(rotary b t z i):ℂ))=rotor b t z:=by
    funext i
    unfold rotary rotor; rw [WithLp.ofLp_toLp]; split_ifs <;> simp
 unfold faun; rw [satire_in colA _ _ (rotary_nz b v p),y,rotary_fee b v]

def weatherBand:Set ℂ:= {z | |z.im| < 1}
lemma sqa_true (p:1≤t) (z:ℂ) (h:z∈weatherBand):
 sqa t z≠0:=by
 intro f
 change |z.im|<1 at h
 have e:=abs_lt.mp h
 have y:=congrArg Complex.re f
 simp [sqa,sq,Complex.mul_re] at y
 nlinarith [sq_nonneg (z.re),mul_pos (by linarith : 0<z.im+1) (by linarith : 0< 1-z.im)]

lemma fauna_d (p:1≤t):
 DifferentiableOn ℂ (faun colA G b t β) weatherBand:=by
 refine DifferentiableOn.mul (by fun_prop) ?_
 exact satire_d _ _ _ _ ⟨fun i=> by
    unfold rotor; split_ifs <;> fun_prop, by unfold sqa; fun_prop, sqa_true _ p⟩

lemma bearing (p:1≤t)(R:ℝ):
 ∃C:ℝ, ∀z:ℂ,|z.im|≤1/2 → ‖z‖≤R → ‖faun colA G b t β z‖≤C:=by
 let X: Set ℂ:=closedBall 0 R ∩ {z | |z.im|≤1/2}
 have k:IsCompact X:= (isCompact_closedBall 0 R).inter_right
            (isClosed_le (by fun_prop) (by fun_prop))
 have sub:X ⊆ weatherBand:= fun z h =>
    lt_of_le_of_lt (show |z.im|≤1/2 from h.2) (by norm_num)
 obtain ⟨C,t0⟩:= k.exists_bound_of_continuousOn
    ((fauna_d colA G b t β p).mono sub).continuousOn
 exact ⟨C,fun z a h=>t0 z ⟨mem_closedBall_zero_iff.mpr h,a⟩⟩
#print axioms bearing
