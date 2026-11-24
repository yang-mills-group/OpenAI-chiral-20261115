import Organdy.Nougat
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Filter Topology Metric
namespace YM.CF.Organdy
open _root_.Zephyr.Chern
variable {V:Type*}[NormedAddCommGroup V][NormedSpace ℝ V]
abbrev maline (F:V→ℂ)(x y:V):ℝ→ℂ:=fun t=> F (x+t•y)
abbrev bean1 (F:V→ℂ)(x y:V) := bud (maline F x y) 1
abbrev bean2 (F:V→ℂ)(x y:V) := bud (maline F x y) 2

structure Almond (r c:ℝ)(F:V→ℂ):Prop where
 pos: 0<r
 paid: 0≤c
 w: ContinuousOn F (ball 0 (r+r))
 current (x y:V):
    ‖x‖< r → y ≠ 0 →
   ∃ H:ℂ→ℂ,
    DifferentiableOn ℂ H (ball 0 (3*(r/‖y‖)))∧
    (∀ z:ℂ,‖z‖<3*(r/‖y‖)→‖H z‖≤c) ∧
    ∀ t:ℝ,|t| * ‖y‖ < r → H t=maline F x y t
section
variable {H:ℂ→ℂ}{R C:ℝ}
private lemma grate {g h:ℂ→ℂ}(u: 0≤R) {w:ℂ}(p: ‖w‖≤R)
 (f:∀ z:ℂ, ‖z‖≤R→ HasDerivAt g (h z) z) (v:∀ z, ‖z‖≤R→ ‖h z‖≤C):
 ‖g w - g 0‖≤C*R:=by

 have c:0≤C:=(norm_nonneg _).trans (v w p)
 refine le_trans (Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x hx=> (f x (mem_closedBall_zero_iff.mp hx)).hasDerivWithinAt)
    (fun x hx=>v x (mem_closedBall_zero_iff.mp hx))
    (convex_closedBall _ _)
    (Metric.mem_closedBall_self u) (mem_closedBall_zero_iff.mpr p)) ?_
 rw [sub_zero]
 exact mul_le_mul_of_nonneg_left p c

private lemma spice (pr:0<R)
    (f:DifferentiableOn ℂ H (ball 0 (3*R))) (v:∀ z:ℂ,‖z‖<3*R→‖H z‖≤C):
 ‖deriv H 0‖ ≤ C/R ∧ ‖deriv (deriv H) 0 / 2‖ ≤ C/R^2 ∧
 ∀ z:ℂ, ‖z‖ ≤ R →
 ‖H z-(H 0+z*deriv H 0+z^2*(deriv (deriv H) 0/2))‖ ≤
    6*C/R^3*‖z‖^3:=by
 have a(i:ℂ)(g:‖i‖≤R)(n:ℕ):‖iteratedDeriv n H i‖ ≤ n.factorial*C/R^n:=by
    have s:(closedBall i R)⊆ball (0:ℂ) (3*R):=by
       intro x r;rw [mem_ball]
       apply (dist_triangle x i _).trans_lt
       rw [dist_zero_right]; linarith [mem_closedBall.mp r]
    exact Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n pr 
      ⟨f.mono (ball_subset_closedBall.trans s),
      f.continuousOn.mono (closure_ball_subset_closedBall.trans s)⟩ 

      (fun x u=>v x (mem_ball_zero_iff.mp (s (sphere_subset_closedBall u))))
 have p:‖(0:ℂ)‖≤R:=by rw [norm_zero]; exact pr.le
 refine ⟨by simpa using a 0 p 1,?_,?_⟩
 · rw [norm_div,Complex.norm_ofNat,div_le_iff₀ (by norm_num)]
   have t:=a 0 p 2
   rw [show Nat.factorial 2=2 from rfl, Nat.cast_ofNat, show iteratedDeriv 2 H=deriv (deriv H) by rw [show (2:ℕ)=1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_one]] at t
   exact t.trans_eq (by ring)
 intro z hz
 let k := 6*C/R^3
 have ai(i:ℂ)(g:‖i‖ ≤ ‖z‖) : AnalyticAt ℂ H i:= f.analyticAt (isOpen_ball.mem_nhds
      (mem_ball_zero_iff.mpr (by linarith)))

 have b₁ (i:ℂ)(g:‖i‖ ≤ ‖z‖):‖deriv (deriv H) i - deriv (deriv H) 0‖ ≤ k*‖z‖:=by
    refine grate (norm_nonneg z) g
        (fun w e=>(ai w e).deriv.deriv.differentiableAt.hasDerivAt) ?_
    intro w l
    have t:=a w (l.trans hz) 3
    rw [show Nat.factorial 3=6 from rfl, Nat.cast_ofNat, show iteratedDeriv 3 H=
       deriv (deriv (deriv H)) by rw [show (3:ℕ)=(1+1)+1 from rfl,iteratedDeriv_succ,iteratedDeriv_succ,iteratedDeriv_one]] at t
    exact t

 let y := deriv (deriv H) 0
 have b₂(i:ℂ)(g:‖i‖ ≤ ‖z‖): ‖deriv H i-deriv H 0-i*y‖ ≤ k*‖z‖*‖z‖:=by
    have e:∀ w, ‖w‖≤ ‖z‖→HasDerivAt (fun j=>deriv H j-j*y) (deriv (deriv H) w - y) w:=by
       intro w t; nth_rw 2 [←one_mul y]; -- changes function y too
       exact (ai w t).deriv.differentiableAt.hasDerivAt.sub ((hasDerivAt_id' w).mul_const y)
    have h:=grate (norm_nonneg z) g e b₁
    rw [show deriv H i-deriv H 0-i*y=deriv H i-i*y-(deriv H 0-0*y) by ring]
    exact h
 have e:∀ w, ‖w‖≤ ‖z‖→HasDerivAt (fun j=> H j-(j*deriv H 0)-(j^2*(y/2)))
    (deriv H w-deriv H 0-w*y) w:=by
    intro w t
    have p:= ((ai w t).differentiableAt.hasDerivAt.sub ((hasDerivAt_id' w).mul_const (deriv H 0))).sub ((hasDerivAt_pow 2 w).mul_const (y/2))
    convert p using 1
    all_goals first |rfl| (norm_num; ring)
 have h:=grate (norm_nonneg z) le_rfl e b₂
 rw [show H z-(H 0+z*deriv H 0+z^2*(y/2))=H z-z*deriv H 0 - z^2*(y/2) - (H 0-0*deriv H 0-0^2*(y/2)) by unfold y;ring]
 exact h.trans_eq (by unfold k;ring)
end

abbrev sweets(r:ℝ):=1/r+1/r^2+6/r^3
variable {F:V→ℂ}{r c:ℝ}(f:Almond r c F)
include f in
lemma Almond.mixer (x y:V)(u:‖x‖<r):
    Bud (maline F x y) ∧
    ‖bean1 F x y‖ ≤ (sweets r * c)*‖y‖∧
    ‖bean2 F x y‖≤(sweets r * c)*‖y‖^2∧
    ∀ t,|t| * ‖y‖ < r →
    ‖skewer F (bean1 F) (bean2 F) x y t‖ ≤ (sweets r * c) * (|t| * ‖y‖)^3:=by
 by_cases h:y=0
 · subst y
   have e:Bloom (maline F x 0) ![F x,0,0]:=by 
      rw [show maline F x 0=fun _=>F x from by funext; simp [maline]]; exact Bloom.constant _
   have w:bean1 F x 0=0:=by rw [bean1,e.bud_eq];rfl
   have w':bean2 F x 0=0:=by rw [bean2,e.bud_eq];rfl
   refine ⟨e.1,by simp [w],by simp [w'],?_⟩
   simp [skewer,w,w']
 obtain ⟨H,a,b,v⟩:= f.current x y u h
 let R:=r/‖y‖
 have p:=f.pos
 have w :0<R:=div_pos p (norm_pos_iff.mpr h)
 have l: AnalyticAt ℂ H 0:=a.analyticAt (ball_mem_nhds _ (mul_pos (by norm_num) w))

 have m:Bloom (maline F x y) ![H 0,deriv H 0,deriv (deriv H) 0 / 2]:=by
    apply (Bloom.cplx l).congr
    exact ((continuous_id'.abs.mul continuous_const).continuousAt (x:=0) |>.tendsto.eventually
       (gt_mem_nhds (show |(0:ℝ)| * ‖y‖ < r by simpa))).mono (fun _ q=> (v _ q).symm)
 obtain ⟨t,o,g⟩:= spice w a b

 have e : bean1 F x y=deriv H 0:=by rw [bean1,m.bud_eq]; rfl
 have q : bean2 F x y=deriv (deriv H) 0 / 2:=by rw [bean2,m.bud_eq]; rfl
 have c0:=f.paid
 have r1:0≤1/r:=by positivity
 have r2:0≤1/r^2:=by positivity
 have r3:0≤6/r^3:=by positivity
 refine ⟨m.1, ?_, ?_, ?_⟩
 · rw [e]; refine t.trans ?_
   unfold R; rw [div_div_eq_mul_div]; rw [show c*‖y‖/r=1/r*c*‖y‖ by ring]
   gcongr
   unfold sweets; linarith
 · rw [q]; refine o.trans ?_
   unfold R; rw [div_pow,div_div_eq_mul_div,show c*‖y‖^2/r^2=1/r^2*c*‖y‖^2 by ring]
   gcongr
   unfold sweets; linarith

 intro z r'
 have n:‖(z:ℂ)‖≤R:=by rw [Complex.norm_real,Real.norm_eq_abs]; exact ((lt_div_iff₀ (norm_pos_iff.mpr h)).mpr r').le 
 have e0:H 0=F x:=by have a:=v 0 (by simpa); simpa [maline] using a
 rw [skewer,e,q,←e0,show F (x+z•y)=H z from (v _ r').symm]
 refine (g z n).trans ?_
 unfold R
 rw [Complex.norm_real,Real.norm_eq_abs,div_pow,div_div_eq_mul_div, show 6*c*‖y‖^3/r^3*|z|^3=6/r^3*c*(|z| * ‖y‖)^3 by ring]
 gcongr; unfold sweets;linarith

lemma sweets_nonneg (s:0≤r) : 0≤sweets r:=by unfold sweets; positivity
include f in
lemma Almond.honey : Sugar r (sweets r*c) F (bean1 F) (bean2 F):=
 ⟨f.pos,mul_nonneg (sweets_nonneg f.pos.le) f.paid,
   f.w,
   fun y=>(f.mixer 0 y (by simpa using f.pos)).2.1,
   fun y=>(f.mixer 0 y (by simpa using f.pos)).2.2.1,
   fun x y t e=>(f.mixer x y e).2.2.2 t⟩ -- f implicit needs include 
