import YM.CF.Haro.Keeps
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Haro
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Stationary Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Fock Tulip Font Spire Nacre Ember Pec
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker MatrixOrder Classical
attribute [local instance] opCStarAlgebra
open Tap Hake Urn Yaw Levier Proa Rill
variable {c f:Side}(G:Ratio c f)(h: Odd G.count.val)
open Branch Laic
variable {t:ℝ}(p:0<t)(Y: cro G t)(W: Meter TailB G t)
open Skye Precision
open Jet Scree
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{z:E}{n:ℕ}{K u v w A' B' C':ℝ}
variable (X:Hub f){P:RG.BudgetPoint}{u' v':ℝ}(F:InkD f)(hp:PressB P X F u' v')(U:E→Pane f)(V:E→ Pane c)
variable (A B: Support (More f))(r s:Prism.Rock f)(i j:Prism.Rock c)(Z:E→Rill.Arch G t)(T:Rill.Arch G t)
variable (C Q:Toll (Iota G))(a:Suite (badge _) (pinH G t true) (pinH G t false) A C (W (true,true) A))(b:Suite (badge _) (pinH G t true) (pinH G t false) B Q (W (true,false) B))
-- path error paid.H.Var slots
section
-- Polarized factor t first approximant. Allows variable error
lemma interpXY {u a b:ℝ}(Y₁ Y₂ X₁ X₂:E→Op Slot)(h:Allows n Y₁ z v)(f:Allows n X₂ z a)(p:Allows n (X₁-Y₁) z b)(r:Allows n (X₂-Y₂) z u): Allows n (X₁*X₂-Y₁*Y₂) z (wheel_l n*b*a + wheel_l n*v*u):=by
 rw [show X₁*X₂-Y₁*Y₂=(X₁-Y₁)*X₂+Y₁*(X₂-Y₂) from (by rw [sub_mul,mul_sub]; abel)]; exact (leaf_h _ _ p f).add (leaf_h _ _ h r)
abbrev litho(g: Seat c→SU.E)(M:Op Slot):= star (putX g i) * (star (fyL G true W (bring p T) A r i)*M*fyL G false W (bring p T) B s j) * putX g j
-- Fc actual, Fb comparison. D controls each Y error scaled with ε. post cost
include p a b hp
lemma glowπ (g:Seat c→SU.E)(Tq:E→Op Slot)(L:Risk n (fun x=>fyL G true W (bring p (herb G (g ∘ (ratio G).parent) (Z x))) A r i) (fyL G true W (bring p T) A r i) z u v) (J:Risk n (fun x=>fyL G false W (bring p (herb G (g ∘ (ratio G).parent) (Z x))) B s j) (fyL G false W (bring p T) B s j) z u w) (fY:Allows n Tq z C')(eY:Allows n ((fun x=> CharM F r s (gauge (g ∘ (ratio G).parent) (U x))) - Tq) z (C'*u))(hu:u≤1) : ∀ x y, Allows n (fun t=> (lyric G p W F A B r s i j (U t) (Z t)- litho G p W A B r s i j T g (Tq t)) x y) z (7*wheel_l n^2*(pole*v)*C'*w*u):=by -- compute 1: Xb norm2; err₀ leaf L.Y ; (2+1)*wheel ; then 2*:6+1.
 let v₁:= (g ∘ (ratio G).parent); let Fp:= fun t:E=> CharM F r s (gauge v₁ (U t)); let X₁:= star ∘ (fun x=> fyL G true W (bring p (herb G v₁ (Z x))) A r i); let Y₁:= fun x:E=>star (fyL G true W (bring p T) A r i); let X₂:= fun x=> fyL G false W (bring p (herb G v₁ (Z x))) B s j; let Y₂:=fun _:E=>fyL G false W (bring p T) B s j
 have Hp:Allows n Fp z (2*C'):=by
    have hh:= eY.add fY; change Allows n ((Fp-Tq)+Tq) z (C'*u+C') at hh; rw [sub_add_cancel] at hh; exact hh.mono (by linarith only [mul_le_mul_of_nonneg_left hu fY.nonneg])
 have hr:= reS _ _ L; have hv: Allows n Y₁ z (pole*v):= allows_const _ hr.1
 have h2:Allows n X₂ z (2*w):=by have hz:= J.2.add (show Allows n Y₂ z w from allows_const _ J.1); change Allows n ((X₂-Y₂)+Y₂) z (w*u+w) at hz; rw [sub_add_cancel] at hz; exact hz.mono (by linarith only [mul_le_mul_of_nonneg_left hu ((norm_nonneg _).trans J.1)])
 have hQ:= interpXY (u:=C'*u) Y₁ Tq X₁ Fp hv Hp hr.2 eY
 have hx:= interpXY (u:=w*u) (Y₁*Tq) Y₂ (X₁*Fp) X₂ (leaf_h _ _ hv fY) h2 hQ J.2
 let Lh(t:E):=lyric G p W F A B r s i j (U t) (Z t);
 let D:=putX g i; let Gz:=putX g j; have hd: D ∈ unitary (Op Slot):=(matter _).property; have hh:Gz∈unitary (Op Slot):=(matter _).property; let K:= X₁*Fp*X₂-Y₁*Tq*Y₂
 let R:=fun t=> star D*K t* Gz; have he:Allows n R z (7*wheel_l n^2*(pole*v)*C'*w*u):=(ship_x _ _ hd hh K hx).mono (le_of_eq (by ring))
 have ht: R=fun t=>Lh t - litho G p W A B r s i j T g (Tq t):=by
    funext x; have h₀:= lyric_g G p W X F hp (U x) A B r s i j (Z x) C Q a b v₁; rw [show Peaks.scaleG G v₁=g from funext fun i=>by simp [v₁,Peaks.scaleG, Ratio.embed_parent]] at h₀; change (X₁*Fp*X₂) x=D*Lh x*star Gz at h₀; unfold R K; rw [Pi.sub_apply,h₀,mul_sub,sub_mul,←mul_assoc,←mul_assoc, hd.1,one_mul,mul_assoc, hh.1,mul_one]; rfl
 rw [ht] at he; exact fun x y=> cape_l _ he x y
end
end YM.CF.Haro
end
