import YM.CF.BPress.Spin.Signed
import YM.CF.BPress.Spin.LatticeFieldEstimates
/-! Interest strong cost and arbitrary smallness on Guard arguments. Last assertion small BEFORE freezing Guard purchase; uses uses patch price variant because winding/trip tolls already incorporated and vanish as d→0 on patch, including when s large. No vacuum. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Spin
open Function Filter Finset Lattice Wilson Fock Cube SU Lat Tenant Branch Tulip Scroll Dial Nacre Laic Font Pledge SpinSign Eye
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators
attribute [local instance] opCStarAlgebra
variable {N:Side}{m:ℕ}{d a ε C:ℝ} {P Q: Pledge}

def color_price (P:Pledge) (m:ℕ):Pledge:= let R:=foilPrice (Sifting.cavilPrice P m); (R.scales (Fintype.card Signed)).scales ‖(Fintype.card Signed:ℝ)⁻¹‖
def aimPrice(P Q:Pledge):Pledge:= (color_price P 1).plus (color_price Q 2)
lemma color_cost {R:Toy m N}(h:CardK N m R P.price P.rate) : Form.Comes (Sifting.outlook N) (color_price P m) (colorX R):=by
 let X(v:Signed):= foil (n:=N) v (cavil R); have hp:= Sifting.sifting R P h; exact Costs.scale (Costs.sums X fun v=>foil_cost v hp) _
lemma aim_cost (R:Aim N)(h:R.toll P.rate Q.rate P.price Q.price): Form.Comes (Sifting.outlook N) (aimPrice P Q) R.den:= Costs.plus (color_cost h.1) (color_cost h.2)
lemma aim_tag (R:Aim N)(h:R.toll P.rate Q.rate P.price Q.price): ripeF R.den:=by
 obtain ⟨r,s⟩:= h; let x:= R.x; let y:= R.y; intro U t; unfold Aim.den; rw [Pi.add_apply,Pi.add_apply, map_add]; exact congrArg₂ (·+·) (troop _ (cobblestone x r.2.1) _ t) (troop _ (cobblestone y s.2.1) _ t)
lemma color_zero (R:Toy m N)(h:0<m):colorX R 1=0:=by simp_rw [colorX,sumU,foil,in_one,Sifting.cavil_one R h,map_zero,sum_const_zero,smul_zero]
lemma aim_zero (R:Aim N):R.den 1=0:=by simp only [Aim.den,Pi.add_apply,color_zero R.x (by decide),color_zero R.y (by decide),zero_add]
namespace Eye
lemma permit (u:ℕ)(p:0<ε) : ∃ d:ℝ,0<d ∧ 4 * ν u ^ 4 *(sphereRate*priceF u d)≤ ε:=by
 have hp : 0< 4 * ν u ^ 4*(sphereRate*priceF u 1):= by unfold priceF; have he:=sphereRate_cost.positive; have ht:=(vol_pos (w:=u)); positivity
 let d:= ε/(4 * ν u ^ 4*(sphereRate*priceF u 1)); refine ⟨d,div_pos p hp,?_⟩
 rw [show priceF u d=priceF u 1*d by unfold priceF; ring,←mul_assoc sphereRate, ←mul_assoc]; unfold d; exact le_of_eq (mul_div_cancel₀ ε hp.ne')
lemma settle (U:Bkg N)(h:Cube.Guard U d)(e:0≤d)(w:ℕ)(p:2*w+2<N.val)(x:Site N) : invitation (bay (terr N) x w) (gauge (hue U x) U) 1 ≤ 4 * ν w ^ 4 *(sphereRate*priceF w d):=by
 have ht:= sphereRate_cost.positive; let g:= gauge (hue U x) U; refine (invitation.size (U:=g) (V:=(1:Bkg N)) (by unfold priceF; positivity) (invitation.gauge_uniform sphereRate_cost w p d e h x)).trans_eq ?_
 rw [volume x (by omega)]; unfold ν; push_cast; ring
lemma traded (v:Tenant.Geometry N)(X:Support (More N))(A:Op (Single N)) : ‖look (home N) X*(twist (tradew N v) A)‖=‖look (home N) X*A‖:= gauge_norm v (bail N 1) (bail N 1) X A
end Eye

/-- This suffices uniformly after buying the two rates in Grace. Rather than bound on plaquette curves of small d globally, use winding-aware entry estimate on after truncation, which also gives smallness of all near reads in `hue` gauge. Fits T_s. -/
lemma invest (P Q:Pledge)(p:0<ε): ∃ (c:ℝ)(v:ℕ), 0<c ∧ ∀ {N:Side},v≤N.val → ∀ (R:Aim N), R.toll P.rate Q.rate P.price Q.price → ∀ (U:Bkg (More N)),Cube.Guard U c → ‖R.den U‖ ≤ ε:=by
 let a:=ε/2; have ha:0<a:=half_pos p; let E:=aimPrice P Q; obtain ⟨w,m,h⟩:= (pledge_lift E ha.le (half_lt_self p)).exists; obtain ⟨k,d,e,X⟩:= latticeFieldEstimates_price E ha; obtain ⟨c,f,H⟩:= permit (w+k) e
 refine ⟨c,m+2*(w+k)+3,f,?_⟩; intro N v R J U T; let F:=R.den; let B:= Sifting.outlook N; let t: B.Comes E F:= aim_cost R J; have ht:(More N).val=N.val*2:=rfl
 apply h (More N) (by omega) rfl F t U; intro z; let V:=gauge (hue U z) U; let o:=terr (More N)
 have he :F V=twist (tradew N (hue U z)) (F U):= aim_tag R J _ _
 let S:=bay o z w; have hp:= traded (hue U z) S (F U)
 have hL : ‖look (home N) S*(F V-F 1)‖ ≤ a:= X t V (1:Bkg (More N)) S (include_patch B.stage rfl V (1:Bkg (More N)) (k:=k) ((settle U T f.le (w+k) (by omega) z).trans H))
 rw [show F 1=0 from aim_zero R,sub_zero,he,hp] at hL; exact hL
end YM.CF.BPress.Spin
