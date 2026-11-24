import SatinThinArbor
import SatinThinMoose
import SatinThinOort

/-! # Greed by omitting WHOLE cities in this frame, all budgets reconciled with the
 shelf/flare in subsequent Fock-Pressure couplings. `shieldC` purpose. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Pannier.Damask
open Filter Function NormedSpace Lattice Finset Cube SU Fock Lat Spire Scroll Peaks Drapes Rush Tulip Pastry Scree Girt Branch Dial Nacre Font Laic Graph Skye
open scoped Pointwise Topology ContDiff Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Classical
attribute [local instance] opCStarAlgebra
open Py.Rate.Pannier Fixed.Extensive Pannier.Chancel Papyrus.Franc Rous Pressure Worth
variable {j m d k:ℕ}{N:Side}{A0:Loom N}{D β γ a C R δ v u t g:ℝ}
abbrev wane_h(r:ℝ)(m:ℝ)(R W:ℝ):= 24*m/r + W*r^4*R
abbrev frame_h(k:ℕ)(r:ℝ)(R:ℝ):= R*4*(((k+4)*2+1)^4:ℕ)* Fintype.card PlaqAxes*r^4
abbrev townDaily (r:Side)(v R g δ:ℝ)(m:ℕ):= (180/16:ℝ)*shortfall g R δ (scaleTown r v) m + 24*((m:ℝ)+1)/(r.val:ℝ)*180*(2*R)
abbrev townDues (r:Side)(R f:ℝ)(k:ℕ):= (frame_h k r.val f :ℝ)*180*(2*R)
abbrev townS (U:Orbit N)(k:ℝ):ℝ:=flakes k U.1

private lemma agency {r n : Side}(u:r.val≤ n.val) : (↑(n.val/r.val)+1:ℝ)≤ 2*(n.val:ℝ)/(r.val:ℝ):=by
 rw [le_div_iff₀ (show (0:ℝ)<↑(r.val:ℕ) from Nat.cast_pos.mpr r.property)]; have h:(↑(n.val/r.val):ℝ)*(r.val:ℝ)≤ (n.val:ℝ):=by exact_mod_cast Nat.div_mul_le_self n.val r.val
 have hv:(r.val:ℝ) ≤ (n.val:ℝ):= Nat.cast_le.mpr u; linarith only [hv,h]
lemma stuff_card : (Fintype.card (Single N):ℝ)=180/16*(↑(More N).val:ℝ)^4 := by
 rw [Pic.units_t]; unfold Cube.More; change _*(↑N.val:ℝ)^4=(180:ℝ)/16*(↑(N.val*2):ℝ)^4 -- tune order
 push_cast; ring
lemma frame_attenuation (W:Colts j N a C δ)(c:0 ≤ C)(b:0<δ)(r:Side)(M:Tulip.Male)(p:0 ≤ v)(g':Roof N u t k A0)(h:v≤u)(x: Orbit N)(w:ℕ)(ht:t≤δ)(Z:Brace.Sparkle N t M j)(g:r.val≤(More N).val):
 Papyrus.Franc.revE (twist (tradew N (metroFrame r (A0 x))) (spar j M (A0 x))- spar j M (1:Pane N)) ≤ townDaily r v C a δ w * (↑(More N).val:ℝ)^4 + townDues r C (townS x v) k:=by
 let s:=(More N).val; apply (frame_gate W c b r M p g' h x w ht Z).trans; rw [stuff_card] -- nat div maybe want explicit
 let Q:=shortfall a C δ (scaleTown r v) w; let R:ℝ:= r.val; let T:ℝ:=s; let Y:= (s/r.val:ℕ); let H:=townS x v; let X:= 2*T/R; unfold townDaily townDues frame_h
 change _ ≤ (180/16*Q+24*((w:ℝ)+1)/R*180*(2*C))*T^4+(H*4*(((k+4)*2+1)^4:ℕ)*↑(Fintype.card PlaqAxes)*R^4)*180*(2*C)
 have hv:=agency g; have ht':0 ≤ T:=Nat.cast_nonneg _; have hp:0 ≤ (w:ℝ)+1:= by positivity
 change (Y:ℝ)+1≤X at hv; let K:ℝ:=4*(( (k+4)*2+1)^4:ℕ)*Fintype.card PlaqAxes
 have hu:(12 * ((Y:ℝ)+1)*((w:ℝ)+1)*T^3) ≤ 24*((w:ℝ)+1)/R*T^4:=by
    refine le_trans (b:=12*X*((w:ℝ)+1)*T^3) ?_ (le_of_eq ?_); · gcongr
    unfold X; ring
 unfold H townS flakes; dsimp only [s,T,Q,R]; dsimp only [Y,s,T,R] at hu; push_cast at *
 -- `R` is only on rhs, proof affine
 nlinarith only [mul_le_mul_of_nonneg_right hu c]

abbrev baseDaily (a C R e:ℝ):=1/16*C*e^2+180^2*((1+R)*R)*(180/16*45*C*(e+e^2))
abbrev debtDaily (r d:ℕ)(C R:ℝ):=rimedR r d 1*(C*4)+180^2*((1+R)*R)*quake r d 1*(45*6*C)
lemma mile_attenuation (W:Colts j N g R δ)(h:0 ≤ R)(Q:t≤δ)(R':GramM N)(l:Ledger D β γ a C R')(c:0≤C)(U:Orbit N)(g':Roof N u t k A0)(p:IsStarProjection (spar j R'.J.M (A0 U)))(ℓ:v ≤ u)(s:0≤a)(w:v≥0)(l':d≤(More N).val)(e:ℝ)(q:v+2*Real.exp (-(a*d))≤e):
    ‖Pec.pigment R'.J.I (A0 U)‖ + revE (actF j R' A0 U) ≤ baseDaily a C R e*(↑(More N).val:ℝ)^4 + debtDaily k d C R * townS U v:=by
 apply (add_le_add (pigment_petite _ l.field.2 U g' ℓ w s c l' e q) (revAct_b R' l c U g' Q W p ℓ s w l' e q h)).trans_eq;
 unfold townS storm baseDaily debtDaily; rw [stuff_card]; unfold rimedR quake Cube.More;
 set S:= N.val; push_cast; ring -- tune
end YM.CF.Pannier.Damask
#print axioms YM.CF.Pannier.Damask.frame_attenuation
#print axioms YM.CF.Pannier.Damask.mile_attenuation
