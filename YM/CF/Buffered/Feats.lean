import YM.CF.Buffered.Cachet
/-! # The broadcast in the donor. Any comparable-k pressure.
-/
set_option autoImplicit false
set_option maxHeartbeats 450000
noncomputable section
namespace YM.CF.Buffered.Region
open Function Filter NormedSpace SU Lat Lattice Cube Finset Mir Mir.Trip Phase RP MeasureTheory Roost Rails Mil RG WilsonStartup Spark Nova Fock Push.SectorMeasure Ordered Cin Stripe Tile Traversed Stack Bays Saddle Stampu MarkCastle
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder Fin.NatCast
attribute [local instance] opCStarAlgebra
variable {m p n v B l:Side}{e x:ℝ}
local notation "X"=>Xmind m B
local notation "N"=>Uniform p
local notation "s"=>Brace.northZ m B
variable (K:Ticket m v B p e x)(Z: Badge v B)(q:Clip)(β u:ℝ)
namespace Ticket
def singleT (x:Pack m B): FC X:= let f:= reel (0:Rail N) (fromCube K.K x); into (Installed.point (erect K.K B) 0) (Z.label f)
def singleZ := heatNum K.pin K.W q β x e u s (K.singleT Z)
local notation "Zs" => heatNum K.pin K.W q β x e u s (K.singleT Z)
local notation "Z0" => moment K 1 q β u
local notation "ZZ" => moment K Z q β u
lemma one_label : K.estate (Stampu.paint Z MarkCastle.first) =K.singleT Z :=by
 funext b;  unfold singleT estate Rect.logo; let F:=erect K.K B; let v' (i: Rail N):= reel i (K.K.fromCube b); let Y:=Rect.Badge.one F (Stampu.paint Z MarkCastle.first) v'; change pal Y (show Pairwise _ from Rect.Badge.paired _ _ _) _=_
 let T: Finset (Rail N):=univ.erase 0; rw [show @univ (Rail N) _=insert (0:Rail N) T from Eq.symm (insert_erase (mem_univ _)),pal_insert _ _ T (show (0:Rail N)∉T from notMem_erase 0 _)] -- tune dependent
 have he: pal Y (Rect.Badge.paired _ _ _) T=1:=by unfold pal; rw [noncommProd_eq_pow_card _ Y _ 1,one_pow]; intro i p; unfold Y Rect.Badge.one Stampu.paint MarkCastle.first; rw [if_neg (by simp [(mem_erase.mp p).1])]; exact Cin.inject_one _
 rw [he,mul_one]; unfold Y Rect.Badge.one Stampu.paint MarkCastle.first; rw [if_pos (by rw [decide_eq_true rfl]), Badge.reflected_zero]
lemma first_v : singleZ K Z q β u=prism N K (Stampu.paint Z MarkCastle.first) q β u:=by unfold singleZ; rw [←one_label]; exact pressure ..
include Z
lemma empty_v : prism N K (Stampu.paint Z (fun _=>false)) q β u=Z0:=by rw [moment_s, show Stampu.paint Z (δ:=N) (fun _=>false)=(1: Rail N→Badge _ _) from funext fun _=> if_neg (by simp), Badge.reflected_one]; rfl -- tune
lemma deck_broadcast (h:0 ≤ u)(v':0 < ‖K.moment 1 q β u‖): (‖singleZ K Z q β u‖/‖Z0‖)^(p.val^4) ≤ ‖ZZ‖/‖Z0‖:=by
 let f(x:FaceM N):= ‖prism N K (Stampu.paint Z x) q β u‖; have he: MarkCastle.Crew f:= ⟨fun _=> norm_nonneg _,fun y i t=>by
    letI : MeasurableSpace (EdgePorts (away i N) v B):=⊤ -- v_ shadow
    haveI : DiscreteMeasurableSpace (EdgePorts (away i N) v B):= inferInstanceAs (@DiscreteMeasurableSpace _ ⊤)
    exact Stampu.cauchy (Traversed.self i N) t K Z q β u K.K.onGrid h y⟩
 have hx:f (fun _=>false)= ‖Z0‖:= congrArg (fun z:ℂ=>‖z‖) (K.empty_v Z q β u); have ha:= MarkCastle.Crew.single K.K.onGrid he (hx.symm ▸ v')
 have ht': Stampu.paint Z (δ:=N) (fun _=>true)=Z.reflected:= rfl
 rw [show Fintype.card (Rail N)=p.val^4 from (by simp [Axis,Rail,Uniform]), show f (fun _=>true)=‖ZZ‖ from (by unfold f; rw [ht',moment_s]),hx, show f MarkCastle.first=‖singleZ K Z q β u‖ from congrArg Norm.norm (first_v K Z q β u).symm] at ha
 rw [div_pow,div_le_div_iff₀ (pow_pos v' _) v']; refine le_trans (mul_le_mul_of_nonneg_right ha v'.le) (le_of_eq ?_); have hp:0<p.val^4:=by positivity
 rw [mul_assoc,←pow_succ,show p.val^4-1+1=p.val^4 by omega]
variable {h:0 ≤ u}
-- combine with anchor estimates of the same Ticket/moon. State analytic final cost
-- ratio at m hence bounded by τ times exp((3/2)⁴*Δ/p⁴), record without n. 
omit Z
private lemma afford {a b b' c c' x d : ℝ}(k M : ℕ)(p:0<k)(m:0< M) (w: 0≤a)(hp:0<b)(hb:0<b')(hc:0≤ c)(t:0< x)
 (z:a^(M*k) ≤ c'/b')(h: c' ≤ c^ M)(T:c ≤ x^k*b)(f: Real.log b- Real.log b'/M ≤ d):
 a ≤ x*Real.exp (d/k):=by
 let A:=x*Real.exp (d/k)
 apply le_of_pow_le_pow_left₀ ((by positivity : 0<M*k) : 0 < M*k).ne' (show 0≤A by unfold A; positivity) -- tune argument?
 refine z.trans ((div_le_div_of_nonneg_right (h.trans (pow_le_pow_left₀ hc T _)) hb.le).trans ?_)
 have he : Real.log b * M - Real.log b' ≤ d * M:=by
    have hx : (Real.log b-d)*(M:ℝ) ≤ Real.log b':= (le_div_iff₀ (by positivity)).1 (by linarith); linarith
 rw [div_le_iff₀ hb]; refine (Real.strictMonoOn_log.le_iff_le ?_ ?_).1 ?_
 · exact Set.mem_Ioi.mpr (by positivity)
 · exact Set.mem_Ioi.mpr (by positivity)
 rw [Real.log_pow, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),Real.log_pow,Real.log_pow,Real.log_mul (by positivity) (by positivity),Real.log_exp]; push_cast; field_simp; nlinarith

include Z
lemma combine {k a b:Side}(K':Ticket n v B l e x)(K₃:Ticket a v B b e x)(h':Coherent K K')(h₃:Coherent K K₃)(p': l=k*p)(f₃:b=3*p)(p₀:0 < ‖Z0‖)(v':0 < ‖moment K₃ 1 q β u‖)(hk: Odd k.val)(hu:0 ≤ u){δ:ℝ}(pδ:0 < δ)(z: ‖ZZ‖ ≤ δ^(p.val^4)*‖Z0‖) :
 let Δ:= lux 3 ‖Z0‖ ‖moment K₃ 1 q β u‖; ‖singleZ K' Z q β u‖/‖moment K' 1 q β u‖ ≤ δ*Real.exp ((3/2)^4*Δ/(p.val:ℝ)^4):=by
 intro Δ; have ⟨w,H⟩:= escort_data K K' q β u h' p' hu K₃ h₃ f₃ hk p₀ v'; rw [←Nat.cast_pow ((↑p:ℕ))]; refine afford (p.val^4) (k.val^4) (by positivity) (by positivity) (div_nonneg (norm_nonneg _) w.le) p₀ w (norm_nonneg _) pδ (c:= ‖ZZ‖) (c':= ‖moment K' Z q β u‖) ?_ (at_most K K' q β u Z h' p' hu) z ?_
 · have he:l.val^4=k.val^4*p.val^4:=by rw [p']; exact mul_pow k.val p.val 4
   rw [←he]; exact deck_broadcast K' Z q β u hu w
 unfold lux at H; unfold Δ lux; simp only [Nat.cast_pow]; exact H
end Ticket
end YM.CF.Buffered.Region
#print axioms YM.CF.Buffered.Region.Ticket.combine
#print axioms YM.CF.Buffered.Region.Ticket.singleZ
