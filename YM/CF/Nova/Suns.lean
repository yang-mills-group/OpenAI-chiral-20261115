import YM.CF.Nova.Star
set_option autoImplicit false
set_option synthInstance.maxSize 8000
noncomputable section
namespace YM.CF.Nova
open Function Filter Metric Finset NormedSpace Lattice Laurent Kea Lat Fir Tulip Rush Cube Jill Ember SU Dial Thera Fock Peaks Cascade Flare Scroll Spire Sods CF.Jet Vault Paige Brace Branch Tenant Broc Pic
open scoped Topology BigOperators Matrix MatrixOrder ContDiff Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {m L B N:Side}{j n:ℕ}{o:Odd L.val}{Y:Pricing j L o (Thread j)}{e b c v K a l r t w:ℝ}{P:Grasp Y B e}{H:Pearl P}(D:Span H K b v c l r n)(p:n≤ (CSide m B).val)
def Stock (x:Bkg (Domain m B))(P:Grasp Y B e)(M:Jill.Male)(A:wit m B)(k u:ℝ):=∃ B:FC (Single (CSide m B)), Pays k B u ∧ A= changeM P x M+acts B (changeM P x M)
def duty(x:ℝ)(t:ℝ)(C:ℝ)(w:ℝ):ℝ:= C*x^10*t+w*(2*C)
local notation "N"=>CSide m B
include D p
lemma emerge(M:Jill.Male)(U:Bkg (Domain m B))(F:Cart (Domain m B))(z:Candle)(y:slowT (Domain m B) z)(m0:lawnK (gauge F U) (Kea.tax z) t)(h:t>0)(lh:t≤1)(k:(CSide m B).val^10*t ≤ min v 1)(A:wit m B)(hc: Stock U P M A (K*(CSide m B).val) w) :
 Guard U e ∧ ‖gleam m P M * beamM m B A - (‖AMP m P z M‖:ℂ)‖≤ duty (CSide m B).val t c w*Kea.angel m P M ∧ Yep (K*(CSide m B).val) (mateK N) (A-changeM P U M) (w*(2*c*Kea.angel m P M)) ∧ Yep (K*(CSide m B).val) (mateK N) A ((1+w)*(2*c*Kea.angel m P M)) :=by
 obtain ⟨v,T,h'⟩:=CostKin D p M U F y m0 h lh k; obtain ⟨B',b,H'⟩:=hc
 let D':=changeM (m:=m) P U M; let W:=acts B' D'; have hp:=angel_p H D.stmt (D.plan m p).1 D.p D.eP M (D.plan m p).2; have hh:=D.cP; have hw:= b.2 _ _ _ (by positivity) T
 refine ⟨v,?_,by rw [H',add_sub_cancel_left]; exact hw,by rw [H',add_mul,one_mul]; exact Yep.join T hw⟩
 let z':=gleam m P M; have ht:= (gleams D p M).1; have hQ : beamM m B A= beamM m B D'+beamM m B W:=by rw [H']; unfold beamM; rw [inner_add_right]
 rw [← (gleams D p M).2,hQ]; change ‖z'*(_+_)-z'*_‖≤_; rw [show (z'*(_+_)-z'*AMP m P z M)=z'*(beamM m B D'-AMP m P z M)+z'*beamM m B W by ring]; apply (norm_add_le ..).trans; rw [norm_mul,norm_mul,show ‖z'‖=1 from ht]; simp only [one_mul]; refine (add_le_add h' (show ‖beamM m B W‖≤_ from Yep.lim hw)).trans_eq ?_; unfold duty; ring
-- all-field orbit and good term at some shift. no need lower bound from gauge selection.
omit D p in
lemma movesh{U:Bkg (Domain m B)}(t:ℝ)(F:Cart (Domain m B))(z:Candle)(e:lawnK (gauge F U) (Kea.tax z) t)(x:Hat):lawnK (gauge (gKey (Domain m B) z x* F) (welt U x)) (Kea.tax (sun z x (Domain m B))) t:=by rw [← windy,←w_g, ← overt]; exact lawnK.join (w_m _ _ _ e x) _
omit D p
lemma habits :∃ (u:ℕ)(k W:ℝ),1 ≤ u∧0<k∧1 ≤ W∧∀ n:Side,∀ U:Bkg n,∀ e:ℝ,0≤e→ PlaqBound firstF U e→∀ t:ℝ,0<t→t≤1→ n.val^2 * e ≤ k*t^u→ ∃ F:Cart n,∃ d:Candle,speedB d n∧lawnK (gauge F U) (Kea.tax d) t:=by
 obtain ⟨r,c,C,h,v,u,Z⟩:= Sods.loft
 let w:=max C 1; have hp:0<w:=lt_max_of_lt_right one_pos; refine ⟨r,c/w^r,w,h,div_pos v (pow_pos hp _),le_max_right ..,fun n U e p P t y f hg=>?_⟩; have hx:t/w ≤ t:=div_le_self y.le (le_max_right ..); obtain ⟨F,G,h,H⟩:=Z n U e p P (t/w) (div_pos y hp) (hx.trans f) (hg.trans_eq (by rw [div_pow]; ring)); exact ⟨F,G,h,fun i=>(H i).trans ((mul_le_mul_of_nonneg_right (le_max_left ..) (by positivity)).trans_eq (show w*(t/w)=t by field_simp))⟩
end YM.CF.Nova
