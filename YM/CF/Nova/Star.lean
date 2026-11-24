import YM.CF.Pic.Cash
set_option autoImplicit false
set_option synthInstance.maxSize 8000
noncomputable section
namespace YM.CF.Nova
open Function Filter Metric Finset NormedSpace Lattice Laurent Kea Lat Fir Tulip Rush Cube Jill Ember SU Dial Thera Fock Peaks Cascade Flare Scroll Spire Sods CF.Jet Vault Paige Brace Branch Tenant Broc Pic
open scoped Topology BigOperators Matrix MatrixOrder ContDiff Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {m L B N:Side}{j i:ℕ}{o:Odd L.val}{Y:Pricing j L o (Thread j)}{e b c v K a l r w:ℝ}{P:Grasp Y B e}
section
variable {H:Pearl P}{n:ℕ} (D:Span H K b v c l r n)(p:n≤(CSide m B).val)(M:Jill.Male)
local notation "N"=> (CSide m B)
def gleam(m:Side)(P:Grasp Y B e)(M:Jill.Male):ℂ:= star (AMP m P emptyC M)/(Kea.angel m P M:ℂ)
include D p
lemma gleams :‖gleam m P M‖=1∧ ∀ d:Candle,gleam m P M*AMP m P d M=‖AMP m P d M‖ :=by
 have h:= D.plan _ p; have hp:= angel_p H D.stmt h.1 D.p D.eP M h.2; refine ⟨?_,fun v=>?_⟩
 · unfold gleam; rw [norm_div,norm_star, Complex.norm_real,Real.norm_of_nonneg hp.le,show ‖AMP m P emptyC M‖= Kea.angel m P M from rfl, div_self hp.ne']
 unfold gleam; rw [div_mul_eq_mul_div,cerule H D.stmt h.1 D.p D.eP M h.2]; apply mul_div_cancel_left₀ _ (by exact_mod_cast hp.ne') -- tune
omit p D
-- comparators support Knit.Any. underlying function F physical REAL phase. 
structure Approx(X Y:wit m B)(K d:ℝ): Prop where
 score : Yep (K*(CSide m B).val) (mateK _) (X-Y) d
include D p
structure Clear (D:Span H K b v c l r n)(P:Bkg (Domain m B))(t:ℝ) :Prop where
 ripe:∃ (f:Cart (Domain m B))(d:Candle), slowT (Domain m B) d∧ lawnK (Lattice.gauge f P) (Kea.tax d) t
lemma CostKin {d:Candle}{t:ℝ}(U:Bkg (Domain m B))(g:Cart (Domain m B))(y:slowT (Domain m B) d)(q:lawnK (gauge g U) (Kea.tax d) t)(h:t>0)(l:t≤1)(k:(CSide m B).val^10*t ≤ min v 1) :Guard U e ∧ Yep (K*(CSide m B).val) (mateK (CSide m B)) (changeM P U M) (2*c*Kea.angel m P M) ∧ ‖beamM m B (changeM P U M) - AMP m P d M‖≤ c*(CSide m B).val^10*t*Kea.angel m P M :=by
 let W:= skim N d; obtain ⟨t',Q⟩:= D.plan _ p; obtain ⟨_,_,_,L⟩:= D.powV _ p M d W; obtain ⟨u,x⟩:= D.pale _ p M d y _ t h l (k.trans (min_le_left ..)) q; have hp:= angel_p H D.stmt t' D.p D.eP M Q
 have hk:= D.kP; have hc:= D.cP; let z:= c*(CSide m B).val^10*t*Kea.angel m P M
 let R:=changeM P (gauge g U) M; have hx: Yep (K*(CSide m B).val) (mateK N) R (c*Kea.angel m P M+z):=by have he:= Yep.join L x; rw [add_sub_cancel] at he; exact he
 obtain ⟨v,V,T⟩:= Jection H D.stmt t' D.p M U g u hx; refine ⟨v,T.weigh ?_ (by positivity),?_⟩
 · have he: z ≤ c*Kea.angel m P M:=by
      apply mul_le_mul_of_nonneg_right ?_ hp.le; rw [mul_assoc]; apply mul_le_of_le_one_right (zero_le_one.trans hc) (k.trans (min_le_right ..))
   linarith
 rw [← V]; change ‖_ - AMP _ _ _ _‖≤_; unfold beamM AMP; rw [←inner_sub_right]; exact Yep.lim x
end
end YM.CF.Nova
