import YM.CF.Gall.Geld
set_option autoImplicit false
noncomputable section
namespace YM.CF.Gall
open Function Filter Metric Finset NormedSpace Lattice Laurent Kea Lat Fir Tulip Rush Cube Jill Ember SU Dial Thera Fock Peaks Cascade Flare Scroll Spire
open scoped Topology BigOperators Matrix MatrixOrder ContDiff Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] opCStarAlgebra
open Sods CF.Jet Vault Paige Brace Branch Tenant Broc
variable {m L B N:Side}{j n:ℕ}{o:Odd L.val}{Y:Pricing j L o (Thread j)}{e b c v K a l t x y T r:ℝ}{P:Grasp Y B e}
lemma rose(X:Pearl P)(S:Stamped j L o Y)(t:P.roundZ ≤ (CSide m B).val)(p:1≤j)(M:Jill.Male)(V:Phase.Skin m B)(f:Cart (Domain m B))(h:Guard (gauge f V) e)(eD:0≤a)(hB:0≤b)(v: Gall.Yep a (mateK _) (changeM P (gauge f V) M) b): Guard V e ∧ Gall.Yep (45*a) (mateK (CSide m B)) (changeM P V M) b:=by
 let N:=CSide m B; have he:gauge f⁻¹ (gauge f V)=V:=(by rw [windy,inv_mul_cancel,windy_u]); let U:=tradew N f⁻¹; let W:= changeM P (gauge f V) M; let q:=mateK N; have hp:Pic.Fone U W=changeM P V M:= Eq.symm (by nth_rw 1 [← he]; exact Hive.honey_x X S t p h f⁻¹); have hm:Pic.Fone U q=q:= Girt.mastC _
 refine ⟨he ▸ h.cov f⁻¹,?_⟩; rw [←hp]; change Gall.Yep _ q _ _; rw [←hm]; exact v.jetF eD hB U (lurk_n _)
lemma chimeT (X:Pearl P)(F:Pic.Span X K b v c l r n):∃ A B' u:ℝ,0<A ∧0<B' ∧0<u∧∃ n':ℕ,n≤n'∧ ∀ m:Side,n' ≤ (CSide m B).val→∀ (M:Jill.Male)(U:Bkg (Domain m B))(d:Candle)(f:Cart (Domain m B))(t:ℝ), slowT (Domain m B) d →0<t→ t≤1 → (CSide m B).val^10*t≤ u→ lawnK (gauge f U) (Kea.tax d) t → Guard U e∧ Gall.Yep A (mateK (CSide m B)) (changeM P U M) (B'*Kea.angel m P M):=by
 obtain ⟨G,A,h,h',X'⟩:= Gall.cash F.p F.rP; obtain ⟨s,t,hS,ht,i,V⟩:= Gall.skin_bounds F.stmt X F.p F.eP h'.le; obtain ⟨o,U⟩:= Pic.sortV F.p r; let d:=G*c; have hC:= F.cP; have hd:0<d:=by unfold d; positivity
 let v':=t*s*d; have hg:0<v':=by unfold v'; positivity
 refine ⟨45*A,d+v',s,by positivity,by positivity,hS,n+i+o,by omega,fun m hv M R b' f t' e' hp hx hW hY=>?_⟩
 let N:=CSide m B; let S:=skim N b'; obtain ⟨U',W,F',hV⟩:=V m (by omega) M _ _ t' e' hp hx hW hY; obtain ⟨e,K'⟩:=F.plan m (by omega); have ha:=angel_p X F.stmt e F.p F.eP M K'; let x:= Kea.angel m P M; have hF:= (F.powV m (by omega) M b' S).2.1; have hq:= sea_g e (Kea.tax b') (tax_guard _ _ _ F.eP.le) M; rw [show spar j M _=_ from K'.2 b' S M] at hq; have hZ: Yep A (mateK N) (changeM (m:=m) P (Kea.tax b') M) (d*x):= (Yep.weigh (X' _ K'.1 (U _ K'.1 (by omega)).2.1 b' S M _ hq) (by unfold d; rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hF h.le) h'.le)
 refine rose X F.stmt e F.p M R f U' h'.le (by positivity) ?_; have ht:= (hZ.join (hV.2 _ _ _ (mul_nonneg hd.le (show 0<x from ha).le) hZ)); rw [F',add_sub_cancel] at ht; refine ht.weigh ?_ h'.le; rw [add_mul]; apply add_le_add_right; exact (mul_le_mul_of_nonneg_right (show t*↑N.val^10*t'≤t*s by nth_rw 1 [show t*↑N.val^10*t'=t*(↑N.val^10*t') by ring]; gcongr) (mul_nonneg hd.le ha.le)).trans_eq (by unfold v'; ring)
end YM.CF.Gall
