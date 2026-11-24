import YM.CF.Pic.Stem
set_option autoImplicit false
set_option synthInstance.maxSize 8000
noncomputable section
namespace YM.CF.Pic
open Function Filter Metric Finset NormedSpace Lattice Laurent Kea Lat Fir Tulip Rush Cube Jill Ember SU Dial Thera Fock Peaks Cascade Flare Scroll Spire Sods CF.Jet Vault Paige Brace Branch Tenant Broc
open scoped Topology BigOperators Matrix MatrixOrder ContDiff Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {m L B N:Side}{j:ℕ}{o:Odd L.val}{Y:Pricing j L o (Thread j)}{e b v K a t:ℝ}{P:Grasp Y B e}
lemma units_t(N:Side): (Fintype.card (Single N):ℝ)=180*N.val^4:=by unfold Single; rw [Fintype.card_prod,Fintype.card_prod,slots,site_card]; simp [SpinIdx]; ring
-- from near P.K
lemma oar {V U:Phase.Skin m B}{X:Pearl P}(p:1≤j)(H:Stamped j L o Y)(k:P.roundZ≤(CSide m B).val)(M:Jill.Male)(q:0≤a)(W: CartP X M U V a t)(v:a ≤1/16)(c: 16*Fintype.card (Single (CSide m B))*a+t≤1)(w:0≤b)(u: 2*a*(Fintype.card (Single (CSide m B)))^2*b^2≤1): ∃ Ψ:FC (Single (CSide m B)),acts Ψ (changeM P U M)= changeM P V M-changeM P U M ∧ Pays b Ψ (48*(Fintype.card (Single (CSide m B))*a+t)+4*a*(Fintype.card (Single (CSide m B)))^2*b^2):=by
 let N:= CSide m B; let A:=spar j M U; let B':=spar j M V; let L:UNI (Single N):=⟨poleC N,LxxX _⟩; let a':=P.broadness _ k M
 have he:L.valᵀ= -L.val:=starC _ (fun _=> hookN ..)
 obtain ⟨Ψ,h,f⟩:= stroll (n:=Single N) (U:=L) (a'.projection U W.lf) (a'.projection V W.rt) he ((norm_sub_rev ..).trans_le W.near) W.stab (sea_g k U W.lf M) (sea_g k V W.rt M) v ((add_le_add_right W.piano _).trans c) (cue X H p k _ U W.lf W.slow_u) (cue X H p k _ V W.rt W.slow_v) w u
 exact ⟨Ψ,h,f.weigh (by gcongr; exact W.piano) w⟩
lemma recoil (h:0<b)(v:0<a)(g:0<K)(p:0≤t):∃ d' c:ℝ,0<d'∧ 0<c ∧∀ n k:ℝ,1 ≤ n→0<k→k ≤ 1→ n^10*k ≤ d'→ k ≤ b∧ a*k≤1/16∧ 16*(180*n^4)*(a*k)+K*n^4*k≤1 ∧ 2*(a*k)*(180*n^4)^2*(t*n)^2 ≤1 ∧ 48*((180*n^4)*(a*k)+K*n^4*k)+4*(a*k)*(180*n^4)^2*(t*n)^2 ≤ c*n^10*k:=by
 let d' := 16*180*a+K; let v':=2*a*180^2*t^2; let P:=48*(180*a+K); have hp:0<d':=by unfold d'; positivity; -- scope
 have he:0≤v':=by unfold v'; positivity; -- scope
 let c:=min (min b (1/(16*a))) (min (1/d') (1/(v'+1))); have hc:0<c:=lt_min (lt_min h (by positivity)) (lt_min (by positivity) (by positivity))
 refine ⟨c,P+2*v',hc,by unfold P; positivity,fun n k l x w h=>?_⟩
 let H:= n^10*k; have hh:0 ≤ H:= by unfold H; positivity
 have hx:k ≤ c := (le_mul_of_one_le_left x.le (one_le_pow₀ l)).trans h
 have ht:c ≤1/(v'+1):= (min_le_right ..).trans (min_le_right ..)
 have hk:n^4*k ≤ n^10*k:=by gcongr; norm_num
 refine ⟨hx.trans ((min_le_left ..).trans (min_le_left ..)) ,?_,?_,?_,?_⟩ -- tune
 · have he:k ≤1/(16*a):= hx.trans ((min_le_left ..).trans (min_le_right ..)); rw [le_div_iff₀ (by positivity :0<16*a)] at he; linarith
 · rw [show 16*(180*n^4)*(a*k)+K*n^4*k=d'*(n^4*k) from (by unfold d'; ring),mul_comm]; exact (_root_.le_div_iff₀ hp).mp (hk.trans (h.trans ((min_le_right ..).trans (min_le_left ..))))
 · rw [show 2*(a*k)*(180*n^4)^2*(t*n)^2=(n^10*k)*v' from (by unfold v'; ring)]; apply le_trans (mul_le_mul_of_nonneg_left (show v' ≤ v'+1 by linarith) hh); exact (le_div_iff₀ (by linarith :0<v'+1)).mp (h.trans ht)
 unfold P v'; nlinarith [mul_le_mul_of_nonneg_left hk v.le,mul_le_mul_of_nonneg_left hk g.le] -- tune
-- pen bound for arbitrary skim, arc
lemma skin_bounds (H:Stamped j L o Y)(X:Pearl P)(p:1≤j)(u:0<e)(w:0≤K):∃ c C:ℝ,0<c ∧0<C∧∃ n:ℕ,∀ m:Side,n≤(CSide m B).val→∀ (M:Jill.Male)(V:Phase.Skin m B) (d:Candle)(t:ℝ), slowT (Domain m B) d → 0<t → t ≤ 1→ (CSide m B).val^10*t≤c→lawnK V (Kea.tax d) t→Guard V e∧ ∃ A:FC (Single (CSide m B)),acts A (changeM (m:=m) P (Kea.tax d) M)= changeM P V M-changeM P (Kea.tax d) M ∧ Pays (K*(CSide m B).val) A (C*(CSide m B).val^10*t):=by
 obtain ⟨A,D,v,a,b,t,n,F⟩:=pencil p u X; obtain ⟨c,C,h,h',L⟩:= recoil t a b w; refine ⟨c,C,h,h',n+P.roundZ,fun m q M V d t k e z s hp=>?_⟩
 let N:=CSide m B; have he: (1:ℝ) ≤ N.val:=(by exact_mod_cast N.property); obtain ⟨tl,r,u0,v,d1⟩:= L N.val t he e z s
 have hh:=F m (by omega) d k V t e tl hp M; refine ⟨hh.rt,?_⟩; have hx:0 ≤ K*N.val:=(by positivity); have hS:P.roundZ ≤ N.val:=(by unfold N; omega); obtain ⟨Ψ,h,Q⟩:=oar p H hS M (by positivity) hh r (by simpa only [units_t] using u0) hx (by simpa only [units_t] using v)
 exact ⟨Ψ,h,Q.weigh (by rw [units_t]; exact d1) hx⟩
end YM.CF.Pic
