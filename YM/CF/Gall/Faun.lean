import YM.CF.Gall.Act
set_option autoImplicit false
set_option synthInstance.maxSize 8000
noncomputable section
namespace YM.CF.Gall
open Function Filter Metric Finset NormedSpace Lattice Laurent Kea Lat Fir Tulip Rush Cube Jill Ember SU Dial Thera Fock Peaks Cascade Flare Scroll Spire Sods CF.Jet Vault Paige Brace Branch Tenant Broc
open scoped Topology BigOperators Matrix MatrixOrder ContDiff Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {n:Type*}[LinearOrder n][Fintype n][Nonempty n]{P Q R K:Op n}{p q f:Wave n}{k v C d w:ℝ}{A B:FC n}{a b:ℂ}{U:UNI n}
lemma stroll(h:IsStarProjection P)(g:IsStarProjection Q)(l: U.valᵀ= -U.val)(t:‖P-Q‖≤k)(e: ‖stage P U.val-U.val‖ ≤1/3)(hp:Sea P p)(hq:Sea Q q)(u:k≤1/16)(c:16*Fintype.card n*k+|(a-b).im|≤1)(x:Complex.exp a • p= filled P U.val)(y:Complex.exp b • q=filled Q U.val)(w':0 ≤ w)(v: 2*k*(Fintype.card n)^2*w^2≤1) :∃ A:FC n,acts A p = q-p ∧ Pays w A (48*(Fintype.card n*k+|(a-b).im|)+4*k*(Fintype.card n)^2*w^2):=by
 obtain ⟨K,H,L⟩:= Pic.wire h g t (by linarith)
 let m:ℂ:=inner ℂ p q; let B:=exp (dg (laneP P 1 K)); have he:B=exp (dg (laneP P 1 K)):=rfl
 have hb: ‖m-1‖≤48*(Fintype.card n*k+|(a-b).im|):=Pic.gross h g l t e hp hq u c x y
 have hp':‖m‖≤1:= le_trans (norm_inner_le_norm ..) (by rw [hp.2,hq.2,mul_one])
 have hk:q=m • acts B p:=by have ht:= broomstick H q p hq hp; rw [quant_one,act_one,skyGlow,quant_one,act_one] at ht; exact ht
 have hr:= Pays.linear ((Pays.brick w' _ L).exp_sub) m
 refine ⟨(m-1) • 1+m • (B-1),?_,?_⟩
 · rw [act_add,act_smul,act_smul,act_one,act_sub,act_one,smul_sub, sub_smul,one_smul, ←hk]; abel
 let c:=2*k*(Fintype.card n)^2*w^2; have he:0≤c:=by have he:= (norm_nonneg _).trans t; unfold c; positivity
 apply ((Pays.uno.linear (m-1)).add hr).weigh _ w'; rw [mul_one]; apply add_le_add hb; change ‖m‖* (Real.exp c-1)≤_; apply (mul_le_of_le_one_left (by linarith [Real.one_le_exp he]) hp').trans; exact (Pic.score he v).trans_eq (by unfold c; ring)

variable {m L B N:Side}{j:ℕ}{o:Odd L.val}{Y:Pricing j L o (Thread j)}{e b v K a t:ℝ}{P:Grasp Y B e}
lemma oar {V U:Phase.Skin m B}{X:Pearl P}(p:1≤j)(H:Stamped j L o Y)(k:P.roundZ≤(CSide m B).val)(M:Jill.Male)(q:0≤a)(W: Pic.CartP X M U V a t)(v:a ≤1/16)(c: 16*Fintype.card (Single (CSide m B))*a+t≤1)(w:0≤b)(u: 2*a*(Fintype.card (Single (CSide m B)))^2*b^2≤1): ∃ Ψ:FC (Single (CSide m B)),acts Ψ (changeM P U M)= changeM P V M-changeM P U M ∧ Pays b Ψ (48*(Fintype.card (Single (CSide m B))*a+t)+4*a*(Fintype.card (Single (CSide m B)))^2*b^2):=by
 let N:= CSide m B; let A:=spar j M U; let B':=spar j M V; let L:UNI (Single N):=⟨Pic.poleC N,LxxX _⟩; let a':=P.broadness _ k M
 have he:L.valᵀ= -L.val:=starC _ (fun _=> hookN ..)
 obtain ⟨Ψ,h,f⟩:= stroll (n:=Single N) (U:=L) (a'.projection U W.lf) (a'.projection V W.rt) he ((norm_sub_rev ..).trans_le W.near) W.stab (sea_g k U W.lf M) (sea_g k V W.rt M) v ((add_le_add_right W.piano _).trans c) (Pic.cue X H p k _ U W.lf W.slow_u) (Pic.cue X H p k _ V W.rt W.slow_v) w u
 exact ⟨Ψ,h,f.weigh (by gcongr; exact W.piano) w⟩
lemma skin_bounds (H:Stamped j L o Y)(X:Pearl P)(p:1≤j)(u:0<e)(w:0≤K):∃ c C:ℝ,0<c ∧0<C∧∃ n:ℕ,∀ m:Side,n≤(CSide m B).val→∀ (M:Jill.Male)(V:Phase.Skin m B) (d:Candle)(t:ℝ), slowT (Domain m B) d → 0<t → t ≤ 1→ (CSide m B).val^10*t≤c→lawnK V (Kea.tax d) t→Guard V e∧ ∃ A:FC (Single (CSide m B)),acts A (changeM (m:=m) P (Kea.tax d) M)= changeM P V M-changeM P (Kea.tax d) M ∧ Pays K A (C*(CSide m B).val^10*t):=by
 obtain ⟨A,D,v,a,b,t,n,F⟩:=Pic.pencil p u X; obtain ⟨c,C,h,h',L⟩:= Pic.recoil t a b w; refine ⟨c,C,h,h',n+P.roundZ,fun m q M V d t k e z s hp=>?_⟩
 let N:=CSide m B; have he: (1:ℝ) ≤ N.val:=(by exact_mod_cast N.property); obtain ⟨tl,r,u0,v,d1⟩:= L N.val t he e z s
 have hh:=F m (by omega) d k V t e tl hp M; refine ⟨hh.rt,?_⟩; have hx:0 ≤ K*N.val:=(by positivity); have hS:P.roundZ ≤ N.val:=(by unfold N; omega); obtain ⟨Ψ,h,Q⟩:=oar p H hS M (by positivity) hh r (by simpa only [Pic.units_t] using u0) w (by rw [Pic.units_t]; refine le_trans ?_ v; apply mul_le_mul_of_nonneg_left; gcongr; exact le_mul_of_one_le_right w he; positivity)
 exact ⟨Ψ,h,Q.weigh (by rw [Pic.units_t]; refine le_trans ?_ d1; apply add_le_add_right; gcongr; exact le_mul_of_one_le_right w he) w⟩
end YM.CF.Gall
