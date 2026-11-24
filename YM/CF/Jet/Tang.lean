import YM.CF.Jet.Pilot
set_option autoImplicit false
noncomputable section
namespace YM.CF.Jet
open Function Filter Metric Lat Finset Tenant Branch Fock Dial MeasureTheory Phase Phase.Sample Lattice Cube Broc Drapes Tulip Peaks Brace Paige
open scoped Topology Matrix BigOperators ContDiff NNReal Matrix.Norms.L2Operator InnerProductSpace
set_option synthInstance.maxSize 8000
attribute [local instance] opCStarAlgebra
variable {j:ℕ}{L B:Side}{ho:Odd L.val}{T:Script Male}{Y:Pricing j L ho T}{e:ℝ}(g:Grasp Y B e)(n:ℕ){K:ℝ}
def radF:ℝ:=rateK g.a g.b/2 /feeG (8*B.val)/2
lemma rad_pos:0<radF g:=by unfold radF feeG; have he:=ratePos _ g.positiveB g.b; positivity
lemma savings (ht:1≤K):∃ C:ℝ,0≤C∧∀ (m:Side),g.roundZ ≤(CSide m B).val→∀ M:Male, Screen (pWorks m B e g.p) (partQ m B e g.p n K) n (fun x=> song m B (g.cost m M) x.val.1 x.val.2) (radF g) C:=by
 obtain ⟨D,d,H⟩:=star_cost n (zero_le_one.trans ht) B
 obtain ⟨C,c,Q⟩:=spritz n D (ht.trans d) g.sprawls g.guardV g.positiveB g.positiveW
 obtain ⟨u,v,T'⟩:=cores B K n ht
 obtain ⟨z,hz,p⟩:=stash u v n (show 0< rateK g.a g.b/2 / feeG (8*B.val) from by unfold feeG; have he:=ratePos _ g.positiveB g.b; positivity)
 let S:=feeG (8*B.val); have hp:0<S:=by unfold S feeG; positivity
 refine ⟨z*(S*C),by positivity,fun m h M=>?_⟩
 let Y:= lag m B e g.p; let A:=portCast (m:=m) g.topB g.baseY.1
 have he:Continuous A:=by
   apply Continuous.subtype_mk
   let P:=fete m B e g.p; let F:= fun i:P=> (i.val.1.val.1,i.val.2); let B':=fun i:P=> i.val.1.val
   have ht: Continuous B':=continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)
   have hF: Continuous F:=(continuous_fst.comp ht).prodMk (continuous_snd.comp continuous_subtype_val)
   refine ((continuous_fst.comp ht).prodMk (Continuous.prodMk ?_ (continuous_snd.comp ht)))
   exact (starfish_c g.topB g.baseY.1).comp_continuous (f:=F) hF (fun x=> ⟨x.val.1.property.1,popT x⟩)
 let F:=fun x:fete m B e g.p=> g.cost m M (A x).val.1 (A x).val.2.1 (A x).val.2.2
 let a:= rateK g.a g.b/2
 have hx : Screen Y.botL (partRose m B e g.p n K) n F (a/S) (S*C):=by
   apply Screen.leaps (Ω:=partRose m B e g.p n K) (F:=fun x=>(g.cost m M) x.val.1 x.val.2.1 x.val.2.2) (Φ:=foam _ (8*B.val)) (b:=foamK _ _ _) (c:=Y.botL) (a:=a) (Q (m*g.K) (CSide m B) (knot_coarse g.sprawls g.guardV g.chosen.symm) (g.clock.trans h) M) (foams _ (mul_pos (show 0<8 by decide) B.property) _) A he c (div_nonneg (half_pos (ratePos _ g.positiveB _)).le hp.le) (le_of_eq (div_mul_cancel₀ _ hp.ne')) ?_ ?_ ?_
   · intro T x y h; refine ⟨fun i f r=> h.1.1 i (foam_in _ _ T f) (foam_in _ _ T r), honor _ _ T h.2 h.1.1,h.1.2.less (foam_in ..)⟩
   · intro x t; let z:= (Y.botL.dress t x); refine ⟨t, Subtype.ext ?_⟩; let U:=starG g.topB g.baseY.1 x.val.1.property.1 (popT x) t
     exact Prod.ext rfl (Prod.ext U rfl)
   intro E _ _ _ V t f p x hx; obtain ⟨h₁,h₂,h₃⟩:= p x hx
   exact ⟨fun i=>(h₁ i).mono d,H E _ _ _ _ h₁ h₃ _ _ g.baseY.1 (f x).val.1.property.1 (popT (f x)) g.topB,fun i=>(h₂ i).mono d⟩
 letI : LocallyCompactSpace ↑(Brace.Chord m B e g.p):= art_c
 have hy:= screen_mean Y (T' m e g.p) hx rate_cap (fun T x=>nick T x) (fun T x y h=> nick_c x y T h) (fun T x=> ⟨fun _ _ _=>rfl,fun _ _=>rfl⟩) hz (fun T w f=> p w f _ _ (rate_cap T))
 convert hy using 1
 swap; rfl
 funext x; unfold means song; apply integral_congr_ae; apply Eventually.of_forall; intro y;
 let z:ℝ:=law m B x.val.1 y; by_cases h:z≠0
 · unfold cream; dsimp only; rw [sampler_p F (x,y) h]; unfold herald; rw [Complex.real_smul]; rfl
 rw [not_not] at h; unfold cream herald; change (z:ℂ)* _= z • _; rw [h, zero_smul]; simp
end YM.CF.Jet
