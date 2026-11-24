import YM.CF.Jet.Tang
import YM.CF.Broc.Opera
set_option autoImplicit false
noncomputable section
namespace YM.CF.Jet
open Function Filter Metric Lat Finset Tenant Branch Fock Dial MeasureTheory Phase Phase.Sample Lattice Cube Broc Drapes Tulip Peaks Brace Paige
open scoped Topology Matrix BigOperators ContDiff NNReal Matrix.Norms.L2Operator InnerProductSpace
set_option synthInstance.maxSize 8000
attribute [local instance] opCStarAlgebra
variable {j:ℕ}{L B:Side}{ho:Odd L.val}{T:Script Male}{Y:Pricing j L ho T}{e:ℝ}{m r:Side}(g:Grasp Y B e)(he:0<e)(n:ℕ){K:ℝ}
def ridQ (G:Ratio (CSide m B) (CSide r B))(K:ℝ): Draw (AcreZ m r g G):= ⟨fun E _ _ _ S p=> (Me n K Y.e G).test E S (Broc.aqua g G ∘ p)⟩
def twistRate := min (min (radF g / feeG L.val) (radF g)) (Y.A/2)
lemma twist_pos:0<twistRate g:=lt_min (lt_min (div_pos (rad_pos g) (by unfold feeG; positivity)) (rad_pos g)) (half_pos Y.rate)
lemma interior_work (hK:1≤K):∃ c:ℝ,0≤c∧∀{m r:Side} (G:Ratio (CSide m B) (CSide r B)),G.count=L→g.roundZ≤ (CSide m B).val→∀ M, Screen (bunchS g G) (ridQ g n G K) n (fun i=> firmL g G i.val M-Matrix.trace (eExp T Y.k M G (post i.val))) (twistRate g) c:=by
 obtain ⟨v,h,H⟩:= vw (K:=Y.C) n (zero_le_one.trans hK) Y.rate Y.range
 obtain ⟨C,hC,P⟩:= savings g n hK
 let L':= feeG L.val; have hp:0<L':=by unfold L' feeG; positivity
 let W:=v*pureS g; have hw:0≤W:= mul_nonneg (zero_le_one.trans h) (le_max_of_le_left zero_le_one)
 let a:=radF g
 refine ⟨W+(‖facet‖*W+‖folio'‖*(L'*C))+(‖facet‖*W+‖folio'‖*C)+W,by positivity,fun {m r} G he k M=>?_⟩
 have ht (u) (A:Chop Male) (p:IndexB L u u A Y.A Y.C Y.e Y.N): Screen (bunchS g G) (ridQ g n G K) n (fun i=> Matrix.trace (A M G (post i.val))) (twistRate g) W:=by
   have hx:Screen (weave G Y.e) (Me n K Y.e G) n (fun i=> Matrix.trace (A M G (post i.val))) (twistRate g) W:=by
     apply Screen.reserve _ _ (H G (A M G) u (p M G he (g.needed.trans k)))
     · exact min_le_right ..
     exact mul_le_mul_of_nonneg_left (le_max_right ..) (zero_le_one.trans h)
   have hv:=hx.leaps (Ω:=ridQ g n G K) (c:= bunchS g G) (q:=twistRate g) (idemX (terr _)) (Broc.aqua g G) (continuous_subtype_val.subtype_mk _) hw (twist_pos _).le (by simp) (fun _ _ _ p=> p) (fun x y=> ⟨y,rfl⟩) (fun E _ _ _ V h f t=> t)
   rw [one_mul] at hv; exact hv
 have ht1:=P m k (upMale L ho M); have ht2:=P r (g.clock_fine G k) M
 have he' :feeG G.count.val=L':=by rw [he]
 have A:= gainW G; rw [he'] at A
 have hy: Screen (bunchS g G) (ridQ g n G K) n (fun i=> song m B (g.cost m (upMale L ho M)) i.val.1.2 i.val.2.2) (twistRate g) (L'*C):=by
   let f:=up_g g G; have hc:Continuous f:=by unfold f up_g; fun_prop
   apply ht1.leaps (Ω:=ridQ g n G K) (c:=bunchS g G) A f hc hC (twist_pos _).le ( (le_div_iff₀ hp).mp ((min_le_left ..).trans (min_le_left ..))) ?_ ?_ ?_
   · intro S x y h; exact ⟨fun i u p=> h.2.1 i (cloud_pool G S u) (cloud_pool G S p), h.2.2.2.less (cloud_pool ..)⟩
   · intro x y; exact ⟨scaleG G y,rfl⟩
   intro E _ _ _ V h P p x t; exact ⟨(p x t).2.1,(p x t).2.2.2⟩
 have hX: Screen (bunchS g G) (ridQ g n G K) n (fun i=>song r B (g.cost r M) i.val.1.1 i.val.2.1) (twistRate g) C:=by
   let F:=underK g G; have he:Continuous F:=by unfold F underK; fun_prop
   have hL:=ht2.leaps (Ω:=ridQ g n G K) (c:=bunchS g G) (idemX (terr _)) F he hC (twist_pos g).le (by rw [mul_one]; exact (min_le_left ..).trans (min_le_right ..)) (fun S x y h=>⟨h.1,h.2.2.1⟩) (fun x t=>⟨t,rfl⟩) (fun E _ _ _ V h f q x t=>⟨(q x t).1,(q x t).2.2.1⟩)
   rw [one_mul] at hL; exact hL
 let A:= ht _ _ Y.earningsK
 let A':= ht _ _ Y.beauty
 let l:= ht _ _ Y.income; let r':= ht _ _ Y.projected
 have F:= ((A.plus ((r'.lin facet (le_refl ‖facet‖)).plus (hy.lin folio' le_rfl))).plus ((l.lin facet le_rfl).plus (hX.lin folio' le_rfl)).minus).plus A'.minus
 convert F using 1; funext i; simp only [firmL,bookL,noteL,Function.comp_apply,facetP,folioT]; abel
end YM.CF.Jet
