import YM.CF.Broc.Gamma
set_option autoImplicit false
noncomputable section
namespace YM.CF.Broc
open Function Filter Lattice Metric Lat Finset Tenant Branch Fock Dial MeasureTheory Paige Phase Phase.Sample Brace Cube Peaks Tulip Rush Drapes
open scoped Topology Matrix BigOperators Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] opCStarAlgebra
lemma gainW {N P:Side}(G:Ratio N P):Exceed (terr _) (terr _) (poolG G) (feeG G.count.val) (feeG G.count.val):=by
 refine ⟨fun {S} h=> grove_pool G _ h,fun {S} h=> (pool_card G S).trans_eq (mul_comm _ _),?_⟩
 intro z; let S:=bay (terr (More P)) z G.count.val
 refine ⟨cloudG G S,(le_trans (by exact_mod_cast cloud_count G S : ((cloudG G S).card:ℝ)≤ S.card) (Tenant.reach ..)),?_⟩
 intro A _ h; obtain ⟨y,h,g⟩:=mem_biUnion.mp h; exact ⟨y,mem_filter.mpr ⟨mem_univ _,(bay_mem _).mpr ((by rw [(terr _).sym]; exact (bay_mem _).mp g))⟩,h⟩
variable {j:ℕ}{L: Side}{ho:Odd L.val}{T:Script Male}{Y:Pricing j L ho T}{B m r: Side}{e:ℝ}
variable (g:Grasp Y B e)(G: Ratio (CSide m B) (CSide r B))(hc:G.count=L)(k:g.roundZ ≤(CSide m B).val)(M:Male)
def up_g(i:AcreZ m r g G) : Brace.Chord m B e g.p:=⟨(i.val.1.2,i.val.2.2),i.property.cap.cg,i.property.loc⟩
def underK(i:AcreZ m r g G): Brace.Chord r B e g.p:=⟨(i.val.1.1,i.val.2.1),i.property.cap.fg,i.property.mist⟩
def ew(g:Grasp Y B e):ℝ:=feeG (8*B.val)*chargeR' g.ea g.a g.w g.b
def sway(g:Grasp Y B e):ℝ:=rateK g.a g.b /feeG (8*B.val)
lemma ew_n:0≤ ew g:=by unfold ew chargeR'; have he:=rate_nonneg g.a _ g.b g.positiveW.le; unfold feeG; positivity
lemma sway_p:0<sway g:=div_pos (ratePos g.a g.positiveB g.b) (by unfold feeG; positivity)
include k
lemma spun :Seat (bunchS g G) (fun i=>song r B (g.cost r M) i.val.1.1 i.val.2.1) (sway g) (ew g):=by
 let F:=underK g G; have he:Continuous F:=by unfold F underK; fun_prop
 have hc:=teak g (g.clock_fine G k) M
 have hp:=Seat.shop (b:=pWorks r B e g.p) (c:=bunchS g G) (K:=ew g) (a:=sway g) (idemX (terr (Domain r B))) hc F he (ew_n g) (sway_p g).le (by rw [mul_one]) (fun S x y h=> ⟨h.1,h.2.2.1⟩) (fun x t=>⟨t,rfl⟩)
 rw [one_mul] at hp; exact hp
include hc
lemma spores: Seat (bunchS g G) (fun i=>song m B (g.cost m (upMale L ho M)) i.val.1.2 i.val.2.2) (sway g/feeG L.val) (feeG L.val*ew g):=by
 let T:=up_g g G; have he:Continuous T:=by unfold T up_g; fun_prop
 have hW:=gainW G; have hx:= show feeG G.count.val=feeG L.val from congrArg (fun L:Side=> feeG L.val) hc; rw [hx] at hW; have hv:0<feeG L.val:=by unfold feeG; positivity
 apply Seat.shop (c:=bunchS g G) (b:=pWorks m B e g.p) hW (a:=sway g) (teak g k (upMale L ho M)) T he (ew_n g) (div_nonneg (sway_p _).le hv.le) (by rw [div_mul_cancel₀ _ hv.ne'])
 · intro S x y h; exact ⟨fun i u p=> h.2.1 i (cloud_pool G S u) (cloud_pool G S p), h.2.2.2.less (cloud_pool ..)⟩
 intro x y; exact ⟨scaleG G y,rfl⟩

def inkp(g:Grasp Y B e):ℝ:= min (min (sway g/feeG L.val) (sway g)) (Y.A/2)
omit k hc in
lemma ink_pos:0< inkp g:=lt_min (lt_min (div_pos (sway_p _) (by unfold feeG; positivity)) (sway_p _)) (half_pos Y.rate)
def pureS(g:Grasp Y B e): ℝ:= max 1 (quartzK Y.A Y.C)
def inkg(g:Grasp Y B e):ℝ:=pureS g+(‖facet‖*pureS g+‖folio'‖*(feeG L.val*ew g))+(‖facet‖*pureS g+‖folio'‖*ew g)+pureS g
omit k hc in
lemma inkp_price:0< inkg g:=by unfold inkg; have ht:=ew_n g; have hp:0<pureS g:=lt_max_of_lt_left zero_lt_one; unfold feeG; positivity
lemma brink: Seat (bunchS g G) (fun i=> firmL g G i.val M-Matrix.trace (eExp T Y.k M G (post i.val))) (inkp g) (inkg g):=by
 let h : sway g/feeG L.val ≥ inkp g := (min_le_left ..).trans (min_le_left ..)
 let hy: sway g ≥ inkp g:= (min_le_left ..).trans (min_le_right ..)
 have hep:inkp g ≤ Y.A/2:=min_le_right ..
 have hv : quartzK Y.A Y.C≤pureS g:=le_max_right ..
 let A:= (traceH g G hc k _ _ Y.earningsK M).solid hep hv
 let B':= (traceH g G hc k _ _ Y.beauty M).solid hep hv
 let H:= (traceH g G hc k _ _ Y.income M).solid hep hv; let Z:= (traceH g G hc k _ _ Y.projected M).solid hep hv
 let F:=(spun g G k M).solid hy le_rfl; let W:=(spores g G hc k M).solid h le_rfl
 have he:= ( (A.adds ((Z.frameH facet _ le_rfl).adds (W.frameH _ ‖folio'‖ (show ‖folio'‖ ≤ _ from le_rfl)))).adds ((H.frameH facet _ le_rfl).adds (F.frameH folio' _ le_rfl)).minus).adds B'.minus
 change Seat (bunchS g G) _ (inkp g) (inkg g)
 convert he using 1; swap; rfl
 funext i; simp only [firmL,bookL,noteL,Function.comp_apply,facetP,folioT]; abel
end YM.CF.Broc
