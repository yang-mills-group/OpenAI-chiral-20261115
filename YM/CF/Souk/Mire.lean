import YM.CF.Souk.Blue
/-! Trace-delta norms for true thermal. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Souk
open Function Filter Set Matrix Lattice Wilson RG Precision Pressure Tree Exterior MeasureTheory Metric
 AnalyticBridge.MarginalMultiplier3b1d AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine Char Jet Newt Hors Neige
open Push.SectorMeasure AnalyticBridge.RelativeLogdet.Ink
open Push
open Push.Uniform (curve Slope meetVar Positions upperCol lowerCol block meet_derivative bolt address Primary tint Multiplicity countCost)
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {P:RG.Patch}{G:Gauge}{c f:Side}{S:StepData c f}{T:Tube G S}{K:Teller G}{F:Forest S.ratio}{X E B:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup B][NormedSpace ℝ B]{t x s D A C Q V r:ℝ}{i n l:ℕ}
variable {ι τ:Type} [Fintype ι][Fintype τ] [DecidableEq τ]
open Planned.JetPort
open Next.SectorChange PatchReads Next.SectorChange.Wisps PhysicalNext.JointLoad
variable {k: S.Choices}{X:Config G c→Matrix (Rows.In x (bareStores S) F (G:=G)) (Rows.In x (bareStores S) F (G:=G)) ℝ}
abbrev lathe(x r:ℝ)(F:Forest S.ratio)(X:Config G c→Matrix (Rows.In x (bareStores S) F (G:=G)) (Rows.In x (bareStores S) F (G:=G)) ℝ)(u:Mast G c):= (X (facadeX G (r • u))).submatrix (pageX F x) (pageX F x)
lemma rad(hr:Ready T x)(p:Key F G)(r:ℕ)(u v:Mast G c)(he:∀ i,separation (address F G (.inr p)) (address F G (.inl i)) ≤ touchH r S.patch.L → u i=v i): Scan S x (front (bareStores S) F (pageX F x p)) r (bareStores S) (bareStores S) F F k k (facadeX G (s•u)) (facadeX G (s•v)) 1 1:=by
 apply Hors.sail hr k 0 s F; intro e ht; let z:=address F G (.inr p); have hb: separation (S.ratio.parent z) e.1 ≤ r:=ht
 have hx: hull G c (s•u) e = hull G c (s•v) e:=by
    ext a; let y: Primary c G:=((e.1,Exterior.coord e.2),a); change s*u y=s*v y
    rw [he]; apply (separation_triangle _ (S.ratio.embed (S.ratio.parent z)) _).trans; change _ + separation _ (S.ratio.embed e.1) ≤ _
    rw [FreeResolvent.Mid.upto]; have ht:=Nat.mul_le_mul_left (S.ratio.count.val) hb; have he:=Corona.near S.ratio z; unfold touchH; change _ ≤ S.ratio.count.val * r + S.ratio.count.val; change separation z _ + _ ≤ _; omega
 unfold facadeX increment; rw [hx]
def flagP(p:Side)(L:ℕ):=touchH L p -- aid grammar
lemma receipt (hr:Ready T x)(p:∀ y:Mast G c,∀ z:Mast G c, Sample k (facadeX G (s • y)) 1 l (X (facadeX G (s • y))) k (facadeX G (s•z)) 1 (X (facadeX G (s•z)))) (ht:ContDiffAt ℝ (n+1:ℕ) (lathe x s F X) 0) (i:Fin (n+1)→Primary c G)(a b:Key F G) (he: touchH l S.patch.L< separation (address F G (.inl (i (Fin.last n)))) (address F G (.inr a))): pS (n+1) (lathe x s F X) i 0 a b=0:=by
 rw [sat ht]; let PP:=pageX (G:=G) F x; let f(y:Mast G c):= lathe x s F X y a b
 apply Uniform.Requests.zero (f:=f) (s:=Set.univ) (l:=address F G ∘ Sum.inl) (R:=touchH l S.patch.L) (y:=address F G (.inr a)) ?_ Filter.univ_mem ?_ _ (Fin.last n) (by rw [separation_comm]; exact he.not_ge)
 · intro i _ j _ hi; exact p i j (PP a) (PP a) (PP b) (PP b) (rad hr a _ i j hi) rfl rfl
 let L:Neige.Shelf (Key F G)→L[ℝ] ℝ:= LinearMap.toContinuousLinearMap { toFun:=fun M=>M a b,map_add':=fun _ _=>rfl,map_smul':=fun _ _=>rfl}
 exact L.contDiff.contDiffAt.comp (f:=lathe x s F X) _ ht
lemma tileBill(hr:Ready T x)(p:∀ y:Mast G c,∀ z:Mast G c, Sample k (facadeX G (s • y)) 1 l (X (facadeX G (s • y))) k (facadeX G (s•z)) 1 (X (facadeX G (s•z)))) (ht: Protected (n+1) (lathe x s F X) 0 C)(q:Fin (n+1)→Primary c G): notesP (pS (n+1) (lathe x s F X) q 0) ≤ raised G S.patch.L l*C:=by
 let a:= address F G (.inl (q (Fin.last n))); let H:= Finset.univ.filter fun i:Key F G=> separation a (address F G (.inr i)) ≤touchH l S.patch.L; let Z:=pS (n+1) (lathe x s F X) q 0
 have he: ∑ i, ∑ j,|Z i j|= ∑ i∈H,∑ j, |Z i j|:= by
    refine (Finset.sum_subset (Finset.subset_univ H) ?_).symm; intro i _ hh; refine Finset.sum_eq_zero fun j _=>?_ ; rw [show Z i j=0 from receipt hr p (steep ht) q i j (by simpa [H] using hh),abs_zero]
 unfold notesP; rw [he]; apply (Finset.sum_le_sum (fun i _=> (row_S Z i).trans (scaleS ht le_rfl q))).trans; rw [Finset.sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (lit F _ a) ht.nonneg
lemma can_tags (hp:Protected n (X ∘Vmove x (1:Config G c)) 0 C): Protected n (lathe x (temp x) F X) 0 (composeCost n C (Uniform.shade G)):=by
 let L:= hull G c; let g:=fun y=>X (Vmove x 1 y); have hg: Allows n (fun y=>paintO (g y)) (L 0) C:=L.map_zero ▸ hp -- orientation
 have hv:Allows n L 0 (Uniform.shade G):=allows_linear hull_n (L.map_zero ▸ (le_trans (show ‖(0: Directions G c)‖ ≤ 0 by rw [norm_zero]) ((norm_nonneg _).trans (hull_n (c:=c) (G:=G)))))
 apply (jump_up (leaveX (G:=G) F x) (visitX (G:=G) F x) (visit_n ..) (leave_n ..) (hg.comp hv)).germ; filter_upwards with y; unfold lathe; rw [tableVisit]; unfold facadeX; rw [map_smul]; unfold g Vmove; rfl -- tune
end YM.CF.Souk
