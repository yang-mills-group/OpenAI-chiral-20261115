import YM.CF.Neige.Morse
set_option autoImplicit false
noncomputable section
namespace YM.CF.Neige
open Char Summit
open Function Filter Set Matrix Lattice Wilson RG Precision Pressure Tree Exterior MeasureTheory Metric Newt Jet
 AnalyticBridge.MarginalMultiplier3b1d AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine
 AnalyticBridge.NonflatCovarianceLocality.Matching
open Push.SectorMeasure Next.Fluctuations Next.SectorChange Next.SectorChange.Wisps Next.SectorChange.Schur PhysicalNext.JointLoad PatchReads
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {P:RG.Patch}{G:Gauge}{c f:Side}{S:StepData c f}{T:Tube G S}{A A':Stores S}{F F':Forest S.ratio}{k k':S.Choices} {V W:Config G c}{x C:ℝ}{r l:ℕ}
 {Y: LinkArray G (Frozen A x F)}{Y':LinkArray G (Frozen A' x F')}{o:Site c}
variable {α E:Type} [Fintype α][DecidableEq α] [NormedAddCommGroup E][NormedSpace ℝ E] {p:α→Site c}{a:ℕ} {K v d s t:ℝ} {n:ℕ}
open Finset Filter
open AnalyticBridge.RelativeLogdet Ink
variable {θ m U D v':ℝ}{q:Chi} {i j:Rows.In x A F (G:=G)}{i' j':Rows.In x A' F' (G:=G)} {M N: Gaussian.Table (Rows.In x A F (G:=G))}{M' N':Gaussian.Table (Rows.In x A' F' (G:=G))}
lemma Names.plus (p:Names M l)(h: Names N l): Names (M+N) l:=by refine ⟨fun i j hh=>?_⟩; rw [Matrix.add_apply,p.rank _ _ hh,h.rank _ _ hh,add_zero]
lemma Names.less (p:Names M l)(h: Names N l): Names (M-N) l:=by refine ⟨fun i j hh=>?_⟩; rw [Matrix.sub_apply,p.rank _ _ hh,h.rank _ _ hh,sub_self]
lemma Names.scaling (t:ℝ)(p:Names M l): Names (t • M) l:=by refine ⟨fun i j hh=>?_⟩; rw [Matrix.smul_apply,p.rank _ _ hh,smul_zero]
lemma lanes_one(l:ℕ): Names (1: Shelf (Rows.In x A F (G:=G))) l:=by refine ⟨fun i j hh=>?_⟩; rw [one_apply,if_neg (fun ht=>by subst ht; rw [separation_self] at hh; omega)]
lemma Sample.less (p:Sample k V Y r M k' W Y' M')(h:Sample k V Y r N k' W Y' N'):Sample k V Y r (M-N) k' W Y' (M'-N'):=by
 intro i i' j j' S hi hj; rw [Matrix.sub_apply,Matrix.sub_apply,p _ _ _ _ S hi hj,h _ _ _ _ S hi hj]
lemma stone_s : Sample k V Y r 1 k' W Y' 1:=fun _ _ _ _ _=>one_eqin
lemma Sample.plus (p:Sample k V Y r M k' W Y' M')(h:Sample k V Y r N k' W Y' N'):Sample k V Y r (M+N) k' W Y' (M'+N'):=by
 intro i i' j j' S hi hj; rw [Matrix.add_apply,Matrix.add_apply,p _ _ _ _ S hi hj,h _ _ _ _ S hi hj]
lemma Sample.scaling (t:ℝ)(p:Sample k V Y r M k' W Y' M'):Sample k V Y r (t•M) k' W Y' (t•M'):=by
 intro i i' j j' S hi hj; rw [Matrix.smul_apply, Matrix.smul_apply,p _ _ _ _ S hi hj]
lemma basic_sr(hr:Ready T x)(h:1000 ≤ radiusB x): Sample k V Y (radiusB x/10) (baseX T x A F k V) k' W Y' (baseX T x A' F' k' W) := fun i i' j j' hh hi hj=> gram_eq hr.rules (hh.lower (by have h:=hr.inputs; omega)) hi hj
lemma basic_n(hr:Ready T x)(h:1000 ≤ radiusB x): Names (baseX T x A F k V) (radiusB x/20):= ⟨fun i j hh=> Char.gram_off hr (fun ht=> hh.not_ge (ball_member ht)) h⟩
-- per interpolation of Gram. need new Cut-window lemma. expose here_p helpers. or adapt
private def hands(h:Scan S x (front A F i) (radiusB x/20) A A' F F' k k' V W Y Y')(hi:PatchReads.lift i=PatchReads.lift i')(j:panels A F i): panels A' F' i':=by
 let J:= h.switch j.val.1 (ball_member j.property)
 let t:Rows.In x A' F' (G:=G):=(J.choose,j.val.2)
 have he:PatchReads.lift j.val=PatchReads.lift t:=Prod.ext J.choose_spec rfl
 exact ⟨t,(meetA hi he).mp j.property⟩
private lemma hands_p(h:Scan S x (front A F i) (radiusB x/20) A A' F F' k k' V W Y Y')(hi:PatchReads.lift i=PatchReads.lift i')(j:panels A F i): PatchReads.lift j.val=PatchReads.lift (hands h hi j).val:=Prod.ext (h.switch j.val.1 (ball_member j.property)).choose_spec rfl
private lemma palp{β:Type}[Fintype β][DecidableEq β]{M: Gaussian.Table α}{N: Gaussian.Table β}{w:α→Set α}{W:β→Set β}{i j:α}{i' j':β}(hp:i∈w i)(hq:i'∈W i')(ht:j∈w i)(hu:j'∈W i')(e:w i≃W i')(he:e ⟨i,hp⟩=⟨i',hq⟩)(hv:e ⟨j,ht⟩=⟨j',hu⟩)(h:Schur.principal M (w i)=(Schur.principal N (W i')).submatrix e e): per w M j i=per W N j' i':=by
 rw [per_read _ _ hp ht, per_read _ _ hq hu,h,Matrix.inv_submatrix_equiv,Matrix.submatrix_apply,he,hv]
private lemma moon (h:120 ≤ radiusB x)(hp: Sample k V Y r M k' W Y' M')(hl:r+2*(radiusB x/20) ≤ l): Sample k V Y l (per (panels A F) M) k' W Y' (per (panels A' F') M'):=by
 intro j j' i i' S' hj hi; by_cases he:j∈panels A F i; swap; · rw [per_zero _ _ he,per_zero _ _ (mt (meetA hi hj).2 he)]
 have hz : separation (front A F j) (front A F i) ≤ radiusB x/20:= by rw [separation_comm]; exact ball_member he
 let H:=S'.shrink (u:=front A F i) (r':=radiusB x/20) (by omega)
 let e:panels A F i≃ panels A' F' i':= { toFun:=hands H hi, invFun:=hands ((faces hi) ▸ H.turn) hi.symm, left_inv:=fun i=>Subtype.ext ((lifting_injective ..) ((hands_p H hi i).trans (hands_p ..)).symm),right_inv:=fun j=> Subtype.ext ((lifting_injective ..) ((hands_p _ _ j).trans (hands_p ..)).symm)}
 have hv (x:panels A F i)(y:panels A' F' i')(v:PatchReads.lift x.val=PatchReads.lift y.val):e x=y:=Subtype.ext ((lifting_injective ..) ((hands_p H hi x).symm.trans v))
 -- hp shrink r from j, need S includes + 2 hops ok
 apply palp (per_self (boards A F G h) i) (per_self (boards A' F' G h) i') he ((meetA hi hj).1 he) e (hv _ _ hi) (hv _ _ hj)
 ext x y; have hh: separation (front A F j) (front A F x.val)  ≤  radiusB _/20+ radiusB _/20:= (separation_triangle _ (front A F i) _).trans (Nat.add_le_add hz (ball_member x.property)) -- metavars
 exact hp _ _ _ _ (S'.shrink (by omega)) (hands_p H hi x) (hands_p H hi y)
lemma perPt(t:ℝ)(hr:Ready T x)(h:1000 ≤ radiusB x): Sample k V Y (radiusB x) (perZ T x k A F V t) k' W Y' (perZ T x k' A' F' W t):=by
 unfold perZ stepM pie; simp only [zero_smul,add_zero]
 exact moon (le_trans (by norm_num) h) (stone_s.plus (((basic_sr (A:=A) (V:=V) (W:=W) hr h).less stone_s).scaling t)) (by omega)
lemma perN(t:ℝ): Names (perZ T x k A F V t) (radiusB x/20):=by
 unfold perZ stepM pie; simp only [zero_smul,add_zero]
 exact ⟨fun i j hp=> per_zero _ _ fun h=>hp.not_ge ((separation_comm ..).trans_le (ball_member h))⟩
lemma neoN (hr:Ready T x)(h:1000 ≤ radiusB x): Names (neo T x k A F V) (radiusB x):=by
 let e:=basic_n (V:=V) (k:=k) (A:=A) (F:=F) hr h
 have he :=tooth hr (V:=V) (k:=k) A F; exact ((((he.turnt.maps e).maps he).under (by omega)).less (lanes_one ..)) -- tune
lemma neo_pt(hr:Ready T x)(hp:1000 ≤ radiusB x): Sample k V Y (4*radiusB x) (neo T x k A F V) k' W Y' (neo T x k' A' F' W):=by
 let L:=radiusB x; have hX:=edgeBill hr (V:=V) (W:=W) (k:=k) (k':=k') (Y:=Y) (Y':=Y'); let M:=bark x V T k A F; let N:=bark x W T k' A' F'; have ht: Sample k V Y L M.transpose k' W Y' N.transpose:=fun i i' j j' h hi hj=> bark_read hr (h.lower (by unfold L; omega)) hi hj
 have hv:=tooth hr A F (V:=V) (k:=k); have hu:=tooth hr (V:=W) (k:=k') A' F'
 have hP:= tile_mul ht (basic_sr hr hp) hv.turnt hu.turnt (b:=2*L) (by unfold L; omega); exact (tile_mul hP hX (hv.turnt.maps (basic_n hr hp)) (hu.turnt.maps (basic_n hr hp)) (b:=4*L) (by unfold L; omega)).less stone_s
lemma accN(hr:Ready T x)(hp:1000 ≤ radiusB x): Names (acc T x k A F q D Y l V) (radiusB x):=by
 unfold acc; simp only [Function.comp_apply]; have he:= (supportV hr hp l (q:=q) (D:=D) (k:=k) (V:=V) (Y:=Y)).foam; have hp := he.less (lanes_one _); simp only [port,add_sub_cancel_left] at hp; exact hp.under (by omega)
lemma accPt(hr:Ready T x)(hp:1000 ≤ radiusB x): Sample k V Y ((l+46)*radiusB x) (acc T x k A F q D Y l V) k' W Y' (acc T x k' A' F' q D Y' l W):=by
 have hh:= tile_pt (bankPass (Y:=Y) (Y':=Y') (k:=k) (k':=k') (V:=V) (W:=W) (l:=l) (q:=q) (D:=D) hr hp) (supportV hr hp l) (supportV hr hp l) (b:=(l+46)*radiusB x) (by simp only [Nat.add_mul]; omega); have hp:=hh.less stone_s; simp only [port,add_sub_cancel_left] at hp; exact hp
end YM.CF.Neige
