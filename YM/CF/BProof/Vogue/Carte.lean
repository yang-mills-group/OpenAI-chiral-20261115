import YM.CF.BProof.Vogue.Halo
/-! Assemble deterministic Loom. Borel chosen.Basic inherited within Week, no bounded-range
statement in the tag argument. Our seed sums in each component instead of smooth function
of minimum value. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Vogue
open Function Filter MeasureTheory ProbabilityTheory Skye Spire Lattice Wilson Mesh Shore Finset
open scoped Topology BigOperators NNReal ENNReal Classical
variable {K:Type} [Fintype K][Nonempty K]{n:Side}{d u:ℝ}{k r L:ℕ}
def timb (S:Finset (Seat n))(x:Ids n):Sweep n:=((x (greet S (priorP x))).2.1)
def brush(K:Type)[Fintype K][Nonempty K](x:Ids n)(S:Finset (Seat n)): K:= Taste K S (priorP x)
variable (P:Spice n K d u k L)(r:ℕ)
def burn(V:Skye.Orbit n):Pane n:=fun i=> let M:=RG.flags u V.1; let S:=soup M r i; if Bubb M r i then mend (P.P (brush K V.2 S)) (timb S V.2) V.1 i else V.1 i
def conic(V:Skye.Orbit n):Pane n:= gauge (frameP V.2)⁻¹ (burn P r (gauge (frameP V.2) V.1,V.2))
def PatchRamped (M:Finset (Seat n))(x:Pane n)(g:Ids n):Pane n:= fun i=> let S:=soup M r i; if Bubb M r i then mend (P.P (brush K g S)) (timb S g) x i else x i
lemma burnM : Measurable (burn P r):=by
 let S(i):= PatchRamped P r i; letI:MeasurableSpace K:=⊤; letI:MeasurableSingletonClass K:=⟨fun _=> trivial⟩
 have hp(M)(i):Measurable (fun x:Skye.Orbit n=> S M x.1 x.2 i):=by
    unfold S PatchRamped; dsimp only; split; swap; · exact (measurable_pi_apply i).comp measurable_fst
    let D:= soup M r i; have hx:Measurable (timb D):= by
       unfold timb; apply measurable_fst.comp; apply measurable_snd.comp; exact seek _ ((mastM _).comp primeV) _ measurable_id -- tune
    let Y(x:Orbit n):=(timb D x.2,brush K x.2 D); have ht:Measurable Y:= (hx.comp measurable_snd).prodMk (((taste_c _).comp primeV).comp measurable_snd)
    apply mealM (F:=Y) (fun j=> ht (measurableSet_singleton j)) (G:=fun j x=>mend (P.P j.2) j.1 x.1 i)
    exact fun j=> (measurable_pi_apply i).comp ((mine (P.ok _) j.1).meas.comp measurable_fst)
 exact measurable_pi_lambda _ fun i=> mealM (F:=fun x:Orbit n=> RG.flags u x.1) (G:=fun j x=>S j x.1 x.2 i) (fun j=>measurable_fst (RG.flags_measurable_eq ..)) fun j=>hp j i
-- helpers
lemma frameM :Measurable (@frameP n):=measurable_pi_lambda _ fun i=> measurable_snd.comp (measurable_snd.comp (measurable_pi_apply i))
lemma gaugeP : Measurable (Function.uncurry (Lattice.gauge (K:=SU.E) (R:=Per (Cube.More n)))):=by
 apply Continuous.measurable; apply continuous_pi; intro i; change Continuous (fun x: (Seat n→SU.E)×Pane n=> _); unfold Function.uncurry Lattice.gauge; fun_prop
lemma conicM : Measurable (conic P r):=by
 let t(x:Orbit n):=frameP x.2; have ht:Measurable t:= frameM.comp (measurable_snd (α:=Pane n)); let b(x:Orbit n):= (Lattice.gauge (t x) x.1,x.2); have he:Measurable b:= ((gaugeP (n:=n)).comp (ht.prodMk measurable_fst)).prodMk measurable_snd
 let H(x:Orbit n):=((frameP x.2)⁻¹,burn P r (b x)) -- syntax
 have hh:Measurable H:= ht.inv.prodMk ((burnM P r).comp he); exact (Measurable.comp (f:=H) (gaugeP (n:=n)) hh)
lemma brushC(U:Pane n)(t:Ids n)(i:reach n)(s:Sweep n): brush K (bun s t) (soup (RG.flags u (flashA s U)) r i)=brush K t (soup (RG.flags u U) r (lane s i)):=by unfold brush Taste; rw [flagsA, soupS, Finset.sum_map]; congr 1; refine sum_congr rfl fun j v=>?_; change pitch _ (priorP t (boxA s ((boxA s).symm j)))=_; rw [Equiv.apply_symm_apply]
lemma burn_spin (s:Sweep n)(V: Pane n)(t:Ids n)(p:Injective (priorP t)): burn P r (flashA s V,bun s t)=flashA s (burn P r (V,t)):=by
 funext i; rw [flash]; unfold burn; dsimp only; have ht : (RG.flags u (flashA s V))=(RG.flags u V).map (boxA s).symm.toEmbedding:= flagsA ..
 have he : soup (RG.flags u (flashA s V)) r i=(soup (RG.flags u V) r (lane s i)).map (boxA s).symm.toEmbedding:=by rw [ht,soupS];
 unfold Bubb; split; swap; next pH=> rw [if_neg (mt (fun t=> he.symm ▸ map_nonempty.mpr t) pH)]; exact flash ..
 next pH=>
    let S:=soup (RG.flags u V) r (lane s i); have hm:S.Nonempty:=map_nonempty.mp (he ▸ pH); rw [if_pos hm,brushC,he,show timb _ _=s⁻¹*timb S t from ?_,mends,flash] -- eq
    change s⁻¹*(t (boxA s (greet (S.map _) (priorP (bun s t))))).2.1=_; rw [mast_rev _ s _ _ t hm p]; rfl
lemma loom_spin (s:Sweep n)(V: Pane n)(t:Ids n)(p:Injective (priorP t)): conic P r (flashA s V,bun s t)=flashA s (conic P r (V,t)):=by
 unfold conic; simp only [boong,burn_spin _ _ _ _ t p]; rw [revG]; congr 2; funext i; unfold frameP; simp only [bun,man,Pi.inv_apply,map_inv]
lemma conic_g (V:Pane n)(t:Ids n)(g:Seat n→SU.E):conic P r (gauge g V,threadG g t)=gauge g (conic P r (V,t)):=by
 have hh:frameP (threadG g t)=frameP t*g⁻¹:= rfl; unfold conic; simp only [hh,_root_.mul_inv_rev, inv_inv,gauge_sq]; simp; congr 1
lemma noop(V:Pane n)(t:Ids n)(i:reach n)(h:Disjoint (RG.flags u V) (win r i)): conic P r (V,t) i=V i:= by
 have he:burn P r (gauge (frameP t) V,t) i=gauge (frameP t) V i:=by unfold burn; dsimp only; rw [RG.gauge_flags]; exact if_neg fun v=> ((pieV ..).1 v) h
 nth_rw 2 [←noon t V]; unfold conic; exact congrArg (fun v=>(frameP t)⁻¹ i.1 * v * _) he -- tune
end YM.CF.BProof.Vogue
