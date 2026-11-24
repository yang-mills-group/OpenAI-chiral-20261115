import YM.CF.Vol.Hang
set_option autoImplicit false
noncomputable section
namespace YM.CF.Vol
open Function Filter Set Matrix Lattice Wilson RG Precision Pressure Tree Exterior MeasureTheory Metric
 AnalyticBridge.MarginalMultiplier3b1d AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine Char Newt
open Push.SectorMeasure AnalyticBridge.RelativeLogdet.Ink
open Push Push.Uniform Hors Finset Laurent Bloch
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {P:RG.Patch}{G:Gauge}{c f:Side}{S:StepData c f}{T:Tube G S}{K:Teller G}{F:Forest S.ratio}{X E B:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup B][NormedSpace ℝ B]{t x s D A C Q V r:ℝ}{i n l:ℕ}
section geom -- path linear
private lemma tour (x y:Cover): (route x y 1).length=size (y-x):=by
 have he:allAxes 1 = [0,1,2,3]:=by decide
 simp [route,axisRoute,he,size,Fin.sum_univ_succ,straight,Axis]
private lemma log_size (L:Side)(x:Site L):size (lift x) ≤ 4*L.val:=calc
 _ ≤ ∑ _i:Axis,L.val :=sum_le_sum fun i _ => by have he:=lift_centers x i; omega
 _ = _ :=by simp [Axis]
private lemma arch(L:Side)(z:Site L)(u:Cover) : ((route (lift z) (L.val • u) 1).length:ℝ) ≤ 4*(L.val:ℝ)*(1+size u):=by
 rw [tour]; have he:= Laurent.size_add (L.val • u) (-lift z); have ht:size (L.val • u)=L.val*size u :=by simp [Laurent.size,Pi.smul_apply,Int.natAbs_mul, Finset.mul_sum]
 have hf:(size (L.val • u-lift z):ℝ) ≤ (L.val:ℝ)*(size u)+4*(L.val:ℝ):=by exact_mod_cast le_trans he (Nat.add_le_add ht.le ((size_neg (lift z)).trans_le (log_size L z))) -- tune
 have hx : 0 ≤ (L.val:ℝ)*(size u):=by positivity
 linarith
lemma stems {α:Type}[Fintype α](p:α→ Cover→Walk)(h:∀ i, Injective (p i))(r:ℕ):∃ S:Finset Cover,∀ i k,(p i k).length ≤ r→k∈S:=by
 let W(i:α):=ConnectedActivityE6.Blaze.bought_walk r (p i) (h i); exact ⟨Finset.univ.biUnion fun i=> (W i).toFinset, fun i k hk=> mem_biUnion.mpr ⟨i,mem_univ i,(W i).mem_toFinset.mpr hk⟩⟩
end geom
section lift
variable {α β τ:Type}[Fintype α][Fintype β][Fintype τ]
def capP(L:Side):ℕ:= Fintype.card (Site L)*Fintype.card Layers2+ Fintype.card Gain +Fintype.card (TypeFace 1)+ Fintype.card Layers2
private lemma fusion {o:α→ Co c β}(p:Injective o)(h:Fintype.card β ≤ l): Multiplicity (fun i=>(o i).1) l:=by
 intro x; apply le_trans _ h; rw [← Finset.card_univ]
 exact card_le_card_of_injOn (fun i=>(o i).2) (fun _ _ => mem_univ _) (fun i hi j hj he=>p (Prod.ext ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm) he))
lemma wheelH.mono {W:E→ α→ β→ Pay G}{x:E}(h:wheelH W n x C)(p:C ≤ D):wheelH W n x D:= ⟨fun _ _ v H i=> ((h.1 _ _ v H i).mono (mul_le_mul_of_nonneg_right p v)), fun _ _ v H i=> ((h.2 _ _ v H i).mono (mul_le_mul_of_nonneg_right p v))⟩
lemma avoids(K:Teller G)(L:Side)(C:ℝ)(h:‖(1:G.Mat)‖ ≤ C)(n:ℕ):∃ D,0<D∧∀{c f:Side}{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E](U:E → Config G c)(x:E), (∀ i:Bond c, Allows n (fun y=> G.mat (U y i)) x C) →∀ S:StepData c f, S.patch.L=L→∀ T:Tube G S, K.Funds S T →∀ i,
 wheelH (fun y=> T.Φ i (U y)) n x D  ∧ wheelH (fun y=>T.Φ' i (U y)) n x D ∧ wheelH (fun y=>T.N i (U y)) n x D:=by
 obtain ⟨Z,hZ,hF⟩:=trek G (A:=|K.C|) (L:=4*(L.val:ℝ)) K.width (by positivity) (abs_nonneg _) ((norm_nonneg _).trans h) n (capP L)
 refine ⟨max Z 1,lt_of_lt_of_le zero_lt_one (le_max_right ..),?_⟩
 intro c f E _ _ U x H S ht T hp i
 obtain ⟨hI,hN,hT,-⟩:=hp.crosses
 let L':= max Z 1; have hL:1 ≤ (L.val:ℝ):=Nat.one_le_cast.mpr L.property
 subst L; let L:=S.patch.L
 let q:= Work.E03.meshEquiv c; let v:= Work.E03.meshEquiv f; let p:Twin f→ Co c (Co L Layers2):=fun i=> (S.ratio.parent (mesh i).1,S.ratio.residue (mesh i).1,(mesh i).2)
 have hq:Multiplicity (fun i=>(q i).1) (capP L):=fusion q.injective (by unfold capP; omega)
 have hx {α β : Type}[Fintype α] (o:α→ Co c β) (X:Row β Layers2) (hX:X.strip K.η K.C)(h:Multiplicity (fun i=>(o i).1) (capP L)):wheelH (fun y u v=> lane i L.val (U y) X (o u) (q v)) n x L':=by
    let W(k:Cover):= route 0 k 1; have he : Injective W:= fun j k h=> Eq.trans (route_end 0 j 1).symm ((congr_arg (stop (0:Cover)) h).trans (route_end ..))
    obtain ⟨B,hb⟩:=stems (fun _:α=>W) (fun _=>he) i
    exact (hF U x H _ _ h hq (fun i=>(o i).1) (fun _=> W) B (fun j k=>by
       unfold W; rw [tour, sub_zero]; exact le_trans (le_add_of_nonneg_left zero_le_one) (le_mul_of_one_le_left (by positivity) (by linarith only [hL])) ) (fun i j=>X (o i).2 (q j).2) (fun i j k=> (stipend hX ..).trans (mul_le_mul_of_nonneg_left (le_abs_self K.C) (Real.exp_pos _).le)) i L.val (fun i j he=> hb i j ((Nat.le_mul_of_pos_right _ L.property).trans he))).mono (le_max_left ..)
 refine ⟨?_,hx (o:= Work.E03.poleEquiv c) _ hI (fusion (Work.E03.poleEquiv c).injective (by unfold capP; omega)), hx (α:=Co c Gain) (Equiv.refl _) _ hN (fusion (Equiv.refl _).injective (by unfold capP; omega))⟩ -- tune explicit args
 let P:=S.ratio; have hg:Injective p:=by
    intro i j h; apply v.injective; refine Prod.ext ?_ (congr_arg (fun x=> x.2.2) h); apply S.ratio.splitSites.injective; rw [← S.ratio.unpack,← S.ratio.unpack]; exact Prod.ext (show (p i).1=(p j).1 from congr_arg Prod.fst h) (show (p i).2.1=(p j).2.1 from congr_arg (fun x=>x.2.1) h) -- tune

 let W(j:Twin f)(k:Cover):= route (lift (p j).2.1) (L.val • k) 1
 obtain ⟨B,hb⟩:=stems W (fun i j l h=> (smul_right_injective _ S.patch.L.property.ne') (show L.val • j=L.val • l from Eq.trans (route_end _ _ 1).symm ((congr_arg (stop (lift (p i).2.1)) h).trans (route_end ..)))) i
 have hw:Multiplicity (fun i=>(p i).1) (capP L):=fusion hg (by unfold capP; change Fintype.card (Site L × Layers2) ≤ _; rw [Fintype.card_prod]; omega)
 let g(y:E):=replica P (U y); have hy(i:Bond f):Allows n (fun y=> G.mat (g y i)) x C:=by unfold g replica; split; exact allows_const _ (by rw [G.mat_one]; assumption); exact H _
 have hh(h':E)(i':Twin f)(j:Twin c): T.Φ i (U h') i' j=∑' k:Cover, (if (W i' k).length*1 ≤ i ∧ (q j).1=(p i').1+wrap c k then rated (g h') (mesh i').1 (W i' k) (T.R.mf (p i').2 (q j).2 k) else 0):=by -- tune
    unfold Tube.Φ leap; refine tsum_congr fun k=>?_ ; rw [mul_one]; rfl
 change wheelH (fun y i' j=> T.Φ i (U y) i' j) n x _; simp_rw [hh]; exact (hF g x hy _ _ hw hq (fun j=>(mesh j).1) W B (fun j k=>arch S.patch.L (p j).2.1 k) (fun i j=> T.R.mf (p i).2 (q j).2) (fun i j k=> (stipend hT ..).trans (mul_le_mul_of_nonneg_left (le_trans (div_le_self (show 0≤ K.C from by have h:= hI (coord 0) (.inl (plaquette ⟨(0,1),by decide⟩)); exact (tsum_nonneg h.1).trans h.2.2) (one_le_pow₀ hL)) (le_abs_self _)) (Real.exp_pos _).le)) i 1 (fun i j he=> hb i j (by simpa using he))).mono (le_max_left ..) -- simp η func T.Φ partial
end lift
end YM.CF.Vol
