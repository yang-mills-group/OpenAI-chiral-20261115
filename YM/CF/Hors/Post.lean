import YM.CF.Hors.Lego
set_option autoImplicit false
noncomputable section
namespace YM.CF.Hors
open Function Filter Set Matrix Lattice Wilson RG Precision Pressure Tree Exterior MeasureTheory Metric
 AnalyticBridge.MarginalMultiplier3b1d AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine Char Jet Newt
open Push.SectorMeasure AnalyticBridge.RelativeLogdet.Ink
open Push
open Push.Uniform (curve Slope meetVar Positions upperCol lowerCol block meet_derivative bolt)
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {P:RG.Patch}{G:Gauge}{c f:Side}{S:StepData c f}{T:Tube G S}{K:Teller G}{F:Forest S.ratio}{X E B:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup B][NormedSpace ℝ B]{t x s D A C Q V r:ℝ}{i n l:ℕ}
open Push.Uniform (address Primary tint)
open Next.SectorChange Next.SectorChange.Wisps PatchReads
abbrev touchH(D:ℕ)(L:Side):ℕ:=L.val*D+L.val
abbrev coverX(T:Tube G S)(x:ℝ)(F:Forest S.ratio) (i:ℕ)(a:Primary c G): Finset (Key F G):= Finset.univ.filter fun j => separation (address F G (.inl a)) (address F G (.inr j)) ≤ touchH ((i+1)*radiusB x) S.patch.L
def raised(G:Gauge)(L:Side)(B:ℕ):ℝ:= let D:=touchH B L; (Uniform.townCost G)*((D:ℝ)+D+1)^4
lemma lit(F:Forest S.ratio)(L:ℕ)(o:Site f): ((Finset.univ.filter fun i:Key F G=> separation o (address F G (.inr i)) ≤ touchH L S.patch.L).card:ℝ) ≤ raised G S.patch.L L:=by
 classical
 let U:=L*S.patch.L.val -- use cover as biUnion bound
 let r:=touchH L S.patch.L; let K:=Finset.univ.filter fun i:Key F G=> separation o (address F G (.inr i)) ≤ r; let M:ℕ:=Uniform.townCost G
 let S':= halo r {o}; let Z(j:Site f):= Finset.univ.filter fun i:Key F G=>address F G (.inr i)=j
 have hh:K ⊆ S'.biUnion Z:=fun i hi=>Finset.mem_biUnion.mpr ⟨_,halo_spec.mpr ⟨_,Finset.mem_singleton_self o,(Finset.mem_filter.mp hi).2⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩⟩
 have hv:S'.card ≤ (r+r+1)^4:= by simpa [S'] using Corona.halo_size ({o}:Support f) r
 have hz := ((Finset.card_le_card hh).trans (Finset.card_biUnion_le ..)).trans (Finset.sum_le_sum (g:=fun _=> M) (fun i _=> show (Z i).card ≤ M from (Uniform.town F).comp Sum.inr_injective i)); simp only [Finset.sum_const,nsmul_eq_mul] at hz
 change (K.card:ℝ) ≤ _; unfold raised; dsimp only
 rw [mul_comm]; exact_mod_cast hz.trans (Nat.mul_le_mul_right _ hv)
lemma sail (hr:PatchReads.Ready T x)(k:S.Choices)(j:ℕ) (s:ℝ)(F:Forest S.ratio)(L:ℕ)(o:Site c)
 {u v:Mast G c}(ht: Next.Fluctuations.AgreeNear id o L (facadeX G (s•u)) (facadeX G (s•v))) : Scan S x o L (bareStores S) (bareStores S) F F k k (facadeX G (s•u)) (facadeX G (s•v)) 1 1:= ⟨fun _ _=> Iff.rfl,fun _ _=>rfl,fun _ _=>rfl,fun _ _=>Iff.rfl, ht,fun _ _ _ _=>rfl⟩
lemma lokal (hr:PatchReads.Ready T x)(k:S.Choices)(j:ℕ)(s:ℝ)(F:Forest S.ratio)(q:Chi)(d:ℝ)(u v:Mast G c)(i:Key F G):
 let L:= (j+1)*radiusB x; let A(z:Mast G c):= orbitP T x (facadeX G (s•z)) k (bareStores S) F q d 1 j (pageX F x i)
 (∀ y, separation (address F G (.inr i)) (address F G (.inl y)) ≤ touchH L S.patch.L → u y=v y) → A u=A v:=by
 intro L A h; apply orbitX hr q d j (sail hr k j s F L _ ?_) rfl
 intro e he; let z:=address F G (.inr i); have hb: separation (S.ratio.parent z) e.1 ≤ L:=he
 have hx: hull G c (s•u) e = hull G c (s•v) e:=by
    ext a; let y: Primary c G:=((e.1,Exterior.coord e.2),a); change s*u y=s*v y
    rw [h]; apply (separation_triangle _ (S.ratio.embed (S.ratio.parent z)) _).trans
    change _ + separation _ (S.ratio.embed e.1) ≤ _
    rw [FreeResolvent.Mid.upto]; have ht:=Nat.mul_le_mul_left (S.ratio.count.val) hb; have he:=Corona.near S.ratio z; unfold touchH; change _ ≤ S.ratio.count.val * L + S.ratio.count.val; change separation z _ + _ ≤ _ ; omega
 unfold facadeX increment; rw [hx]
lemma glide (hr:PatchReads.Ready T x)(k:S.Choices)(j:ℕ)(s:ℝ)(F:Forest S.ratio)
 (m:Mast G c→ Fish (Key F G))(q:Chi)(d:ℝ)(h:∀ y, ‖y‖<1→ orbitP T x (facadeX G (s•y)) k (bareStores S) F q d 1 j=leaveX F x (m y)) (x':Mast G c)(hq:‖x'‖<1)(hd:ContDiffAt ℝ 1 m x')(i:Primary c G): ∀ t, t ∉ coverX T x F j i → glance m i x' t=0:=by
 classical
 intro t ht; let W:=ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : Key F G=> ℝ) t
 have hh:=hd.differentiableAt (by simp); have hw: glance m i x' t=Uniform.entry (W ∘ m) x' (k:=1) (fun _=>i):=by -- tune
    unfold Uniform.entry; rw [iteratedFDeriv_one_apply,fderiv_comp _ W.differentiableAt hh, W.fderiv]; rfl
 rw [hw]; apply Uniform.Requests.zero (s:=ball 0 1) (l:=address F G ∘ Sum.inl) (y:=address F G (.inr t)) (R:=touchH ((j+1)*radiusB x) S.patch.L) ?_ (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hq)) (by norm_cast; exact W.contDiff.contDiffAt.comp _ hd) _ 0 ?_
 · intro u hu v hv he; refine le_antisymm ?_ ?_ <;> apply Eq.le
   all_goals have hj:= lokal hr k j s F q d u v t he; dsimp only at hj; rw [h _ (mem_ball_zero_iff.mp hu), h _ (mem_ball_zero_iff.mp hv)] at hj; change (m u) t=(m v) t at hj
   · exact hj
   exact hj.symm
 rw [separation_comm]; simpa [coverX] using ht
end YM.CF.Hors
