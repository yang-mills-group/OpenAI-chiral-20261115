import YM.CF.Rink.Spin
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Rink
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch MeasureTheory NormedSpace Nacre Braid Font
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Push.Uniform (curve Slope tint partSpace meetVar)
open AnalyticBridge.Annulus1AD AnalyticBridge.SectorAffine Oriented Esti Vol Bloch Exterior Jet
open RG Forge Cay Slate Rel
open Arena Tarn Reef
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
local notation "G"=> SU.group
variable {c f:Side}{S:StepData c f}{T:Tube SU.group S}{F:Forest S.ratio}{q:Chi}{s:Signed}{l n:ℕ}{x d β C D σ m:ℝ}{P:Tab S}{V:Config SU.group c}
variable {K:Teller G}
open AnalyticBridge.GaussianFieldAlignment Tensor Orthogonal PhysicalNext.OrderedAffine2B.SymRows Channels Locations
open scoped ENNReal
lemma preserve_q: MeasurePreserving qG SU.group.probHaar SU.group.probHaar:= MonoidHom.measurePreserving (f:=qG.toMonoidHom) icyC qG.surjective rfl
section
open MeasureTheory Set
lemma ratio_f{B:ChartRatio G}(h:LocalRatio B){x: Ox}(hx:x∈ball 0 B.radius): B.J (frolic x)=B.J x:= by
 let u(x:Ox):= B.scale*B.J x
 have he{a:Ox}(p:a∈ball 0 B.radius): frolic a∈ball 0 B.radius:=by simpa using p
 have hh{x:Ox}(hp:x∈ball 0 B.radius):B.J (frolic x)≤ B.J x:=by
    apply le_of_mul_le_mul_left _ h.scale; refine price_le_of_caps (s:=ball 0 B.radius) (isOpen_ball.mem_nhds hp) (u:=u) (v:=u∘frolic) (continuousAt_const.mul (h.germ x hp).continuousAt) ((continuousAt_const.mul (h.germ (frolic x) (he hp)).continuousAt).comp frolic.continuous.continuousAt) (mul_pos h.scale (h.pos _ hp)).le ?_; intro T hT hB
    let W:=frolic '' T; let F:= LinearIsometryEquiv.ofSurjective frolic (fun q=> ⟨frolic q,fiz2 _⟩); have hw :W ⊆ ball 0 B.radius:=by rintro _ ⟨a,x,rfl⟩; exact he (hB x)
    have hZ :MeasurePreserving F volume volume:= F.measurePreserving
    have ht:=hZ.setLIntegral_comp_emb F.toHomeomorph.measurableEmbedding (fun y=>ENNReal.ofReal (u y)) T
    change (∫⁻ y in T, ENNReal.ofReal (u (frolic y)))= ∫⁻ y in W, ENNReal.ofReal (u y) at ht; change (∫⁻ y in T, ENNReal.ofReal _)=∫⁻ y in T,ENNReal.ofReal (u (frolic y)); rw [ht]; unfold u; rw [← cap_price h _ hT hB,← cap_price h W (hT.image frolic.continuous) hw]
    have hp: SU.group.lieExp '' W=qG ⁻¹' (SU.group.lieExp '' T):=by
       ext a; constructor
       · rintro ⟨_,⟨y,b,rfl⟩,rfl⟩; exact ⟨y,b,by rw [cool_a,q0]⟩
       rintro ⟨y,b,e⟩; exact ⟨frolic y,Set.mem_image_of_mem _ b,by rw [cool_a,e,q0]⟩
    rw [hp, preserve_q.measure_preimage (hT.image SU.group.lieExp_cont).measurableSet.nullMeasurableSet]
 exact le_antisymm (hh hx) (by simpa [fiz2] using hh (he hx))
lemma log_p{R:ChartRatio G}{t:ℝ}(p: LocalRatio R)(h:0<t)(hp:4*t < R.radius)(q:Chi)(x:Ox): logGuard q R t (frolic x)=logGuard q R t x:=by
 unfold logGuard; rw [show broad q (2*t) (frolic x)=broad q (2*t) x from by simp [broad]]; by_cases he:broad q (2*t) x=0; simp [he]; have hh:= broad_span q (mul_pos (by norm_num) h) x he; rw [ratio_f (x:=x) p (mem_ball_zero_iff.mpr (by linarith))]
end
open AnalyticBridge.GaussianFieldAlignment Tensor Orthogonal PhysicalNext.OrderedAffine2B.SymRows Channels Locations Gauges
lemma witnessP (A:Stores S)(s:Signed)(b: Site c)(i:Bond f)(m:ℕ): witnesses (Locations.book s b A) m i ↔ witnesses A m (sendEdge s (S.ratio.embed b) i):=by
 have hp(A:Stores S)(i:Bond f) : witnesses A m i ↔ ∃ j∈Next.SectorChange.points S i,j∈A.dome m:=by simp [witnesses,Next.SectorChange.points]
 rw [hp,hp,Tensor.moves_points]; simp only [Set.exists_mem_image,dome_map]
lemma prod_p{ι P α:Type*}[Fintype ι][Fintype P][CommMonoid α](f:ι≃P)(X:Finset ι)(Z:Finset P)(e:∀ i,i∈X↔f i∈Z)(Q:ι→α)(B:P→α)(h:∀ i∈X,Q i=B (f i)): ∏ i∈X,Q i=∏ i∈Z,B i:=by rw [← show Finset.map f.toEmbedding X=Z from by ext i; obtain ⟨j,rfl⟩:= f.surjective i; simpa using e j, prod_map]; exact prod_congr rfl h
variable (T: Tube G S)(x:ℝ)(q:Chi)(d:ℝ)(l:ℕ)(β:ℝ)(r:ℕ)(A:Stores S)(s:Signed)(b:Site c)(g:Site c→ SU.group.El)(M:Monk G S)
section
open Primitives.HaarLogJets.Guard
variable (h:K.Funds S T)(p: FreeResolvent.Gap (baseX T x M.key M.park M.k M.V) m)(hm:0 < m)(hf:120 ≤ radiusB x)(R: ChartRatio SU.group)(e:LocalRatio R)(u:0<d)(v:4*d<R.radius)
include h p hm hf e u v
lemma pearl_c: (clue S s b M).copper x T (Locations.book s b A) q d l β R r=M.copper x T A q d l β R r:=by
 let F:=clue S s b M; let C:= canE x s b M; let Y:=page s b M; let B:=Locations.book s b A; let L:= (r+104)*radiusB x
 have he(i:Active F.key x F.park): i∈locals F.key B x F.park L ↔ C.onKey i∈locals M.key A x M.park L:=by
    unfold locals; erw [mem_filter,mem_filter,and_iff_right (mem_univ _), and_iff_right (mem_univ _)]; exact witnessP A s b i.val.val L
 let f:=tape (F.fuel x T q d l β); let z:=tape (M.fuel x T q d l β); have hh(i:F.zoo x): f i=Y i.val.val (z (C.onKey i)):=by unfold f F; rw [space_f T x q d l β s b M h p hm hf]; exact move_tape (onBond Y) C.onKey (M.fuel x T q d l β) i
 refine congrArg₂ (·*·) (prod_p C.onKey _ _ he (extended q R d ∘ f) (extended q R d ∘ z) ?_) (prod_p C.onKey _ _ he (broad q d ∘ f) (broad q d ∘ z) ?_)
 · intro i t; unfold Function.comp; rw [hh]; change Real.exp (logGuard q R d (Channels.scatter s (S.ratio.embed b) (replica S.ratio M.V) i.val.val _))=Real.exp _; unfold Channels.scatter; split; exact congrArg Real.exp (log_extended_turn _ true q u e v _); rfl
 intro i t; unfold Function.comp; rw [hh]; simp [broad]
lemma pearl_g:(shiftZ g M).copper x T A q d l β R r=M.copper x T A q d l β R r:=by
 let F:= shiftZ g M; let f:=tape (F.fuel x T q d l β); let z:=tape (M.fuel x T q d l β); let Y:= Gauges.rotating (constantGauge g S.ratio); let X:=locals M.key A x M.park ((r+104)*radiusB x)
 have he(i:Active M.key x M.park):f i= Y i.val.val (z i):=by unfold f F; rw [buzz g M q x β d h l m p hm hf]; exact move_tape (onBond Y) (Equiv.refl (M.zoo x)) (M.fuel x T q d l β) i
 refine congrArg₂ (·*·) (prod_p (Equiv.refl _) X X (fun _=> Iff.rfl) (extended q R d ∘ f) (extended q R d ∘ z) ?_) (prod_p (Equiv.refl _) X X (fun _=>Iff.rfl) (broad q d ∘ f) (broad q d ∘ z) ?_)
 · intro i t; unfold Function.comp; rw [he]; exact congrArg Real.exp (log_extended_turn _ false q u e v _)
 intro i t; unfold Function.comp; rw [he]; simp [broad]
lemma pearl_f(H:Reef.Rare T.up):(cedar M).copper x T A q d l β R r=M.copper x T A q d l β R r:=by
 let F:=cedar M; let f:=tape (F.fuel x T q d l β); let z:=tape (M.fuel x T q d l β); let X:= locals M.key A x M.park ((r+104)*radiusB x)
 have he(i:Active M.key x M.park): f i=frolic (z i):=by unfold f F; rw [echo_f T x q d l β M h p hm hf H]; exact move_tape (onBond (Char.shiftF _)) (Equiv.refl (M.zoo x)) (M.fuel x T q d l β) i
 refine congrArg₂ (·*·) (prod_p (Equiv.refl _) X X (fun _=> Iff.rfl) (extended q R d ∘ f) (extended q R d ∘ z) ?_) (prod_p (Equiv.refl _) X X (fun _=>Iff.rfl) (broad q d ∘ f) (broad q d ∘ z) ?_)
 · intro i t; unfold Function.comp; rw [he]; exact congrArg Real.exp (log_p e u v q _)
 intro i t; unfold Function.comp; rw [he]; simp [broad]
end
end YM.CF.Rink
