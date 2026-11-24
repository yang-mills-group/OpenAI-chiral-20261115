import YM.CF.Hom.Myrrh
set_option autoImplicit false
noncomputable section
namespace YM.CF.Hom
open Function Filter Lattice Laurent Bloch Wilson Precision RG Work Exterior Next.Free Work.F08 Craft Pressure Stationary Tree
open Reef
open scoped Topology BigOperators ContDiff Matrix Matrix.Norms.Frobenius
local notation "G5"=> SU.group
variable {j:ℕ}{K:KernelChoices}{p q:Clip}{ρ b δ h₀ η a C:ℝ}{n:ℕ}
structure Signets (X:Flight j j)(K:KernelChoices) (T:Towers X.L)(p:Clip)(M U:RG.PathData G5)(α:ℝ) (Y:ChartRatio G5)(Θ ν η:ℝ)(n:ℕ):Prop where
 all (c f:Side)(h:f.val=c.val*X.L.val)(hp:n≤c.val)(F:Forest (X.visitRatio h)):
    let v:= X.visit K h; PriceGap (S:=v) F p M η∧ ∀ z:fieldDir G5 c 1→ AxisChart G5 F, Critical (S:=v) F p M z → ClassicalMatch (S:=v) F p p M U z ∧ FiniteBound (S:=v) F M U p p α Y z Θ ν 1
 existP (c f:Side)(h:f.val=c.val*X.L.val)(hp:n≤c.val)(F:Forest (X.visitRatio h)):
    ∃ z, Critical (S:=X.visit K h) F p M z ∧ Guessed (S:=X.visit K h) F (installed (X.visitRatio h) T.A0) z
private def sizeX(n i:ℕ):Side:= ⟨n+i+1,by omega⟩
variable {σ e f r d w γ:ℝ}{Θ Λ:Side→ℝ}{W: Flight j j}
lemma authorize (S:ChartRatio G5)(x:LocalRatio S)(H:Transition G5 K j η a C p.direct a C p.direct b ρ h₀ d σ γ n Θ Λ)(g:n≤W.L.val) (hs:W.patch.Branches K G5){B V:Bed}{P:Towers W.L}(Y:Paddle W K B V p P a C)(hf:MainIn G5 p B η a C)(hp:MainIn G5 p V η a C) {R:PathData G5}(k:R.Bounds p ρ b δ)(kb:Rare R)(r:Attached B R)(v:ρ≤σ)(hu:Λ W.L≤δ)(hb:1≤δ)(hR:h₀≤b)(hu3: girk 3*h₀≤ b)(hu4:girk 4*h₀ ≤ b)(M:ℕ)(y:∀ (c f:Side)(e:f.val=c.val*W.L.val)(k:M < c.val), Bid.Larger (G:=G5) (W.visit K e))(hE:0<f)(h:∀ (c f':Side)(z:f'.val=c.val*W.L.val)(g:M < c.val)(F:Forest (W.visitRatio z)), PriceGap (S:=W.visit K z) F p R f ∧ ∃ u,Critical (S:=W.visit K z) F p R u ∧ Guessed (S:=W.visit K z) F (installed (W.visitRatio z) P.A0) u ∧ Bid.HeatG (S:=W.visit K z) F p R u V):∃ T:PathData G5, T.Bounds p ρ b δ ∧ Rare T∧Attached V T∧∃ α,|α+SU.group.slopeConstant* Real.log W.L.val|+1≤d ∧ Signets W K P p R T α S (Θ W.L) γ f (M+1):=by
 let C':= sizeX M; let Z(i):= C' i*W.L; have ht(i): (Z i).val=(C' i).val*W.L.val:=rfl
 let T(i):= W.visit K (ht i); have hy(i):M<(C' i).val:=by change _< M+i+1; omega
 choose z hP hQ hJ using fun i (A:Forest (W.visitRatio (ht i)))=> (h _ _ _ (hy i) A).2
 let gX(i):Forest (T i).ratio:=Classical.choice (Tree.select _ W.patch.odd_side); let A:Armada C' Z W.patch K:=⟨ht⟩; let F(i):Forest (A.boot i).ratio:=gX i; let u(i): fieldDir G5 (C' i) 1 → AxisChart G5 (F i):=z i (F i); have hs'(i): Bid.Larger (G:=G5) (T i):= y _ _ (ht i) (hy i)
 have H' : Scud A G5 p p R F u a ρ C b C η δ a C η B V P f := by
    refine ⟨fun i=>y _ _ _ (hy i),⟨hf.1.2.1,hf.1.2.2.2.1,hf.2.1,fun i=> hf.2.2 _⟩,⟨hp.1.2.1,hp.1.2.2.2.1,hp.2.1,fun i=>hp.2.2 _⟩,r,k,?_,fun i=> Y.link (ht i),fun i=> (h _ _ _ (hy i) (F i)).1,fun i=>hP i _,fun i=>hQ i _,fun i=>hJ i _⟩
    intro l hl; have hh:= W.legal; exact (Y.pay.2.2.2 _ (by omega)).1
 obtain ⟨U,α,hx,he,hB,hV,hW,Ht⟩:= H C' Z W.patch A p p R F u B V P δ η f S rfl g (tendsto_atTop_mono (g:=fun i=>(C' i).val) (f:=id) (fun i=>by change i ≤ M+i+1; omega) tendsto_id) le_rfl le_rfl H' hb hE x
 have hz:= hB _ _ _ k.width v le_rfl hu (by linarith)
 obtain ⟨hK,hc⟩:= gem_b hz hR hu3 hu4; refine ⟨solvent U,hK,hc,⟨he.layout⟩,α,hV,⟨fun c f₁ h' hk A' =>?_,fun c f₁ h' hk A'=>?_⟩⟩
 · let jx:= c.val-1-M; have hX : c=C' jx:= Subtype.ext (by change c.val=M+jx+1; unfold jx; omega); -- replace let jx via general
   obtain ⟨i,hi⟩:= (show ∃ i,c=C' i from ⟨jx,hX⟩); clear hX jx; subst c; have ht': f₁= Z i:=Subtype.ext (h'.trans (ht i).symm); subst f₁; intro v; refine ⟨(h _ _ h' (hy i) _).1,fun z' p'=>?_⟩; let u':= z i A'; have hv: u'=ᶠ[𝓝 0] z':= by
      let t: v.Choices:=Classical.arbitrary _; let G5':= (h (C' i) _ h' (hy i) A').1; let s':= hP i A'
      apply Work.F05.station_unique (F:=tested (S:=T i) A' t p R) (p'.2.2 t).1 (fun j hj=> by by_contra x; exact (Work.F05.tested_diag hE G5' t j x).ne' hj) (s'.1 ▸ s'.2.1.continuousAt.tendsto) (p'.1 ▸ p'.2.1.continuousAt.tendsto) (((s'.2.2 t).2).mono fun _ l=> l.fderiv) (((p'.2.2 t).2).mono fun _ l=> l.fderiv)
   have Hg:= Bid.one_for_all (T i) Work.F05.answer (H'.ample i) (F i) p p R U ρ b δ _ hE k S x (z i) (fun F'=> hP i F') (fun F'=> (h _ _ _ (hy i) F').1) (hW i) A'
   refine ⟨Reef.reserve (S:=T i) hs k hz kb p' ((h _ _ _ (hy i) A').1) hE ?_, Reef.rode (transfer_bound (H'.ample i) k x hE p' (hP _ _) ((h _ _ _ (hy i) A').1) ((h _ _ _ (hy i) (F i)).1) (Ht _ _ le_rfl le_rfl i))⟩
   intro j hj t; obtain ⟨h1,h2,h3⟩:= Hg j hj t
   have hp:(fun v=> tested (S:=T i) A' t p R v (z' v))=ᶠ[𝓝 0] fun v=> tested (S:=T i) A' t p R v (z i A' v):=hv.mono fun u hi=> congrArg (tested (S:=T i) A' t p R u) hi.symm
   exact ⟨h1.congr_of_eventuallyEq hp,h2, ((hp.iteratedFDeriv ℝ j).eq_of_nhds).trans h3⟩
 obtain ⟨u,C,hP,hG⟩:=(h _ _ _ hk A').2; exact ⟨u,C,hP⟩
end YM.CF.Hom
