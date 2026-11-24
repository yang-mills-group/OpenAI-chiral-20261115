import YM.CF.Hom.Harpy
set_option autoImplicit false
noncomputable section
namespace YM.CF.Hom
open Function Filter Lattice Laurent Bloch Wilson Precision RG Work Exterior Next.Free Work.F08 Craft Pressure Stationary Tree Reef
open scoped Topology BigOperators ContDiff Matrix Matrix.Norms.Frobenius
local notation "G5"=> SU.group
variable {j:ℕ}{K:KernelChoices}{p q:Clip}{η a C b ρ d γ h₀:ℝ}{n:ℕ}
structure Postal where
 bar:ℝ
 peak:ℝ
 rise:ℝ
 parcel:ℝ
 gap:ℝ
 n:ℕ
 large:0<peak
 rental:1≤bar
 slow:0<rise
 reserve:0<parcel
 tame:0<gap
structure Claims(Q:Teller G5)(S:ChartRatio G5)(Y:Patch)(X:Postal):Prop where
 bound {c f:Side} (h:f.val=c.val*Y.L.val) : X.n≤c.val→Bid.Larger (G:=G5) (⟨Y,Q.bind,h⟩:StepData c f)
 note (W: Flight Q.j Q.j)(B V:Bed)(P:Towers W.L)(R:PathData G5)(h:W.patch=Y)(i:ℝ) : Paddle W Q.bind B V Q.top.clip P Q.η Q.C → MainIn G5 Q.top.clip B i Q.η Q.C → MainIn G5 Q.top.clip V i Q.η Q.C→ R.Bounds Q.top.clip Q.top.width Q.top.paths X.bar → Rare R → Attached B R →i=X.parcel→∃ T, T.Bounds Q.top.clip Q.top.width Q.top.paths X.bar ∧ Rare T∧Attached V T∧∃ α, |α+SU.group.slopeConstant * Real.log W.L.val|+1≤ Q.top.drift ∧ Signets W Q.bind P Q.top.clip R T α S X.peak X.rise X.gap X.n -- issue X.parcel gap η != floor shared ν
-- define start law keep both top and regular fees; Trail params distinct original D reroute
structure Linear (Q:Teller G5)(n:ℕ)(ε:ℝ) :Prop where
 oath:∀ P:Patch,P.Branches Q.bind G5
 fit:Q.top.clip.direct≤1
 old:∀ v, 1≤v → (solvent (WilsonStartup.Design.top G5 Q.top.clip)).Bounds Q.top.clip Q.top.width Q.top.paths v∧ Rare (solvent (WilsonStartup.Design.top G5 Q.top.clip))
 stable:Q.top=Q.below
 issue (P:Patch) : n≤P.L.val → ∀ h:P.J=Q.j, ∃ H:ℕ→ Bed,Attached (H 0) (solvent (WilsonStartup.Design.top G5 Q.top.clip)) ∧(∀ i,MainIn G5 Q.top.clip (H i) ε Q.η Q.C)∧∀ i, ∃ W:Flight Q.j Q.j, W.patch=P ∧∃ T:Towers W.L,Paddle W Q.bind (H i) (H (i+1)) Q.top.clip T Q.η Q.C
private def resizeC(p:Clip)(w:ℝ)(h:0<w) :Clip := {p with relaxation:=12/w, radius_pos:=by positivity}
private def tuneC(p:Clip)(w f d:ℝ)(h:0<w)(p':0<f)(hD: 0≤d): RG.Stage:=⟨resizeC p w h,8,4,1,w,f,d,1,by decide,by decide,one_pos,h,p', by change _≤12/w*w; rw [div_mul_cancel₀ 12 h.ne'],le_rfl,hD⟩ -- tune clip field
lemma surrounds (P:Patch)(hs:P.Branches K G5) : ∃ n:ℕ, ∀ {c f:Side} (h:f.val=c.val*P.L.val), n≤c.val → Bid.Larger (G:=G5) (⟨P,K,h⟩:StepData c f):=by
 let N:=100*macroR P; refine ⟨N+3,fun {c f} h x=>⟨hs,?_,by omega⟩⟩; change N ≤ f.val; rw [h]; exact le_trans (by omega : N≤ c.val) (Nat.le_mul_of_pos_right _ P.L.property)
section
-- assemble loop budget etc externally after pricing; R.top bounds on C choose independently of clip via phase
variable {g a b c x A y t d:ℝ} -- K shadow
lemma sizes_pay (f:ℝ)(w:0≤f)(x:ℝ)(p:0<x) :∃ C:ℝ,0<C∧ f≤ C ∧ girk 3*f ≤ C∧ girk 4*f≤ C ∧ x≤ C ∧ girk 3*x≤ C ∧ girk 4*x≤ C:= by
 have hx:0≤girk 3:=by unfold girk; positivity
 have ht:0≤girk 4:=by unfold girk; positivity
 refine ⟨(1+girk 3+girk 4)*(f+x),?_,?_,?_,?_,?_,?_,?_⟩ <;> nlinarith
end
private lemma linearK (j:ℕ)(h:4≤ j) (d:ℝ)(a η:ℝ)(p:Clip)(η1 C1 :ℝ)(g:Trail j K d n p a η C) (S:RG.Stage)(ht:S.clip.direct=p.direct)(he:1 ≤ C1)(hy:1≤C)(hv:η1≤a)(hy':C≤C1)(M:ℕ)(hm:n≤M)(D:∀ q:Clip,q.direct=p.direct→∀ P: Flight j j,n≤P.L.val→∀ m v:ℝ,0≤m→0≤v→ HopQuote K j j m v a η C n→∀ X Y:Bed,MainIn G5 q X η a C→MainIn G5 q Y η a C→Defined K.penalty m P.wing X→Defined K.penalty v P.land Y→∃ W:Towers P.L,Paddle P K X Y q W η1 C1)(P:Patch)(hi:M≤ P.L.val)(hj:P.J=j) : ∃ H: ℕ→ Bed,Attached (H 0) (solvent (WilsonStartup.Design.top G5 S.clip)) ∧(∀ i,MainIn G5 S.clip (H i) η η1 C1) ∧∀ i,∃ X:Flight j j,X.patch=P∧∃ T:Towers X.L, Paddle X K (H i) (H (i+1)) S.clip T η1 C1:=by
 let q:= S.clip; have hh:q.direct≤1:= ht.trans_le g.tight
 let f(v:Train j): Flight j j:= ⟨P.L,P.odd_side,P.coarse,h,le_rfl,by omega,v⟩
 have hp(y): (f y).patch=P:=by unfold Flight.patch; cases P; subst j; rfl
 let w: ℕ→Train j:=Nat.rec (Train.top j) (fun _ (y: Train j)=>(f y).land)
 have hu(i:ℕ): w (i+1)=(f (w i)).land:=rfl
 obtain ⟨U,H,hX,W⟩:= worship (G:=G5) (p:=q) hh j h _ hy q.direct (g.initial q ht) le_rfl
 choose V t hY hv0 hU L using fun i:ℕ => g.standard S.clip ht q le_rfl (w (i+1))
 let T:=fun i:ℕ=>match i with|0=> U|j+1=> V j
 have hc(i): MainIn G5 S.clip (T i) η a C:= by cases i with | zero=>exact W| succ i=> exact ⟨hY i,hv0 i,fun n=>hU i n _⟩
 refine ⟨T,⟨hX.layout⟩,fun i=> ⟨cover_revise (hc i).1 hv hy', fun n=>floor_revise ((hc i).2.1 n) le_rfl hy', (hc i).2.2⟩,fun i=>⟨f (w i), hp _,?_⟩⟩
 have hr :n ≤ (f (w i)).L.val:= hm.trans hi
 cases i with
 | zero=> exact D q ht (f (w 0)) hr 0 d le_rfl g.sturdy g.hopI _ _ W (hc 1) H (t 0) -- cast?
 | succ i=> exact D q ht (f (w (i+1))) hr _ _ g.sturdy g.sturdy g.hopT _ _ (hc (i+1)) (hc (i+2)) (t i) (t (i+1))
lemma clay(j:ℕ)(u:4≤j)(S:ChartRatio G5)(v:LocalRatio S):∃ (K:Teller G5)(ε:ℝ)(N:ℕ), K.j=j∧0<ε ∧1≤K.C ∧ K.top=K.below ∧ Linear K N ε ∧ ∀ P:Patch,N≤P.L.val → P.J=j → ∃ X,Claims K S P X∧ X.parcel=ε:=by
 obtain ⟨K,hκ,h⟩:= Axial.viable G5 1 one_pos
 obtain ⟨n,x,η,a,C,g',ha,hC,p,hT⟩:= trailV j u K
 obtain ⟨z,W,f,g,hw,hy,φ⟩:= packageK (n:=n) (K:=K) (G:=G5) (C:=C) ha g' p u C
 have hη:=hC.trans hw; let G':= Thera.yet_one; obtain ⟨i⟩:= colorAvail G5 G'; obtain ⟨κ,w,hp,k,hB⟩:= transition_cap G5 i G' K j η z W p.direct z W p.direct g' f g.le p.quadratic_pos.le f g.le p.quadratic_pos.le
 let p':= resizeC p w k; have hx:p'.direct=p.direct:=rfl; have hp':p'.direct≤1:=hx.trans_le hT.tight
 obtain ⟨l,hl,U⟩:= WilsonStartup.Design.bound_arbitrary p' G5 hp' w k; obtain ⟨c,hL,r,s,t,e,i1,i2⟩:= sizes_pay _ hp l hl; obtain ⟨d,γ,R,Θ,Λ,hZ,hd,X⟩:=hB w c k hL.le (pouring G5 G' z η W p.direct w c f g' g.le p.quadratic_pos.le k hL.le) -- tune
 let S':=tuneC p w c d k hL hZ; let P:Teller G5:=⟨K,S',S',j,z,W,f⟩
 refine ⟨P,η,max R n,rfl,g',hη,?_,?_,fun A v' wj=>?_⟩ -- stableT remove
 · exact rfl
 · exact ⟨h,hp',fun V v=> gem_b (U _ le_rfl _ (zero_le_one.trans v)) e i1 i2,rfl, linearK j u x a η p z W hT S' rfl hη hC hy hw _ (le_max_right ..) φ⟩
 obtain ⟨e,hϵ,h'⟩:= (Integrated.stationary_scene (G:=G5) A.L j K η g').χ
 obtain ⟨M,hM⟩:= surrounds _ (h A)
 let L:=max 1 (Λ A.L); let H:= max 1 (Θ A.L); have hu: 1≤ L:= le_max_left ..; have hW:0<H:=zero_lt_one.trans_le (le_max_left ..)
 let B:= Postal.mk L H γ η e (M+1) hW hu hd g' hϵ
 refine ⟨B, ⟨fun q hk=>hM q (by change M+1≤_ at hk; omega), fun Wg Y Z D E iy d Wp HA HB hE hr hA hi=>?_⟩,rfl⟩
 subst A; change d=η at hi; subst d
 have hg{c f:Side}(u:f.val=c.val*Wg.L.val)(he:M<c.val): Bid.Larger (G:=G5) (Wg.visit K u):= hM u (Nat.le_of_lt he)
 obtain ⟨U,hU,hR,hT,A',ha,hD⟩:= authorize (p:=P.top.clip) S v X ((le_max_left ..).trans v') (h Wg.patch) Wp HA HB hE hr hA (le_refl w) (le_max_right ..) hu r s t M (fun _ _ y k=> hg y k) hϵ (by 
    intro c f' p hV V; let G:= Wg.visit K p; apply h' c f' G rfl rfl rfl (hg p hV) V Y Z S'.clip S'.clip E _ _ _ _ _ _ D (Wp.link p) (HA.2.1 f') hE hA (HA.2.2 _) (HB.2.1 _))
 refine ⟨U,hU,hR,hT,A',ha,{ hD with all:= fun c f y k K=> ⟨(hD.all c f y k K).1, fun i v=> ?_⟩ }⟩ -- tune
 obtain ⟨x,hB⟩:= (hD.all c f y k K).2 i v; refine ⟨x,higher_bill hB ?_⟩; unfold B; dsimp only; gcongr; exact le_max_right ..
end YM.CF.Hom
