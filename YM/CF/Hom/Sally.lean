import YM.CF.Hom.Wing
set_option autoImplicit false
set_option synthInstance.maxSize 8000
noncomputable section
namespace YM.CF.Hom
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Kennel Laic Pec Next.Free Pressure Cascade Reef
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {L B m A:Side}{ho:Odd L.val}{j k:ℕ}{a b d r s u v n X l η e:ℝ}{Y:Pricing j L ho (Thread j)}{P:Grasp Y B e}{K:Teller group}
structure Credit where
 F:ℝ
 f:ℝ
 U:ℝ
 u:ℝ
 B:ℝ
 b:ℝ
 P:ℝ
 i:ℕ
 posF:0<F
 posf:0<f
 posU:0<U
 posu:0<u
 posB:0<B
 posb:0<b
 posP:0<P
structure InterestX(C:Credit)(n:Side)(J:Interest n):Prop where
 leanJ: J.under C.f C.F C.u C.U C.b C.B
 ready:Cry J.P
 tilt: ClearP J.I
structure Mint (P:Grasp Y B e)(C:Credit)(α:ℝ) (K:Teller group)(J₁:Interest (CSide A B))(J₂:Interest (CSide m B))(G:Ratio (CSide m B) (CSide A B))(T:Roam m A B)(V W: RG.PathData group):Prop where
 courage: InterestX C (CSide m B) J₂
 grown:J₂.M= upMale L ho J₁.M
 fiscal: |α|≤ C.P
 hope(F:Forest T.ratio)(z: Vox m B→ AxisChart group F): Critical F K.top.clip V z→ cFoot 3 (emergence L j ho G F z J₁.M J₁.P.den-flareP L j ho J₁.M J₂.P.den) ∧ cFoot 3 (myth G F z K.top.clip W P J₁.M J₁.P.den J₁.I J₂.I α)
structure Reward (P:Grasp Y B e) (T:Teller group)(S:Credit)(R:ChartRatio group)(T':RG.Patch)(p:Postal): Prop where
 earns {D V: Bed} {W: Flight T.j T.j} (hx:W.patch=T')(y:L=W.L) (H:MainIn group T.top.clip D p.parcel T.η T.C) (Z:MainIn group T.top.clip V p.parcel T.η T.C)
    (X:Towers W.L) (R' V':RG.PathData group) (w:Paddle W T.bind D V T.top.clip X T.η T.C) (s:R'.Bounds T.top.clip T.top.width T.top.paths p.bar) (q:V'.Bounds T.top.clip T.top.width T.top.paths p.bar) (r:Rare R') (t:Attached V V'){β:ℝ}(v: Signets W T.bind X T.top.clip R' V' β R p.peak p.rise p.gap p.n):
    ∀ {m A: Side}(G:Ratio (CSide m B) (CSide A B))(h:G.count=L)(e:(More (CSide A B)).val=(More (CSide m B)).val*W.L.val), S.i≤ (CSide m B).val →∀ I:Interest (CSide A B),InterestX S _ I→∃ I' α',Mint P S α' T I I' G (W.visit T.bind e) R' V'
lemma rat_eq{G:Ratio (CSide m B) (CSide A B)}{f:Flight K.j K.j}{e: (More (CSide A B)).val=(More (CSide m B)).val*f.L.val}(h:G.count=f.L): (f.visit K.bind e).ratio= ratio G:=by cases G; unfold Rush.ratio RG.StepData.ratio; simp_all; congr
lemma printsG {k':ℕ}(x:0<X)(y:0<u)(q:0<a)(w:0<b)(hy:0<d)(h:Spack j L ho a b d k)(B':Pearl P)(r_bad:Even j)(hv:1≤j)(j':K.j=j)(t:Stamped j L ho Y)(e':0<e)(k0:1≤K.C)
 (A₁ B₁ A₂ B₂ ap b' f:ℝ) (hk:0<A₁)(hd:0<A₂)(hl:0<B₁)(hg:0<B₂)(hm:0<ap)(hc:0<b')(hz:0<f) (n:ℕ)(p:Postal) (V: RG.Patch) (S:ChartRatio group) (i: V.L=L)
 (Vh:Claims K S V p)(hop:Magic j K.η (roseT K) L ho X u K.C a b d k A₁ B₁ A₂ B₂ n) -- binder shadow ho
 (B0:∀ {m r:Side}(T:RG.StepData (More m) (More r)) (F:Forest T.ratio){z:Cloud m→ AxisChart group F}(R:RG.PathData group), Bid.Larger (G:=group) T → T.kernel=K.bind → T.patch=V→ V.J=K.j→ ∀ l:ℝ,R.Bounds K.top.clip K.top.width K.top.paths l→ Critical F K.top.clip R z → Laic.Horizon F z 2 X u)
 (D:∀ {m A: Side}{G:Ratio (CSide m B) (CSide A B)}{T:Roam m A B} {F:Forest T.ratio} {y:Vox m B → AxisChart group F}{U:RG.PathData group}{q:RG.Clip}{H:Bed}{σ η c d' m':ℝ},Hull j L _ a b d e k m A B G T F y Y P → U.Bounds q σ η c → Floor H q (More (CSide m B)) d' m' → H.metric.strip K.η K.C → Attached H U → Bid.Sworn H (More (CSide m B)) group → k' ≤ (More (CSide m B)).val → Laic.Horizon F y 2 X u → Gazes T F y K.η K.C (roseT K) → ∀ M:Male,∀ A':Aim (CSide A B),A'.toll B₁ B₂ A₁ A₂ → ∀ I:Pride (CSide A B),Lac I ap b'→ ∃ Q:Pride (CSide m B), Lac Q ap b'∧∃ t':ℝ, |t'|≤f ∧cFoot 3 (myth G F y q U P M A'.den I Q t')) : ∃ T', T'.F=A₁∧ T'.f=B₁ ∧ T'.U=A₂ ∧ T'.u=B₂ ∧ Reward P K T' S V p:=by
 let C:=Credit.mk A₁ B₁ A₂ B₂ b' ap f (k+k'+p.n+n+P.roundZ) hk hl hd hg hc hm hz
 refine ⟨C,rfl,rfl,rfl,rfl, ⟨fun {B0' v1 Wg} hx H Q R T' V₁ V₂ Wp g g1 a' u' β ζ {m r} G p' L' HH F G0=>?_⟩⟩
 let T:= Wg.visit K.bind L'; have hkA: V.J=K.j:=hx ▸ rfl; let N:= CSide m B; have ht':p.n ≤ (More N).val:= by change _≤ (CSide m B).val * 2; change k+k'+p.n+n+P.roundZ≤ (CSide m B).val at HH; omega
 have he: T.ratio= ratio G:=rat_eq (p'.trans H)
 have hp: Bid.Larger (G:=group) T:=by
    have hg(e:(More (CSide r B)).val=(More (CSide m B)).val*V.L.val): Bid.Larger (G:=group) (⟨V,K.bind,e⟩:RG.StepData (More N) (More (CSide r B))):=Vh.bound e ht'
    subst V; exact hg L'
 let A:=Classical.choice (Tree.select T.ratio Wg.patch.odd_side); obtain ⟨z,Y',pZ⟩:= ζ.existP _ _ L' ht' A; let V'(F:Forest T.ratio):= ζ.all _ _ L' ht' F |>.1; let z':Vox m B→ AxisChart group A:=z; have hn: k ≤ N.val ∧ k' ≤(More N).val ∧n≤(More N).val∧P.roundZ≤N.val:=by change k+k'+p.n+n+P.roundZ≤ (CSide m B).val at HH; change _≤ (CSide m B).val ∧_≤(CSide m B).val*2 ∧ _≤(CSide m B).val*2∧_≤(CSide m B).val; omega
 have hw: Hull j L _ a b d e k m r B G T A z Y P:= ⟨t,p',he,hn.1,hn.2.2.2,r_bad,hv,h,⟨_,_,_,_,_,_,Classical.arbitrary T.Choices,Y',hp.1,g, V' A,p.tame⟩, e',hy⟩ -- r shadow
 have hx0:= B0 T A V₁ hp rfl hx hkA p.bar g Y'; have hl':= road_b (G:=G) k0 Wp hw.native Q R pZ; obtain ⟨K1,K2⟩:= G0.leanJ
 obtain ⟨I,U,Bx⟩:=hop.give hw hl' hx0 hn.2.2.1 F.M F.P K1; obtain ⟨T1,T2,T3⟩:=D hw g1 (R.2.1 _) (R.1.2.1) u' (R.2.2 _) hn.2.1 hx0 hl' F.M F.P K1 F.I K2
 obtain ⟨b3,hb3,H3⟩:= T3; refine ⟨⟨upMale L ho F.M,dod I, shineP T1⟩,b3,?_⟩
 have hr : CryK A z':=station_cp hp.1 g a' Y' (V' A) p.tame; obtain ⟨j',X,Ht⟩:=mood hw hr G0.ready K1 F.M I U Bx; have Hc:= shimmering hw B' hr G0.ready K1 F.M F.I T1 G0.tilt b3 (Cascade.pos_l hw F.M F.P K1 B' q w hl hg hk hd hx0 x y) H3 g1 -- shadow
 obtain ⟨Ht',Hb⟩:=proof_c T1 T2; exact ⟨⟨⟨X,Hb⟩,j',Ht'⟩,rfl,hb3, fun i z t=> moveP hw B' F.M F.P (dod I) F.I (shineP T1) K.top.clip b3 (den_r K1) Ht Hc g hp.1 Y' t (V' i) p.tame⟩
lemma printing {k':ℕ}(x:0<X)(y:0<u)(q:0<a)(w:0<b)(hy:0<d)(h:Spack j L ho a b d k)(B':Pearl P)(r_bad:Even j)(hv:1≤j)(j':K.j=j)(t:Stamped j L ho Y)(e':0<e)(k0:1≤K.C)
 (A₁ B₁ A₂ B₂ ap b' f:ℝ) (hk:0<A₁)(hd:0<A₂)(hl:0<B₁)(hg:0<B₂)(hm:0<ap)(hc:0<b')(hz:0<f) (n:ℕ)(p:Postal) (V: RG.Patch) (S:ChartRatio group) (i: V.L=L)
 (Vh:Claims K S V p)(hop:Magic j K.η (roseT K) L ho X u K.C a b d k A₁ B₁ A₂ B₂ n) -- binder shadow ho
 (B0:∀ {m r:Side}(T:RG.StepData (More m) (More r)) (F:Forest T.ratio){z:Cloud m→ AxisChart group F}(R:RG.PathData group), Bid.Larger (G:=group) T → T.kernel=K.bind → T.patch=V→ V.J=K.j→ ∀ l:ℝ,R.Bounds K.top.clip K.top.width K.top.paths l→ Critical F K.top.clip R z → Laic.Horizon F z 2 X u)
 (D:∀ {m A: Side}{G:Ratio (CSide m B) (CSide A B)}{T:Roam m A B} {F:Forest T.ratio} {y:Vox m B → AxisChart group F}{U:RG.PathData group}{q:RG.Clip}{H:Bed}{σ η c d' m':ℝ},Hull j L _ a b d e k m A B G T F y Y P → U.Bounds q σ η c → Floor H q (More (CSide m B)) d' m' → H.metric.strip K.η K.C → Attached H U → Bid.Sworn H (More (CSide m B)) group → k' ≤ (More (CSide m B)).val → Laic.Horizon F y 2 X u → Gazes T F y K.η K.C (roseT K) → ∀ M:Male,∀ A':Aim (CSide A B),A'.toll B₁ B₂ A₁ A₂ → ∀ I:Pride (CSide A B),Lac I ap b'→ ∃ Q:Pride (CSide m B), Lac Q ap b'∧∃ t':ℝ, |t'|≤f ∧cFoot 3 (myth G F y q U P M A'.den I Q t')) : ∃ T', Reward P K T' S V p:=by
 obtain ⟨v',_,_,_,_,z⟩:= printsG x y q w hy h B' r_bad hv j' t e' k0 A₁ B₁ A₂ B₂ ap b' f hk hd hl hg hm hc hz n p V S i Vh hop B0 D; exact ⟨v',z⟩
end YM.CF.Hom
namespace YM.CF.Hom
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Kennel Laic Pec Next.Free Pressure Cascade Reef
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
lemma box_price(K:Teller group)(p:1 ≤ K.C)(v:Even K.j)(h:4≤K.j): ∃ n:ℕ, ∀ (V:RG.Patch),n≤V.L.val →∀ {B:Side}{e a b d:ℝ}{Y: Pricing K.j V.L V.odd_side (Thread K.j)} {P:Grasp Y B e}{l:ℕ}(S:ChartRatio group)(T:Postal),Claims K S V T→Stamped K.j V.L V.odd_side Y→ Pearl P→0<e→ Spack K.j V.L V.odd_side a b d l → 0<a →0<b →0<d → ∃ C, Reward P K C S V T:=by
 have hv:=rose_y K p; have hb:= K.width; have hk:=p.trans' zero_le_one; obtain ⟨n,X⟩:= travelW K.j (by omega) v hb hv; obtain ⟨N,H⟩:= ulster hb hv hk hb (zero_lt_one.trans_le p)
 refine ⟨max n N, fun V e {B e' a b d Y P l} S T x y v' t g ha hB hD=>?_⟩; let W:= V.L; obtain ⟨i,j,hs,hx,H'⟩:=cover_u 2 K V
 obtain ⟨A,B',A',U,hA,hQ,hP,hU,w,Y⟩:=X W ((le_max_left ..).trans e) V.odd_side l i j K.C a b d hs hx hk ha hB hD g
 have hv':1≤K.j:=by omega
 obtain ⟨B1,B2,B3,h₁,h₂,h₃,m,r⟩:=H W V.odd_side ((le_max_right ..).trans e) v' y g ha hB hD t hv' i j B' A U A' hs hx hQ hA hU hP
 exact printing hs hx ha hB hD g v' v hv' rfl y t p A B' A' U B1 B2 B3 hA hP hQ hU h₁ h₂ h₃ w T V S rfl x Y H' r
lemma peace_price(K:Teller group)(p:1 ≤ K.C)(v:Even K.j)(h:4≤K.j): ∃ n:ℕ, ∀ (V:RG.Patch),n≤V.L.val →∀ {a b d:ℝ}{Y: Pricing K.j V.L V.odd_side (Thread K.j)}{l:ℕ}(S:ChartRatio group)(T:Postal),Claims K S V T→Stamped K.j V.L V.odd_side Y→ Spack K.j V.L V.odd_side a b d l → 0<a →0<b →0<d → ∃ F f U u:ℝ,0<F∧0<f∧0<U ∧0<u ∧∀ {B:Side}{e:ℝ}{P:Grasp Y B e},Pearl P→0<e→∃ C:Credit,C.F=F∧ C.f=f ∧ C.U=U ∧ C.u=u∧ Reward P K C S V T:=by
 have hv:=rose_y K p; have hb:= K.width; have hk:=p.trans' zero_le_one; obtain ⟨n,X⟩:= travelW K.j (by omega) v hb hv; obtain ⟨N,H⟩:= ulster hb hv hk hb (zero_lt_one.trans_le p)
 refine ⟨max n N, fun V e {a b d Y l} S T x y g ha hB hD=>?_⟩; let W:= V.L; obtain ⟨i,j,hs,hx,H'⟩:=cover_u 2 K V
 obtain ⟨A,B',A',U,hA,hQ,hP,hU,w,Y'⟩:=X W ((le_max_left ..).trans e) V.odd_side l i j K.C a b d hs hx hk ha hB hD g
 have hv':1≤K.j:=by omega
 refine ⟨A,B',A',U,hA,hQ,hP,hU,@fun B e' P v' t=>?_⟩
 obtain ⟨B1,B2,B3,h₁,h₂,h₃,m,r⟩:=H W V.odd_side ((le_max_right ..).trans e) v' y g ha hB hD t hv' i j B' A U A' hs hx hQ hA hU hP
 exact printsG hs hx ha hB hD g v' v hv' rfl y t p A B' A' U B1 B2 B3 hA hP hQ hU h₁ h₂ h₃ w T V S rfl x Y' H' r
end YM.CF.Hom
