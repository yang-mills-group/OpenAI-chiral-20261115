import YM.CF.Cascade.Pear
set_option autoImplicit false
noncomputable section
namespace YM.CF.Cascade
open Function Filter Metric Finset Lattice Wilson Next.Free Bloch Laurent Scroll Precision Exterior Lat Ember Aroma
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate Matrix MatrixOrder Kronecker
variable {j t:ℕ}{n c f:Side}{k a b:ℝ}
open Tree SU Font Cube Extra.Iteration Nacre
open Thera Fock Dial Peaks Tulip Paige NormedSpace
open Spire Vault Laic Kennel Rush Fir Branch Tenant
open scoped Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {m X B L:Side}{ho:Odd L.val}{d e:ℝ}{Y:Pricing j L ho (Vault.Thread j)}{P:Grasp Y B e} {G:Ratio (CSide m B) (CSide X B)}{T:Roam m X B}{F:Forest T.ratio}{z:Vox m B→AxisChart group F}{M: Male}
open Pec
local notation "dη"=>Aroma.port
variable {V K:ℕ}{Tg:Flight V K}{R:RG.PathData group}{r:RG.Clip}
abbrev card_c(N:Side):ℕ:= (More N).val
lemma barsX (w:Stamped j L ho Y)(l:0<e)(p:1≤j)(h:P.roundZ≤ (CSide m B).val)(X: CoreX)(M:Male)(U:Dress (CSide m B))(I:Pride (CSide m B))(hp:WordK I)(k:Ample U)(Q:ContDiffAt ℝ ω (spar j M ∘ represent (n:=More (CSide m B))) 0): Gird (copper _ X (assets j M U I∘ represent)):=by
 let n:=CSide m B; let f:= assets j M U I ∘represent; let V := Complex.reCLM ∘ f ∘ pour n X; have he:ContDiffAt ℝ ω f 0:=(worthW w l p h M U I k Q).2; have hx:= (show ContDiffAt ℝ ω f (pour n X 0) from (map_zero (pour n X)).symm ▸ he).comp _ (pour n X).contDiff.contDiffAt
 have ht: ContDiffAt ℝ ω V 0:= Complex.reCLM.contDiff.contDiffAt.comp _ hx
 intro t y z; exact secondY (rake t) (ContinuousLinearMap.id _ _) V ht (assets_up M _ _ (lagX t) _ p Q w h k hp l t) y z
variable {η ν C α:ℝ}
abbrev TimeC (M:Male)(U:Aim (CSide X B))(V:Aim (CSide m B)) (I:Pride (CSide X B))(J:Pride (CSide m B))(H:Hull j L ho a b d e t m X B G T F z Y P)(q:RG.Clip) (W:RG.PathData group)(t:ℝ):Prop:= cFoot 3 (emergence L j ho G F z M U.den -flareP L j ho M V.den) ∧ cFoot 3 (myth G F z q W P M U.den I J t)
lemma pos_l (H:Hull j L ho a b d e t m X B G T F z Y P)(M:Male)(U:Aim (CSide X B)){J W A B':ℝ}(T':U.toll J W A B')(K:Pearl P)(hc:0<a)(hv:0<b)(hs:0<J)(hw:0<W)(hx:0<A)(ht:0<B'){r t':ℝ}(v:Horizon F z 2 r t')(y:0<r)(g:0<t'): ContDiffAt ℝ (↑(2:ℕ)) (deflate (lush G P M U.den∘ ears F z)) 0:=by
 obtain ⟨p,V,h,k,Q⟩:=pullPay L ho J A W B' hs hx hw ht 2; obtain ⟨l,u,m,j,E⟩:=ink_w K H.stamp H.tape hc hv H.po H.hi H.above h k y g
 exact (E H v M U.den (den_r T') (Q F H.alignT H.fromL U T')).1
noncomputable abbrev baser(N:Side)(W:Bed):= ‖brok N‖^2 * (W.metric.read (dη N) (plaquette pee) (plaquette pee)).re / (Ember.pinch N)^2
lemma paying (H:Hull j L ho a b d e t m X B G T F z Y P)(M:Male)(U:Aim (CSide X B))(V':Aim (CSide m B))(I:Pride (CSide X B))(J:Pride (CSide m B))(v: CoreX)(w:‖v‖=1)(hp:Ample U.den)(hq:Ample V'.den)(hK:WordK I)(hT:TimeC M U V' I J H r R α)(P':Bed) {B' d':ℝ}(A:R.Bounds r η ν C)(p:Floor P' r (More (CSide m B)) B' d')(hx:Attached P' R)(g: Bid.Sworn P' (More (CSide m B)) group)(l:P'.metric.safe)(L':3 ≤ card_c (CSide m B))(f:4 ≤ V)(hQ:4 ≤ K)(N: (More (CSide X B)).val=(More (CSide m B)).val*Tg.L.val)(y:0<k)(u:Guessed F (installed (Tg.visitRatio N) (Tg.duo k).A0) z) (s:ContDiffAt ℝ ω (spar j M ∘ represent (n:=More (CSide X B))) 0)(e: ContDiffAt ℝ ω (spar j (upMale L ho M) ∘ represent (n:=More (CSide m B))) 0)(t':ContDiffAt ℝ (↑(2:ℕ)) (deflate (lush G P M U.den ∘ ears F z)) 0): let x:=CSide m B; let Y:=CSide X B
 bookie x v V' (upMale L ho M) j J (dη x)+α * (base_u x*baser x P') =∑ i:Site Tg.L, ‖angel k Tg (dη x) i‖^2 * bookie Y v U M j I (aliasAt (dη x) i) :=by
 intro x Y; let R':=assets j M U.den I∘represent; let S:=Tg.visitRatio N; let W:=installed S (Tg.duo k).A0; obtain ⟨ht,hv⟩:= worthW H.stamp H.hi H.above (P.clock_fine G H.size_p) M _ I hp s
 have hp':ContDiffAt ℝ (↑(2:ℕ)) R' 0:=hv.of_le le_top; have ht':= bio ht; have hu:=ht'.first (by unfold deflate; rw [sub_self]) ((def_c hp').of_le (by norm_num)); let q:=dη x; let A':= copper Y v R'
 have hU (G Z:Cloud Y)(f:Orig Y→ CoreX)(p:collect group G=collect group Z+Font.pure f):trim 2 R' G=trim 2 R' Z:=by
    rw [←trim_L R' hp',← (show trim 2 (deflate R') (fullG 0 G)=_ from (ht'.invariant hu (def_c hp') G).1 0), fullB G Z f 0 p]; exact (ht'.invariant hu (def_c hp') Z).1 0
 let X':=assets j (upMale L ho M) V'.den J ∘ represent; let B:= hike (n:= More x) q; let σ:= ∑ i: Site Tg.L, angel k Tg q i • hike (n:=More Y) (aliasAt q i); let Fm:=secondM (n:=x) r R; let Kv:=copper x v X'; let Kf:= copper x v Fm
 have he(B:ℂ→L[ℝ]ℝ)(g':=groan (n:=x) B (hike q))(y':=groan (n:=Y) B σ)(p':g'=groan (n:=x) B (hike q))(e':y'=groan (n:=Y) B σ): Kv g' g'+α *Kf g' g'= A' y' y':=by
    have he:=angSpan Tg y f hQ N L' B
    let L:=pour x v g'; let U0:=pour Y v y'; let X:=Channel.rising F W L
    obtain ⟨o,r⟩:= climb F W y' g' v (by rw [p',e']; exact he)
    have hz:= nais H M _ _ I J hp hq hT.1 hT.2 A s e t' L; have hS: ContDiffAt ℝ (↑(2:ℕ)) X' 0:=((worthW H.stamp H.hi H.above H.size_p _ _ _ hq e).2).of_le le_top; obtain ⟨_,_,_,_,_,_,_,hr,_⟩:= H.native.was
    have ht: fderiv ℝ (chartOf F z) 0 L=X:=chart_tangent z hr u L
    change (trim 2 X' _).re+α*(trim 2 Fm L).re=(trim 2 R' _).re at hz; rw [ht,hU X U0 _ r] at hz; unfold Kv Kf A'; rw [copperP _ _ hS, copperP _ _ ((sane A).of_le le_top),copperP _ _ hp']; change 2* _ + α*(2*_)= 2*(trim 2 R' U0).re; rw [← hz]; ring -- tune
 have hA:=syl_b S Tg.odd (barsX H.stamp H.hi H.above (P.clock_fine G H.size_p) v _ _ _ hK hp s) (tyM x) (angel k Tg q); rw [show mon (tyM x)=q from mon0 L'] at hA
 have hm :=price_b R r P' A p l hx g v w L'; have hk : base_u x*baser x P'= date x*(‖brok x‖^2*(P'.metric.read q (plaquette pee) (plaquette pee)).re):=by unfold base_u baser q; have hp:= pinch_pos x; field_simp
 rw [hk,show date x*_=(syl Kf B B).re from hm.symm,show _ = _ from (show ∑ i:Site Tg.L, ‖angel k Tg q i‖^2 * bookie Y v U M j I (aliasAt q i) = _ from hA.symm) ]
 change Kv _ _ + Kv _ _ + α* (Kf _ _ + Kf _ _) = A' _ _ + A' _ _; linarith only [he Complex.reCLM (grove x B) (grove _ σ) rfl rfl, he Complex.imCLM (waveL x B) (waveL _ σ) rfl rfl]
end YM.CF.Cascade
