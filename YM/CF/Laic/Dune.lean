import YM.CF.Laic.Sax
set_option autoImplicit false
noncomputable section
namespace YM.CF.Laic
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Kennel Planned.JetPort Push.Uniform
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {m A B L N:Side}{j k:ℕ}{ho:Odd L.val}{d a b:ℝ}{n:ℕ}
variable {e:ℝ}{G:Ratio (CSide m B) (CSide A B)}{T:Roam m A B}{F:Forest T.ratio}{z:Vox m B→ AxisChart group F}{Y:Pricing j L ho (Thread j)}{V:Grasp Y B e}
structure Ample (U:Dress N):Prop where
 across:Nacre.Across U
 plane:Hull.Plane U
 ripe : ripeF U
 self : relic U
lemma bare : Ample (0:Dress N):=⟨fun _ _=> (map_zero _).symm,fun _ _=> (map_zero _).symm, ripZ 0,relic_zero⟩ -- tune unused argument
lemma amp_P(U:Toy k N)(w:0<k)(p:Prints U)(g: handy U): Ample (sumU (cavil U)):=by
 let T:=cavil U; refine ⟨fun t x=> rent_tx t T (fun i j=>pre_a _ _ _ p) x,fun t x=> hail_tx t T x,troop T (cobblestone U g), (relic_r k w _).2.1⟩
lemma amp_plus {U V:Dress N}(h:Ample U)(p:Ample V): Ample (U+V):=by
 refine ⟨fun i x=>?_,fun i x=>?_, ripP _ _ h.ripe p.ripe, relic_up h.self p.self⟩
 · rw [Pi.add_apply,Pi.add_apply,h.across,p.across,map_add]
 rw [Pi.add_apply,Pi.add_apply,h.plane,p.plane,map_add]
lemma capQ {κ:Type*}[LinearOrder κ][Fintype κ]{P C:Op κ}(p:TagG P C): capT P C=C:=by rw [capT,p.pen,p.2]
abbrev flareP (L:Side)(j:ℕ)(o:Odd L.val) (M:Male)(U:Dress (CSide m B)): Vox m B→ Op (Single (CSide m B)):= partM L j o m B M U ∘ represent
private def polarCF (j:ℕ)(M:Male): Cloud N→ Op (Single N):= spar j M ∘ represent
lemma symmetryP (H:Hull j L ho a b d e n m A B G T F z Y V)(M:Male){U:Dress (CSide m B)}(p: Ample U):Nacre.Motion (flareP L j ho M U):=by
 let Y0:= CSide m B; let V':=upMale L ho M;   let R:= V.broadness _ H.size_p V'; have hx: ∀ᶠ i: Vox m B in 𝓝 0,Cube.Guard (represent i) e:= (H.native.melod e H.hi G).mono fun x h=>h.cg -- fix
 have he(u:Bkg (More Y0))(x)(h:Cube.Guard u e): partM L j ho m B M U (Lattice.gauge x u) = ActZ x (partM L j ho m B M U u):=by unfold partM ActZ; rw [R.covary u _ h,p.ripe]; unfold capT; simp; rfl -- tune
 have ht(u:Bkg (More Y0))(x:Shape)(h: Cube.Guard u e)(f:U (Yg x u)=ZoneH x (U u)):partM L j ho m B M U (Yg x u)=ZoneH x (partM L j ho m B M U u):=by
    let S:=prepU x (spinX x.s) inert Y0; let P:= spar j V' u; let V0:= spar j V' (Yg x u); let r:=detX x.s; have he: twist S P= swapX r V0:=funde_f _ _ _ (bud_s _) _ _ H.above _ _ (H.stamp.fields_one _ (V.needed.trans H.size_p)) (h.shrink (V.gem))
    rw [zone_c]; unfold partM; rw [f,zone_c]; exact (soil _ _ _ _ S (R.projection _ h) (R.projection _ (keepC inert x u e h)) he).symm
 constructor
 · intro g x; filter_upwards [(Hull.ray_home x).eventually hx] with i hi; unfold flareP Function.comp; rw [orderD]; exact he _ _ hi
 · intro t x; filter_upwards [(Hull.ray_home x).eventually hx] with i hi; unfold flareP Function.comp; rw [height]; exact ht _ (lagX t) hi (p.across _ _)
 · intro a x; filter_upwards [(Hull.ray_home x).eventually hx] with i hi; unfold flareP Function.comp; rw [←roomy]; exact ht _ (incX a) hi (p.plane _ _)
 intro x v; filter_upwards [(Hull.ray_home x).eventually hx, wraps v x] with i hi hp; unfold flareP Function.comp; rw [hp]; exact he _ _ hi
lemma partZero (M: Male): flareP (B:=B) (m:=m) L j ho M 0=0:=by funext i; change (1-_)*(0:Op (Single (CSide m B)))*_= _; rw [mul_zero,zero_mul]; rfl
variable (H:Hull j L ho a b d e n m A B G T F z Y V)(M:Male)
include H
lemma headed {U:Dress (CSide A B)}{u:Dress (CSide m B)}(p:relic U):∀ᶠ x in 𝓝 0, capT (polarCF j (upMale L ho M) x) (emergence L j ho G F z M U x-flareP L j ho M u x)=emergence L j ho G F z M U x-flareP L j ho M u x:=by
 filter_upwards [H.native.melod e H.hi G,H.native.melod d H.po G,H.nickP M p] with x he hh hu
 let Z:= ears F z x; have hp: IsStarProjection (foal j true M G (unionP Z)):= (H.tape.AlongC G H.fromL H.request M Z hh true).lead
 let C:= crux j G M Z (U Z.1); have hz:= (voice H.hi G H.fromL H.size_p M Z he C (tag_g _ hp) hu.1).1
 have hk :TagG (polarCF j (upMale L ho M) x) (emergence L j ho G F z M U x):=hz; have hq: TagG (polarCF j (upMale L ho M) x) (flareP L j ho M u x):=tag_g _ ((V.broadness _ H.size_p (upMale L ho M)).projection _ he.cg); refine capQ ⟨?_,?_⟩; rw [mul_sub,hk.1,hq.1,sub_zero]; rw [sub_mul,hk.2,hq.2]
lemma poleCF (M:Male):ContinuousAt (polarCF (N:=CSide m B) j M) 0:=by
 let f:=V.broadness _ H.size_p M
 apply ContinuousWithinAt.continuousAt (s:={x|Cube.Guard (represent (G:=group) x) e}); swap
 · exact (H.native.melod e H.hi G).mono fun i hi=> hi.cg
 refine (f.continuousOn (x:=represent (0:Vox m B)) ?_).comp (army_repr.cont.continuousWithinAt) (fun _ h=> h); rw [link_one]; exact guard0 H.hi.le -- army_repr.cont wrong
-- use smooth leading matching then apply actual projection
lemma mender {U:Dress (CSide A B)}{u:Dress (CSide m B)} (p:relic U)(f:Toy k (CSide m B))(hc:Nacre.crystal k (emergence L j ho G F z M U-flareP L j ho M u) (spurTx f)):
 Nacre.crystal k (emergence L j ho G F z M U-flareP L j ho M (u+sumU (cavil f))) 0:=by
 intro x; let r:=𝓝[≠] (0:ℝ); let D:=emergence L j ho G F z M U;   let Z(i:ℝ):= D (i • x)- flareP L j ho M u (i • x); let g:=sumU (cavil f); let P:=polarCF j (upMale L ho M) (N:=CSide m B) -- shadow B fix
 let V:=spurTx f x; let R(i:ℝ):=P (i • x); let w(i:ℝ):=(i^k)⁻¹; have hd:= (Hull.ray_home x).mono_left (nhdsWithin_le_nhds (s:={(0:ℝ)}ᶜ)); have hv:Tendsto R r (𝓝 (P 0)):= (poleCF H (upMale L ho M)).tendsto.comp hd
 have he:= hc x; have hz:capT (P 0) V=V:=by
    apply tendsto_nhds_unique _ (hc x); refine ((((tendsto_const_nhds.sub hv).mul he).mul hv)).congr' ?_
    filter_upwards [hd.eventually (headed H M p (u:=u))] with i ht; change (1-R i)*(w i • Z i)*R i=_; rw [Matrix.mul_smul, Matrix.smul_mul,show (1-R i)*Z i*R i=Z i from ht]; rfl
 have hh:= (he.sub (((tendsto_const_nhds (x:=(1:Op (Single (CSide m B))))).sub hv).mul (priced x f) |>.mul hv)); rw [show spurTx f x-(1-P 0)*spurTx f x*P 0=0 from sub_eq_zero.mpr hz.symm] at hh
 refine hh.congr fun i=> ?_
 change w i • Z i - (1-R i)*(w i • g (represent (i • x)))*R i=w i • (D (i • x)-(1-R i)*(u (represent (i • x))+_)*R i); simp only [mul_add,add_mul,smul_sub, smul_add, Matrix.mul_smul, Matrix.smul_mul,Z]; rw [show flareP L j ho M u (i • x)=(1-R i)*u (represent (i • x))*R i from rfl]; change _= w i • D _ -( w i • ((1-R i)*u (represent (i • x))*R i)+ w i • ((1-R i)*g (represent (i • x))*R i)); abel
end YM.CF.Laic
