import YM.CF.Kennel.Hawk
set_option autoImplicit false
noncomputable section
namespace YM.CF.Kennel
open Function Filter Metric Lattice RG Wilson Laurent Precision Tree Stationary Finset Exterior Bloch Lat Rush Cube Scroll SU Peaks Nacre
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.Frobenius -- army uses f
variable {N X: Side}{T:StepData (More N) (More X)}{F:Forest T.ratio}{z:Cloud N→AxisChart SU.group F}
structure Nativity (F:Forest T.ratio)(z:Cloud N→AxisChart SU.group F):Prop where
 was : ∃(p:Clip)(R:PathData SU.group)(a b c d:ℝ)(_:T.Choices),Critical F p R z ∧ T.patch.Branches T.kernel SU.group∧ R.Bounds p a b c ∧ PriceGap F p R d∧ 0<d

def natJoint(F:Forest T.ratio)(z:Cloud N→AxisChart group F)(x:Cloud N): Joint group (More N) (More X):=encamp F z ((arm group _ _).symm x)
def baby(F:Forest T.ratio)(z:Cloud N→AxisChart group F)(x:Cloud N):Config group (More X):=(natJoint F z x).1
def ears (F:Forest T.ratio)(z:Cloud N→AxisChart group F)(x:Cloud N):= Prod.mk (baby F z x) (represent x)
lemma bornL(x:Cloud N):input group (More N) ((arm group _ _).symm x)=represent x:=by unfold Stationary.input; rw [(arm ..).apply_symm_apply]
lemma neo (x:Cloud N): natJoint F z x=(baby F z x,1):=rfl
namespace Nativity
variable (P:Nativity F z)
include P
lemma flat':natJoint F z 0=1:=by obtain ⟨_,_,_,_,_,_,_,h,_⟩:=P.was; rw [natJoint,map_zero,encamp_zero h]
lemma flat:baby F z 0=1:=congrArg Prod.fst P.flat'
lemma army:Thaw (natJoint F z) 0:=by obtain ⟨_,_,_,_,_,_,_,h,_⟩:=P.was; apply Thaw.comp (g:=encamp F z) (w:=(arm group _ _).symm); rw [map_zero]; exact camp_thaw h; exact ContinuousLinearEquiv.contDiff _|>.contDiffAt
variable {x y:ℝ→Cloud N}(g:ContDiffAt ℝ ω x 0)(k:x 0=0)(l:ContDiffAt ℝ ω y 0)(e:y 0=0)
section motion
include g k l e
lemma wages_t (U:ℝ→ Site (More N)→E)(V:ℝ→ Site (More X)→E)(t:Thaw (fun a=>wages T (V a) (U a) (natJoint F z (x a))) 0)(w:wages T (V 0) (U 0) (natJoint F z (x 0))=1)(h:∀ᶠ i in 𝓝 0, represent (y i)=Lattice.gauge (U i) (represent (x i))):
 ∀ᶠ i in 𝓝 0,∃ K:Site (More X)→ E, K∘ T.ratio.embed=U i ∧ baby F z (y i)= Lattice.gauge K (baby F z (x i)):=by
 obtain ⟨p,R,a,b,c,d,q,hc,h',hv,hp,hA⟩:=P.was
 let L:=(arm group (More N) 1).symm; let Y(i:ℝ):=L (y i); let J(i:ℝ):= wages T (V i) (U i) (natJoint F z (x i))
 have ht : Tendsto (fun i=>L (x i)) (𝓝 0) (𝓝 0):=by refine (show L (x 0)=0 from ?_) ▸ (L.contDiff.contDiffAt.comp 0 g).continuousAt.tendsto; rw [k,map_zero]
 have hy : Y 0=0:=by unfold Y; rw [e,map_zero];
 have he : ∀ᶠ i in 𝓝 0,Shell T q p R (input group _ (Y i)) (J i):=by
    filter_upwards [ht.eventually (camp_station hc h' hv q),h] with i hz hu; unfold Y; rw [show input group _ (L _)=_ from bornL _, hu, ← bornL]; exact hz.wage h' hv _ _
 filter_upwards [veterans hc h' hv hp hA q t w (L.contDiff.contDiffAt.comp 0 l) hy he] with i hz
 let K:= boots T F (J i); let r:=K* V i
 change wages T K 1 (wages T (V i) (U i) (natJoint F z (x i)))= natJoint F z (y i) at hz
 rw [wage_comp,one_mul,neo,neo] at hz; refine ⟨r,?_,(Prod.mk.inj hz).1.symm⟩; funext j; have hh:=congrFun (congrArg Prod.snd hz) j
 change U i j*1*(r (T.ratio.embed j))⁻¹=1 at hh; rw [mul_one] at hh
 exact (mul_inv_eq_one.mp hh).symm

lemma translation {G:Ratio N X}(hp:T.ratio= Rush.ratio G)(b: Cover)(h:∀ᶠ i in 𝓝 0, represent (y i)=Yg (lagX b) (represent (x i))): ∀ᶠ i in 𝓝 0,∃ K:Site (More X)→ E,K ∘ (Rush.ratio G).embed=1 ∧ baby F z (y i)= Lattice.gauge K (Yg ((lagX b).broad G) (baby F z (x i))):=by
 obtain ⟨p,R,a,d,c,v,t,hc,hT,hv,hx,hw⟩:=P.was
 let L:=(arm group (More N) 1).symm; let Y(i:ℝ):=L (y i); let s:=wrap (More N) (2 • b); let J(i:ℝ):= dragU (S:=T) s (natJoint F z (x i)); have ht : Thaw J 0:=thawT s 0 (Thaw.comp (g:=natJoint F z) (w:=x) (by rw [k]; exact P.army) g)
 have hu:J 0=1:=by unfold J; rw [k,P.flat']; rfl
 have hy : Y 0=0:=by unfold Y; rw [e,map_zero]
 have hh : Tendsto (fun i=>L (x i)) (𝓝 0) (𝓝 0):=by refine (show L (x 0)=0 from ?_) ▸ (L.contDiff.contDiffAt.comp 0 g).continuousAt.tendsto; rw [k,map_zero]
 let q:=T.withinChoice 1 s t
 have he: ∀ᶠ i in 𝓝 0,Shell T t p R (input group _ (Y i)) (J i):=by
   filter_upwards [hh.eventually (camp_station hc hT hv q),h] with i ht hx; unfold Y; rw [show input group _ (L _)= _ from bornL _,hx,Ylag,← bornL]; exact sailT s t _ _ hT ht
 filter_upwards [veterans hc hT hv hx hw t ht hu (L.contDiff.contDiffAt.comp 0 l) hy he] with i hz
 let K:=boots T F (J i); change wages T K 1 (J i)=natJoint F z (y i) at hz
 refine ⟨K,?_,?_⟩; funext u; rw [←hp]; have hh:=congrFun (congrArg Prod.snd hz) u; change 1 * (1:E) * (K (T.ratio.embed u))⁻¹=1 at hh; exact inv_eq_one.mp (by simpa using hh)
 change (natJoint F z (y i)).1=_; rw [←hz]; refine congrArg (Lattice.gauge K) ?_; change Lattice.translate (T.ratio.embed s) (baby F z (x i))=_; have hX:(lagX b).broad G=lagX (G.count.val • b):=rfl; rw [hX,Ylag, hp]; congr 1; unfold s; rw [Ratio.embed_wrap,smul_comm]; rfl
lemma slash {G:Ratio N X}(hp:T.ratio=Rush.ratio G)(b:Signed)(h:∀ᶠ i in 𝓝 0,represent (y i)=Yg (incX b) (represent (x i))):∀ᶠ i in 𝓝 0,∃ K:Site (More X)→ E,K ∘ (Rush.ratio G).embed=1 ∧ baby F z (y i)=Lattice.gauge K (Yg ((incX b).broad G) (baby F z (x i))):=by
 obtain ⟨p,R,a,d,c,v,t,hc,hT,hv,hx,hw⟩:=P.was
 let L:=(arm group (More N) 1).symm; let Y(i:ℝ):=L (y i); let J(i:ℝ):= twistUniform b (natJoint F z (x i)); have ht : Thaw J 0:=stationed_twist b (Thaw.comp (g:=natJoint F z) (w:=x) (x:=0) (by rw [k]; exact P.army) g); have hu:J 0=1:=by unfold J; rw [k,P.flat',twistUniform_one]
 have hy : Y 0=0:=by unfold Y; rw [e,map_zero]
 have hh : Tendsto (fun i=>L (x i)) (𝓝 0) (𝓝 0):=by refine (show L (x 0)=0 from ?_) ▸ (L.contDiff.contDiffAt.comp 0 g).continuousAt.tendsto; rw [k,map_zero]
 let q:=T.withinChoice b 0 t
 have he:∀ᶠ i in 𝓝 0, Shell T t p R (input group _ (Y i)) (J i):=by
    filter_upwards [hh.eventually (camp_station hc hT hv q),h] with i ht hx; unfold Y; rw [show input group _ (L _)= _ from bornL _,hx,Ywin, ←bornL]; exact sail b t hT _ _ ht
 filter_upwards [veterans hc hT hv hx hw t ht hu (L.contDiff.contDiffAt.comp 0 l) hy he] with i hz
 let K:=boots T F (J i); change wages T K 1 (J i)=natJoint F z (y i) at hz
 refine ⟨K,?_,?_⟩; funext u; rw [←hp]; have hh:=congrFun (congrArg Prod.snd hz) u; change 1 * (1:E) * (K (T.ratio.embed u))⁻¹=1 at hh; exact inv_eq_one.mp (by simpa using hh)
 rw [show (incX b).broad G=incX b from by simp [incX,Shape.broad],Ywin]; exact (congrArg Prod.fst hz).symm
end motion
lemma mirrors (U:E)(x:Cloud N):∀ᶠ s:ℝ in 𝓝 0,∃ V:Site (More X)→ E, V ∘ T.ratio.embed=(fun _=> U) ∧ baby F z (s • MarkT U x)= Lattice.gauge V (baby F z (s • x)):=by
 let f(s:ℝ):=s • x; let g(s:ℝ):=s • MarkT U x
 have hf: ContDiffAt ℝ ω f 0:=by unfold f; fun_prop
 let k(_:ℝ)(_:Site (More X)):=U; refine P.wages_t (x:=f) (y:=g) hf (zero_smul ..) (by unfold g; fun_prop) (zero_smul ..) (fun _ _=>U) k ?_ ?_ (Eventually.of_forall fun _=>orderD ..); exact ((Thaw.comp (g:=natJoint F z) (x:=0) (w:=f) (by unfold f; rw [zero_smul]; exact P.army) hf)).wages T (Army.park _ _) (Army.park _ _)
 unfold f; rw [zero_smul,P.flat']; refine Prod.ext (funext fun i=>?_) (funext fun i=>?_); simp [wages,Lattice.gauge,k]; simp [wages,k]
lemma shower (x:Site (More N))(f:Cloud N):∀ᶠ s:ℝ in 𝓝 0,∃ V:Site (More X)→ E,V ∘ T.ratio.embed=ramps x f s ∧ baby F z (race x f s)= Lattice.gauge V (baby F z (s • f)):=by
 let A(s:ℝ):=s • f; have he: ContDiffAt ℝ ω A 0:=by unfold A; fun_prop
 refine P.wages_t (x:=A) (y:=race x f) he (zero_smul ..) (sport ..) (roundS ..) _ (fun _=>1) ?_ ?_ (wraps ..)
 · apply (Thaw.comp (w:=A) (g:=natJoint F z) (x:=0) (by unfold A; rw [zero_smul]; exact P.army) he).wages T; exact Army.park _ _; intro i; unfold ramps; exact group.exp_jet.contDiffAt.comp (g:=fun z=>group.mat (group.lieExp z)) (f:=fun t:ℝ=>t • Font.sap x (collect group f) i) _ (by fun_prop)
 unfold A; rw [zero_smul,P.flat',ramps_0,wages_zero]
end Nativity
end YM.CF.Kennel
