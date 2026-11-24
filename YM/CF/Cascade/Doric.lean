import YM.CF.Cascade.Seashore
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
def gala (M:Male)(j:ℕ)(U:Dress n)(x:Bkg (More n)):= OrbT (tickA n) (spar j M x) (Crops j M U x)
lemma yuE {A:Op (Single n)}{U:Op (Single n)}{t:UNI (Single n)}(p:twist t (tickA n)=tickA n):OrbT (tickA n) (twist t A) (twist t U)= OrbT (tickA n) A U:=by
 let X(A U:Op (Single n)):= tickA n*(1+U)*A; let Y:=X A U; have he:X (twist t A) (twist t U)=twist t Y:=by unfold X Y; unfold X; rw [map_mul,map_mul,map_add,map_one,p]
 change -(Real.log ((Zoom n _).det.re))/2= -(Real.log ((Zoom n Y).det.re))/2 -- zoom def
 have hk : Zoom n (X (twist t A) (twist t U))=twist t (Zoom n Y):=by rw [he]; unfold Zoom; rw [map_add,map_mul (twist t) Y,map_star,map_sub,map_one,p]
 change -(Real.log ((Zoom n (X _ _)).det.re))/2= _; rw [hk]; let F:= Zoom n Y
 rw [twist_formula,Matrix.det_mul,Matrix.det_mul, mul_comm t.val.det, mul_assoc, ←Matrix.det_mul,t.property.2,Matrix.det_one,mul_one]
lemma vase (w:P.roundZ≤ n.val)(M:Male)(l:0<e)(U:Dress n)(u:ripeF U):Pec.Vale (Complex.ofRealCLM ∘ gala M j U ∘ represent):=by
 let A:= spar j M (N:=n); let B:=gala M j U; let Z:= Crops j M U; let V:=Complex.ofRealCLM; have he(x) (hx: Guard x e)(g): V (B (Lattice.gauge g x))= V (B x):=by
    have hx:= (P.broadness n w M).covary x g hx; change V (OrbT _ (A _) _)=_; unfold A; rw [hx]; apply congrArg V; change OrbT _ _ (Crops j M U (Lattice.gauge g x))= _; rw [show Crops j M U (Lattice.gauge g x)= twist (tradew n g) (Z x) from ?_]; apply yuE (tick_g _); unfold Crops Z capT; rw [hx,u]; change capT _ _ = twist _ _ -- tune
    simp [Crops, capT]
 have hk:= nearB (n:=n) e l; constructor; intro g x; filter_upwards [(Hull.ray_home x).eventually hk] with i hi; simp only [Function.comp_apply,orderD]; exact he _ hi _
 intro x v; filter_upwards [(Hull.ray_home x).eventually hk,wraps v x] with i hi hx; change V (B _)= _; rw [show represent (race v x i)=_ from hx]; exact he _ hi _
lemma gala_h (s:P.roundZ≤n.val)(l:0<e)(p:1≤j)(h:Stamped j L ho Y)(M:Male)(U:Dress n) (v:Ample U)(Q:ContDiffAt ℝ ω ((spar j M) ∘ represent (n:=More n)) 0):ContDiffAt ℝ ω (gala M j U ∘ represent) 0:=by
 let u:CoreX:=0; have he:= hourZ U M u (Grace u l p h M s U v Q); have hx: ContDiffAt ℝ ω (grace j M U) 0:= (((contDiffAt_const (c:=tickA n)).mul (contDiffAt_const.add (((contDiffAt_const.sub Q).mul v.self.2).mul Q))).mul Q)
 have hm:gala M j U ∘ represent= foray n ∘ grace j M U:=funext fun i=> (beamCash ..).symm; rw [hm]; exact (heat_n n _ he).comp _ hx
lemma inkJ (F: Nom (CSide m B) (CSide X B))(p:Dress (CSide X B)): foot G (Crops j M p F.1)=crux j G M F (p F.1):=by
 let V:= spar j M F.1; rw [crux,Crops,capT]; change foot G ((1-V)*_* V)=(1-foot G V)*_* _; rw [foot_mul,foot_mul,foot_sub,foot_one]; rfl
lemma koh (V: Nom (CSide m B) (CSide X B))(p: JointB G V e) (H:G.count=L)(Z:P.roundZ≤ (CSide m B).val)(N:Op (Single (CSide X B)))(h: ‖desire L j ho G M V (foot G N)‖<1)(hx: IsUnit ((love _).symm (Zoom _ (tickA _*(1+N)*spar j M V.1))))(w: Matrix.trace (tickA (CSide X B))=Matrix.trace (spar j M V.1)): skyGlow (oceanA G) (1+foot G N) (graft G P V.1 M)≠0:=by
 let A:=tickA (CSide X B); let U:=spar j M V.1; let C:= A*(1+N)*U; let X':= Zoom (CSide X B) C; let s:=V.1; let g:= P.broadness _ (P.clock_fine G Z) M; have hv: IsStarProjection U:=g.projection _ p.fg; have he: IsStarProjection (foot G U):=carts_p (switchG G).symm hv; let Y:=lobe G true
 have hy:Y=foot G A:= lobe_t G; have hp (X :Op (Single (CSide X B))): Matrix.trace (foot G X)=Matrix.trace X:= Equiv.sum_comp (switchG G) (fun i=> X i i)
 have hq:Matrix.trace Y=Matrix.trace (foot G U):=by rw [hy,hp,hp]; exact w
 have hl:Matrix.det X'≠0:= by rw [←Matrix.det_submatrix_equiv_self (helix _).symm]; exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hx) -- tune arg order
 intro hx; have hh:= prismK he (lobe_sq ..) hq (1+foot G N) _ (show Sea (foot G U) (graft G P V.1 M) from carts_sea (switchG G).symm hv (sea_g (P.clock_fine G Z) s p.fg M)) _ (seaA G); rw [show skyGlow _ _ _ = _ from hx] at hh; simp only [norm_zero,zero_pow (show (2:ℕ)≠0 by omega),Complex.ofReal_zero] at hh; apply hl; apply Eq.trans _ hh.symm; rw [show lobe G true=_ from hy]; rw [←foot_one,←foot_sub,←foot_add,←foot_mul,←foot_mul,←foot_s,←foot_mul,←foot_add]; exact (Matrix.det_submatrix_equiv_self ..).symm
lemma shear (U:Dress (CSide X B))(H:Hull j L ho a b d e t m X B G T F z Y P)(q:Ample U)(M:Male)(A:ContDiffAt ℝ ω ((spar j M (N:=CSide X B)) ∘ represent) 0): ∀ᶠ x:Vox m B in 𝓝 0, gala M j U (baby F z x)= (Pec.lush G P M U (ears F z x)).re+ OrbT (tickA _) (spar j (upMale L ho M) (represent x)) (emergence L j ho G F z M U x):=by
 let L':= CSide X B; let P':=spar j M (N:=L'); let K:=tickA L'; let Cs(w:Cloud L'):= Crops j M U (represent w)
 have hs:= H.native.melod e H.hi G; let V:=grace j M U; have hv:ContDiffAt ℝ ω V 0:= ((contDiffAt_const (c:=K)).mul (contDiffAt_const.add (((contDiffAt_const.sub A).mul q.self.2).mul A))|>.mul A)
 have ht:∀ᶠ i in 𝓝 (0:Cloud L'), IsUnit ((love L').symm (Zoom _ (V i))):=by -- use Continuous
    have he:ContinuousAt (fun i:Cloud L'=>(love L').symm (Zoom _ (V i))) 0:=by unfold Zoom; let X:= (love L').symm.toAlgEquiv.toLinearEquiv.toLinearMap.toContinuousLinearMap; exact X.continuous.continuousAt.comp ((hv.continuousAt.mul hv.continuousAt.star).add continuousAt_const)
    exact he.tendsto.eventually (Units.isOpen.mem_nhds (hourZ U M 0 (Grace 0 H.hi H.above H.stamp M (P.clock_fine G H.size_p) U q A)))
 have hr:P.roundZ≤L'.val:=P.clock_fine G H.size_p; have hp:= trace_near (0:Cloud L') (P'∘ represent) A.continuousAt ((nearB (n:=L') e H.hi).mono fun i hi=> (P.broadness _ hr M).projection _ hi)
 let f:= chartOf F z; have hx:Tendsto f (𝓝 0) (𝓝 0):=by have hv:= H.native.kala.continuousAt; change Tendsto f _ _; exact (H.native.icicle: f 0=0) ▸ hv.tendsto
 filter_upwards [hx.eventually ht,hx.eventually hp,H.nickP M q.self,hs,H.native.foldM] with x hs hl hk hb ht
 let Q:= ears F z x; let N:=Crops j M U Q.1; have hu:Cs (f x)=N:=by unfold Cs N; rw [show represent (f x)=_ from ht.symm]; rfl
 have he:foot G N= _:= inkJ Q U (G:=G) (j:=j) (M:=M); have hS : ‖desire L j ho G M Q (foot G N)‖<1:=he.symm ▸ hk.1; have ha:Matrix.trace K=Matrix.trace (P' Q.1):=by
    change Matrix.trace (P' (represent (f x)))= Matrix.trace (P' (represent 0)) at hl; rw [show represent (f x)=Q.1 from ht.symm,link_one] at hl; exact (rank_z L' H.above M).symm.trans hl.symm
 have hg: IsUnit ((love L').symm (Zoom _ (tickA L'*(1+N)*spar j M Q.1))):=by
    change IsUnit ((love L').symm (Zoom _ (K*(1+Cs (f x))*spar j M (represent (f x))))) at hs; rw [hu,show represent (f x)=Q.1 from ht.symm] at hs; exact hs
 have hw := laser H.hi G H.fromL H.size_p M Q hb (show TagG _ N from tag_g _ ((P.broadness _ hr M).projection _ hb.fg)) hS ha (koh Q hb H.fromL H.size_p N hS hg ha)
 rw [he,Complex.add_re, neg_add] at hw; unfold Pec.lush; rw [Complex.sub_re,Complex.neg_re,sub_eq_add_neg]; exact hw
end YM.CF.Cascade
