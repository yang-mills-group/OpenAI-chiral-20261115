import YM.CF.Kennel.Alive
set_option autoImplicit false
noncomputable section
namespace YM.CF.Kennel
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {m A B L:Side}{j:ℕ}{ho:Odd L.val}{d a b:ℝ}{n:ℕ}
abbrev Vox(m B:Side):=Cloud (CSide m B)
abbrev Roam(m A B:Side):=RG.StepData (More (CSide m B)) (More (CSide A B))
structure Hull(j:ℕ)(L:Side)(ho:Odd L.val)(a b d e:ℝ)(n:ℕ) (m A B:Side) (G:Ratio (CSide m B) (CSide A B)) (T:Roam m A B) (F:Forest T.ratio) (z:Vox m B→ AxisChart group F) (Y:Pricing j L ho (Thread j))(V:Grasp Y B e):Prop where
 stamp :Stamped j L ho Y
 fromL:G.count=L
 alignT:T.ratio=ratio G
 request:n≤ (CSide m B).val
 size_p:V.roundZ≤(CSide m B).val
 even : Even j
 above : 1≤j
 tape : Spack j L ho a b d n
 native : Nativity F z
 hi:0<e
 po:0<d
variable {e:ℝ}{G:Ratio (CSide m B) (CSide A B)}{T:Roam m A B}{F:Forest T.ratio}{z:Vox m B→ AxisChart group F}{Y:Pricing j L ho (Thread j)}{V:Grasp Y B e} (M:Male)
variable (G j L ho F z) in
def emergence(f:Dress (CSide A B))(x:Vox m B):Op (Single (CSide m B)):=era L j ho G M (ears F z x) (f (baby F z x))
lemma betP (p:Op (Iota G)) : endorse G (0:Op (Single (CSide m B)))=0:=by ext i j; by_cases h:en G i∧ en G j<;> simp [endorse,extendK,h] -- tune
namespace Hull
variable (H:Hull j L ho a b d e n m A B G T F z Y V){U:Dress (CSide A B)}(p:relic U)
include H p
lemma kind(x:nomA m A B): crux j G M (ears F z 0) (U (baby F z 0))=0:=by unfold crux capT; rw [H.native.flat,p.1,show foot G (0:Op (Single (CSide A B)))=0 from rfl,mul_zero,zero_mul]
lemma kin : gate L j ho G M (ears F z 0) (U (baby F z 0))=0∧ leftN L j ho G M (ears F z 0) (U (baby F z 0))=0:=by unfold gate leftN desire bentT; rw [H.kind M p (ears F z 0), star_zero, neg_zero,mul_zero,mul_zero]; trivial -- order
lemma val: emergence L j ho G F z M U 0=0:=by
 unfold emergence era; rw [kind M H p 1]; unfold fruit traitP creep; let x:= ears F z 0; have hy: unionP x=1:=by
    unfold unionP x; rw [show ears F z 0= (1:nomA m A B) from Prod.ext H.native.flat link_one]; change (profile (1:Bkg _),profile (1:Bkg _))= _; simp [profile_trivial]
 rw [show unionP _= _ from hy]; simp only [bentT,mul_zero,add_zero,one_mul,mul_one,inv_one]; apply Thera.endorseI G; rw [spry]; change lum _ _ _ _ true M G 1=endorse G 0; rw [cologne j L ho H.even H.above (Thread j) (canUse _ _ ho) _ _ H.fromL,betP (0:Op (Iota G))] -- tune name/order
lemma terms : ContDiffAt ℝ ω (fun x=> crux j G M (ears F z x) (U (baby F z x))) 0∧ ContDiffAt ℝ ω (fun x=> gate L j ho G M (ears F z x) (U (baby F z x))) 0 ∧ContDiffAt ℝ ω (fun x=> leftN L j ho G M (ears F z x) (U (baby F z x))) 0 ∧ ContDiffAt ℝ ω (emergence L j ho G F z M U) 0:=by
 have ht:= H.native.melod d H.po G
 let g:=chillQ H.tape H.fromL H.request M 0 H.native.tarnish (combine H.native p) (ambient _ _ H.po le_rfl ht.self_of_nhds)
 refine ⟨g.1,g.2.1,g.2.2.1,g.2.2.2 ?_⟩; rw [Function.comp_apply,H.kin M p|>.1]; simp
lemma nickP: ∀ᶠ x in 𝓝 0, ‖gate L j ho G M (ears F z x) (U (baby F z x))‖<1 ∧ ‖leftN L j ho G M (ears F z x) (U (baby F z x))‖<1:=by
 obtain ⟨-,f,q,u⟩:= H.terms M p; obtain ⟨r,h⟩:= H.kin M p
 apply Eventually.and; · exact f.continuousAt.norm.tendsto.eventually (gt_mem_nhds (show ‖gate L j ho G M (ears F z 0) (U (baby F z 0))‖<1 from by simp [r]))
 exact q.continuousAt.norm.tendsto.eventually (gt_mem_nhds (show ‖leftN L j ho G M (ears F z 0) (U (baby F z 0))‖<1 from by simp [h]))
omit p
section legs
variable {X X':ℝ→ Vox m B}(f:Tendsto X (𝓝 0) (𝓝 0))
include p f
private lemma scenery (q:ripeF U)(t:ℝ→ Site (More (CSide m B))→E)(h:∀ᶠ s in 𝓝 (0:ℝ), ∃ g:Site (More (CSide A B))→E, g∘ T.ratio.embed=t s∧ baby F z (X' s)=Lattice.gauge g (baby F z (X s)))(v:∀ᶠ s in 𝓝 (0:ℝ),represent (X' s)=Lattice.gauge (t s) (represent (X s))): ∀ᶠ s in 𝓝 (0:ℝ), emergence L j ho G F z M U (X' s)=ActZ (t s) (emergence L j ho G F z M U (X s)):=by
 filter_upwards [h,v,f.eventually (H.native.melod d H.po G),f.eventually (H.nickP M p)] with s hs hy hv ht; obtain ⟨g,r,R⟩:=hs
 let x:=ears F z (X s); have he: scaleG G g=t s:= by unfold scaleG; rw [←H.alignT]; exact r
 unfold emergence; rw [show ears F z (X' s)=july G g x from Prod.ext R (by rw [←he] at hy; exact hy),R,q]; exact he ▸ (Dusk H.tape G M H.fromL H.request x (ambient _ _ H.po le_rfl hv) g (U x.1) ht.1).1 -- tune
lemma ranger {W:Dress (CSide A B)} (q:ripeF W)(a:Shape)(h:∀ᶠ s in 𝓝 0, ∃ g:Site (More (CSide A B))→E,g ∘ (ratio G).embed=1 ∧ baby F z (X' s)= Lattice.gauge g (Yg (a.broad G) (baby F z (X s))))(l:∀ᶠ s in 𝓝 (0:ℝ), represent (X' s)=Yg a (represent (X s)))(v:∀ x:Bkg (More (CSide A B)), W (Yg (a.broad G) x)= ZoneH (a.broad G) (U x)): ∀ᶠ s in 𝓝 (0:ℝ), emergence L j ho G F z M W (X' s)=ZoneH a (emergence L j ho G F z M U (X s)):=by
 filter_upwards [h,l,f.eventually (H.native.melod e H.hi G),f.eventually (H.native.melod d H.po G), f.eventually (H.nickP M p)] with s hs hy hu hv ht; obtain ⟨g,r,R⟩:=hs
 let x:=ears F z (X s); let V:=U (baby F z (X s)); let t:=scaleG G g; let y:=stanza G a inert x; have he: ears F z (X' s)=july G g y:= Prod.ext R (show _=_ from hy.trans (by change y.2= Lattice.gauge t y.2; rw [show t=1 from r,Stationary.gauge_one])) -- tune
 let Z:=ZoneH (a.broad G) V; obtain ⟨Hq,Hx,Hz⟩:= duelX H.above H.hi H.stamp H.fromL H.size_p hu (H.tape.tape _ H.fromL H.request M (unionP x) (ambient _ _ H.po le_rfl hv)) V a _ rfl ht.1 ht.2
 unfold emergence; rw [he,R,q,v]; change era L _ _ G M (july G g y) (ActZ g Z)= _; have hr:ActZ (n:=CSide m B) (1:Site _ → E) = id:=by funext i; unfold ActZ tradew; simp only [Pi.one_apply,map_one, twist_formula]; rw [show (jump (Equiv.refl (Site (CSide m B) × SpinIdx)) (fun _=> (1:UNI Slot).val))=1 from jump_id,one_mul,star_one,mul_one]; rfl -- tune
 have hG:=Dusk H.tape G M H.fromL H.request y (ambient _ _ H.po le_rfl (alongS inert a G (ears F z (X s)) d hv)) g Z Hz
 rw [show scaleG G g=1 from r, hr] at hG; exact hG.1.trans Hq
end legs
include p
def Plane {N:Side}(V:Dress N):Prop:=∀ (a:Signed)(U:Bkg (More N)), V (Yg (incX a) U)= ZoneH (incX a) (V U)
structure Glowing {N:Side}(V:Rhyme N):Prop where
 strong(g:E)(x:Cloud N):∀ᶠ s:ℝ in 𝓝 0,V (s • MarkT g x)=ActZ (fun _=> g) (V (s • x))
 way(t:Cover)(x:Cloud N):∀ᶠ s:ℝ in 𝓝 0,V (s • SubMotion t x)=ZoneH (lagX t) (V (s • x))
omit H p in
lemma ray_home {X:Type*}[NormedAddCommGroup X][NormedSpace ℝ X](x:X):Tendsto (fun t:ℝ=>t • x) (𝓝 0) (𝓝 0):=by simpa only [zero_smul] using (show Continuous (fun t:ℝ=> t • x) from by fun_prop).tendsto 0
lemma glen (q:ripeF U)(k:Across U): Glowing (emergence L j ho G F z M U) :=by
 constructor; intro g x; exact H.scenery M p (ray_home x) q (fun _ _=>g) (H.native.mirrors g x) (Eventually.of_forall fun s=>orderD g x s)
 intro t x; let f:=lagX t; apply H.ranger M p (ray_home x) q f ?_ (Eventually.of_forall fun s=>height x t s) (fun u=> k _ _); exact H.native.translation (x:=fun s:ℝ=> s • x) (y:=fun s:ℝ=> s • SubMotion t x) (by fun_prop) (zero_smul ..) (by fun_prop) (zero_smul ..) H.alignT t (Eventually.of_forall fun s=>height ..) -- tune
lemma breeze (i:Signed){W:Dress (CSide A B)}(q:ripeF W)(h:∀ x:Bkg _, W (Yg (incX i) x)=ZoneH (incX i) (U x)) (x: Vox m B):∀ᶠ s:ℝ in 𝓝 0,emergence L j ho G F z M W (s • litX i x)=ZoneH (incX i) (emergence L j ho G F z M U (s • x)):=by
 let f:= incX i; have he : f.broad G=f:=by simp [f,incX,Shape.broad]
 have ht: ∀ᶠ s:ℝ in 𝓝 0,represent (s • litX i x)=Yg f (represent (s • x)):= Eventually.of_forall fun s=> (roomy i x s).symm
 exact H.ranger M p (ray_home x) q f (H.native.slash (x:=fun s:ℝ=>s • x) (y:=fun s:ℝ=>s • litX i x) (by fun_prop) (zero_smul ..) (by fun_prop) (zero_smul ..) H.alignT i ht) ht (by rw [he]; exact h)
lemma nimbus(q:ripeF U)(k:Across U)(h: Plane U):Nacre.Motion (emergence L j ho G F z M U):=by
 obtain ⟨t,y⟩:=H.glen M p q k; constructor; exact t; exact y; exact fun i=> H.breeze M p i q (h i)
 intro x z; exact H.scenery M p (ray_home x) q (ramps z x) (H.native.shower z x) (wraps ..)
end Hull
end YM.CF.Kennel
