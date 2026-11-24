import YM.SU5.Celeste.Claret
import YM.SU5.Celeste.Stanzas
/-! # Flat comparisons BEFORE pruning. tools. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 200000
noncomputable section
namespace YM.CF.Lamour.Bridge.Celeste
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye Pannier.Chancel Brace Velvet Hours Flare Cliplet RG Reed
open Py.Rate.Pannier
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
open Py Py.Rate Py.Rate.LocalLimit
open Py.Rate.LocalLimit.Papal (Weaver household)
open Signal.Interval (separationCost)
open Buffered.Afterglow
variable {N:Side}{j d r:ℕ}
variable {S T:Finset Cover} {F Z:Weaver}
abbrev dBook (N:Side)(S:Finset Cover):= S.image (wrap (More N)) -- Sart region
variable {ζ C B v ε:ℝ}
lemma liftMoney (S:Finset Cover):∀ᶠ N:Side in atTop,∀ x∈ S,∀ y∈ S,separation (wrap (More N) x) (wrap (More N) y)=separationCost x y:=by
 apply (Finset.eventually_all ..).2; intro x hx; apply (Finset.eventually_all ..).2; intro y hy;
 let v:= separationCost x y; filter_upwards [eventually_ge_atTop (⟨2*v+1,by omega⟩:Side)] with N e; have ht:Lattice.lift (wrap (More N) (x-y))=x-y:=by apply lift_eq_iff.mpr; refine ⟨rfl,fun i=>?_⟩; have h:((x-y) i).natAbs≤v:= Finset.le_sup (f:=fun i=> ((x-y) i).natAbs) (mem_univ _); rw [show (More N).val=N.val*2 from rfl]; change 2*v+1 ≤ N.val at e; omega
 unfold separation pdist separationCost; rw [←map_sub]; simp_rw [ht]
lemma distantBook (h:∀ x∈ S,∀ y∈ T,d≤ separationCost x y):∀ᶠ N:Side in atTop, Distant d (dBook N S) (dBook N T):=by
 filter_upwards [liftMoney (S∪T)] with N he x hp y t; obtain ⟨x,u,rfl⟩:= mem_image.mp hp; obtain ⟨y,v,rfl⟩:=mem_image.mp t; rw [he _ (mem_union_left _ u) _ (mem_union_right _ v)]; exact h _ u _ v
def breadth (o:Cover)(S:Finset Cover):ℕ:=S.sup fun x=>separationCost o x
lemma breadthMoney (o:Cover)(S:Finset Cover):∀ᶠ N:Side in atTop, dBook N S⊆ BlockP (breadth o S) (wrap (More N) o):=by
 filter_upwards [liftMoney (insert o S)] with N h x u; obtain ⟨x,p,rfl⟩:=mem_image.mp u; exact blocks_test.mpr ((h _ (mem_insert_self ..) _ (mem_insert_of_mem p)).trans_le (le_sup (f:=fun x=> separationCost o x) p))
def Temperature (F:Weaver)(S:Finset Cover):Prop:=∀ ε>(0:ℝ),∀ᶠ ζ:ℝ in 𝓝[>] (0:ℝ),∀ (N:Side)(x:Fields N),Rightful (dBook N S) x.1 1 ζ → Rightful (dBook N S) x.2 1 ζ →‖F N x-F N (1,1)‖≤ ε
structure Passion (F:Weaver)(S:Finset Cover)(b:Bool) : Prop where
 rent : ∃ C:ℝ,0≤ C∧∀ (N:Side)(x:Fields N),‖F N x‖≤ C
 fee : Temperature F S
 bounded (N:Side): AtSupport b (dBook N S) (F N)
 narrow (K:Calibration) : InTest K false S b (household K F)
namespace Passion
variable {b c:Bool}
lemma htM_N (t:Temperature F S)(g:S⊆T): Temperature F T:=by intro e he; filter_upwards [t e he] with ζ h N X u v; exact h N X (loft_rightful u le_rfl (image_subset_image g)) (loft_rightful v le_rfl (image_subset_image g))
lemma mono (p:Passion F S b)(q:S⊆T): Passion F T b:=⟨p.rent,htM_N p.fee q,fun N=>(p.bounded N).mono (image_subset_image q),fun K=>(p.narrow K).mono q⟩
lemma zero(S:Finset Cover)(b:Bool): Passion 0 S b:=⟨⟨0,le_rfl,by simp⟩,fun a h=> Eventually.of_forall (fun v _ _ _ _=> by simpa using h.le),fun _=>AtSupport.zeroM,fun _=>.zero⟩
lemma one(S:Finset Cover):Passion 1 S false:=⟨⟨1,zero_le_one,by simp⟩,fun a h=> Eventually.of_forall (fun v _ _ _ _=> by simpa using h.le),fun _=>AtSupport.oneM _,fun _=>.one⟩ -- no prop map comp
lemma haze (p: Passion F S b)(u:ℂ):Passion (u • F) S b:=by
 obtain ⟨C,f,h⟩:=p.rent; refine ⟨⟨‖u‖*C,by positivity,fun N x=> (norm_smul u (F N x)).trans_le (mul_le_mul_of_nonneg_left (h N x) (norm_nonneg _))⟩,?_,fun N=>(p.bounded N).smulM u,fun K=>.smul u (p.narrow K)⟩
 intro a hu; let t:= a/(‖u‖+1); have he:0<t:=by unfold t; positivity
 filter_upwards [p.fee t he] with ζ h N X hx hy; change ‖u • (F N X)-u • (F N (1,1))‖≤_; rw [← smul_sub,norm_smul]; exact (mul_le_mul_of_nonneg_left (h N X hx hy) (norm_nonneg _)).trans (by have ht:t*(‖u‖+1)=a:= div_mul_cancel₀ _ (by positivity); linarith) -- tune
lemma fuse (p:Passion F S b)(q:Passion Z S b): Passion (F+Z) S b:=by
 obtain ⟨u,e,v⟩:=p.rent; obtain ⟨l,g,t⟩:=q.rent; refine ⟨⟨u+l,add_nonneg e g,fun N x=> (norm_add_le ..).trans (add_le_add (v N x) (t N x))⟩,?_,fun N=>(p.bounded N).addM (q.bounded N),fun K=>.add (p.narrow K) (q.narrow K)⟩
 intro a he; filter_upwards [p.fee (a/2) (by positivity),q.fee (a/2) (by positivity)] with ζ h hz N X k i; rw [Pi.add_apply, Pi.add_apply,Pi.add_apply,add_sub_add_comm]; exact (norm_add_le ..).trans ((add_le_add (h N X k i) (hz N X k i)).trans (by linarith only [he]))
lemma shade (p:Passion F S b)(q:Passion Z S b): Passion (F-Z) S b:=by rw [sub_eq_add_neg,←neg_one_smul ℂ]; exact p.fuse (q.haze _)
lemma spun (h:Passion F S b)(u:Passion Z S c): Passion (F*Z) S (b.xor c):=by
 obtain ⟨C,p,q⟩:=h.rent; obtain ⟨D,d,l⟩:=u.rent; refine ⟨⟨C*D,by positivity,fun N x=> (norm_mul_le ..).trans (mul_le_mul (q N x) (l N x) (norm_nonneg _) p)⟩,?_,fun N=>(h.bounded N).mulM (u.bounded N),fun K=>.mul (h.narrow K) (u.narrow K)⟩
 intro a e; let v:= a/(C+D+1); have hv:0<v:= by unfold v; positivity
 filter_upwards [h.fee v hv,u.fee v hv] with t f g N x t1 t2; let k:Fields N:=(1,1); rw [Pi.mul_apply, Pi.mul_apply,Pi.mul_apply]; rw [show F N x* Z N x - F N k * Z N k= F N k*(Z N x-Z N k)+(F N x-F N k)*Z N x from (by simp only [mul_sub, sub_mul]; abel)]; -- tune meta
 refine (norm_add_le ..).trans ((add_le_add ((norm_mul_le ..).trans (mul_le_mul (q N k) (g N x t1 t2) (norm_nonneg _) p)) ((norm_mul_le ..).trans (mul_le_mul (f N x t1 t2) (l N x) (norm_nonneg _) hv.le))).trans ?_); have he:v*(C+D+1)=a:= div_mul_cancel₀ _ (by positivity); linarith
lemma weaveSum{α:Type*}(V:Finset α)(F:α→Weaver)(p:∀i∈V,Passion (F i) S b):Passion (∑ i∈ V,F i) S b:=by classical
 induction V using Finset.induction_on with| empty=>rw [sum_empty]; exact zero S b| @insert i V x ih=> rw [sum_insert x]; exact fuse (p i (mem_insert_self ..)) (ih fun j t=> p j (mem_insert_of_mem t))
end Passion
def fluent (i:Axis)(z:ℤ)(F:Weaver) : Weaver:= fun N=> reflMark i z (F N)
def traction (i:Axis)(z:ℤ)(F:Weaver) : Weaver:= fluent i z (fluent i 0 F)
lemma d_Book_flip (i:Axis)(z:ℤ)(S:Finset Cover):dBook N (Tower.reflectedBox i z S)=hyphen i z (dBook N S):=by unfold dBook hyphen Tower.reflectedBox; rw [image_image,image_image]; exact image_congr fun x h=> (Shape.anno ..).symm
lemma Passion.turn {b:Bool}(p:Passion F S b) (i:Axis)(z:ℤ):Passion (fluent i z F) (Tower.reflectedBox i z S) b:=by
 obtain ⟨v,h,x⟩:= p.rent; refine ⟨⟨v,h,fun N y=>?_⟩,?_,fun N=>d_Book_flip (N:=N) i z S ▸ (p.bounded N).refl i z,fun K=> Tower.axial K i z (p.narrow K)⟩
 · rw [fluent,reflMark,theta,twist_norm,norm_cc]; exact x _ _
 intro e hz; filter_upwards [p.fee e hz] with ψ ht N X g T;
 have hh:=turnBox (F:=F N) (show BoxProof ψ v e (F N) _ from ⟨x N,ht N⟩) i z; rw [d_Book_flip] at g T; exact hh.2 X g T
lemma Passion.tract {b:Bool}(p: Passion F S b)(i:Axis)(z:ℤ): Passion (traction i z F) (Tower.address i z S) b:= by
 let h:= (p.turn i 0).turn i z; rw [Tower.support_translation,sub_zero] at h; exact h
def Speak (F:Weaver) : Prop:=∀ N:Side, Buffered.covariant (F N)
lemma Speak.one: Speak 1:=fun N _ _=> (map_one _).symm
lemma Speak.sub (p:Speak F)(q: Speak Z): Speak (F-Z):=fun N g U=>by rw [Pi.sub_apply, Pi.sub_apply,Pi.sub_apply,p N g U,q N g U,map_sub]
lemma Speak.haze (p:Speak F)(u:ℂ):Speak (u • F):= fun N g U=>by rw [Pi.smul_apply,Pi.smul_apply,Pi.smul_apply,p N g U, twist_scalar]
lemma Speak.spun (p:Speak F)(q: Speak Z):Speak (F*Z):= fun N g U=> by rw [Pi.mul_apply,Pi.mul_apply,Pi.mul_apply,p N g U,q N g U,map_mul]
lemma Speak.flip {b:Bool}(h:Passion F S b)(p: Speak F)(i:Axis)(z:ℤ): Speak (fluent i z F):= fun N=> covariant_reflected (h.bounded N) (p N) z i
lemma Speak.tract {b:Bool}(h:Passion F S b)(p:Speak F)(i:Axis)(z:ℤ): Speak (traction i z F):=Speak.flip (h.turn i 0) (p.flip h i 0) i z -- dot notation order tune
def Clarity (F: Weaver) (j:ℕ)(ε:ℝ):Prop:=∀ᶠ N:Side in atTop, Even N.val →∀ M:Tulip.Male,∀ (x:Wave (Single N)),Sea (spar j M (1:Pane N)) x→ ‖alleyR (mateK N) x (F N (1,1))‖≤ε
lemma Clarity.turn (h:1≤ j)(p:Clarity F j ε)(i:Axis)(z:ℤ): Clarity (fluent i z F) j ε:=by filter_upwards [ownsHalo h,p] with N h u t M x v; change ‖alleyR _ x (reflMark i z (F N) (1,1))‖≤_; rw [mirror_fare i z (h t) v v,norm_star]; exact u t M x v
lemma Clarity.tract (h:1≤ j)(p:Clarity F j ε)(i:Axis)(z:ℤ): Clarity (traction i z F) j ε:= (p.turn h i 0).turn h i z
def Voice (F: Weaver) (S: Finset Cover) : Prop:= Passion F S false ∧ Speak F
lemma Voice.mono (h: Voice F S)(p:S⊆ T): Voice F T:=⟨h.1.mono p,h.2⟩
lemma Voice.sub (p: Voice F S)(q: Voice Z S): Voice (F-Z) S:=⟨p.1.shade q.1,p.2.sub q.2⟩
lemma Voice.mul (p:Voice F S)(q:Voice Z T): Voice (F*Z) (S∪T):=⟨(p.1.mono (subset_union_left (s₂:=T))).spun (q.1.mono subset_union_right),p.2.spun q.2⟩
lemma Voice.hushed (p:Voice F S)(z:ℂ): Voice (z • F) S:=⟨p.1.haze z,p.2.haze z⟩
lemma Voice.turn(p:Voice F S)(i:Axis)(z:ℤ):Voice (fluent i z F) (Tower.reflectedBox i z S):=⟨p.1.turn i z,p.2.flip p.1 i z⟩
lemma Voice.tract(p:Voice F S)(i:Axis)(z:ℤ):Voice (traction i z F) (Tower.address i z S):=⟨p.1.tract i z,p.2.tract p.1 i z⟩
lemma Voice.one(S:Finset Cover): Voice 1 S:=⟨Passion.one S, Speak.one⟩
lemma recital_turn (F:Weaver)(h:HaloTw j N)(M:Tulip.Male)(x:Wave (Single N))(u:Sea (spar j M (1:Pane N)) x)(i:Axis)(z:ℤ):
 let E:=alleyR (mateK N) x; E (traction i z F N (1,1))=E (F N (1,1)):= by
 intro E; change alleyR _ _ _= _; rw [traction,fluent,mirror_fare i z h u u,fluent,mirror_fare i 0 h u u,star_star]
-- from this world to BroadWeld uniformly after height & stencil demand, all Weaver with these geometry & estimates. -/
lemma buys (o:Cover)(h:Voice F S)(u:o∈S)(p:Clarity F j (B/4)) (he:S.card≤ d)(hv:breadth o S ≤ r)
    (q:∀ (N:Side)(y:Fields N),‖F N y‖≤C)(e:0<ε) : ∀ᶠ t:ℝ in 𝓝[>] (0:ℝ),∀ᶠ N:Side in atTop,Even N.val → Py.Rate.LocalLimit.Papal.BroadWeld N F r d j ε t C B:=by -- delete -/ at comments
 filter_upwards [h.1.fee ε e] with t ht; filter_upwards [p,breadthMoney o S] with N p z v M; let I:=dBook N S; let j₀:=wrap (More N) o
 exact ⟨I, j₀,⟨⟨q N,ht N⟩,h.2 N,h.1.bounded N,card_image_le.trans he,fun y t=> blocks_test.mpr ((blocks_test.mp (z t)).trans hv),mem_image_of_mem _ u,p v _ ⟩⟩
end YM.CF.Lamour.Bridge.Celeste
#print axioms YM.CF.Lamour.Bridge.Celeste.buys
#print axioms YM.CF.Lamour.Bridge.Celeste.Voice.turn
