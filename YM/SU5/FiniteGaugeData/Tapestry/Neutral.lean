import YM.SU5.FiniteGaugeData.Tapestry.Symphony
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tapestry
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock
open Satin
attribute [local instance] opCStarAlgebra

/-!
# Gauge actions on cover. Singlets at a single hospitable side are singlets even on
small sides, and the same local covariance condition passes through the limits.
-/
set_option quotPrecheck false
open Haro Tap Cascade Dial Mir Girt Nacre Pastry Phase RP
section
variable (N: Side)(g: Seat N→ SU.E)
private lemma turn_basis (x:Site N × SpinIdx)(u:SU.Slot):
    acts (tradew N g).val (basisKet (x,u))= ∑ i:SU.Slot,(matter (g (node x.1))).val i u • basisKet (x,i):=by -- adapt Emu/Fill
  apply PiLp.ext; intro j; rw [basis_act]; simp only [WithLp.ofLp_sum,Finset.sum_apply,basis_apply,ite_true,WithLp.ofLp_smul,Pi.smul_apply, smul_eq_mul, mul_ite,mul_one,mul_zero]; rcases j with ⟨j,i⟩; -- tune
  rw [sum_eq_single i]; swap; · intro m _ e; rw [if_neg (fun w=>e (Prod.mk.inj w).2.symm)]
  swap; · simp
  change jump (Equiv.refl (Site N × SpinIdx)) (fun i=> (matter (g (node i.1))).val) (j,i) (x,u)=_; rw [jump_apply]; simp only [Equiv.refl_apply,Prod.mk.injEq, and_self,and_true,eq_self]; split
  · next h=> subst j; rfl
  next _=> rfl
lemma turn_basisC (x:Cover)(i:SpinIdx)(a:SU.Slot): acts (tradew N g).val (basisC N x i a)=∑ j:SU.Slot,(matter (g (wrap (More N) (nodeC x)))).val j a • basisC N x i j:=by
  unfold basisC Lifted.index; rw [map_smul,turn_basis N g (wrap N x,i) a]; simp_rw [smul_comm (_ : ℂ) (Lifted.winding N x), Finset.smul_sum,← node_of] -- tune
lemma summonBasisC (x:Cover)(i:SpinIdx)(a:SU.Slot):
 acts (tradew N g).val (∑ j:SU.Slot,(matter ((g (wrap (More N) (nodeC x)))⁻¹)).val j a • basisC N x i j) = basisC N x i a:=by
  let w:=nodeC x; let W:=turn_basisC N g⁻¹ x i a
  let X:= tradew N g; let Y:= tradew N g⁻¹
  have ht:X*Y=1:= (Hive.trade_c g⁻¹ g).trans (by rw [mul_inv_cancel,Hive.trade_p])
  calc
   _ = acts X.val (acts Y.val (basisC N x i a)):= by rw [show acts Y.val _=_ from W]; rfl -- pi inv
   _ = _ := by rw [←act_mul,←show (X*Y).val=X.val*Y.val from rfl, ht]; exact act_one _
end

variable {K: Calibration}(T: Cover→SU.E) {S:Finset Cover}
variable {wide b:Bool}

def TraceGauge (S:Finset Cover)(T:Cover→SU.E){m:Side}(g:Seat m→ SU.E):Prop:= ∀ a ∈ S,g (wrap (More m) a) = T a
-- set of possible local rearrangements, all agree on S at periods

def Circular (S:Finset Cover) (T:Cover→SU.E) (f F:Family K):Prop:=∀ n:Side,∀ g: Seat (K.c n)→ SU.E, TraceGauge S T g→ Harmony g (f n) (F n)

lemma calibrateTilt (K:Calibration) (x:Cover) (i:SpinIdx)(a:SU.Slot)(hp:i∈plusHalf)(p:nodeC x∈S) : ∃ f, InTest K wide S true f∧Circular S T (creation K x i a) f:=by
  let C (j:SU.Slot):= (matter ((T (nodeC x))⁻¹)).val j a
  refine ⟨∑ j,C j • creation K x i j, InTest.sum _ _ (fun j _=> .smul _ (.creator _ hp p)),?_⟩
  intro m g h u; let n:=K.c m; simp_rw [Finset.sum_apply, Pi.smul_apply]; change create (basisC n x i a)=twist (quantU _) (∑ j,C j • create _)
  have hg:= summonBasisC n g x i a; rw [h _ p] at hg
  simp_rw [← map_smul (create (n:=Single n))]; rw [←map_sum, twist_create]; exact congrArg create hg.symm
lemma calibrateRip (K:Calibration) (x:Cover) (i:SpinIdx)(a:SU.Slot)(hp:i∉plusHalf)(p:nodeC x∈S) : ∃ f, InTest K wide S true f∧Circular S T (removal K x i a) f:=by
  let C (j:SU.Slot):= (matter ((T (nodeC x))⁻¹)).val j a
  refine ⟨∑ j,star (C j) • removal K x i j, InTest.sum _ _ (fun j _=> .smul _ (.remover _ hp p)),?_⟩
  intro m g h u; let n:=K.c m; simp_rw [Finset.sum_apply, Pi.smul_apply];
  let W:=∑ j:SU.Slot,C j • basisC n x i j; let Z:= twist (quantU (tradew n g));
  have he: Fock.remove W= ∑ j,star (C j) • (removal K x i j m u):=by unfold Fock.remove W removal; simp_rw [map_sum,map_smul,star_sum,star_smul]; rfl -- tune
  rw [←he, twist_remove (tradew n g)]; have hg:= summonBasisC n g x i a; rw [h _ p] at hg; change Fock.remove _= _; exact congrArg Fock.remove hg.symm

private lemma gaugeCover_cont : Continuous (fun f:LinksC=> Lattice.gauge T f):= by
  apply continuous_pi; intro e; unfold Lattice.gauge; fun_prop
lemma gauge_trace {m:Side}{g:Seat m→ SU.E}(p:TraceGauge S T g)(A:Pane m): Agrees S (onC m (gauge g A)) (Lattice.gauge T (onC m A)) := by
  rintro ⟨x,i⟩ h w;
  change onC _ _ (x,i)= T x * onC _ _ _ * (T (x+Lattice.step i))⁻¹
  rw [onC_spec,onC_spec]; change g (wrap _ x) * _ * (g _)⁻¹=_; rw [p x h,show g (wrap (More m) x+Lattice.step i)=(T (x+Lattice.step i)) from (by rw [← p (x+Lattice.step i) w, map_add,wrap_step])]
private lemma turned_agree {x y:LinksC}(p:Agrees S x y) : Agrees S (Lattice.gauge T x) (Lattice.gauge T y):= by intro i u v; unfold Lattice.gauge; rw [p _ u v]
lemma calibrateScalar (K:Calibration) (u: PairsC →ℂ)(p:Coeff wide S u): ∃ f, InTest K wide S false f∧ Circular S T (scalar K u) f:=by
  let W:=fun x:LinksC=> Lattice.gauge T x; let f:=u ∘ Prod.map W W
  refine ⟨scalar K f,.seed { env:= Env.along p.env ((gaugeCover_cont T).measurable.prodMap (gaugeCover_cont T).measurable), narrow:=?_, locus:=fun X Y a b=> p.locus _ _ (turned_agree T a) (turned_agree T b)},?_⟩
  · intro w; obtain ⟨v,h,q⟩:= p.narrow w; refine ⟨v∘W,h.comp (gaugeCover_cont T),?_⟩; unfold f; rw [q]; rfl
  intro m g h v; change u _ • (1:FC _)=twist (quantU _) (_ • (1:FC _)); rw [twist_scalar,map_one]; exact congrArg (fun (z:ℂ)=> z • (1:FC _)) (p.locus _ _ (gauge_trace T h v.1) (gauge_trace T h v.2))
lemma Circular.add (S:Finset Cover) {f g F G: Family K} (p:Circular S T f g)(q:Circular S T F G): Circular S T (f+F) (g+G) := by intro m u h i; simp_rw [Pi.add_apply,map_add]; rw [p _ _ h,q _ _ h]
lemma Circular.mul (S:Finset Cover) {f g F G: Family K} (p:Circular S T f g)(q:Circular S T F G): Circular S T (f*F) (g*G) := by intro m u h i; simp_rw [Pi.mul_apply,map_mul]; rw [p _ _ h,q _ _ h]
lemma Circular.scale (S:Finset Cover) {f g: Family K}(p:Circular S T f g)(z:ℂ): Circular S T (z • f) (z • g) := by intro m u h i; simp_rw [Pi.smul_apply, twist_scalar]; rw [p _ _ h]
lemma reColor {f:Family K}(p:InTest K wide S b f): ∃ g, InTest K wide S b g ∧ Circular S T f g:=by
  induction p with
  | seed p=> exact calibrateScalar T K _ p
  | creator a g p=> exact calibrateTilt T K _ _ a g p
  | remover a g p=> exact calibrateRip T K _ _ a g p
  | add _ _ h i=> obtain ⟨g,p,u⟩:=h; obtain ⟨v,e,w⟩:=i; exact ⟨g+v,.add p e,u.add T S w⟩
  | mul _ _ h i=> obtain ⟨g,p,u⟩:=h; obtain ⟨v,e,w⟩:=i; exact ⟨g*v,.mul p e,u.mul T S w⟩
  | smul c _ h=> obtain ⟨g,p,u⟩:=h; exact ⟨c • g,.smul c p, u.scale T S c⟩
  | zero=> exact ⟨0,.zero, fun i g h v=> (map_zero _).symm⟩
  | one=> exact ⟨1,.one, fun i g h v=> (map_one _).symm⟩
-- singlet family (use unrestricted PairsC scalar or separately link-only as needed)
def Neutral (K:Calibration) (f:Family K):Prop:= ∀ m:Side, covariant (f m)
lemma harmonicHere {f:Family K}: Neutral K f ↔ ∀ (T:Cover→SU.E), Circular S T f f:= by constructor; exact fun h T n g _=> h n g; exact fun h n g=> h (g ∘ wrap (More (K.c n))) n g (fun _ _=> rfl)
lemma scoreTrace {m:Side}(p:Hosp S m) : ∃ g, TraceGauge S T (m:=m) g:=by
  let g(t):= if h:∃ x∈S,wrap (More m) x=t then T (Classical.choose h) else 1
  refine ⟨g,fun x h=>?_⟩; let w:∃ a∈S,wrap (More m) a=wrap _ x:= ⟨x,h,rfl⟩; unfold g; rw [dif_pos w]; exact congrArg T (p.seat_ (Classical.choose_spec w).1 h (Classical.choose_spec w).2)
lemma looksLike {m:Side} {F f:Family K}(p: Hosp S (K.c m))(a:InTest K true S false f)(b: InTest K true S false F)(h:f m=F m): f=F:=by
  obtain ⟨x,rfl⟩:= rendered S K a; obtain ⟨y,rfl⟩:= rendered S K b; exact congrArg _ (appear_inj S K m p h)
lemma onceNeutral {f:Family K}(p: InTest K true S false f){m:Side} (a:Hosp S (K.c m))(v:covariant (f m)): Neutral K f:=by
  apply (harmonicHere (S:=S)).2; intro T; obtain ⟨u,h,H⟩:= reColor T p
  obtain ⟨g,t⟩:= scoreTrace T a
  have he: f=u := looksLike a p h (funext fun x=> (twist (quantU (tradew (K.c m) g))).injective ((v g x).symm.trans (H m g t x)))
  rwa [←he] at H
lemma impliesSinglet {f:Family K}(p:Neutral K f): Singlet f:= Eventually.of_forall fun i _ => p i
lemma ofSinglet {f:Family K}(h:InTest K true S false f)(p:Singlet f): Neutral K f:=by -- find K.takes cofinal using odd multiples
  obtain ⟨T,g⟩:= eventually_atTop.mp ((separates K S).and p)
  let r:Side := ⟨1+2*T.val,by positivity⟩; let m:= K.q*r
  have hl:T ≤ m:= by
    change T.val ≤ K.q.val*(1+2*T.val); have he:= K.q.property; exact le_trans (by omega : T.val≤1+2*T.val) (Nat.le_mul_of_pos_left _ he)
  have hz:K.takes m := ⟨r,(by use T.val; change 1+_=2*T.val+1; omega),rfl⟩
  exact onceNeutral h ⟨(g m hl).1⟩ ((g m hl).2 hz)
end YM.CF.Buffered.Afterglow.Tapestry
#print axioms YM.CF.Buffered.Afterglow.Tapestry.ofSinglet
