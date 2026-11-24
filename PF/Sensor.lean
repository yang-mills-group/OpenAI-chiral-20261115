import PF.Taps
set_option autoImplicit false
set_option maxHeartbeats 380000
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open Spine
open CF.Velvet CF.Pannier.Chancel
open QuadClock
open Aria Casting MacroGrid Preparation.Yoke Yoke.Travel
open SatinNucleus Six DoseTravel Set

-- Physical gating on a single LP satellite
namespace PureForce
open Lattice
variable {N : Side}
namespace Native
structure Leaf (o : Cover) where
  face : Face ℤ
  path : Lattice.Walk
  stops : Lattice.stop o path = face.1

-- Could have generalized PF.bud and then transported. Keep this *cover*
-- incarnation separate to issue the P.Test registration even on tiny periodic
-- costs, no accidental implication from AtSupport at large s only.
variable {o : Cover}
local notation "𝒢"=> SU.group

def sprout (p:Leaf o)(U:LinksC) := let V:= Lattice.travel U o p.path;
                                     (𝒢).curvature (V * faceValue U p.face * V⁻¹)
lemma sprout_cost (p:Leaf o)(U:LinksC): ‖sprout p U‖≤2 := (Gauge.curvature_norm ..).trans (Gauge.chord_le_two ..)
lemma sprout_cont (p:Leaf o) : Continuous (sprout p):=by
  unfold sprout faceValue; dsimp
  apply Gauge.continuous_curvature (𝒢) |>.comp
  fun_prop
lemma sprout_cov (p:Leaf o)(U:LinksC)(g:Cover→SU.E):sprout p (Lattice.gauge g U)=(𝒢).adjoint (g o) (sprout p U):=by
  unfold sprout; rw [travel_gauge,face_gauge,p.stops]; dsimp only
  rw [← Gauge.curvature_conjugate]; apply congrArg (Gauge.curvature (𝒢)); group

def planted (S:Finset Cover)(p:Leaf o):Prop:=
  (∀ x∈Lattice.visits o p.path,x∈S) ∧ Calico.Tch p.face ⊆ S
lemma planted_price (S:Finset Cover)(p:Leaf o)(b:planted S p):LocalOn (↑S) (sprout p) := by
  intro U V h
  have he: Lattice.travel U o p.path = Lattice.travel V o p.path:= travel_local o p.path _ _ (fun i l t=>h i (b.1 _ l) (b.1 _ t))
  have hf:faceValue U p.face=faceValue V p.face:= travel_local p.face.1 (Lattice.square ..) _ _
      (fun i l t=> h i (b.2 (List.mem_toFinset.mpr l)) (b.2 (List.mem_toFinset.mpr t)))
  change sprout p U=sprout p V; unfold sprout; rw [he,hf]

abbrev Ruler(o:Cover):= List (ℝ × Leaf o)
def corner (f:Ruler o)(U:LinksC) : (𝒢).Color:=
  (f.map fun t=> t.1 • sprout t.2 U).sum
def cropCost (f:Ruler o):ℝ:=(f.map fun t=>|t.1|).sum
lemma corner_cost (f:Ruler o)(U:LinksC):‖corner f U‖ ≤ cropCost f *2 := by
  induction (show List (ℝ × Leaf o) from f) with
  | nil=>simp [cropCost,corner]
  | cons t f ih=>
    simp only [corner,cropCost,List.map_cons,List.sum_cons] at *
    have he : ‖t.1 • sprout t.2 U‖ ≤ |t.1| * 2 := by rw [norm_smul,Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_left (sprout_cost ..) (abs_nonneg _)
    exact (norm_add_le ..).trans ((add_le_add he ih).trans_eq (Eq.symm (add_mul ..)))
lemma corner_cont (f:Ruler o) : Continuous (corner f):=by
  induction (show List (ℝ × Leaf o) from f) with
  | nil=>exact continuous_const
  | cons t f ih=> exact (Continuous.const_smul (sprout_cont t.2) t.1).add ih
lemma corner_cov (f:Ruler o)(U:LinksC)(g:Cover→SU.E):corner f (Lattice.gauge g U)=(𝒢).adjoint (g o) (corner f U):=by
  unfold corner; rw [map_list_sum,List.map_map]
  apply congrArg List.sum; congr 1; funext d; simp [sprout_cov]
lemma corner_price (S:Finset Cover)(f:Ruler o)(p:∀ t∈f,planted S t.2): LocalOn (↑S) (corner f):= by
  intro U V h
  exact congrArg List.sum <| List.map_congr_left (fun t ht=> congrArg (t.1 • ·) (planted_price S t.2 (p _ ht) U V h))

lemma onC_gauged (g:Skye.Seat N→ SU.E) (U:Pane N) : onC N (Lattice.gauge g U)=Lattice.gauge (g ∘ wrap (More N)) (onC N U):= by
  funext i; rw [Lifted.onC_spec]; simp [Lattice.gauge,Lifted.onC_spec,wrap_step]

def perLeaf (N:Side)(b:Leaf o):Staple N (wrap (More N) o) := ⟨Calico.freeze b.face,b.path, by rw [← wrap_stop_cover,b.stops]; rfl⟩
def perRuler (N:Side)(f:Ruler o): Tap N (wrap (More N) o):=
  f.map (Prod.map id (perLeaf N))
lemma sprout_period (p:Leaf o)(U:Pane N): sprout p (onC N U)=bud (perLeaf N p) U:=by
  unfold sprout; rw [Calico.frame_freeze]
  unfold onC; rw [travel_at,add_zero]; rfl
lemma corner_period (p:Ruler o)(U:Pane N):corner p (onC N U)=play (perRuler N p) U:=by
  unfold corner play perRuler; rw [List.map_map]; apply congrArg List.sum; congr 1; funext; dsimp; rw [sprout_period]

lemma perFits (S:Finset Cover){p:Leaf o}(v:planted S p): Fits (Finset.image (wrap (More N)) S) (perLeaf N p) := by
  refine ⟨fun x hx=>?_,?_⟩
  · have handle (u:Cover)(a:Lattice.Walk): (Lattice.visits u a).map (wrap (More N)) = Lattice.visits (wrap (More N) u) a:= by
      induction a generalizing u with
      | nil=>rfl
      | cons t l ih=>simp [Lattice.visits,ih,wrap_vec]
    rw [show (perLeaf N p).path=p.path from rfl,←handle] at hx; obtain ⟨y,t,rfl⟩:=List.mem_map.mp hx
    exact Finset.mem_image_of_mem (wrap (More N)) (v.1 _ t)
  intro x hv; exact Finset.image_subset_image v.2 ((Calico.Vag p.face).symm ▸ hv)

def pingC (s:ℝ)(C: Finset Cover)(U:LinksC):Prop:=∀ p:Face ℤ,¬ Disjoint C (Calico.Tch p)→ (𝒢).chord (faceValue U p)<s
lemma ping_wrap (s:ℝ)(C:Finset Cover)(U:Pane N):
    pingC s C (onC N U) ↔ Scree.pingS s (C.image (wrap (More N))) U := by
  rw [←pingClean]
  constructor
  · rintro p i x h v; obtain ⟨y,t,rfl⟩:= Finset.mem_image.mp h
    obtain ⟨j,rfl,k⟩:=Calico.touch_fill i _ v
    rw [←Calico.frame_freeze]
    exact p j (Finset.not_disjoint_iff.mpr ⟨y,t,k⟩)
  rintro p i h; rw [Calico.frame_freeze]; obtain ⟨y,t,k⟩:= Finset.not_disjoint_iff.mp h
  apply p _ _ (Finset.mem_image_of_mem (wrap (More N)) t); rw [←Calico.Vag]; exact Finset.mem_image_of_mem (wrap (More N)) k

-- Countable conjunction suffices for Borel; for LocalOn request every *used*
-- face. 8-box layers suffice by Calico.shiftF.
lemma ping_borel (s:ℝ)(C:Finset Cover):MeasurableSet {U:LinksC|pingC s C U}:= by
  simp only [pingC,Set.setOf_forall]
  refine MeasurableSet.iInter fun p=>MeasurableSet.iInter fun _=>?_
  exact (isOpen_lt ((𝒢).continuous_chord.comp (Wilson.continuous_travel ..)) continuous_const).measurableSet

def outfit (C S:Finset Cover):Prop:= ∀ (i:Face ℤ), ¬Disjoint C (Calico.Tch i)→Calico.Tch i⊆ S
def sleeves (C:Finset Cover):Finset Cover:= C.biUnion fun x=> (Lattice.box 8).image (x+·)
lemma dressed (C:Finset Cover):outfit C (sleeves C):=by
  intro i h y p; obtain ⟨x,v,t⟩:=Finset.not_disjoint_iff.mp h
  refine Finset.mem_biUnion.mpr ⟨x,v,Finset.mem_image.mpr ⟨y-x,?_,add_sub_cancel _ _⟩⟩
  have hP(z:Cover)(h:z∈Calico.Tch i):=(box_test.mp (Calico.shiftF i z h))
  obtain ⟨l,u⟩ := hP x t; obtain ⟨d,w⟩:=hP y p
  rw [box_test]; constructor <;> intro a <;> specialize u a <;> specialize l a <;> specialize d a <;> specialize w a <;> simp at * <;> omega
lemma ping_occurs (s:ℝ){C S : Finset Cover}(e:outfit C S):LocalOn (↑S) (pingC s C):=by
  intro U V h; apply propext
  exact forall_congr' (fun i=> forall_congr' (fun v=> by rw [show faceValue U i=faceValue V i from
    travel_local i.1 (Lattice.square ..) U V (fun j m t=>h j (e i v (List.mem_toFinset.mpr m)) (e i v (List.mem_toFinset.mpr t)))]))
lemma ping_cov (s:ℝ)(C:Finset Cover)(U:LinksC)(g:Cover→SU.E):pingC s C (Lattice.gauge g U)↔pingC s C U:= by
  simp [pingC,Lattice.face_gauge]


set_option quotPrecheck false
local notation "𝔉" => Axis → Axis → (𝒢).Color

def flux (x:𝔉)(a b:Axis):ℝ:= (∑ i:Axis, inner ℝ (x a i) (x b i)) -
  (if a=b then 1/4 else 0)*∑ j:Axis,∑ i:Axis, inner ℝ (x j i) (x j i)
lemma flux_cont (a b:Axis): Continuous (fun x:𝔉=>flux x a b):= by
  unfold flux; fun_prop
lemma flux_cov (x:𝔉)(a b:Axis)(G:SU.E): flux (fun i l=> (𝒢).adjoint G (x i l)) a b = flux x a b := by
  have he(l r:(𝒢).Color): inner ℝ ((𝒢).adjoint G l) ((𝒢).adjoint G r)=inner ℝ l r :=
    (LinearIsometry.inner_map_map (⟨(𝒢).adjoint G, Gauge.norm_adjoint _ G⟩: (𝒢).Color →ₗᵢ[ℝ] (𝒢).Color) l r)
  unfold flux; simp only [he]

/-- Pure sensor calibrated by PB.3, with the radial factor included in the
Ruler. Mask on support C in gauge sites (includes the touching-face tests, incurred S
includes their actual links). -/
def stress (f:Axis → Axis → Ruler o)(a b:Axis)(U:LinksC) :ℂ:= ↑(flux (fun i j=>corner (f i j) U) a b)
lemma stress_cont (f:Axis→ Axis→ Ruler o)(a b:Axis):Continuous (stress f a b):=by
  have hX: Continuous (fun U:LinksC=>flux (fun i l=>corner (f i l) U) a b):=(flux_cont a b).comp (f:=fun U i l=>corner (f i l) U) (continuous_pi fun i=>continuous_pi fun l=>corner_cont (f i l))
  exact Complex.continuous_ofReal.comp hX
lemma stress_cov (f:Axis→ Axis→ Ruler o)(a b:Axis)(g:Cover→SU.E)(U:LinksC): stress f a b (Lattice.gauge g U)=stress f a b U:= by
  simp_rw [stress,corner_cov]; rw [flux_cov]
lemma stress_price {S:Finset Cover}(f:Axis→Axis→ Ruler o)(h:∀ i j,∀ t∈f i j,planted S t.2)(a b:Axis):
    LocalOn (↑S) (stress f a b):= by
  intro U V t; apply congrArg Complex.ofReal; apply congrArg (fun x=>flux x a b)
  funext i j; exact corner_price S _ (h i j) U V t

noncomputable def stressPlate (f:Axis→ Axis→ Ruler o)(τ:ℝ)(C:Finset Cover)(i j:Axis):LinksC→ℂ:=
  {U:LinksC|pingC τ C U}.indicator (stress f i j)
lemma costPlate {S:Finset Cover}(f:Axis→Axis→ Ruler o)(τ:ℝ)(C:Finset Cover)(i j:Axis)(h:∀ a b,∀ t∈f a b,planted S t.2)(e:outfit C S) :
    Coeff true S (stressPlate f τ C i j ∘ Prod.fst):= by
  obtain ⟨c,hc⟩:= bddAbove_def.mp (isCompact_range (stress_cont f i j).norm).bddAbove
  have hc'(U:LinksC) : ‖stress f i j U‖ ≤ c:= hc _ ⟨U,rfl⟩
  have hn:0≤c:= (norm_nonneg _).trans (hc' 1)
  constructor
  · intro; contradiction
  · refine Env.along (g:=Prod.fst) (⟨((stress_cont f i j).measurable.indicator (ping_borel τ C)),c,fun x=>?_⟩: Envelope (stressPlate f τ C i j)) measurable_fst
    unfold stressPlate; rw [Set.indicator_apply]; split_ifs; exact hc' x; simpa using hn
  intro x y t _
  have hm:pingC τ C x.1=pingC τ C y.1:=ping_occurs τ e x.1 _ t
  have hz:=stress_price f h i j x.1 y.1 t
  unfold Function.comp stressPlate
  simp_rw [Set.indicator_apply]; exact congrArg₂ (fun (P:Prop) (s:ℂ)=> @ite ℂ P (Classical.propDecidable P) s 0) hm hz

lemma stressPlateCov (f:Axis→Axis→Ruler o)(τ:ℝ)(C:Finset Cover)(a b:Axis)(g:Cover→SU.E)(U:LinksC):stressPlate f τ C a b (Lattice.gauge g U)=stressPlate f τ C a b U:= by
  unfold stressPlate; simp_rw [Set.indicator_apply]; simp only [Set.mem_setOf_eq,ping_cov,stress_cov]

abbrev Component (N:Side):= Axis → Axis → Tap N (0:Skye.Seat N) -- more often anchor ≠0

def localT {e:Skye.Seat N} (f:Axis→Axis→Tap N e)(τ:ℝ)(C:Finset (Skye.Seat N))(a b:Axis):Evaluation N:= by
  classical
  exact fun V=> {U| Scree.pingS τ C U}.indicator (fun U=> (↑(flux (fun i j=>play (f i j) U) a b):ℂ) • (1:FC (Single N))) V

variable (K:Calibration)
-- Mark and equality for both panes.
def Tm (f:Axis →Axis →Ruler o)(τ:ℝ)(C:Finset Cover)(a b:Axis): Buffered.Family K:= Buffered.scalar K (stressPlate f τ C a b ∘ Prod.fst)

lemma pattern (f:Axis →Axis →Ruler o)(τ:ℝ)(C:Finset Cover)(a b:Axis)(m:Side)(X:Fields (K.c m)):
    Tm K f τ C a b m X=localT (fun i j=>perRuler _ (f i j)) τ (C.image (wrap (More (K.c m)))) a b X.1:=by
  change stressPlate f τ C a b (onC _ X.1) • 1 = _
  classical
  simp only [stressPlate,localT,Set.indicator_apply, Set.mem_setOf_eq, ping_wrap, stress, corner_period]
  split_ifs; rfl; rw [zero_smul]
lemma Tqualified {S:Finset Cover}(f:Axis→Axis→ Ruler o)(τ:ℝ)(C:Finset Cover)(i j:Axis)(h:∀ a b,∀ t∈f a b,planted S t.2)(e:outfit C S): InTest K true S false (Tm K f τ C i j):= .seed (costPlate f τ C i j h e)
lemma Tcovariant (f:Axis →Axis → Ruler o)(τ:ℝ)(C:Finset Cover)(a b:Axis): CovCover K (Tm K f τ C a b):=by
  intro n g z
  change stressPlate f τ C a b (onC (K.c n) (Lattice.gauge g z.1)) • 1 = (twist (quantU (tradew (K.c n) g))) (stressPlate f τ C a b (onC (K.c n) z.1) • 1)
  rw [onC_gauged,stressPlateCov,twist_scalar,map_one]

variable (P:Spine)
def tensorMark {S:Finset Cover}(C:Finset Cover)(f:Axis→Axis→ Ruler o)(h:∀ a b,∀ t∈f a b,planted S t.2)(e:outfit C S) (τ:ℝ)(a b:Axis):P.Test:=⟨_,Tapestry.broadCompile _ S (Tqualified P.calibration f τ C a b h e)⟩
-- purchase Purity as RawWard (first Pane only version), covariant and measured
lemma gauged_tensor {S:Finset Cover}(C:Finset Cover)(f:Axis→Axis→ Ruler o)(h:∀ a b,∀ t∈f a b,planted S t.2)(e:outfit C S) (τ:ℝ)(a b:Axis):
    let F:=tensorMark P C f h e τ a b; Six.PureGauge P.calibration F ∧ CovCover P.calibration F.val ∧ InTest P.calibration true S false F.val ∧
    ∀ (m:Side)(x:Fields (P.calibration.c m)),F.val m x=localT (fun i j=>perRuler _ (f i j)) τ (C.image (wrap (More (P.calibration.c m)))) a b x.1:= by
  intro F; exact ⟨⟨S,_,costPlate f τ C a b h e,rfl⟩,Tcovariant _ f τ C a b,Tqualified _ f τ C a b h e,pattern _ f τ C a b⟩


-- Strengthen PureGauge usage to meet **literal first Pane only** LP.6 even
-- after any advancement-free poses. This isn't a preserved sector assertion
-- through projection/advancement in the regulator law or arbitrary Frame
-- orientation used in strengthening the checker cost.
def First (K:Calibration)(f:Dome K):Prop:=∃ S:Finset Cover,∃ g:LinksC→ℂ,Coeff true S (g ∘ Prod.fst)∧ f.val=Buffered.scalar K (g ∘ Prod.fst)
lemma First.pure {f:Dome K}(h:First K f):Six.PureGauge K f:=by obtain ⟨S,g,h,p⟩:=h; exact ⟨S,_,h,p⟩

private lemma first_bounce {K:Calibration}(i:Axis)(z:ℤ){m:Buffered.Family K}{g:LinksC→ℂ}{S:Finset Cover}(h:m=Buffered.scalar K (g∘Prod.fst))(p:Coeff true S (g ∘ Prod.fst)):
    ∃ S',∃ g':LinksC→ℂ,Coeff true S' (g' ∘ Prod.fst)∧Tower.mirror K i z m=Buffered.scalar K (g' ∘ Prod.fst):=by
  subst m
  -- adapted project/YM/SU5/FiniteGaugeData/Tapestry/Sandwich.lean reflection rule
  let F:=Lifted.moveC i z
  let M:PairsC→PairsC:=Prod.map F F
  let g'(U:LinksC):=star (g (F U))
  refine ⟨S.image ((plane i z).motion),g',?_,?_⟩
  · refine ⟨nofun, Girt.pole_w _ star continuous_star (Env.along (g:=Prod.map F F) p.env ((Lifted.move_cont i z).prodMap (Lifted.move_cont i z)).measurable),?_⟩
    exact fun x y a b=> congrArg star (p.locus (M x) (M y) (Lifted.moved_agree _ _ a) (Lifted.moved_agree _ _ b))
  funext m x; unfold Buffered.scalar Tower.mirror reflMark; rw [theta_smul,theta_one]; apply congrArg (fun c:ℂ=> c • 1); unfold g'; simp only [reflFields,Prod.map_fst,Prod.map_snd,reflect_onC]; rfl
lemma First.shifted {P:Spine}{f:P.Test}(h:First P.calibration f)(i:Axis)(z:ℤ):First P.calibration (P.shifts i z f):=by
  obtain ⟨S,g,p,H⟩:=h
  obtain ⟨S',g',p',h'⟩:=first_bounce i 0 H p
  obtain ⟨S'',g'',p'',h''⟩:=first_bounce i (SlabMark.gaugeT P.calibration z) h' p'
  exact ⟨S'',g'',p'',h''⟩
lemma First.mirrored {P:Spine}{f:P.Test}(h:First P.calibration f)(i:Axis): First P.calibration (P.reflectTest i f):=by
  obtain ⟨S,g,p,H⟩:=h
  exact first_bounce _ _ H p -- tune def
private lemma plusCoeff {a b: PairsC→ℂ}{S:Finset Cover}(p:Coeff true S a)(q:Coeff true S b): Coeff true S (a+b):=by
  refine ⟨nofun,Girt.kitE a b (fun x y=> x+y) (continuous_fst.add continuous_snd) p.env q.env,fun x y h w=>?_⟩
  exact congrArg₂ (·+·) (p.locus _ _ h w) (q.locus _ _ h w)
private lemma timesCoeff {a:PairsC→ℂ}{S:Finset Cover}(p:Coeff true S a)(c:ℂ):Coeff true S (c • a) :=by
  refine ⟨nofun,Girt.pole_w _ (c • ·) (Continuous.const_smul continuous_id c) p.env,fun x y h w=>?_⟩
  exact congrArg (c • ·) (p.locus _ _ h w)
lemma First.add {x y:Dome K}(hx:First K x)(hy:First K y):First K (x+y):= by
  obtain ⟨S,f,p,hx⟩:=hx; obtain ⟨T,g,q,hy⟩:=hy
  refine ⟨S∪T,f+g,plusCoeff (p.mono (Finset.subset_union_left)) (q.mono (Finset.subset_union_right)),?_⟩
  change x.val+y.val=_; rw [hx,hy]; funext i z; exact (add_smul ..).symm
lemma First.smul {x:Dome K}(c:ℂ)(h:First K x): First K (c • x):=by
  obtain ⟨S,f,p,h⟩:=h
  refine ⟨S,c•f,timesCoeff p c,?_⟩; change c • x.val=_; rw [h]; funext i z; exact smul_smul c (f (onC (K.c i) z.1)) (1:FC (Single (K.c i)))
lemma first_one : First K 1:= by
  refine ⟨∅,fun _=>1, Coeff.fromC true _ continuous_const (fun _ _ _=>rfl),?_⟩
  funext m x; exact (one_smul ..).symm
protected def First.space : Submodule ℂ (Dome K) where
 carrier:={p|First K p}
 add_mem' := fun h p=>First.add K h p
 zero_mem' := (show (0:ℂ) • (1:Dome K) = 0 from zero_smul _ _) ▸ First.smul _ _ (first_one K)
 smul_mem' :=fun _ _=> First.smul _ _ -- check

lemma First.exhibited {P:Spine}{f:P.Test}(t:First P.calibration f)(s i:ℕ):
    ∃ A : Evaluation (side P.run i s), Tapestry.exhibit P.run P.large s i f.val=toMark A:= by
  obtain ⟨S,g,h,p⟩:=t
  have he (U V:Side)(l:U=V): arrange U V l (toMark (fun x:Pane U=>g (onC U x) • 1)) = toMark (fun x:Pane V=>g (onC V x) • 1) := by
    subst V; rfl
  exact ⟨fun x=>g (onC (side P.run i s) x) • 1,(p ▸ he _ _ (terrain P.run P.large (P.run.ir i) s))⟩

local notation "χ"=> P.calibration
-- LP chrono Mark layout, covers optional poses via Spine.shifts. keep p_s maturity as hypothesis on use in tap.
def DivM {S:Finset Cover}{C: Finset Cover}(f : Axis→ Axis→ Ruler (0:Cover))(h:∀ a b,∀ t∈f a b,planted S t.2)(e:outfit C S) (τ:ℝ)(a:Axis)(n:ℕ)(v:ℤ→ℂ) : P.Test :=
  ∑ b:Axis, ∑ m∈(Finset.Icc (-(n:ℤ)) (n:ℤ)), v m • (P.shifts b m (tensorMark P C f h e τ b a))

def strictExpense (S:Finset Cover)(n:ℕ): Finset Cover:=
  (Finset.univ:Finset Axis).biUnion fun b=> (Finset.Icc (-(n:ℤ)) (n:ℤ)).biUnion fun m=> SlabMark.plow (χ) b m S

lemma forceBook {S: Finset Cover}(C:Finset Cover)(f : Axis→ Axis→ Ruler (0:Cover))(h:∀ a b,∀ t∈f a b,planted S t.2)(e:outfit C S) (τ:ℝ)(a:Axis)(n:ℕ)(v:ℤ→ℂ) :
    let X:= DivM P f h e τ a n v
    X ∈ bay (χ) (strictExpense P S n) true ∧ CovCover (χ) X.val ∧ First (χ) X := by
  intro X
  let M := Finset.Icc (-(n:ℤ)) (n:ℤ)
  have H(b:Axis):= gauged_tensor P C f h e τ b a
  let g(b:Axis):=tensorMark P C f h e τ b a
  have ht(b:Axis)(m:ℤ)(q:m∈M): P.shifts b m (g b)∈bay (χ) (strictExpense P S n) true:= by
    have hz:=P.shifts_support b m S ((Tapestry.locates ..).2 (show InTest _ true _ _ _ from (H b).2.2.1))
    apply Tapestry.locates _ _ true|>.2; apply InTest.mono ((Tapestry.locates ..).1 hz)
    intro p k; exact Finset.mem_biUnion.mpr ⟨_,Finset.mem_univ _,Finset.mem_biUnion.mpr ⟨_,q,k⟩⟩
  let B:=bay (χ) (strictExpense P S n) true
  let Y:= enclave (χ)
  let T:= First.space (χ)
  constructor
  · apply B.sum_mem; intro b _; exact B.sum_mem fun m l=> B.smul_mem (ht b m l) _
  constructor
  · apply (show X ∈ Y→ _ from fun h=>h); apply Y.sum_mem; intro b _; exact Y.sum_mem fun m _=>Y.smul_mem
      (P.shifts_keep _ _ (show g b∈Y from (H b).2.1)) _
  apply (show X ∈ T→ _ from fun h=>h); apply T.sum_mem; intro b _; exact T.sum_mem fun m _=> T.smul_mem _
    (show (P.shifts _ m (g b))∈T from First.shifted (show First (χ) (g b) from ⟨S,stressPlate f τ C b a,costPlate f τ C b a h e,rfl⟩) _ m)

lemma force_mean {S:Finset Cover}{C: Finset Cover}(f : Axis→ Axis→ Ruler (0:Cover))(h:∀ a b,∀ t∈f a b,planted S t.2)(e:outfit C S) (τ:ℝ)(a:Axis)(n:ℕ)(v:ℤ→ℂ)(p:∑ m∈Finset.Icc (-(n:ℤ)) (n:ℤ),v m=0)(s:ℕ)(x:P.Spectrum0 3):
    P.singleState 3 s x (DivM P f h e τ a n v)=0:= by
  simp only [DivM,map_sum,map_smul,smul_eq_mul,P.stamp_title]
  simp_rw [←Finset.sum_mul,p,zero_mul,Finset.sum_const_zero]

private lemma rawMirror {K:Calibration}(i:Axis)(z:ℤ)(f:LinksC→ℂ):
    Tower.mirror K i z (Buffered.scalar K (f ∘ Prod.fst))=
      Buffered.scalar K ((fun x=>star (f (moveC i z x))) ∘ Prod.fst):=by
  funext m x; unfold Buffered.scalar Tower.mirror reflMark; rw [theta_smul,theta_one]; apply congrArg (fun c:ℂ=> c • 1); simp only [reflFields,Prod.map_fst,Prod.map_snd,reflect_onC]; rfl
lemma translates {K:Calibration}(i:Axis)(z:ℤ)(f:LinksC→ℂ):
    chime K i z (Buffered.scalar K (f ∘ Prod.fst)) = Buffered.scalar K
       ((fun x=> f (Lattice.translate ((2:ℕ) • (z • Lattice.step i:Cover)) x)) ∘ Prod.fst):=by
  unfold chime; rw [rawMirror _ _ f,rawMirror]; apply congrArg (fun (g:LinksC→ℂ)=> Buffered.scalar K (g ∘ Prod.fst)); funext x
  simp only [star_star,moveC,pull_pull] --(Signed.mirror_inv i).symm ▸ inv_mul_cancel (Signed.mirror i)]
  rw [show Signed.mirror i*Signed.mirror i=(1:Signed) by nth_rw 2 [← Signed.mirror_inv i]; exact mul_inv_cancel _, pull_one]
  congr 3; simp [affine]

lemma raw_step {K:Calibration}(i:Axis)(z:ℤ)(f:LinksC→ℂ): relocate K i z (Buffered.scalar K (f ∘ Prod.fst)) =
    Buffered.scalar K ((fun x=>f (Lattice.translate ((ruler K.B*z) • Lattice.step i:Cover) x)) ∘ Prod.fst):= by
  rw [relocate,translates]
  rw [show (2:ℕ) • (gaugeT K z • step i:Cover) = (ruler K.B*z) • step i from ?_]
  rw [two_smul ℕ,←add_smul,←two_mul, ruler_offset]

local notation "qK" m:max => P.calibration.c m
lemma raw_derivative {S:Finset Cover}{C: Finset Cover}(f : Axis→ Axis→ Ruler (0:Cover))(h:∀ a b,∀ t∈f a b,planted S t.2)(e:outfit C S) (τ:ℝ)(a:Axis)(n:ℕ)(v:ℤ→ℂ)(m:Side)(U:Fields (qK m)):
    (DivM P f h e τ a n v).val m U=
       (∑ b:Axis,∑ j∈(Finset.Icc (-(n:ℤ)) (n:ℤ)), v j* stressPlate f τ C b a (Lattice.translate ((16*(P.calibration.B.val:ℤ)*j) • step b:Cover) (onC (qK m) U.1))) • 1 := by
  let L: P.Test →ₗ[ℂ] FC (Single (qK m)) := (LinearMap.proj (R:=ℂ) U).comp ((LinearMap.proj (R:=ℂ) m).comp ((screenHall (χ)).val.toLinearMap))
  change L (DivM P f h e τ a n v) = _
  unfold DivM; rw [map_sum, Finset.sum_smul]; refine Finset.sum_congr rfl fun b _=> ?_
  rw [map_sum, Finset.sum_smul]; refine Finset.sum_congr rfl fun i _=> ?_
  rw [map_smul]
  change _ • (relocate (χ) b i (Buffered.scalar (χ) (stressPlate f τ C b a ∘ Prod.fst)) m U)= _
  rw [raw_step]; unfold Buffered.scalar Function.comp; rw [smul_smul]; rfl

-- Attach E and selected one-point and reflected bills
variable {C S:Finset Cover}(s n:ℕ)(f:Axis→Axis→Ruler 0)(t:ℝ)(a:Axis)
    (h:∀ i j,∀ d∈f i j,planted S d.2)(e:outfit C S)(c:ℤ→ℂ)(pc:∑ j∈Finset.Icc (-(n:ℤ)) (n:ℤ),c j=0)
local notation "D"=> DivM P f h e t a n c
local notation "σ"=> strictExpense P S n

private lemma estate (F:P.Test): (∫ x,P.singleState 3 s x F ∂ P.pillars 3)=P.E s F.val:=
  Eq.trans (P.recovery 3 (P.reading 3 s F)) (P.occupied 3 s F)
include pc in
theorem ticket (z:ℤ)(x:P.Spectrum0 3):
    let A:= P.shifts 3 z (D);
    let T:=plow (χ) 3 z (σ);
    A∈ bay (χ) T true ∧ A∈enclave (χ) ∧
    First (χ) A ∧ Six.PureGauge (χ) A ∧
    First (χ) (P.reflectTest 3 A) ∧
    (∀ i:ℕ,∃ L:Evaluation (side P.run i s),
      Tapestry.exhibit P.run P.large s i A.val=toMark L∧ AtSupport false (Satin.region T (side P.run i s)) (toMark L) ∧ covariant (toMark L))∧
    P.singleState 3 s x A=0 ∧ P.E s A.val=0 ∧
    (Tower.region 3 0 P.calibration.ℓ T → ∃ w:P.birthF 3 s A,
     (P.singleState 3 s x) ((P.reflectTest 3) A * A) = ↑(‖P.viewF 3 x s w‖^2:ℝ) ∧
     P.E s ((P.reflectTest 3) A * A).val=(∫ y, (↑(‖P.viewF 3 y s w‖^2:ℝ):ℂ)∂P.pillars 3)) := by
  intro A T
  obtain ⟨v,W',n'⟩:= forceBook P C f h e t a n c
  have p':A∈ bay (χ) T true:= P.shifts_support _ _ _ (show (D)∈bay (χ) (σ) true from v)
  have he:A∈enclave (χ):= P.shifts_keep _ _ (show (D) ∈ enclave (χ) from W')
  have hf: First (χ) A:= n'.shifted ..
  have hm(x): P.singleState 3 s x A=0:= (P.stamp_title x s 3 z (D)).trans (force_mean P _ _ _ _ _ _ _ pc _ x)
  have L(i:ℕ):= First.exhibited hf s i
  refine ⟨p',he,hf,hf.pure,hf.mirrored _,fun i=>?_,hm _,?_,?_⟩
  · obtain ⟨B,H⟩:= L i
    exact ⟨B,H,H ▸ Tapestry.exhibited P.run P.large s i T (Tapestry.locates _ _ _ |>.1 p'), H ▸ Tapestry.validate P.run P.large s i he⟩
  · rw [←estate]; simp_rw [hm,integral_zero]
  intro h'; let hhV := P.criteria 3 s p' h' he
  have hx (x:P.Spectrum0 3):(P.singleState 3 s x) ((P.reflectTest 3) A * A) = ↑(‖P.viewF 3 x s hhV‖^2:ℝ) :=by
    rw [←P.released_gram _ _ _ hhV hhV,inner_self_eq_norm_sq_to_K,Complex.ofReal_pow]; rfl
  exact ⟨hhV,hx _,Eq.trans (estate P s ((P.reflectTest 3) A * A)).symm (integral_congr_ae (ae_of_all _ hx))⟩

-- Means removed without comparator subtraction drift. On ANY agenda of selected sectors
-- qualifying with an arbitrary earlier AE agenda, the reflected field budget
-- can reach this lower joint signal if we force it on P.E. More precisely
-- can choose x from that agenda. Uses *actual* S both places. This doesn't yet
-- transfer the signal from moving Mark to local fields; designed for choosing s
-- and x with the IC-sequence licenses and conull comparisons simultaneously.
-- Term-by-term x uniform lower desirable for choosing *all* IC probes.
lemma sector_cont (F:P.Test): Continuous (fun x=>P.singleState 3 s x F):=P.chi_joint 3 _
lemma sectorInt (F:P.Test): Integrable (fun x=>P.singleState 3 s x F) (P.pillars 3) :=
  (sector_cont P s F).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
-- General sensor permits mixtures from sums at same height (grid quadrature).
theorem canChoose (A B:P.Test)(xAgenda:P.Spectrum0 3 → Prop)(e:∀ᵐ x ∂P.pillars 3, xAgenda x)
    (p:∀ x,P.singleState 3 s x A=0 ∨ P.singleState 3 s x B=0)(c:ℝ)(h:c< ‖P.E s (A*B).val‖) :
    ∃ x,xAgenda x∧c<‖P.singleState 3 s x (A*B)-P.singleState 3 s x A * P.singleState 3 s x B‖:= by
  by_contra! v
  have he:‖P.E s (A*B).val‖ ≤ ∫ x, ‖P.singleState 3 s x (A*B)‖ ∂P.pillars 3:=by rw [←estate P]; exact norm_integral_le_integral_norm _
  have hv:(∫ x, ‖P.singleState 3 s x (A*B)‖ ∂P.pillars 3)≤∫ _x:P.Spectrum0 3,c∂ P.pillars 3:=by
    refine integral_mono_ae (sectorInt P s (A*B)).norm (integrable_const _) (e.mono fun x he=>?_)
    have hk:= v x he
    rcases p x with b|b
    · rwa [b,zero_mul,sub_zero] at hk
    rwa [b,mul_zero,sub_zero] at hk
  simp only [integral_const,probReal_univ,one_smul] at hv; exact h.not_ge (he.trans hv)

-- Proof of L² comparison receipt with only unselected E residual price
-- at that sequence of *translated* operands (as in W.3 and IA.9 for Marks).
-- Translation in time first at height itself; permits two-operand A on
-- a space separated layout or arbitrary smear sums supported in one union.
-- No degradation factor; linear prediction k may be complex. Doesn't use
-- positivity of the mark volume flux itself.
lemma ecompare (A:P.Test)(T:Finset Cover)(k:ℂ)(z:ℤ)(hz:A∈ bay (χ) T true)
      (he:Tower.region 3 0 P.calibration.ℓ (plow (χ) 3 z T)):
    let F:= (P.shifts 3 z A)-k • 1
    (∫ x, ‖P.singleState 3 s x A-k‖^2∂ P.pillars 3)≤
      ‖P.E s (P.reflectTest 3 F * F).val‖:=by
  intro F
  let W:= plow (χ) 3 z T; let K:= bay (χ) W true
  have hp : F∈K:= K.sub_mem (P.shifts_support 3 z T hz) (K.smul_mem K.one_mem k)
  have ht:= P.rosaryV 3 s F ⟨P.positiveVox 3 s W F hp he,rfl⟩
  have hx(x): P.singleState 3 s x F=P.singleState 3 s x A-k:=by
    rw [show F=_ from (show F=(P.shifts 3 z A)-k • 1 from rfl), map_sub,map_smul,P.slide_single,P.single_state _ _ _ 1,P.reading_unit,map_one, smul_eq_mul,mul_one]
  simp_rw [hx] at ht; exact ht

end Native
end PureForce
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
