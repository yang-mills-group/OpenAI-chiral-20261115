import YM.SU5.FiniteGaugeData.Tower.GermEngine
/- Product of axis operators and smoothing with no topology assumptions on
other spectral components. Index enumeration given, not a cont topology on
families of operators in norm. Also here, rule giving full recovery even
after all projections if correlation is separately continuous in the
motion of each at the target location, with no requirement on modulus wrt
other coordinates. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Germ
open Function Set Filter Metric ContinuousLinearMap
open scoped Topology InnerProductSpace Classical
structure Alliance (I:Type*) (Γ:AddSubgroup ℝ)(H:Hilbert) where
 crew : I→ Players Γ H
 cCom(i j:I)(x y:Γ): ((crew i).play x).comp ((crew j).play y)=((crew j).play y).comp ((crew i).play x)
namespace Alliance
variable {I:Type*}{Γ:AddSubgroup ℝ}{H:Hilbert}(S:Alliance I Γ H)(d:Dense (Γ:Set ℝ))
set_option quotPrecheck false
local notation "P" i:max=>S.crew i
local notation "U" i:max x:max=> (P i).play x
local notation "R" i:max x:max=> (P i).route d x
local notation "π" i:max=> (P i).pi_c
local notation "Id"=> ContinuousLinearMap.id ℂ H.space
lemma unit_x (f:H.Op):f.comp Id=f:=rfl
lemma unit_l (f:H.Op):(Id).comp f=f:=rfl
lemma just (f g h:H.Op):(f.comp g).comp h=f.comp (g.comp h):=rfl
lemma slide (a b T:H.Op)(p:a.comp T=T.comp a)(t:b.comp T=T.comp b):(a.comp b).comp T =T.comp (a.comp b):=by rw [just,t,←just,p]; rfl
lemma doublet (a b c k:H.Op)(t:b.comp c=c.comp b):(a.comp b).comp (c.comp k)=(a.comp c).comp (b.comp k):=by rw [just,←just b,t,just,←just]

lemma floatZ(i j:I)(x y:Γ):(U i x).comp (π j)=(π j).comp (U i x):=(P j).commutes_c _ (fun t=>S.cCom j i t x)
lemma floats(i j:I)(x:ℝ)(y:Γ): (R i x).comp (U j y)=(U j y).comp (R i x):=(P i).route_fixed d _ (fun t=> S.cCom ..) _
lemma floatPi(i j:I)(x:ℝ): (R i x).comp (π j)=(π j).comp (R i x):=(P j).commutes_c _ (fun y=>(S.floats d i j x y).symm)
lemma floatR(i j:I)(x y:ℝ):(R i x).comp (R j y)=(R j y).comp (R i x):=(P i).route_fixed d _ (fun t=>(S.floats d j i y t).symm) _
lemma floatP(i j:I):(π i).comp (π j)=(π j).comp (π i):= (P j).commutes_c _ (fun x=>S.floatZ j i x 0)

variable(t:List I)
noncomputable def stackS : H.Op:= t.foldr (fun i (p:H.Op)=> (π i).comp p) Id
noncomputable def raw (x:I→Γ) : H.Op:=t.foldr (fun i (p:H.Op)=> (U i (x i)).comp p) Id
noncomputable def flight (x:I→ℝ): H.Op:=t.foldr (fun i (p:H.Op)=> (R i (x i)).comp p) Id
lemma raw_nil (x:I→Γ): S.raw [] x=Id:=rfl
lemma raw_step (i:I)(x:I→Γ): S.raw (i::t) x=(U i (x i)).comp (S.raw t x):=rfl
lemma fly_step (i:I)(x:I→ℝ):S.flight d (i::t) x=(R i (x i)).comp (S.flight d t x):=rfl
lemma shel_step(i:I):S.stackS (i::t)=(π i).comp (S.stackS t):=rfl
lemma hard (T:H.Op)(p:∀i∈t,∀ x:Γ,(U i x).comp T=T.comp (U i x))(x:I→Γ): (S.raw t x).comp T=T.comp (S.raw t x):=by
 induction t with
 | nil=> rfl
 | cons i t ih=> rw [raw_step]; exact slide _ _ _ (p i (List.Mem.head ..) _) (ih fun i u=>p i (List.Mem.tail _ u))
lemma ground(T:H.Op)(p:∀i∈t,∀ x:Γ,(U i x).comp T=T.comp (U i x)): T.comp (S.stackS t)=(S.stackS t).comp T:=by
 induction t with
 | nil=>rfl
 | cons i t ih=> rw [shel_step]; exact (slide _ _ _ ((P i).commutes_c T (p i (List.Mem.head ..))).symm (ih (fun i u=>p i (List.Mem.tail _ u))).symm).symm
lemma fluid(T:H.Op)(p:∀i∈t,∀ x:Γ,(U i x).comp T=T.comp (U i x))(x:I→ℝ): (S.flight d t x).comp T=T.comp (S.flight d t x):=by
 induction t with
 | nil=>rfl
 | cons i t ih=>rw [fly_step]; exact slide _ _ _ ((P i).route_fixed d T (p i (List.Mem.head ..)) _) (ih (fun i u=>p i (List.Mem.tail _ u)))
lemma raw_zero: S.raw t 0=Id:=by induction t with
 | nil=> rfl
 | cons i t ih=>rw [raw_step,Pi.zero_apply,(P i).play_zero,ih,unit_l (H:=H)]
lemma start: S.flight d t 0=S.stackS t:=by induction t with
 | nil=> rfl
 | cons i t ih=>rw [fly_step,shel_step,Pi.zero_apply,(P i).route_source,ih]
lemma smooth_notch(x:I→Γ): S.flight d t (fun i=>(x i:ℝ))=(S.raw t x).comp (S.stackS t):=by
 induction t with
 | nil=>rfl
 | cons i t ih=>
    have h:(S.raw t x).comp (π i)=(π i).comp (S.raw t x):=S.hard t (π i) (fun j v y=> S.floatZ j i y 0) x
    have ht:R i (x i:ℝ)=(U i (x i)).comp (π i):=by ext1 v; exact (P i).route_on d ..
    rw [fly_step,raw_step,shel_step,ht,ih, doublet _ _ _ _ h.symm]
lemma travelR(x y:I→Γ):S.raw t (x+y)=(S.raw t x).comp (S.raw t y):=by
 induction t with
 | nil=>rfl
 | cons i t ih=>rw [raw_step,raw_step,raw_step,ih, doublet _ _ _ _ (S.hard t _ (fun j _ _=>S.cCom ..) x),Pi.add_apply,(P i).piles]
lemma travel(x y:I→ℝ):S.flight d t (x+y)=(S.flight d t x).comp (S.flight d t y):=by
 induction t with
 | nil=>rfl
 | cons i t ih=>rw [fly_step,fly_step,fly_step,ih,doublet _ _ _ _ (S.fluid d t _ (fun j _ _=> (S.floats d _ _ _ _).symm) _),Pi.add_apply,(P i).route_sum]

lemma symmetricstack: (S.stackS t).adjoint=S.stackS t:=by
 induction t with
 | nil=>simp [stackS, ContinuousLinearMap.adjoint_id]
 | cons i t ih=>rw [shel_step,ContinuousLinearMap.adjoint_comp,ih,(P i).pi_adj,S.ground t _ (fun j _ k=> S.floatZ j i k 0)] -- bad last
lemma symmetricflight(x:I→ℝ): (S.flight d t x).adjoint=S.flight d t (-x):=by
 induction t with
 | nil=>simp [flight, ContinuousLinearMap.adjoint_id]
 | cons i t ih=>
    have ht:(R i (x i)).adjoint=R i (-x i):=by ext1 u; apply ext_inner_right ℂ; intro y; rw [ContinuousLinearMap.adjoint_inner_left]; rw [((P i).revolve d),neg_neg] -- signs
    rw [fly_step,ContinuousLinearMap.adjoint_comp,fly_step, Pi.neg_apply,ht,ih, S.fluid d t _ (fun j _ _=> (S.floats d _ _ _ _).symm)]

lemma flyer_end {x:H}(J:x∈ ⋂ i∈ {i:I|i∈t}, ((P i).lives H:Set H)): S.stackS t x=x:=by
 simp only [mem_iInter,mem_setOf_eq] at J
 induction t with
 | nil=> rfl
 | cons i t ih=>rw [shel_step,ContinuousLinearMap.comp_apply, ih (fun j u=>J j (List.Mem.tail _ u)),(P i).pi_fixer (J i (List.Mem.head ..))]
lemma flyer_lives(i:I)(p:i∈t)(x:H): S.stackS t x∈(P i).lives H:=by
 induction t with
 | nil=>simp at p
 | cons j t ih=>
    rw [shel_step,ContinuousLinearMap.comp_apply]; rcases List.mem_cons.mp p with rfl|h
    · exact (P i).repaired _
    have h':ContinuousAt (fun a=>(U i a) ((S.stackS t) x)) 0:=ih h
    have he: ∀a:Γ,(U i a) ((π j) ((S.stackS t) x))=(π j) ((U i a) ((S.stackS t) x)):=fun a=> congrArg (fun k:H.Op=>k _) (S.floatZ i j a 0)
    change ContinuousAt (fun a=>(U i a) ((π j) _)) _ -- annotate
    simp_rw [he]; exact (π j).continuous.continuousAt.comp h'
lemma sailed(v:I→ℝ)(x:H):‖S.flight d t v x‖≤‖S.stackS t x‖:=by
 apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
 rw [←inner_self_eq_norm_sq (𝕜:=ℂ),← ContinuousLinearMap.adjoint_inner_right,S.symmetricflight,←ContinuousLinearMap.comp_apply,← travel,neg_add_cancel,S.start]
 rw [←inner_self_eq_norm_sq (𝕜:=ℂ),← ContinuousLinearMap.adjoint_inner_right,S.symmetricstack,←ContinuousLinearMap.comp_apply]
 rw [← start S d t,←travel S d t,zero_add] -- naming
-- continuity on whole (partial isometry norm <=1)
lemma route_le(i:I)(b:ℝ)(x:H): ‖(R i b) x‖≤‖x‖:=by
 rw [show ‖(R i b) x‖=_ from (P i).wind_norm d x b]
 exact ((P i).lives H).norm_starProjection_apply_le x
lemma moves {D:Type*}[TopologicalSpace D](z:D→ I→ℝ)(p:∀i∈t,Continuous (fun x=>z x i))(y:D→H)(q:Continuous y):Continuous (fun x=> S.flight d t (z x) (y x)):=by
 induction t with
 | nil=> exact q
 | cons i t ih=>
    let T (x:D):=S.flight d t (z x) (y x)
    have hT: Continuous T:=ih (fun j v=>p j (List.Mem.tail _ v))
    simp_rw [fly_step,ContinuousLinearMap.comp_apply]
    change Continuous (fun x=> (R i (z x i)) (T x))
    refine continuous_iff_continuousAt.mpr fun b=> Metric.tendsto_nhds.mpr fun ε e=>?_
    have he: ContinuousAt (fun x=> (R i (z x i)) (T b)) b:= ((P i).route_uc d _).continuous.continuousAt.comp (p _ (List.Mem.head ..)).continuousAt
    filter_upwards [Metric.tendsto_nhds.mp he.tendsto (ε/2) (by positivity),Metric.tendsto_nhds.mp (hT.tendsto b) (ε/2) (by positivity)] with x hx hw
    apply lt_of_le_of_lt (dist_triangle _ ((R i (z x i)) (T b)) _)
    refine add_lt_add_of_lt_of_lt ?_ hx |>.trans_le (le_of_eq (add_halves ε))
    rw [dist_eq_norm,←map_sub]; apply (route_le S d _ _ _).trans_lt; simpa [dist_eq_norm] using hw

-- General retention. One can put some scalar tolerance on continuity
-- using the same averages (not formalized; also one-sided for reals).
-- Here no such. Need all possible settings on earlier coordinates in the
-- order; no assertion in the sunless chart near overlap.
variable {Y:Type*}[NormedAddCommGroup Y][NormedSpace ℂ Y]
def public_test (x:H)(p:I→Γ):List I→(H→L[ℂ]Y)→ Prop
| [],_=>True
| i::t,E=> ContinuousAt (fun v=> E ((U i v) (S.raw t p x))) (p i) ∧ ∀v, public_test x p t (E.comp (U i v))

lemma faith (x:H)(p:I→Γ)(E:H→L[ℂ]Y)(q:S.public_test x p t E):
 E ((S.raw t p).comp (S.stackS t) x)=E (S.raw t p x):=by
 induction t generalizing E with
 | nil=> rfl
 | cons i t ih=>
    obtain ⟨v,h⟩:=q
    have he(k:Γ):E ((U i k) (S.raw t p (S.stackS t x))) = E ((U i k) (S.raw t p x)):= ih (E.comp _) (h k)
    have hspot:ContinuousAt (fun k=>E ((U i k) (S.raw t p (S.stackS t x)))) (p i):=(funext he) ▸ v
    have hp := (P i).retains_at E ((S.raw t p) (S.stackS t x)) (p i) hspot
    rw [shel_step,raw_step]
    change E ((U i (p i)) (S.raw t p ((π i) (S.stackS t x))))= E ((U i (p i)) (S.raw t p x))
    rw [← ContinuousLinearMap.comp_apply (S.raw t p),S.hard t (π i) (fun j v k=> S.floatZ j i k 0) p,ContinuousLinearMap.comp_apply,hp,he]
lemma faithful (x:H)(p:I→Γ)(E:H→L[ℂ]Y)(q:S.public_test x p t E):
 E (S.flight d t (fun i=>(p i:ℝ)) x)= E (S.raw t p x):=(S.smooth_notch d t p).symm ▸ S.faith t x p E q

-- packaging condition over arbitrary prefix of grid movers
variable (x:H)
noncomputable def band (v:List (I×Γ)):H.Op:=v.foldr (fun i (a:H.Op)=> (U i.1 i.2).comp a) Id
lemma band_step (v:List (I×Γ))(i : I×Γ): S.band (i::v)=(U i.1 i.2).comp (S.band v):=rfl
lemma band_raw (p:I→Γ):S.raw t p=S.band (t.map fun i=>(i,p i)):=by induction t with
| nil=> rfl
| cons i v ih=> rw [raw_step,ih]; rfl
def Window (p:I→Γ)(E:H→L[ℂ]Y)(j:I):Prop:=∀ (v:List (I×Γ)) (_:∀i∈v,(i:I×Γ).1≠j), ContinuousAt (fun c : Γ => E (S.band v ((U j c) x))) (p j)
lemma covered(p:I→Γ)(E:H→L[ℂ]Y)(q:∀i∈t,Window S x p E i)(h:t.Nodup): S.public_test x p t E:=by
 induction t generalizing E with
 | nil=> trivial
 | cons i t ih=>
    obtain ⟨v,ht⟩:=List.nodup_cons.mp h
    constructor
    · have hw(k:Γ): (U i k) (S.raw t p x)=S.raw t p ((U i k) x) :=by rw [←ContinuousLinearMap.comp_apply, ←S.hard t _ (fun j _ b=> S.cCom j i b k) p]; rfl
      simp_rw [hw,S.band_raw]
      refine q i (List.Mem.head ..) _ ?_
      rintro y my e; obtain ⟨j,hj,rfl⟩:=List.mem_map.mp my; exact v ((show j=i from e) ▸ hj)
    intro a
    apply ih _ _ ht
    intro r hr T pv
    change ContinuousAt (fun c=>E ((U i a) (S.band T ((U r c) x)))) _
    have hk:=q r (List.Mem.tail _ hr) ((i,a)::T) (by intro x h; rcases List.mem_cons.mp h with h|h; exact h.symm ▸ (show i≠r from fun eq=>v (eq.symm ▸ hr)); exact pv x h)
    exact hk
end Alliance
end YM.CF.Buffered.Afterglow.Tower.Germ
#print axioms YM.CF.Buffered.Afterglow.Tower.Germ.Alliance.covered
