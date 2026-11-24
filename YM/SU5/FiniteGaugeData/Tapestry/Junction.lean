import YM.SU5.FiniteGaugeData.Tapestry.LiftMark
set_option autoImplicit false
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tapestry
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock
open Satin
attribute [local instance] opCStarAlgebra

-- Included here: the exact sharp interlevel operation, linearity and its
-- reading, including on the *original Course*. No limit in these identities.
section
variable {N P:Side}(G:Ratio N P)(A:StepData (More N) (More P))(j:ℕ)
  (Q:Op SU.Slot)(M:Male)(ho:Odd G.count.val)(q:Chi)(d β:ℝ)(l:Loom N)
local notation "run"=> gathered G j Q M ho q d
local notation "push"=>pushMark G A j Q M ho q d β l
variable (f g:Mark N)
lemma collectPlus (V W) : run (f+g) V W=run f V W+run g V W:=by
  unfold gathered avgF before; simp_rw [Pi.add_apply,map_add, sum_add_distrib, smul_add]
lemma collectScale (z:ℂ)(V W) : run (z • f) V W=z • run f V W:=by
  unfold gathered avgF before; simp_rw [Pi.smul_apply,map_smul, ←smul_sum]; rw [smul_comm]
lemma collectUnit(V W) : run (1:Mark N) V W=1:= by
  letI : Nonempty (Forest (ratio G)):= Tree.select (ratio G) ho
  unfold gathered avgF before
  have he:(Fintype.card (Forest (ratio G)):ℝ)≠0:=by positivity
  simp [sub_one,←Nat.cast_smul_eq_nsmul (R:=ℝ), inv_smul_smul₀ he] -- may loop
variable {R:ℕ}(p:LaurentRadius j G.count R) (t:Measurable l)
  (B:A.patch.Branches A.kernel SU.group)(a:0<d)(b:2*d<firstRadius SU.group)
include p t B a b
lemma pushIntegrable (h:Envelope f)(W:Fields P)(V:Pane P):
  Integrable (fun y:Orbit N=> A.density β V y.1 • run f W (drawn l y)) (city N):= Env.integrableX (Env.scale (Env.along (g:=Prod.fst) (slice_env A β B V) measurable_fst) (Env.along (g:=fun x=>(W,drawn l x)) (env_gathered G j Q M ho q d p a b f h) (measurable_const.prodMk (drawn_m l t)))) (city N)
lemma pushPlus(h:Envelope f)(w:Envelope g): push (f+g)= push f + push g:=by
  have hi: Envelope (f+g):= Girt.kitE _ _ (· + ·) (by fun_prop) h w
  funext W; rw [Pi.add_apply,outright G A j Q M ho q d β l p t B a b _ h,outright G A j Q M ho q d β l p t B a b _ w, outright G A j Q M ho q d β l p t B a b _ hi]; simp_rw [collectPlus,smul_add]; exact integral_add (pushIntegrable G A j Q M ho q d β l f p t B a b h W W.1) (pushIntegrable G A j Q M ho q d β l g p t B a b w W W.1)
lemma pushScale (h:Envelope f)(z:ℂ): push (z • f)= z • push f:=by
  have hi:Envelope (z • f):= Girt.pole_w _ (fun y:FC (Single N)=> z • y) (by fun_prop) h
  funext W; rw [Pi.smul_apply,outright G A j Q M ho q d β l p t B a b _ hi,outright G A j Q M ho q d β l p t B a b _ h]; simp_rw [collectScale, smul_comm (A.density β _ _) z]; rw [integral_smul]
omit p t a b
lemma pushUnit : push 1=1:=by
  funext W; change linkLaw A β _ W.1=1; unfold linkLaw Advance.assembled; simp_rw [collectUnit]; simp only [integral_const,probReal_univ,one_smul]; rw [integral_smul_const,(A.isKernel B β).total,one_smul]
end

open Py Py.Rate LocalLimit Preparation Journey Vale
variable {Λ: Preparation} {l : ℕ} (Y:Course Λ (VolumeCape.Dream.Nimbus l)) (H:Real.exp 1 ≤ Λ.x)
variable (s i k:ℕ)

-- casts: fields use mark of size `tent.c (momentm ...)` at level s.
def arrange (N P:Side)(h:N=P) : Mark N ≃ₗ[ℂ] Mark P:= h ▸ LinearEquiv.refl ℂ (Mark N)
lemma arranged (N P:Side)(p:N=P)(f:Mark N) : arrange N P p f=(p ▸ f):=by subst P; rfl
lemma displayPositive {N P:Side}(p:N=P)(A:ℝ)(f:Mark N) : (∀ x,‖f x‖ ≤ A) ↔ (∀ x,‖arrange N P p f x‖≤ A):=by subst P; rfl
lemma displayMult {N P:Side}(p:N=P)(f g:Mark N): arrange N P p (f*g)=arrange N P p f * arrange N P p g:=by subst P; rfl
lemma displayRef {N P:Side}(p:N=P)(z:ℤ)(a:Axis)(f:Mark N): arrange N P p (reflMark a z f)=reflMark a z (arrange N P p f):=by subst P; rfl
variable (S:Finset Cover)
lemma displaySupport {N P:Side}(p:N=P)(b:Bool)(f:Mark N) : AtSupport b (region S N) f ↔ AtSupport b (region S P) (arrange N P p f):=by subst P; rfl

local notation "K"=>tent Y H
local notation "μ"=>momentm Y i s
local notation "σ" => side Y i s
local notation "nP"=> (Λ.Ctor (Y.ir i) (s+1))
local notation "Z"=> ((Y.voyage i).X (Y.uv k))
local notation "G"=> (Vale.apt (Y.ir i) Λ.block Λ.R.L s)
local notation "ΦA"=> steps Λ.V (Y.ir i) Λ.block (Y.uv k) s
local notation "C" => (Y.voyage i).CapeT
local notation "T" => terrain Y H (Y.ir i) s

def present: Swatch S→ₗ[ℂ] Mark (side Y i s) := (arrange _ _ (terrain Y H (Y.ir i) s)).toLinearMap.comp (appear S (tent Y H) (momentm Y i s))
def exhibit : Family (tent Y H) →ₗ[ℂ] Mark (side Y i s) := (arrange _ _ (terrain Y H (Y.ir i) s)).toLinearMap.comp (LinearMap.proj μ)
-- Y H s i order except S first or last per file declaration
lemma present_exhibit (f:Swatch S): present Y H s i S f = exhibit Y H s i (render S K f):=rfl
lemma present_send (F:Family K) : exhibit Y H s i F= Journey.send Y H i s (F μ) := arranged ..
lemma actual_add (F D:Family K) : exhibit Y H s i (F+D)= exhibit Y H s i F + exhibit Y H s i D:= map_add ..
lemma actual_product (F D:Family K) : exhibit Y H s i (F*D)= exhibit Y H s i F * exhibit Y H s i D:= displayMult ..
lemma actual_one : exhibit Y H s i 1=1:= casts T where casts {N P:Side}(p:N=P) : arrange _ _ p 1=1:= by subst_vars; rfl
lemma actual_reflect (z:ℤ) (f:Family K): exhibit Y H s i (reflected K z f)=reflMark 3 z (exhibit Y H s i f):= displayRef ..
lemma exhibited {u:Bool}{f:Family K} (p:InTest K true S u f) : AtSupport u (region S σ) (exhibit Y H s i f) := (displaySupport S T u _).mp (p.support μ)
lemma presented (f:Swatch S): AtSupport false (region S σ) (present Y H s i S f) := (displaySupport S T false _).mp (appearSupport S K μ f)
lemma present_bound (f:Swatch S)(x): ‖present Y H s i S f x‖ ≤ spread S * ‖f‖:= (displayPositive T _ _).1 (appearLe S K μ f) x
lemma present_sample (p: Hosp S σ)(f:Swatch S){A':ℝ}(h:∀ x, ‖present Y H s i S f x‖ ≤ A') : ‖f‖ ≤ A':= sampling S K μ ((T).symm ▸ p) f ((displayPositive T _ _).mpr h)
lemma present_inj (p: Hosp S σ): Injective (present Y H s i S):= (arrange _ _ T).injective.comp (appear_inj S K μ ((T).symm ▸ p))
lemma present_mend (p: Roomy S σ){f:Mark σ}(u: AtSupport false (region S σ) f): ∃ v:Swatch S, present Y H s i S v=f:= by
  let W:=arrange _ _ T; let t:= W.symm f; have h: arrange _ _ T t=f:= W.apply_symm_apply f
  have he : AtSupport false (region S ((K).c μ)) t:= (displaySupport S T _ _).2 (h.symm ▸ u)
  refine ⟨mend S K μ ((T).symm ▸ p) he,?_⟩; change arrange _ _ _ (appear _ _ _ _) = _; rw [appear_mend,h]
lemma eyes_native (p: Hosp S σ): ∃ m : Evens S → FC (Single σ) →L[ℂ] ℂ, ∀ f: Swatch S,∀ x:PairsC,∀ t:Evens S,
   (∀ A, ‖m t A‖ ≤ ‖A‖) ∧ daub S (f t) x=m t (present Y H s i S f (replant S σ x)):= castEyes S (tent Y H) μ _ T p
where castEyes (S:Finset Cover)(K':Calibration)(o N:Side)(h:K'.c o=N)(p: Hosp S N) : ∃ m : Evens S → FC (Single N) →L[ℂ] ℂ,∀ f: Swatch S,∀ x:PairsC,∀ t:Evens S,(∀ A, ‖m t A‖ ≤ ‖A‖) ∧ daub S (f t) x=m t (arrange _ _ h (appear S K' o f) (replant S N x)):=by
        subst N; exact ⟨fun i=>(eye S K' o p i).toContinuousLinearMap,fun f x i=> ⟨eye_bounded S K' o p i, (eye_readCover S K' o p f x i).symm⟩⟩
include H in
lemma roomyTail : ∀ᶠ i in atTop, Roomy S (side Y i s):=by
  filter_upwards [(momentum Y s).eventually (separates K (tips S))] with i p
  change Roomy S (Λ.Ctor (Y.ir i) s)
  exact terrain Y H (Y.ir i) s ▸ (show Roomy S ((K).c (momentm Y i s)) from ⟨p⟩)
lemma actualRead (f:Family K): Journey.sharp Y H s i k f=Journey.compass Y i k s (exhibit Y H s i f):=by rw [present_send]; rfl
-- identification all kicked cutoffs and funded observing levels (including possibly before Ferry).
lemma funds {f:Mark (side Y i s)}(p:Envelope f)(t:(Y.voyage i).kick ≤ k)(u:s≤ Y.uv k) :
    let P':= (Z).gram s; let l':= C s; let w:=partitionZ P' Λ.U l'
    let v:= fun x=> inner ℂ (Dial.mateK σ) (acts (f (drawn l' x)) (denZ P' Λ.U l' x))
    Integrable v (city σ) ∧ w≠0 ∧ Journey.compass Y i k s f=(∫ x,v x∂city σ)/w:=by
  intro _ _ _ v; have l:= Y.each_level i k s t u
  exact ⟨mark_integrable ((Y.voyage i).ownership s).paid.bill p (Marks.can_read _ _ _ _ l), l.valid, rfl⟩

/- Critical renormalization/level identity: `ascender` is a function of
   BOTH tori's true links in the original prescription and produces a
   fine-level test to use before *that* marked functional. Even on cone this
   map varies with i,k. `costume` represents its output on the fixed cover. -/
abbrev patternGram := ((Y.voyage i).X (Y.uv k)).gram
abbrev patternQ := ((Y.voyage i).X (Y.uv k)).wave s
abbrev patternA := steps Λ.V (Y.ir i) Λ.block (Y.uv k) s
abbrev ascender (f:Mark (side Y i s)) : Mark (side Y i (s+1)):= nextMark (ho:=Λ.R.odd_side) (j:=Λ.K.j) (Z).gram C Chi.canonical Λ.J.d (Z).wave (steps Λ.V (Y.ir i) Λ.block (Y.uv k)) s f
abbrev followBox := liner (S.image (fun a=> Λ.R.L.val • a)) (Λ.R.L.val*gross (aliasLaw Λ) (distanceLaw l) Λ.R.J)
variable (p: Satin.PairIdx Y s i k)
local notation "B"=> followBox (Λ:=Λ) (l:=l) S
include p
lemma ascendSupport {g:Mark σ}{u:Bool}(t : AtSupport u (region S σ) g): AtSupport u (region B nP) (ascender Y s i k g):= by
  have a:= (fullness Y i k p.1).cap_grant; obtain ⟨l'⟩:= a.grant s p.2
  obtain ⟨_,_,_,V',_⟩:= l'.cap
  have h:= surround G ΦA Λ.K.j (patternQ Y s i k).val ((Z).gram (s+1)).J.M Λ.R.odd_side Chi.canonical Λ.J.d ((Z).gram (s+1)).beta (C s) (Journey.legal _) V'.bill (a.branch s p.2) l'.legal.1 l'.legal.2 _ t (Journey.tissue Y i s) (a.aligned s p.2)
  have eq: (patternA Y s i k).patch.J= Λ.R.J:= a.radius s p.2; rw [eq] at h
  exact h.mono (next_contains S _ σ G)
omit p
variable (r : Roomy (followBox (Λ:=Λ) (l:=l) S) (side Y i (s+1)))

protected def costume (f:Swatch S): Swatch (followBox (Λ:=Λ) (l:=l) S) := (present_mend Y H (s+1) i _ r (ascendSupport Y s i k S p (presented Y H s i S f))).choose
include p r
lemma costumed (f:Swatch S): present Y H (s+1) i B (Tapestry.costume Y H s i k S p r f)=ascender Y s i k (present Y H s i S f):= (present_mend Y H (s+1) i B r (ascendSupport Y s i k S p (presented Y H s i S f))).choose_spec
omit r
lemma ascendPlus (f g:Mark σ)(u:Envelope f)(v:Envelope g): ascender Y s i k (f+g)=ascender Y s i k f+ascender Y s i k g:=by
  let a:= (fullness Y i k p.1).cap_grant; obtain ⟨L⟩:= a.grant s p.2
  exact pushPlus G ΦA Λ.K.j (patternQ Y s i k).val ((Z).gram (s+1)).J.M Λ.R.odd_side Chi.canonical Λ.J.d ((Z).gram (s+1)).beta (C s) f g (Journey.legal _) ((Y.voyage i).ownership s).paid.bill (a.branch s p.2) L.legal.1 L.legal.2 u v
lemma ascendScale (f:Mark σ)(u:Envelope f)(z:ℂ):ascender Y s i k (z • f)=z • ascender Y s i k f:=by
  let a:= (fullness Y i k p.1).cap_grant; obtain ⟨L⟩:= a.grant s p.2
  exact pushScale G ΦA Λ.K.j (patternQ Y s i k).val ((Z).gram (s+1)).J.M Λ.R.odd_side Chi.canonical Λ.J.d ((Z).gram (s+1)).beta (C s) f (Journey.legal _) ((Y.voyage i).ownership s).paid.bill (a.branch s p.2) L.legal.1 L.legal.2 u z
lemma ascendUnit : ascender Y s i k 1=1:=pushUnit G ΦA _ (patternQ Y s i k).val _ Λ.R.odd_side Chi.canonical Λ.J.d ((Z).gram (s+1)).beta _ ((fullness Y i k p.1).cap_grant.branch s p.2) -- implicit M l etc

def gangway : Swatch S →ₗ[ℂ] Swatch (followBox (Λ:=Λ) (l:=l) S) where
  toFun:= Tapestry.costume Y H s i k S p r
  map_add' f g:= by
    apply present_inj _ _ _ _ B (Roomy.seats r); rw [map_add,costumed,costumed,costumed,map_add,ascendPlus Y s i k p _ _ (presented Y H s i S _).env (presented Y H s i S _).env]
  map_smul' z f:= by
    apply present_inj _ _ _ _ B (Roomy.seats r); rw [map_smul,costumed,costumed,map_smul,ascendScale Y s i k p _ (presented Y H s i S _).env]; rfl

lemma partake {f:Mark σ}(h:AtSupport false univ f) : Journey.compass Y i k s f=Journey.compass Y i k (s+1) (ascender Y s i k f):=by
  unfold Journey.compass; rw [single_num Λ.U (Z).gram C Chi.canonical Λ.J.d (Y.uv k) (Z).wave (steps Λ.V (Y.ir i) Λ.block (Y.uv k)) (Journey.legal Λ) (fullness Y i k p.1).cap_grant h p.2, (Z).balance s p.2.le,← (Z).balance (s+1) p.2]
include r
lemma readStep (f:Swatch S) : sharp Y H s i k (render S K f)=sharp Y H (s+1) i k (render B K (gangway Y H s i k S p r f)):=by -- order
  rw [actualRead,actualRead,←present_exhibit,←present_exhibit]
  change _ = Journey.compass Y i k (s+1) (present _ _ _ _ B (Tapestry.costume Y H s i k S p r f)); rw [costumed]; exact partake _ _ _ _ p ((presented _ _ _ _ S f).mono (subset_univ _))
end YM.CF.Buffered.Afterglow.Tapestry
#print axioms YM.CF.Buffered.Afterglow.Tapestry.readStep
