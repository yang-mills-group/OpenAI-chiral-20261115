import YM.OS.Flow
/-!
# From compatible discrete clocks on a resolution hierarchy to continuous heat

No estimate of continuity on *transfer operators* required. The range-before-zero
condition (available from the padding improvement, Flood.lean) is the only further
condition. By two contractions, the norm loss in one double step bounds the size
of the jump in that step; telescope from a predecessor. This permits robust use on
other clocks (without assuming nonnegative spectra for odd steps).
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower
open Function Filter Topology Set
open scoped InnerProductSpace NNReal
namespace MeshClock
-- Λ=8B etc abstract
structure Mesh where
 L : ℕ
 Llarge : 2≤L
 base : ℝ≥0
 baseP : 0<base
variable (M:Mesh)

def acts (s t:ℕ) (i:ℕ):ℕ:= M.L^(t-s) * i
@[simp] lemma same (s i:ℕ): acts M s s i=i:=by simp [acts]
lemma adds (s t i j:ℕ): acts M s t (i+j)=acts M s t i+acts M s t j:=by simp [acts,Nat.left_distrib]
lemma distributes (s t i j:ℕ): acts M s t (i*j)=i*acts M s t j:=by unfold acts; ring
lemma finer (s t r i:ℕ)(a:s≤ t)(b:t≤r):acts M t r (acts M s t i)=acts M s r i:=by rw [acts,acts,acts,←mul_assoc,←pow_add]; congr 2; omega

lemma cast_p (S:Mesh): 0< (S.L:ℝ≥0):= by exact_mod_cast Nat.lt_of_lt_of_le (by decide : 0<2) S.Llarge

def mill (s:ℕ): ℝ≥0:= M.base / (M.L:ℝ≥0)^s
lemma mill_pos (S:Mesh)(s:ℕ): 0<mill S s := div_pos S.baseP (pow_pos (cast_p S) _)
def whenly (s i:ℕ):ℝ≥0 := i * mill M s
lemma when_zero (s:ℕ):whenly M s 0=0:=by simp [whenly]
lemma when_pos (s i:ℕ)(h : 0 < i):0<whenly M s i:=mul_pos (by exact_mod_cast h) (mill_pos M s)
lemma when_le (s i j:ℕ):whenly M s i ≤ whenly M s j ↔ i≤ j:=by unfold whenly; simp [mul_le_mul_iff_left₀ (mill_pos M s)]
lemma when_inj (s:ℕ):Injective (whenly M s):=by intro i j h; exact Nat.le_antisymm ((when_le M s ..).mp h.le) ((when_le M s ..).mp h.ge)
lemma when_add (s i j:ℕ):whenly M s (i+j)=whenly M s i+whenly M s j:=by simp [whenly,add_mul]
lemma mill_finer (s t:ℕ)(h:s≤t): (M.L:ℝ≥0)^(t-s)*mill M t=mill M s :=by
 let L:ℝ≥0 := M.L
 change L^(t-s)*(M.base/L^t) = M.base/L^s
 have hn:L≠0:= (cast_p M).ne'
 field_simp; rw [mul_comm _ M.base, mul_assoc]; rw [←pow_add]; simp [h]
lemma matchR (s t i:ℕ)(h:s≤ t): whenly M t (acts M s t i)=whenly M s i:=by
 simp only [whenly,acts,Nat.cast_mul,Nat.cast_pow]; rw [mul_comm _ (i:ℝ≥0),mul_assoc,mill_finer M s t h]

def times : Set ℝ≥0 := {x|∃ (s i:ℕ), whenly M s i = x}
theorem each (s i:ℕ):whenly M s i∈times M:=⟨s,i,rfl⟩
lemma split {x:ℝ≥0}(h:x∈times M):∃ (s i:ℕ), whenly M s i=x:= h
lemma common {x y:ℝ≥0}(p:x∈times M)(q:y∈times M):∃ (s i j:ℕ), whenly M s i=x∧whenly M s j=y:=by
 obtain ⟨s,i,rfl⟩:= split _ p; obtain ⟨t,j,rfl⟩:= split _ q
 exact ⟨max s t,acts M s (max s t) i,acts M t (max s t) j,matchR M _ _ _ (le_max_left ..),matchR M _ _ _ (le_max_right ..)⟩
lemma plr {x y:ℝ≥0}(p:x∈times M)(q:y∈times M):x+y∈times M:=by
 obtain ⟨s,i,j,rfl,rfl⟩:= common _ p q; rw [← when_add]; apply each

lemma vanishes (M:Mesh): Tendsto (fun s=> mill M s) atTop (𝓝 0):=by
 unfold mill
 apply NNReal.tendsto_coe.mp
 simp only [NNReal.coe_div,NNReal.coe_pow,NNReal.coe_natCast,NNReal.coe_zero]
 apply Filter.Tendsto.div_atTop (a:=(M.base:ℝ)) tendsto_const_nhds
 apply tendsto_pow_atTop_atTop_of_one_lt
 exact_mod_cast Nat.lt_of_lt_of_le (by decide:1<2) M.Llarge
lemma shade (x:ℝ≥0): Tendsto (fun s=> whenly M s (⌊ x / mill M s⌋₊+1)) atTop (𝓝 x):=by
 have hx:Tendsto (fun s=>x+mill M s) atTop (𝓝 x):=by simpa using (tendsto_const_nhds (x:=x)).add (vanishes M)
 refine tendsto_of_tendsto_of_tendsto_of_le_of_le (tendsto_const_nhds (x:=x)) hx ?_ ?_
 · intro s; have h:=Nat.lt_floor_add_one (x/mill M s); change x≤whenly ..; unfold whenly
   rw [←div_le_iff₀ (mill_pos M s),Nat.cast_add_one]; exact h.le
 intro s; unfold whenly; push_cast; rw [add_mul,one_mul]; gcongr
 rw [←le_div_iff₀ (mill_pos M s)]; exact Nat.floor_le (by simp)
lemma fills : Dense (times M) := by
 intro x
 exact mem_closure_of_tendsto (shade M x) (Eventually.of_forall fun i=>each ..)

/- A scale-compatible additive family of lattice moves, includes both
   parities. Demand that strictly positive *even* times have dense total
   range (support margin handles this on motion meshes -- alternatively
   continuity at zero proven directly suffices). -/
structure Many (X:Hilbert) where
 move (s i:ℕ): X.Op
 source(s:ℕ):move s 0=ContinuousLinearMap.id ℂ _
 add(s i j:ℕ):(move s i).comp (move s j)= move s (i+j)
 refines(s t i:ℕ)(h:s≤ t):move s i=move t (acts M s t i)
 close(s i:ℕ): (move s i).adjoint=move s i
 small(s i:ℕ): ‖move s i‖≤1
 early : Dense (⋃ s:ℕ, range (fun x=> (move s 2) x))
variable {M}
namespace Many
variable {X:Hilbert} (F:Many M X)
def double (s i:ℕ): X.Op:=F.move s (2*i)
lemma double_source (s:ℕ): F.double s 0=ContinuousLinearMap.id ℂ X:=by unfold double; rw [mul_zero]; exact F.source _
lemma double_add (s i j:ℕ): (F.double s i).comp (F.double s j)=F.double s (i+j):=by unfold double; rw [F.add,Nat.left_distrib]
lemma double_finer (s t i:ℕ)(h:s≤t): F.double s i=F.double t (acts M s t i) :=by unfold double; rw [F.refines s t _ h,distributes]
lemma double_small (s i:ℕ): ‖F.double s i‖≤1:= F.small ..
lemma swing (s i:ℕ)(x y:X): inner ℂ (F.double s i x) y = inner ℂ x (F.double s i y):=by unfold double; rw [←ContinuousLinearMap.adjoint_inner_right,F.close]
lemma less (s i:ℕ)(x:X): ‖F.double s i x‖≤‖x‖:= ((F.double s i).le_opNorm x).trans (mul_le_of_le_one_left (norm_nonneg _) (F.double_small ..))
lemma closer (s i:ℕ)(x y:X): dist (F.double s i x) (F.double s i y) ≤ dist x y :=by simp only [dist_eq_norm]; rw [←map_sub]; exact F.less ..
lemma cord (s i j:ℕ)(x:X): F.double s i (F.double s j x)=F.double s (i+j) x:=by rw [←ContinuousLinearMap.comp_apply,F.double_add]
lemma flip (s i j:ℕ)(x:X): F.double s i (F.double s j x)=F.double s j (F.double s i x):=by rw [F.cord,F.cord,add_comm]

/- earlier differences to bound motion at any still later time. -/
lemma later (s i j:ℕ)(x:X):
 dist (F.double s j (F.double s i x)) (F.double s i x) ≤ dist (F.double s j x) x:= by rw [F.flip]; exact F.closer ..
lemma earned (s i:ℕ)(x:X): dist (F.double s i x) x ^ 2 ≤ ‖x‖^2 - ‖F.double s i x‖^2:= by
 rw [dist_comm,dist_eq_norm,norm_sub_sq (𝕜:=ℂ)]
 have h:F.double s i x=F.move s i (F.move s i x):=by unfold double; rw [two_mul,← F.add,ContinuousLinearMap.comp_apply]
 have ht:inner ℂ x (F.double s i x)=inner ℂ (F.move s i x) (F.move s i x):=by rw [←ContinuousLinearMap.adjoint_inner_right,F.close,← h]
 rw [ht,inner_self_eq_norm_sq]
 have he: ‖F.double s i x‖ ≤ ‖F.move s i x‖:=by
    rw [h]; exact ((F.move s i).le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) (F.small ..))
 have hp:=norm_nonneg (F.double s i x)
 nlinarith
-- (include the deduction to avoid summation and bad truncation bounds)
lemma deduct (s j:ℕ)(x:X)(n k:ℕ) (e:n*j≤k):
  (n:ℝ)*dist (F.double s j (F.double s k x)) (F.double s k x)^2 ≤ ‖x‖^2-‖F.double s (n*j) x‖^2:=by
 induction n with
 | zero=> simp [F.double_source]
 | succ n ih =>
    rw [Nat.cast_add_one,Nat.add_mul,one_mul]
    have hv: n*j≤k:=by rw [Nat.add_mul,one_mul] at e; omega
    obtain ⟨a,ha⟩:= Nat.exists_eq_add_of_le hv
    have h: F.double s k x = F.double s a (F.double s (n*j) x):=by rw [ha,F.cord,add_comm]
    have ht:=F.earned s j (F.double s (n*j) x)
    have hg:dist (F.double s j (F.double s k x)) (F.double s k x) ≤ dist (F.double s j (F.double s (n*j) x)) (F.double s (n*j) x):=h ▸ (F.later s a j (F.double s (n*j) x)) -- direction h substitution?
    rw [F.cord,add_comm j] at hg ht; rw [F.cord,add_comm j] at hg
    have hw:=sq_le_sq₀ dist_nonneg dist_nonneg |>.mpr hg
    have hy:=ih hv
    rw [F.cord,add_comm j] at hy ⊢; linarith
lemma bound_at (s j k N:ℕ)(x:X)(e:N*j≤k):
  (N:ℝ)*dist (F.double s j (F.double s k x)) (F.double s k x)^2 ≤ ‖x‖^2:=
 (F.deduct _ _ _ _ _ e).trans (sub_le_self _ (sq_nonneg _))

-- Evaluate even subgroup semigroup on physical times. Done on the
-- whole half-line via extension step later.
variable (x : times M)
def stepU : X.Op:=F.double (split M x.property).choose (split M x.property).choose_spec.choose
lemma atM (s i:ℕ)(h:x.val=whenly M s i):F.stepU x=F.double s i:=by
 unfold stepU; set a:=(split M x.property).choose
 set b:=(split M x.property).choose_spec.choose
 have h': whenly M a b = x.val := (split M x.property).choose_spec.choose_spec
 let t:=max a s
 have e:a ≤ t:=le_max_left ..; have p:s≤t:=le_max_right ..
 rw [F.double_finer _ _ _ e,F.double_finer s _ _ p]
 have he:acts M a t b=acts M s t i:=when_inj M t ((matchR M _ _ _ e).trans ((h'.trans h).trans (matchR M _ _ _ p).symm))
 rw [he]
lemma on_close (i j:X):dist (F.stepU x i) (F.stepU x j)≤dist i j:=F.closer ..

lemma earlier (v:X)(h:v∈ (⋃ s:ℕ, range (fun x=> (F.move s 2) x))):UniformContinuous (fun i => F.stepU i v) := by
 obtain ⟨s,w,rfl⟩ : ∃ s:ℕ,∃ w:X,F.double s 1 w=v := by
   obtain ⟨s,hs⟩:=mem_iUnion.mp h; obtain ⟨w,rfl⟩:=hs; exact ⟨s,w,by simp [double]⟩
 rw [Metric.uniformContinuous_iff]; intro ε e
 let X0:=F.double s 1 w
 obtain ⟨N,hN⟩:=exists_nat_gt (‖w‖^2/ε^2)
 have hn:0 < (N:ℝ) := lt_of_le_of_lt (by positivity) hN
 have hN':‖w‖^2<(N:ℝ)*ε^2:=(div_lt_iff₀ (pow_pos e 2)).mp hN
 let δ := ((mill M s):ℝ) / N
 have d:0 < δ:= div_pos (mill_pos M s) hn
 have price(i k:times M)(h:dist i k <δ)(h0:i.val≤ k.val):dist (F.stepU i X0) (F.stepU k X0)<ε:=by
    obtain ⟨u,a,b,ha,hb⟩:=common M i.property k.property
    let t:=max s u
    let A:=acts M u t a; let B:=acts M u t b; let Z:=acts M s t 1
    have g:s≤t:=le_max_left ..; have p:u≤t:=le_max_right ..
    have ha':whenly M t A=i:= (matchR M _ _ _ p).trans ha
    have hb':whenly M t B=k:= (matchR M _ _ _ p).trans hb
    have hz:whenly M t Z=mill M s:=by unfold Z; rw [matchR M _ _ _ g,whenly,Nat.cast_one,one_mul]
    have ha:A≤B:=(when_le M t A B).mp (by rwa [ha',hb'])
    obtain ⟨j,hj⟩:= Nat.exists_eq_add_of_le ha
    have hs:X0=F.double t Z w:= by unfold X0; rw [F.double_finer _ _ _ g]
    rw [F.atM i t A ha'.symm,F.atM k t B hb'.symm,hj,←F.cord]
    apply (F.closer t A _ _).trans_lt
    rw [dist_comm,hs]
    have hpow:N * j ≤ Z:=by
      -- distance exactly whenly j; δ choice wins at common scale
      change dist (i.val:ℝ≥0) k.val < δ at h
      rw [← ha',← hb',hj,when_add] at h
      change dist ((whenly M t A:ℝ≥0):ℝ) ((whenly M t A+whenly M t j:ℝ≥0):ℝ) < δ at h
      rw [NNReal.coe_add,Real.dist_eq] at h
      have hw:((whenly M t j:ℝ≥0):ℝ) < δ:=by simpa using h
      have hj':(N:ℝ) * (whenly M t j:ℝ≥0) < ((mill M s:ℝ≥0):ℝ):=by rw [mul_comm]; exact (lt_div_iff₀ hn).mp hw
      refine (when_le M t (N*j) Z).mp ?_; rw [hz]
      change ((whenly M t (N*j):ℝ≥0):ℝ) ≤ ((mill M s:ℝ≥0):ℝ)
      apply le_trans _ hj'.le; unfold whenly; simp [mul_assoc]
    have hv:=F.bound_at t j Z N w hpow
    refine (sq_lt_sq₀ dist_nonneg e.le).mp ((mul_lt_mul_iff_right₀ hn).mp (hv.trans_lt hN'))
 refine ⟨δ,d,fun i k h=> ?_⟩
 rcases le_total i.val k.val with p|p
 · exact price i k h p
 rw [dist_comm]
 exact price k i (dist_comm i k ▸ h) p

lemma evenly (w:X): UniformContinuous (fun i => F.stepU i w):=by
 rw [Metric.uniformContinuous_iff]; intro ε p
 obtain ⟨u,h,he⟩:=Metric.mem_closure_iff.mp (F.early w) (ε/3) (by positivity)
 obtain ⟨δ,e,t⟩:=Metric.uniformContinuous_iff.mp (F.earlier u h) (ε/3) (by positivity)
 refine ⟨δ,e,fun a b v=> ?_⟩
 change dist (F.stepU a w) (F.stepU b w) < ε
 apply lt_of_le_of_lt (dist_triangle _ (F.stepU a u) _)
 have h1:= dist_triangle (F.stepU a u) (F.stepU b u) (F.stepU b w)
 have h2:=F.on_close a w u; have h3:=F.on_close b u w; rw [dist_comm u] at h3
 have hv:=t v; change dist (F.stepU a u) (F.stepU b u) < ε/3 at hv; linarith

def river (v:X):ℝ≥0→ X:= (fills M).extend (fun i => F.stepU i v)
lemma river_uc (v:X):UniformContinuous (F.river v):= (fills M).uniformContinuous_extend (F.evenly v)
lemma river_at (s i:ℕ)(v:X):F.river v (whenly M s i)=F.double s i v:=by
 unfold river
 let y:times M:=⟨whenly M s i,each M s i⟩
 have h: (fills M).extend (fun i=> F.stepU i v) y.val = F.stepU y v := (fills M).extend_of_ind (F.evenly v) y
 exact h.trans (by rw [F.atM y s i rfl])
private lemma resolve (M:Mesh){Y:Type*}[TopologicalSpace Y][T2Space Y]{f g:ℝ≥0→Y}(a:Continuous f)(b:Continuous g)(h:∀s i:ℕ,f (whenly M s i)=g (whenly M s i))(x:ℝ≥0):f x=g x:=by
 suffices f=g by rw [this]
 apply (fills M).denseRange_val.equalizer a b
 funext y; dsimp only [Function.comp_apply]; obtain ⟨s,i,h1⟩:= split M y.property; rw [←h1]; exact h ..

lemma river_plus (u v:X)(t:ℝ≥0):F.river (u+v) t=F.river u t+F.river v t:=
 resolve M (F.river_uc _).continuous ((F.river_uc _).continuous.add (F.river_uc _).continuous) (fun s i=>by simp [F.river_at]) t
lemma river_smul (c:ℂ)(u:X)(t:ℝ≥0):F.river (c•u) t=c•F.river u t:=
 resolve M (F.river_uc _).continuous (continuous_const.smul (F.river_uc _).continuous) (fun s i=>by simp [F.river_at]) t
lemma river_small (u:X)(t:ℝ≥0):‖F.river u t‖≤‖u‖:=by
 let q n:=whenly M n (⌊ t / mill M n⌋₊+1)
 have h:Tendsto (fun n=>‖F.river u (q n)‖) atTop (𝓝 ‖F.river u t‖):=((F.river_uc _).continuous.norm.tendsto _).comp (shade M t)
 apply le_of_tendsto h
 exact Eventually.of_forall fun i=>by unfold q; rw [F.river_at]; exact F.less ..
lemma river_source (u:X):F.river u 0=u:=by
 rw [←when_zero M 0,river_at,F.double_source]; rfl

def track (t:ℝ≥0):X.Op:= (show X→ₗ[ℂ] X from {
   toFun (v:X):=F.river v t
   map_add' u v:=F.river_plus u v t
   map_smul' c v:=F.river_smul c v t}).mkContinuous 1 (fun i=>by change ‖F.river _ _‖≤ _; simpa using F.river_small i t)
lemma trek (t:ℝ≥0)(x:X):F.track t x=F.river x t:=rfl
lemma trekU (x:X): UniformContinuous (fun t=> F.track t x):=F.river_uc _
lemma track_even (s i:ℕ):F.track (whenly M s i)=F.double s i:=by ext1 v; exact F.river_at _ _ _
lemma track_le (t:ℝ≥0): ‖F.track t‖≤1 :=ContinuousLinearMap.opNorm_le_bound _ zero_le_one (by intro v; simp; exact F.river_small v t)

lemma track_times (t u:ℝ≥0):(F.track t).comp (F.track u)=F.track (t+u):=by
 ext1 x; change F.track t (F.track u x)=F.track (t+u) x
 apply resolve M (f:=fun u=>F.track t (F.track u x)) (g:=fun u=>F.track (t+u) x)
 · exact (F.track t).continuous.comp (F.trekU _).continuous
 · exact (F.trekU _).continuous.comp (continuous_const.add continuous_id)
 intro s i; apply resolve M (f:=fun t=>F.track t _) (g:=fun t=>F.track (t+_) _)
 · exact (F.trekU _).continuous
 · exact (F.trekU _).continuous.comp (continuous_id.add continuous_const)
 intro a b
 let m:=max a s; have h:a ≤ m:=le_max_left ..; have p:s≤m:=le_max_right ..
 let A:=acts M a m b; let B:=acts M s m i
 have ht:whenly M a b=whenly M m A:=(matchR M _ _ _ h).symm
 have hp:whenly M s i=whenly M m B:=(matchR M _ _ _ p).symm
 rw [ht,hp,←when_add,F.track_even,F.track_even,F.track_even,F.cord]

lemma track_adjoint (t:ℝ≥0): (F.track t).adjoint=F.track t:=by
 ext1 x
 apply ext_inner_left ℂ
 intro y; rw [ContinuousLinearMap.adjoint_inner_right]
 apply resolve M (f:=fun t=>inner ℂ (F.track t y) x) (g:=fun t=>inner ℂ y (F.track t x))
 · exact (F.trekU _).continuous.inner continuous_const
 · exact continuous_const.inner (F.trekU _).continuous
 intro s i; rw [F.track_even,F.swing]
lemma track_invariant (x:X)(h:∀s i,F.double s i x=x)(t:ℝ≥0):F.track t x=x:=by
 apply resolve M (f:=fun t=> F.track t x) (g:=fun t=>x) (F.trekU _).continuous continuous_const
 intro s i; rw [F.track_even,h]
lemma track_birth: F.track 0=ContinuousLinearMap.id ℂ _:=by ext v; exact F.river_source v

/-- No assertion about spatial directions in this implementation (U dummy).
    Useful for exposing unconditional spectral conclusions along chosen axis only. -/
def monoAxis (a:Axis): OS.Semigroup X a where
 E := F.track
 U s := ContinuousLinearMap.id ℂ X
 eZero:=F.track_birth
 time t s:=(F.track_times t s).symm
 shrinks t:= F.track_le t
 sym t := F.track_adjoint t
 uZero := rfl
 space t s:=rfl
 independent t s:=rfl
 unitary t v:=rfl
 continuousE v:=(F.trekU v).continuous
 continuousU v:=continuous_const
end Many
end MeshClock
end YM.CF.Buffered.Afterglow.Tower
#print axioms YM.CF.Buffered.Afterglow.Tower.MeshClock.Many.track_adjoint
#print axioms YM.CF.Buffered.Afterglow.Tower.MeshClock.Many.monoAxis
