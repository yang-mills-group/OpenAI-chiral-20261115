import YM.SU5.FiniteGaugeData.Mist.Artery
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 420000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Endless.Piper
open Function Filter Metric Finset Lattice Hills Mist Complex
open scoped Topology BigOperators InnerProductSpace
-- finite averages, no integral.Prep. use composite
variable {T: Type} {V W R:Type*}
inductive Knot (S: Type): Type where
 | pin (x:S)
 | turn (m l: Knot S) (x y:ℝ) (p:0≤x)(q:0 ≤ y)(v:x+y=1)
namespace Knot
section
variable [AddCommGroup V][Module ℂ V][AddCommGroup W] [Module ℂ W]
def eval(f:T→V):Knot T→ V
 | .pin t=> f t
 | .turn p q x y _ _ _=> (x:ℂ) • p.eval f+ (y:ℂ) • q.eval f
lemma push (T0:V→ₗ[ℂ] W)(z:Knot T)(f:T→V): eval (fun i=> T0 (f i)) z=T0 (z.eval f):= by induction z with
 | pin x=>rfl
 | turn x y a b p q s ih ig=> unfold eval; rw [map_add,map_smul,map_smul,ih,ig]
lemma lift (z:Knot T)(v:V): eval (fun _=> v) z=v:=by induction z with
 | pin x=>rfl
 | turn x y a b p q s ih ig=> unfold eval; rw [ih,ig,←add_smul,←ofReal_add,s,ofReal_one,one_smul]
end
#check pin
section
variable (z l:Knot T)
variable (P:T→ Prop)
def Covers (P:T→Prop): Knot T→ Prop
 | .pin x=> P x
 | .turn l p ..=> Covers P l ∧ Covers P p
lemma every (p:∀ x:T,P x):Covers P z := by induction z with
 | pin x=> exact p x
 | turn x y a b p q _ ih iz=> exact ⟨ih,iz⟩
def evolves (f:T→ Knot T):Knot T→ Knot T
 | .pin x=> f x
 | .turn l m a b p q z=> .turn (evolves f l) (evolves f m) a b p q z
lemma burrow(Q:T→V)[AddCommGroup V][Module ℂ V](f:T→Knot T): (evolves f z).eval Q=z.eval (fun i=>(f i).eval Q):=by induction z with
 | pin x=>rfl
 | turn x y a b p q s ih ig=> unfold evolves eval; rw [ih,ig]
-- shadow issue variable order [V inst] after Q OK.
lemma evol_cov (f:T→ Knot T)(w:z.Covers P)(S:T→Prop)(k:∀ i,P i→ Covers S (f i)): Covers S (evolves f z):=by induction z with
 | pin x=> exact k _ w
 | turn x y a b p q s ih ig=> exact ⟨ih (show Covers P x ∧ _ from w).1,ig (show Covers P x∧ Covers P y from w).2⟩
variable (f:T→V) [NormedAddCommGroup V] [NormedSpace ℂ V]
variable {c:ℝ}
lemma mix [AddCommGroup R][Module ℂ R] (f g:T→R)(a b:ℂ):z.eval (fun i=> a • f i+b • g i)=a • z.eval f+b • z.eval g:=by induction z with
 | pin x=>rfl
 | turn x y t u p q w ih ig=> unfold eval; rw [ih,ig]; module
lemma decr [AddCommGroup R][Module ℂ R] (f g:T→R):z.eval (fun i=>f i-g i)=z.eval f-z.eval g:=by simpa only [neg_smul,one_smul,←sub_eq_add_neg] using mix z f g 1 (-1)
lemma exchange(z l:Knot T)(f:T→T→V): z.eval (fun i=>l.eval (fun j=> f i j))=l.eval (fun j=> z.eval (fun i=> f i j)):=by
 -- exact Fub.Clock. linearity
 induction z with
 | pin x=> rfl
 | turn x y a b p q s ih ig=>
      simp only [eval.eq_2, ih, ig]; exact (mix l (fun j=>x.eval (fun i=>f i j)) (fun j=>y.eval (fun i=>f i j)) a b).symm
lemma normEval (h:z.Covers P)(v:∀ x,P x→ ‖f x‖ ≤ c) : ‖z.eval f‖≤ c:=by induction z with
 | pin x=> exact v x h
 | turn x y a b p q s ih ig=>
      obtain ⟨u,t⟩:=(show Covers P x∧ Covers P y from h); let x':=x.eval f; let y':=y.eval f; apply (norm_add_le ((a:ℂ) • x') ((b:ℂ) • y')).trans; rw [norm_smul,norm_smul, Complex.norm_real,Complex.norm_real,Real.norm_of_nonneg p,Real.norm_of_nonneg q]; exact (add_le_add (mul_le_mul_of_nonneg_left (ih u) p) (mul_le_mul_of_nonneg_left (ig t) q)).trans_eq (by rw [←add_mul,s,one_mul])
-- also diff
end
end Knot
variable {T:Type}[NormedAddCommGroup T]
variable (r:ℝ)(z l:Knot T)
abbrev Tiny : Prop := z.Covers fun t=> ‖t‖<r
def fusion (z l: Knot T) : Knot T:=z.evolves fun i=>l.evolves fun j=> Knot.pin (i+j)
lemma fuse_tiny (p:Tiny (r/2) z)(g:Tiny (r/2) l):Tiny r (fusion z l):= Knot.evol_cov z _ _ p _ fun i h=> Knot.evol_cov l _ _ g _ fun j g=> (norm_add_le ..).trans_lt ((add_lt_add h g).trans_le (add_halves r).le)
section
variable [NormedAddCommGroup V] [NormedSpace ℂ V](Q:T→V){ε:ℝ}
lemma funded (F:T→V) : Knot.eval F (fusion z l)=z.eval (fun i=>l.eval (fun j=> F (i+j))):=by unfold fusion; rw [Knot.burrow]; refine congrArg (fun f:T→V=>z.eval f) (funext fun i=>?_ ); rw [Knot.burrow]; rfl
lemma funded_swap (F:T→V) : Knot.eval F (fusion z l)=Knot.eval F (fusion l z):=by rw [funded,funded,Knot.exchange]; simp [add_comm]
lemma Tiny.distEval (p:Tiny r z)(b:V)(c:∀ t:T,‖t‖<r→ dist (Q t) b≤ε) : dist (z.eval Q) b ≤ ε := by rw [dist_eq_norm,show z.eval Q-b=z.eval (fun i=>Q i-b) from (by rw [Knot.decr z Q (fun _=>b),Knot.lift])]; exact z.normEval _ _ p fun i h=> by have he:=c i h; rwa [dist_eq_norm] at he
end
variable {H:Hilbert}{B:Type} {m:ℝ}
variable (Q:Willow H T) (x:H)
local notation "P"=> planeP Q.Standard
local notation "Qs"=> Q.U
open Knot Willow
lemma Willow_take (p:0<r)(e:0 < m) : ∃ z:Knot T,Tiny r z∧ dist (z.eval (fun i=> (Qs) i x)) (P x) ≤ m:=by
 obtain ⟨y,p,t⟩:= atGate Q x r p m e; let f(i:T):=(Qs) i x
 have hx:∃ z:Knot T,Tiny r z ∧ z.eval f=y:=by clear t; induction p with
    | glide x p=> exact ⟨Knot.pin _, p,rfl⟩
    | mount _ _ a b p q v ih ik=> obtain ⟨z,t,y⟩:=ih; obtain ⟨w,y',e⟩:=ik; exact ⟨turn z w a b p q v, And.intro t y',(congrArg₂ (·+·) (congrArg ((a:ℂ) •·) y) (congrArg ((b:ℂ) •·) e))⟩
 obtain ⟨s,p,t'⟩:=hx; refine ⟨s,p,?_⟩; change dist (s.eval f) _ ≤ _; rw [t',dist_comm,dist_eq_norm]; exact t.le
lemma spend (b m:ℝ)(c:0< m) (h:Tiny (r/2) z) (d: dist (l.eval (fun i=>(Qs) i x)) (P x)≤ b) (v:∀ i:T,‖i‖<r→dist (Qs i (P x)) (P x) ≤ m) : dist ((fusion z l).eval (fun i=> Q.U i x)) (P x) ≤ b+m:=by
 let f(i:T):= Q.U i x; change dist ((fusion z l).eval f) _≤ _; rw [funded]; apply Tiny.distEval (r/2) z _ h
 intro u e; have hx:l.eval (fun i=>f (u+i))=Q.U u (l.eval f):= Eq.trans (congrArg (fun F:T→H.space=>l.eval F) (funext fun i=>(Q.both_inner ..).symm)) (Knot.push (Q.U u).toLinearMap l f)
 change dist (l.eval _) _≤ _; rw [hx]; exact (dist_triangle _ (Q.U u (P x)) _).trans (add_le_add ((Q.keepD ..).trans_le d) (v u (by linarith [norm_nonneg u])))
lemma tiny_ball (c:0< m)(v:x∈Q.Standard) : ∀ᶠ r:ℝ in 𝓝[>] 0, ∀ i:T,‖i‖<r→dist (Q.U i x) x≤ m:=by
 obtain ⟨p,h,t⟩:= Metric.mem_nhds_iff.mp (Metric.tendsto_nhds.mp (show Q.AllowsR x from v) m c); filter_upwards [nhdsWithin_le_nhds (gt_mem_nhds h)] with i z y v; exact (show dist _ _<_ from t (show y∈ball (0:T) p from Metric.mem_ball.mpr (by simpa using (v.trans (show i<p from z))))).le
lemma twoWorld {U:Hilbert}(X:Willow U T)(y:U)(c:0< m) : ∀ᶠ r:ℝ in 𝓝[>] 0,∃ z:Knot T,Tiny r z ∧ dist (z.eval (fun i=> Q.U i x)) (P x)≤ m ∧ dist (z.eval (fun i=>X.U i y)) (planeP X.Standard y)≤ m :=by
 let e:=m/2; filter_upwards [tiny_ball Q (P x) (half_pos c) (through x), tiny_ball X _ (half_pos c) (through y), self_mem_nhdsWithin] with r hr hp v
 obtain ⟨l,t,d⟩:=Willow_take (r/2) Q x (half_pos (show 0<r from v)) (half_pos c); obtain ⟨z,t',d'⟩:=Willow_take (r/2) X y (half_pos (show 0<r from v)) (half_pos c);
 exact ⟨fusion z l,fuse_tiny r z l t' t,(spend r z l Q x e e (half_pos c) t' d hr).trans_eq (add_halves _),(congrArg (fun x:U.space=>dist x _) (funded_swap z l (fun i=> X.U i y))).le.trans ((spend r l z X y e e (half_pos c) t d' hp).trans_eq (add_halves _))⟩
#print axioms twoWorld
noncomputable section
variable (A:H.Op)
def faced (i:T):H.Op:= (Qs) i*A* Q.U (-i)
abbrev brace:= eval (faced Q A) z
#check brace
lemma advert (k:T→ H.Op)(x:H) : z.eval (fun i=>k i x) = (z.eval k) x := z.push ((ContinuousLinearMap.apply ℂ H.space x).toLinearMap) k -- signature
lemma tiny_eff (c:0 < m)(v:x∈Q.Standard) : ∀ᶠ r:ℝ in 𝓝[>] 0, ∀ z:Knot T,Tiny r z→ dist (brace z Q A x) (z.eval (fun i=> Q.U i (A x))) ≤ m:=by
 let a:=(‖A‖+1); have ha:0<a:=by positivity
 filter_upwards [tiny_ball Q x (div_pos c ha) v] with r p z h
 have hx(i:T)(e:‖i‖<r): ‖faced Q A i x-(Qs) i (A x)‖≤ m:= by
    unfold faced; simp_rw [mul_apply_eq_comp,←map_sub,(Q.keep)]; refine le_trans (A.le_opNorm _) ?_; have hm:=p (-i) (by rw [norm_neg]; exact e); rw [dist_eq_norm] at hm; apply (mul_le_mul_of_nonneg_left hm (norm_nonneg A)).trans; rw [mul_comm]; exact (mul_le_mul_of_nonneg_left (show ‖A‖≤a by unfold a; linarith) (div_nonneg c.le ha.le)).trans_eq (div_mul_cancel₀ m ha.ne') -- issue both sides rw m at hm ???
 change dist (z.eval (faced Q A) x) _≤ m; rw [←advert z (faced Q A),dist_eq_norm,←Knot.decr]; exact z.normEval _ _ h hx
lemma braceC : ‖brace z Q A‖≤ ‖A‖:=by
 have he(i:T): ‖Q.U i‖≤1:= ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y=>by rw [Q.keep,one_mul]
 exact z.normEval (fun _=>True) _ (z.every _ (fun _=>trivial)) fun i _=> (norm_mul_le ..).trans ((mul_le_mul ((norm_mul_le ..).trans (by apply le_trans (mul_le_mul_of_nonneg_right (he i) (norm_nonneg A)); rw [one_mul])) (he (-i)) (norm_nonneg _) (norm_nonneg _)).trans_eq (mul_one ..)) -- tune rw closure
lemma ask_s {G:Hilbert} (F:Willow G T)(B:G.Op)(y:G)(e:0 < m)(p:x∈Q.Standard)(h:y∈ F.Standard) : ∀ᶠ r:ℝ in 𝓝[>] 0,∃ z:Knot T,Tiny r z ∧ dist (brace z Q A x) ((P*A*P) x)≤ m ∧ dist (brace z F B y) ((planeP F.Standard*B*planeP F.Standard) y) ≤ m:=by
 let M:=m/2; filter_upwards [twoWorld Q (A x) F (B y) (half_pos e), tiny_eff Q x A (half_pos e) p, tiny_eff F y B (half_pos e) h] with r hp ht hK
 obtain ⟨z,a,g,v⟩:=hp; refine ⟨z,a,?_,?_⟩
 · rw [mul_apply_eq_comp,mul_apply_eq_comp,inlet p]; exact (dist_triangle _ _ _).trans ((add_le_add (ht z a) g).trans_eq (add_halves _))
 rw [mul_apply_eq_comp,mul_apply_eq_comp,inlet h]; exact (dist_triangle _ _ _).trans ((add_le_add (hK z a) v).trans_eq (add_halves _))
-- for any radius choose sequence of ensembles.Tiny deterministic sets.
lemma Tiny.inc {t}(z:Knot T)(p:Tiny t z)(u:t≤r): Tiny r z:= by induction z with
 | pin x=> exact lt_of_lt_of_le p u
 | turn l x a b p' q v ih ig=> exact And.intro (ih p.1) (ig p.2) -- tune unfold
lemma ask_p (c:0<r) {G:Hilbert}(F:Willow G T)(B:G.Op)(y:G)(p:x∈Q.Standard)(h:y∈ F.Standard) : ∃ Z:ℕ→ Knot T,(∀ i,Tiny r (Z i)) ∧ Tendsto (fun i=>brace (Z i) Q A x) atTop (𝓝 ((P*A*P) x)) ∧ Tendsto (fun i=>brace (Z i) F B y) atTop (𝓝 ((planeP F.Standard*B*planeP F.Standard) y)):=by
 let v (i:ℕ):=(1:ℝ)/(i+1:ℕ); have he(i:ℕ):∃ z:Knot T,Tiny r z ∧ dist (brace z Q A x) ((P*A*P) x)≤ v i ∧ dist (brace z F B y) ((planeP F.Standard*B*planeP F.Standard) y) ≤ v i:=by
    obtain ⟨t,p'⟩:= ((ask_s Q x A F B y (show 0<v i from by unfold v; positivity) p h).and (nhdsWithin_le_nhds (gt_mem_nhds c))).exists; obtain ⟨⟨z,hv,t⟩,u⟩:=p'; exact ⟨z,Tiny.inc r _ hv (show _<r from u).le,t⟩
 choose Z p w u using he; have h:Tendsto v atTop (𝓝 0):=by simpa only [v,Nat.cast_add,Nat.cast_one] using tendsto_one_div_add_atTop_nhds_zero_nat
 refine ⟨Z,p, Metric.tendsto_nhds.mpr fun ε e=>?_,Metric.tendsto_nhds.mpr fun ε e=>?_⟩
 · filter_upwards [h.eventually (gt_mem_nhds e)] with i t; exact (w i).trans_lt t
 filter_upwards [h.eventually (gt_mem_nhds e)] with i t; exact (u i).trans_lt t
#print axioms ask_s
end
end YM.CF.Buffered.Afterglow.Hierarchy.Endless.Piper
