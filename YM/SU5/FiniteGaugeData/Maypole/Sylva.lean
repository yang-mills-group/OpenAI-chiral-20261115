import YM.SU5.FiniteGaugeData.Maypole.Scythe
/-! # Lift, on the word domain of the actual estimate -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin
open Filter Function Set OS OS.Semigroup Mink Mink.General Mink.Lorentz Complex Flute MeasureTheory Boundary Probe
open scoped Topology ContDiff NNReal InnerProductSpace
local notation "tt"=>timeAxis
variable {H:Hilbert}{α:Type}(M':Canopy H α)(S: OS.Semigroup H timeAxis)(Ω:Bench S)(hΩ:∀ z:E4,M S z Ω.val=Ω.val)
variable {n:ℕ} (p q:Mink.Poincare)
namespace Canopy
open _root_.YM.CF.Buffered.Afterglow.Hierarchy.Seld.Vp.Luft
variable (t u:M'.Token)(chip:M'.Chip)(g:Test4)(w:List M'.Token)
local notation "D"=>Bench S
local notation "£" x:max=>M'.dep x
local notation "V"=>M'.stampL
local notation "★"=> M'.Wval S Ω
local notation "p₀" g:max=>Mink.Poincare.motion g
variable (F:M'.Warrant S Ω)(pB:∀ b:Mink.Ray,Shelf S (reduced (magnet b)))(z:Fin n→ M'.Chip) (x:Fin n→Test4)
variable (t:Mink.Lorentz)
include F hΩ pB
lemma stationaryK (u:Pin t): Wval M' S Ω z x=★ (M'.stampL t z) (active (p₀ t) x):= by
 let b:=Mink.Ray.fromAxis 0; apply roomV S Ω.val _ _ _ b (pB b) t u _ Ω hΩ x rfl; exact ((show M'.stampL t z=M'.stampE (polar t u) z from funext fun i=> congrArg (Sigma.mk (z i).fst) (DFunLike.congr_fun ((M'.P (z i).fst).pin t u) _)) ▸ F.supports n z _)
lemma villing(e:Mink.Ray)(r:ℝ)(t:Sleeps r): Wval M' S Ω z x= ★ (V (e.boost r) z) (active (p₀ (e.boost r)) x):= by
 let xF(y:ℂ)(i:Fin n):= let v:= z i; M'.flash v.fst ((M'.P v.fst).link e y v.snd); let P:=M'.stampL (e.boost r) z; have he(t:ℝ):M'.senses (M'.stampE (moveB e t) z)= xF t:=funext fun i=> by change M'.flash _ ((M'.P (z i).fst).E (moveB e t) _) =_; rw [(M'.P _).base]
 apply spit S (M'.senses z) (M'.senses P) (M'.credit z) e (pB e) r Ω hΩ x xF _ (fun x=> he x ▸ F.supports n z _) (funext fun i=> by change M'.flash _ _=M'.flash ((z i).fst) ((M'.P (z i).fst).L (e.boost r) (z i).snd); rw [(M'.P _).journey]) t
 intro i x; let v:=z i; let p:= M'.P v.fst; let J:= ContinuousLinearMap.apply ℂ (colorP p.amount) v.snd; exact (M'.flash v.fst).analyticAt _|>.comp (J.analyticAt _|>.comp (p.ink e x))
omit F hΩ pB
abbrev Envision (t:Mink.Lorentz): Prop:= ∀ (n:ℕ)(v:Fin n→ M'.Chip)(x:Fin n→ Test4),Wval M' S Ω v x = Wval M' S Ω (M'.stampL t v) (active (p₀ t) x)
lemma trades {x y:Mink.Lorentz}(p:M'.Envision S Ω x)(q: M'.Envision S Ω y):M'.Envision S Ω (x*y):=fun n v f=> by
 refine Eq.trans (q n v f) ((p n (V y v) (active (p₀ y) f)).trans ?_); rw [tailor, ← Poincare.overL, show M'.stampL x (M'.stampL y v)=M'.stampL (x*y) v from funext fun i=> Lmult M' _ _ _]
include F hΩ pB
lemma jealous (e:Mink.Ray)(r:ℝ): Envision M' S Ω (e.boost r):= by
 obtain ⟨ε,h,g⟩:= sleeps; let E(q:ℝ):=M'.Envision S Ω (e.boost q); have he: ∀ t:ℝ, |t|≤ ε→E t:=fun t v n z x=>villing M' S Ω hΩ F pB z x e t (g _ v); have ht(x y:ℝ)(h:E x)(p:E y): E (x+y):=by unfold E; exact (show e.boost x*e.boost y=e.boost (x+y) from (e.boost_add ..).symm) ▸ trades M' S Ω h p
 obtain ⟨N,v⟩:= exists_nat_gt (|r|/ε); have hz:0<(N:ℝ):= by exact lt_of_le_of_lt (by positivity) v
 let z:= r/(N:ℝ); have hp: |z|≤ε:=by unfold z; rw [abs_div,abs_of_nonneg hz.le]; rw [div_le_iff₀ hz]; rw [div_lt_iff₀ h] at v; linarith
 have hy(n:ℕ): E (n • z):=by induction n with | zero=> rw [zero_smul]; exact he _ (by rw [abs_zero]; exact h.le)| succ n ih=> rw [add_smul,one_smul]; exact ht _ _ ih (he _ hp)
 exact (show N • z=r from (by unfold z; rw [nsmul_eq_mul]; field_simp)) ▸ hy N
lemma weeping(t:Lorentz): Envision M' S Ω t:=by obtain ⟨e,s,H,h,rfl⟩:=nilBoost t; refine trades M' S Ω (jealous M' S Ω hΩ F pB e s) (fun n y g=>?_); exact stationaryK M' S Ω hΩ F pB y g H h
local notation "L"=> M'.Ticket S Ω
local notation "Q"=> M'.EVal S Ω
local notation "Nt"=> M'.moved
lemma amberV (K: Mink.Lorentz): Q (Nt (p₀ K) w)=Q w:= by
 suffices he:∀ n (t: Fin n→ M'.Token), Q (Nt (Poincare.motion K) (List.ofFn t))=Q (List.ofFn t) from List.ofFn_get w ▸ he w.length w.get
 intro n t; unfold moved; rw [List.map_ofFn,←worlddoc, ←worlddoc]; exact (weeping M' S Ω hΩ F pB K n (fun i=>(t i).1) (fun i=>(t i).2)).symm
lemma voyageV (p:Mink.Poincare): Q (Nt p w)=Q w:=by
 let p':= Poincare.translation p.b; let K:=Poincare.motion p.Λ; rw [show p=p'*K from by apply Poincare.ext <;> simp [p',K,Poincare.translation,Poincare.motion], ← joins]; unfold EVal Ticket; rw [← bring _ _ _ hΩ]
 nth_rw 1 [← hΩ p.b]; let z:=Nt K w; change inner ℂ (M S p.b Ω.val) (M S p.b (L z))=_; rw [tsees]; exact amberV M' S Ω hΩ w F pB p.Λ
lemma grainV (v:List M'.Token): inner ℂ (L (Nt p w)) (L (Nt p v))=inner ℂ (L w) (L v):=by
 suffices he:∀ (x:List M'.Token)(y:List M'.Token), inner ℂ (L x) (L y)=Q ((x.map M'.reve).reverse++y) by
    let W:=travel M' p; rw [he,he,← show Nt p ((w.map M'.reve).reverse++v) = (((Nt p w).map M'.reve).reverse++(Nt p v)) from (by simp only [moved,List.map_append, List.map_reverse,List.map_map]; rw [show W ∘ M'.reve=M'.reve ∘ W from funext (travel_reveal M' p)]), M'.voyageV S Ω hΩ _ F pB]
    -- tune applies.M'
 intro x; induction x with
 | nil=> exact fun y=>rfl
 | cons i x ih=> intro y; unfold Ticket; rw [planeV,legPaid]; change inner ℂ (L x) (L (M'.reve i::y))= _; rw [ih]; simp
#print axioms jealous
#print axioms grainV
variable (E:M'.Climb S Ω=⊤)
include E
lemma Hatchment : ∃ Z:H.Op,M'.Use S Ω p Z∧ ‖Z‖≤1:=by
 let Ve(f):= L (M'.moved p f); let h:= Hat M' S Ω E; let T:= Finsupp.linearCombination ℂ Ve; have he(w:List M'.Token →₀ ℂ):inner ℂ (T w) (T w)=inner ℂ (h.stems w) (h.stems w):=by
    let L':= L; change inner ℂ (T w) (T w)=inner ℂ (Finsupp.linearCombination ℂ L' w) (Finsupp.linearCombination ℂ L' w); unfold T; simp only [Finsupp.linearCombination_apply,Finsupp.sum,sum_inner,inner_sum, inner_smul_left,inner_smul_right]; have ht(i j): inner ℂ (Ve i) (Ve j)=inner ℂ (L' i) (L' j):= grainV M' S Ω hΩ p i F pB j
    simp only [ht]
 suffices ht: ∀ f,‖T f‖ ≤ 1*‖h.stems f‖ from let ⟨U,b,q⟩:= Kernel.Gram.by_bound h Ve 1 zero_le_one ht; ⟨U,q,b⟩
 intro f; rw [one_mul,@norm_eq_sqrt_re_inner ℂ, he f,←@norm_eq_sqrt_re_inner ℂ]
omit hΩ F pB in
private lemma muscleV (Ve:Mink.Poincare→ H.Op)(p:∀ g,M'.Use S Ω g (Ve g))(q:∀ g,‖Ve g‖≤1)(y:H): Continuous fun g=> Ve g y:=by
 let T:=M'.Hat S Ω E
 have he(g:Mink.Poincare)(w): Ve g (M'.Ticket S Ω w)=M'.Ticket S Ω (M'.moved g w):=p g w
 let TT:= Finsupp.linearCombination ℂ (L); have hTT: DenseRange TT:= T.whole
 have hv (t: List M'.Token→₀ℂ): Continuous (fun x => (Ve x) (TT t)) := by
    induction t using Finsupp.induction_linear with
    | zero => simp only [map_zero]; exact continuous_const
    | add i j hi hj => simp_rw [map_add]; exact hi.add hj
    | single x k=> simp_rw [TT,Finsupp.linearCombination_single,map_smul]; change Continuous (fun t=> k • (Ve t (L x))); simp_rw [he]; exact continuous_const.smul (lifting ..)
 have Hk(g:Mink.Poincare)(u:H): ‖Ve g u‖≤‖u‖:= ((Ve g).le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) (q g))
 refine continuous_iff_continuousAt.mpr fun x=>Metric.tendsto_nhds.mpr fun ε hε=>?_
 obtain ⟨_,⟨f,rfl⟩,h⟩:= Metric.mem_closure_iff.mp (hTT y) (ε/4) (by positivity)
 have Hx(g:Mink.Poincare): dist (Ve g y) (Ve g (TT f)) < ε/4:=by rw [dist_eq_norm,←map_sub]; exact lt_of_le_of_lt (Hk ..) ((dist_eq_norm y (TT f)) ▸ h)
 filter_upwards [Metric.tendsto_nhds.mp ((hv f).tendsto x) (ε/4) (by positivity)] with z hz
 have h₁:= dist_triangle (Ve z y) (Ve z (TT f)) (Ve x y); have h₂:= dist_triangle (Ve z (TT f)) (Ve x (TT f)) (Ve x y); rw [dist_comm (Ve x (TT f))] at h₂; linarith [Hx z,Hx x]
-- Some parameters included.E/h.W.WH future.
theorem actionR : ∃ Ve: Boundary.Action H, ∀ p:Mink.Poincare, M'.Use S Ω p (Ve.V p):=by
 choose U ht h using fun (p:Mink.Poincare)=> M'.Hatchment S Ω hΩ p F pB E
 have v(p:Mink.Poincare)(w): U p (L w) = L (M'.moved p w):= ht p w
 have he: U 1=1:= arch_eq M' S Ω E _ _ fun i=>by rw [v,stayed]; rfl
 have hp(p q:Mink.Poincare): U (p*q)=U p*U q:= arch_eq M' S Ω E _ _ fun i=>by change _= U p (U q (L i)); rw [v,v,v,joins]
 refine ⟨⟨U,he,hp,?_,muscleV M' S Ω E U ht h⟩,ht⟩
 let fee(p:Mink.Poincare)(u:H): ‖U p u‖≤‖u‖:= ((U p).le_opNorm u).trans (mul_le_of_le_one_left (norm_nonneg _) (h p)); intro p y; refine le_antisymm (fee p y) ?_; have hz: U p⁻¹ (U p y)=y:= DFunLike.congr_fun (show U p⁻¹*U p=1 from by rw [←hp,inv_mul_cancel,he]) y; nth_rw 1 [← hz]; exact fee p⁻¹ (U p y)
#print axioms actionR
end Canopy
end YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin
