import YM.SU5.FiniteGaugeData.Marked.Journey.Perch

/-!
# Rolls, all resolutions on one actual course. Prove joint directly on paths
(only those on the chosen sequences). One universal buyer for all `TestFamily
true` and levels. Include normalized products and RP at limiting readings.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Journey
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py.Rate Py.Rate.LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1 ≤ Λ.x) (s i k:ℕ)
local notation "K"=> tent Y H
local notation "Ω" i:max=> (K).c (momentm Y i s)
local notation "σ" i:max=> side Y i s
local notation "ρ" i:max=> (Y.voyage i).CapeT s
local notation "L" i:max=> deltaL Y H i s
local notation "m" i:max=> momentm Y i s

def sharp (a:Family (tent Y H)):= listen Y H i k s (a (m i))
def hot (a:Family (tent Y H)):=if p:(Y.voyage i).kick ≤ k then collector Y H i k p s (a (m i)) else 0
lemma qualify (S:Finset Cover)(a:Chorus)(w:Bracket S a)(u:Purse S)(p:Ferry Y s i k): hot Y H s i k (note K u.val a)=output Y H s S a u i k:=by
  unfold hot output counter; rw [dif_pos p.depth,dif_pos ⟨p,w⟩]
private lemma envCast {i k:Side}{l:Loom k}{f:Mark i}{b:ℝ}(h:i=k) (p:Measurable l) (hx:Envelope f)(w:∀ x,‖f x‖≤ b) :
    let g:Mark k:=h ▸ f; let Q:=g∘drawn l
    Envelope Q ∧ ∀ x,‖Q x‖≤ b:=by subst i; exact ⟨mark_pay p hx,fun x=> w _⟩
private lemma envCast' {i k:Side}{f:Mark i}(h:i=k) (hx:Envelope f):Envelope (show Mark k from h ▸ f):= by subst i; exact hx

variable {S:Finset Cover}{f:Family (tent Y H)}
lemma valuation {b:Bool}(w:InTest (tent Y H) true S b f): ∃ v:ℝ,∀ (i:Side)(x:Fields ((K).c i)),‖f i x‖ ≤ v:= by
  induction w using @InTest.rec with
  | @seed f p=>
    obtain ⟨d,h⟩:=p.env.cost
    refine ⟨d,fun i x=>?_⟩; change ‖_ • (1: Fock.FC (Single ((K).c i)))‖≤_; rw [norm_smul,norm_one,mul_one]; exact h _
  | @creator x i b p _=> exact ⟨1,fun y v=> by have hp:= Sound.moderate K y v (x,i,b); simpa [Sound.chord, p] using hp⟩
  | @remover x i b p _=> exact ⟨1,fun y v=> by have hp:= Sound.moderate K y v (x,i,b); simpa [Sound.chord,p] using hp⟩
  | zero=> exact ⟨0,by simp⟩
  | one=> exact ⟨1, fun i x=> (norm_one : ‖(1:Fock.FC (Single ((K).c i)))‖=1).le⟩
  | add _ _ t r=> obtain ⟨a,h⟩:=t; obtain ⟨u,v⟩:=r; exact ⟨a+u,fun i x=> (norm_add_le ..).trans (add_le_add (h ..) (v ..))⟩
  | mul _ _ t r=> obtain ⟨a,h⟩:=t; obtain ⟨u,v⟩:=r; exact ⟨a*u,fun i x=> (norm_mul_le ..).trans (mul_le_mul (h i x) (v i x) (norm_nonneg _) ((norm_nonneg _).trans (h i x)))⟩
  | smul a _ t=> obtain ⟨v,g⟩:= t; refine ⟨‖a‖*v,fun i x=>?_⟩; rw [Pi.smul_apply,Pi.smul_apply,norm_smul]; exact mul_le_mul_of_nonneg_left (g i x) (norm_nonneg _)

variable {i k}
lemma rate (x:TestFamily (tent Y H) true f)(e:ℝ)(q:0<e): ∀ᶠ k:ℕ in atTop,∀ i:ℕ,(Y.voyage i).kick ≤ k → ‖sharp Y H s i k f - hot Y H s i k f‖ ≤ e:=by
  obtain ⟨S,w⟩:=x.paid
  obtain ⟨v,u⟩:= valuation Y H w
  have hv:0 ≤ v:= (norm_nonneg _).trans (u 1 (1,1)); have h:0<v+1:=by positivity
  filter_upwards [Y.thaw s (e/(v+1)) (div_pos q h)] with k t i p
  have he:v≤ v+1:=by linarith
  obtain ⟨hx,V⟩:= envCast (terrain Y H (Y.ir i) s) ((Y.voyage i).ownership s).paid.bill (w.support (m i)).env (fun x=> (u _ x).trans he)
  let g:= (send Y H i s (f (m i))) ∘ drawn (ρ i)
  change Envelope g at hx
  unfold hot; rw [dif_pos p]
  exact (t i p g (v+1) hx.meas V).trans (div_mul_cancel₀ e h.ne').le


lemma hot_add {g:Family (tent Y H)}(x:TestFamily (tent Y H) true f)(v:TestFamily (tent Y H) true g)(p:Ferry Y s i k):hot Y H s i k (f+g)=hot Y H s i k f+hot Y H s i k g:=by
  obtain ⟨S,e⟩:=x.paid; obtain ⟨s',w⟩:=v.paid
  unfold hot; rw [dif_pos p.depth,dif_pos p.depth,dif_pos p.depth]
  exact (boxprice Y H i k p.depth s p.fire p.enters).sum _ _ (e.support _).env (w.support _).env
lemma hot_mul {f:Family (tent Y H)}(a:ℂ)(p:Ferry Y s i k):hot Y H s i k (a • f)=a*hot Y H s i k f:=by
  unfold hot; rw [dif_pos p.depth,dif_pos p.depth]
  exact (boxprice Y H i k p.depth s p.fire p.enters).mult _ _
lemma paid {p:Ferry Y s i k}(x:TestFamily (tent Y H) true f) :
    let a:=send Y H i s (f (m i)); let v:= ((Y.voyage i).X (Y.uv k)).gram s; let T:=ρ i; let Z:= partitionZ v Λ.U T
    Integrable (fun x=> inner ℂ (Dial.mateK (σ i)) (acts (a (drawn T x)) (denZ v Λ.U T x))) (city (σ i)) ∧ Z≠0 ∧
      sharp Y H s i k f=(∫ x, inner ℂ (Dial.mateK (σ i)) (acts (a (drawn T x)) (denZ v Λ.U T x)) ∂city (σ i))/Z := by
  intro a v T Z; obtain ⟨s',e⟩:=x.paid
  have hp: Measurable T:= ((Y.voyage i).ownership s).paid.bill
  have hv:Envelope a:= envCast' (terrain Y H (Y.ir i) s) (e.support _).env
  exact ⟨mark_integrable hp hv (Marks.can_read _ _ v T p.fire.priceA),p.fire.priceA.valid,rfl⟩

structure Cabinet (Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)(u v:ℕ→ℕ):Prop where
  grow_i: StrictMono u
  grow_k: StrictMono v
  ticket (i k:ℕ): legacy Y (u i) (v k) → (Y.voyage (u i)).kick ≤ v k
  prices(s:ℕ)(S:Finset Cover)(a:Chorus)(x:Purse S): ∃ F z,Couplet u v (output Y H s S a x) F z (fun e=> ∀ᶠ r in atTop,legacy Y (u r) (v (e r)))
namespace Cabinet
variable {u v:ℕ→ℕ}(p:Cabinet Y H u v)
local notation "inCone" z:max=> ∀ᶠ r in atTop,legacy Y (u r) (v (z r))
private abbrev Fig (X:Family K) (F:ℕ→ℂ) (z:ℂ) := Couplet u v (fun i k=> hot Y H s i k X) F z (fun z=> inCone z)
include p
lemma pass (s:ℕ)(i:ℕ):∀ᶠ k:ℕ in atTop,Ferry Y s i (v k):= p.grow_k.tendsto_atTop.eventually (ferry_later ..)
lemma walks {z:ℕ→ℕ}(h:inCone z):Tendsto (fun r=>v (z r)) atTop atTop:=by
    let a:= ((tendsto_pow_atTop (α:=ℕ) (by decide : (5:ℕ) ≠ 0)).comp (Y.ir_grows.comp p.grow_i).tendsto_atTop)
    refine tendsto_atTop.2 (fun i=> ?_)
    filter_upwards [h,a.eventually_ge_atTop (Y.uv i)] with k h p
    exact Y.uv_grows.le_iff_le.mp (p.trans h)
lemma cone_ferry {z:ℕ→ℕ}(h:inCone z): ∀ᶠ r in atTop,Ferry Y s (u r) (v (z r)):=
  (((p.walks Y H h).eventually (ferry_all Y s)).and h).mono (fun i v=> v.1 _ (p.ticket i _ v.2))

lemma recursion (x:TestFamily (tent Y H) true f): ∃ F z, Fig Y H s (u:=u) (v:=v) f F z:=by
  obtain ⟨s',e⟩:=x.paid
  have ht {f:Family K}(w:f∈arias K s' false): TestFamily K true f:=⟨⟨s',test_span w⟩,fun u=>by contradiction⟩
  refine Submodule.span_induction (p:=fun f _=>∃ F z,Fig Y H s (u:=u) (v:=v) f F z) (fun f h=>?_) ?_ ?_ ?_ (whole e)
  · obtain ⟨f',y,q,t,z,rfl⟩:= h; let g:=p.prices s s' y ⟨f',q⟩; obtain ⟨F,Z,w⟩:=g
    have G(i k:ℕ)(x:Ferry Y s i k): output Y H s s' y ⟨f',q⟩ i k=hot Y H s i k (note K f' y):=(qualify Y H s i k s' y ⟨t,z⟩ _ x).symm
    exact ⟨F,Z,⟨(fun n=> (w.inner n).congr' ((p.pass Y H s n).mono fun _=>G n _)),w.periods,(fun a h=> (w.paths a h).congr' ((p.cone_ferry Y H s h).mono fun _=>G _ _))⟩⟩
  · have g i k (h:Ferry Y s i k): hot Y H s i k 0=0:=by simpa only [zero_smul,zero_mul] using (hot_mul Y H s (f:=0) 0 h)
    exact ⟨0,0,⟨(fun n=>tendsto_const_nhds.congr' ((p.pass Y H s n).mono fun _ h=> (g _ _ h).symm)),tendsto_const_nhds,(fun _ h=>tendsto_const_nhds.congr' ((p.cone_ferry Y H s h).mono fun _ h=> (g _ _ h).symm))⟩⟩
  · intro x y hx hy F G; obtain ⟨A,z,a⟩:=F; obtain ⟨B,c,b⟩:=G
    exact ⟨A+B,z+c,⟨fun n=> ((a.inner n).add (b.inner n)).congr' ((p.pass Y H s n).mono fun _ h=> (hot_add Y H s (ht hx) (ht hy) h).symm),a.periods.add b.periods,fun e t=> ((a.paths e t).add (b.paths e t)).congr' ((p.cone_ferry Y H s t).mono fun _ h=> (hot_add Y H s (ht hx) (ht hy) h).symm)⟩⟩
  intro a x _ F; obtain ⟨X,z,e⟩:=F
  exact ⟨a • X,a*z,⟨fun n=> ((e.inner n).const_mul a).congr' ((p.pass Y H s n).mono fun _ h=> (hot_mul Y H s a h).symm),e.periods.const_mul a,fun v h=> ((e.paths v h).const_mul a).congr' ((p.cone_ferry Y H s h).mono fun _ h=> (hot_mul Y H s a h).symm)⟩⟩

private abbrev FigA (X:Family K)(F:ℕ→ℂ)(z:ℂ):= Couplet u v (fun i k=> sharp Y H s i k X) F z (fun z=> inCone z)
lemma both (x:TestFamily (tent Y H) true f): ∃ F z, Fig Y H s (u:=u) (v:=v) f F z ∧ FigA Y H s (u:=u) (v:=v) f F z:=by
  obtain ⟨F,z,t⟩:=p.recursion Y H s x
  let δ (i k):= sharp Y H s i k f-hot Y H s i k f
  have he (n e:ℕ→ℕ)(a:Tendsto e atTop atTop)(hp:∀ᶠ i:ℕ in atTop,(Y.voyage (n i)).kick ≤ e i): Tendsto (fun i=>δ (n i) (e i)) atTop (𝓝 0):= by
    refine Metric.tendsto_nhds.mpr fun r h=> ?_
    filter_upwards [a.eventually (rate Y H s x _ (half_pos h)),hp] with y v t
    rw [dist_zero_right]; exact (v _ t).trans_lt (by linarith)
  refine ⟨F,z,t,⟨?_,t.periods,?_⟩⟩
  · intro n; simpa only [δ,sub_add_cancel,zero_add] using (he (fun _=> n) v p.grow_k.tendsto_atTop ((p.pass Y H s n).mono (fun _ h=> h.depth))).add (t.inner n)
  intro v' h
  simpa only [δ,sub_add_cancel,zero_add] using (he u _ (p.walks Y H h) ((p.cone_ferry Y H s h).mono fun _ h=> h.depth)).add (t.paths v' h)
-- total definitions for both limits, at once; the marks qualified in the
-- corollary (and even their gauge non-invariant Borel extension)
def field (f:Family K):ℕ→ ℂ := if x:TestFamily K true f then (p.both Y H s x).choose else 0
def audience (f:Family K):ℂ:= if x:TestFamily K true f then (p.both Y H s x).choose_spec.choose else 0
lemma booked (x: TestFamily K true f):Fig Y H s (u:=u) (v:=v) f (p.field Y H s f) (p.audience Y H s f) ∧
    Couplet u v (fun i k=> sharp Y H s i k f) (p.field Y H s f) (p.audience Y H s f) (fun z=> inCone z):=by
  rw [field,audience,dif_pos x,dif_pos x]; exact (p.both Y H s x).choose_spec.choose_spec
end Cabinet
end YM.CF.Buffered.Afterglow.Journey
#print axioms YM.CF.Buffered.Afterglow.Journey.Cabinet.booked
